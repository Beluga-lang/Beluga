open Support
open Beluga
open Beluga_syntax.Syncom
open Beluga_syntax.Synint

module F = Fun
module P = Prettyint.DefaultPrinter

module Disambiguation_state = Beluga_parser.Parser.Disambiguation_state
module Disambiguation = Beluga_parser.Parser.Disambiguation
module Indexing_state = Index_state.Indexing_state
module Indexer = Index.Indexer

let dprintf, _, _ = Debug.(makeFunctions' (toFlags [15]))
open Debug.Fmt

type t =
  { disambiguation_state : Disambiguation_state.state
  ; indexing_state : Indexing_state.state
  ; theorems : Theorem.t DynArray.t
  ; finished_theorems: (Theorem.t * Comp.exp option) DynArray.t
  ; mutual_group : Id.cid_mutual_group
  }

let make disambiguation_state indexing_state mutual_group thms =
  { disambiguation_state
  ; indexing_state
  ; theorems = DynArray.of_list thms
  ; finished_theorems = DynArray.make 32
  ; mutual_group
  }

let with_disambiguation_state state f =
  Disambiguation_state.with_bindings_checkpoint state.disambiguation_state f

let with_indexing_state state f =
  Indexing_state.with_bindings_checkpoint state.indexing_state f

(** Gets the list of mutual declarations corresponding to the
        currently loaded theorems in the active session.
 *)
let get_mutual_decs (s : t) : Comp.total_dec list =
  Store.Cid.Comp.lookup_mutual_group s.mutual_group

(** Constructs a list of all theorems in this session, both
    incomplete and finished.

    The incomplete theorems come before the complete theorems.
 *)
let full_theorem_list c =
  DynArray.to_list c.theorems
  @ List.map Pair.fst (DynArray.to_list c.finished_theorems)

let remove_current_theorem s =
  DynArray.delete s.theorems 0

let mark_current_theorem_as_proven s e_trans =
  let t = DynArray.get s.theorems 0 in
  remove_current_theorem s;
  DynArray.add s.finished_theorems (t, e_trans)

let defer_theorem s =
  let t = DynArray.get s.theorems 0 in
  remove_current_theorem s;
  DynArray.add s.theorems t

(** Gets the next theorem from the interpreter state.
        Returns `None` if there are no theorems left,
        i.e. all theorems in the mutual block have been proven.
 *)
let next_theorem s : Theorem.t option =
  DynArray.head s.theorems

(** Decides whether a given `cid` is in among the currently being
        proven theorems. *)
let cid_is_in_current_theorem_set s c =
  List.exists (F.flip Theorem.has_cid_of c) (DynArray.to_list s.theorems)

(** Infer invocation kind based on `exp_syn` and the current theorem
 *)
let infer_invocation_kind s (i : Comp.exp) : Comp.invoke_kind =
  match Comp.head_of_application i with
  | Comp.Const (_, c) when cid_is_in_current_theorem_set s c -> `ih
  | _ -> `lemma

let lookup_theorem c name =
  let open Option in
  DynArray.rfind_opt_idx
    c.theorems
    F.(flip Theorem.has_name_of name)
  $> Pair.snd

(** Selects a theorem by name in the current session.
        Returns whether the selection succeeded. (A theorem by such name could be found.)
 *)
let select_theorem c name =
  match
    DynArray.rfind_opt_idx
      c.theorems
      (F.flip Theorem.has_name_of name)
  with
  | None -> false
  | Some (i, t) ->
     DynArray.delete c.theorems i;
     DynArray.insert c.theorems 0 t;
     true

let get_session_kind c : [`introduced | `loaded] =
  let existing_holes = Holes.get_harpoon_subgoals () in
  (* If the theorems in the session do not have
   * any predefined holes in the loaded files,
   * that session is newly defined in this harpoon process,
   *)
  let is_loaded =
    full_theorem_list c
    |> List.exists
         begin fun thm ->
         existing_holes
         |> List.map (fun (_location, cid, _state) -> cid)
         |> List.exists (Theorem.has_cid_of thm)
         end
  in
  if is_loaded
  then `loaded
  else `introduced

let prepare_translated_proofs tes total_decs =
  let trans_name name =
    Name.mk_some_string ("_" ^ Name.show name ^ "_trans")
  in
  (* create the totality declarations for the translated
         proofs, and allocate the mutual group with them. *)
  let total_decs =
    List.map
      (fun dec ->
        let open Comp in
        { dec with name = trans_name dec.name })
      total_decs
  in
  let mutual_group_id =
    Store.Cid.Comp.add_mutual_group total_decs
  in
  (* map from old cids to new cids *)
  let h = Hashtbl.create 8 in
  let etaus =
    List.map
      begin fun (t, e) ->
      let cid, entry = Theorem.get_entry' t in
      let tau = entry.Store.Cid.Comp.Entry.typ in
      let _ =
        (* the type to store for the newly allocated must be without
        inductive stars, so we obtain it directly from the store entry
        for the proof. *)
        Store.Cid.Comp.add
          begin fun cid' ->
          (* associate the cid of this theorem to the newly allocated
                 cid for the translated proof *)
          Hashtbl.add h cid cid';
          Store.Cid.Comp.mk_entry
            (trans_name entry.Store.Cid.Comp.Entry.name)
            tau
            entry.Store.Cid.Comp.Entry.implicit_arguments
            mutual_group_id
            None
          (* We use None for the declaration number here.
             This technically means that these definitions are
             considered floating. However, this will not be a problem
             during late scopechecking because definitions belonging
             to the same mutual group skip late scopechecking. *)
          end
      in
      (* we need to check the translated proof against the type *with*
      inductive stars, so we obtain it from the initial subgoal of the
      theorem *)
      let tau_ann = Theorem.get_statement t |> Whnf.cnormCTyp in
      (e, tau_ann)
      end
      tes
  in
  (* Now h is populated, so we can rewrite the programs with the
         new cids.
         First, convert the hashtable to a function sending unmapped
         entries to themselves.
   *)
  let cid_map k =
    Hashtbl.find_opt h k |> Option.value ~default:k
  in
  let etaus =
    List.map
      (fun (e, tau) -> (CidProgRewrite.exp cid_map e, tau))
      etaus
  in
  (etaus, total_decs)

type translation_check_result =
  [ `some_translations_failed
  | `check_error of exn
  | `ok
  ]

(** Checks the translated proofs in the session.
        All theorems in the session must be finished.

        This function will allocate one new mutual group, and for each
        theorem, a new cid for the translated proof.
        Next, it will rewrite the cids in each translated proof to
        refer to the new cids.
        Finally, it checks each program.
 *)
let check_translated_proofs c : translation_check_result =
  match
    DynArray.to_list c.finished_theorems
    |> List.traverse (fun (t, e) -> let open Option in e $> fun e -> (t, e))
  with
  | None -> `some_translations_failed
  | Some tes ->
     let ettaus, total_decs =
       prepare_translated_proofs tes (get_mutual_decs c)
     in
     dprintf begin fun p ->
       let open Format in
       p.fmt "[check_translated_proofs] @[<v>total_decs:\
              @,@[%a@]@]"
         (pp_print_list ~pp_sep: pp_print_cut
            P.fmt_ppr_cmp_total_dec)
       total_decs
       end;
     try
       List.iter
         (fun (e, tau) ->
           dprintf begin fun p ->
             p.fmt "[check_translated_proofs] statement @[%a@]"
               P.(fmt_ppr_cmp_typ LF.Empty l0) tau
             end;
           Check.Comp.check None LF.Empty LF.Empty total_decs
             e (tau, Whnf.m_id))
         ettaus;
       `ok
     with
     | exc -> `check_error exc

let parse_quit_or_theorem_identifier_opt location input =
  let open Beluga_parser in
  let open Parser in
  let token_sequence = Lexer.lex_string ~initial_location:location input in
  let parsing_state =
    Parser_state.initial ~initial_location:location token_sequence
  in
  let quit =
    Parsing.(
      colon &> keyword "quit" $> (fun () -> `quit) |> labelled "`:quit'")
  in
  let theorem_name =
    Parsing.(
      identifier
      $> (fun identifier -> `theorem_name identifier)
      |> labelled "Theorem identifier")
  in
  Parsing.(eval_exn (only (maybe (alt quit theorem_name))) parsing_state)

let prompt_quit_or_theorem_identifier_opt io =
  Io.prompt_input io ~msg:"  Name of theorem (:quit or empty to finish): "
    ~history_file:None parse_quit_or_theorem_identifier_opt

let parse_harpoon_totality_declaration_opt location input =
  let open Beluga_parser in
  let open Parser in
  let token_sequence = Lexer.lex_string ~initial_location:location input in
  let parsing_state =
    Parser_state.initial ~initial_location:location token_sequence
  in
  Parsing.(
    eval_exn
      (only
         (maybe
            (alt trust_totality_declaration numeric_totality_declaration)))
      parsing_state)

let disambiguate_harpoon_totality_declaration disambiguation_state
    totality_declaration =
  Disambiguation_state.with_bindings_checkpoint disambiguation_state
    (fun disambiguation_state ->
      Disambiguation.disambiguate_totality_declaration disambiguation_state
        totality_declaration)

let read_harpoon_totality_declaration_opt disambiguation_state location input
    =
  let totality_declaration_opt =
    parse_harpoon_totality_declaration_opt location input
  in
  Option.map
    (fun totality_declaration ->
      disambiguate_harpoon_totality_declaration disambiguation_state
        totality_declaration)
    totality_declaration_opt

let rec elaborate_totality_order :
          'a.
          'a Synext.signature_totality_order -> 'a Synint.Comp.generic_order
    = function
  | Synext.Signature.Totality.Order.Argument { argument; _ } ->
      Synint.Comp.Arg argument
  | Synext.Signature.Totality.Order.Lexical_ordering { arguments; _ } ->
      let arguments' = List1.map elaborate_totality_order arguments in
      Synint.Comp.Lex (List1.to_list arguments')
  | Synext.Signature.Totality.Order.Simultaneous_ordering { arguments; _ } ->
      let arguments' = List1.map elaborate_totality_order arguments in
      Synint.Comp.Simul (List1.to_list arguments')

and elaborate_totality_declaration typ declaration =
  match declaration with
  | Synext.Signature.Totality.Declaration.Trust _ -> `trust
  | Synext.Signature.Totality.Declaration.Numeric { order; _ } -> (
      match order with
      | Option.None -> `not_recursive
      | Option.Some order ->
          `inductive
            (Reconstruct.numeric_order typ (elaborate_totality_order order)))
  | Synext.Signature.Totality.Declaration.Named _ ->
      Error.raise_violation
        (Format.asprintf "[%s] unsupported named totality declaration"
           __FUNCTION__)

let parse_harpoon_theorem_type location input =
  let open Beluga_parser in
  let open Parser in
  let token_sequence = Lexer.lex_string ~initial_location:location input in
  let parsing_state =
    Parser_state.initial ~initial_location:location token_sequence
  in
  Parsing.(eval_exn (only comp_typ) parsing_state)

let disambiguate_harpoon_theorem_type disambiguation_state typ =
  Disambiguation_state.with_bindings_checkpoint disambiguation_state
    (fun disambiguation_state ->
      Disambiguation.disambiguate_comp_typ disambiguation_state typ)

let read_harpoon_theorem_typ disambiguation_state location input =
  let typ = parse_harpoon_theorem_type location input in
  disambiguate_harpoon_theorem_type disambiguation_state typ

let elaborate_typ state cD tau =
  let apx_tau =
    Indexing_state.with_bindings_checkpoint state (fun state ->
        Indexing_state.add_all_mctx state cD;
        Indexer.index_open_comp_typ state tau)
  in
  (* FIXME: The following elaboration steps need checkpoints *)
  (* FIXME: These calls are sketchy as hell. There must be a better place to
     put them -je *)
  Reconstruct.reset_fvarCnstr ();
  Store.FCVar.clear ();
  apx_tau
  |> Reconstruct.comptyp_cD cD
  |> Abstract.comptyp
  |> Pair.map_left (fun tau -> Whnf.cnormCTyp (tau, Whnf.m_id))
  |> F.through (fun (tau, _) -> Check.Comp.checkTyp cD tau)

(** Runs the theorem configuration prompt to construct a mutual group of
    theorems. *)
let configuration_wizard' disambiguation_state indexing_state io
    automation_state : Id.cid_mutual_group * Theorem.t list =
  let rec do_prompts ~theorem_number : Theorem.Conf.t list =
    Io.printf io "Configuring theorem #%d@\n" theorem_number;
    (* prompt for name, and allow using empty to signal we're done. *)
    match prompt_quit_or_theorem_identifier_opt io with
    | Option.None (* Blank input *)
    | Option.Some `quit (* [`:quit'] input *) ->
        []
    | Option.Some (`theorem_name name) (* Theorem name input *) ->
        let tau, k =
          (* Now prompt for the statement, and disallow empty to signal we're
             done. *)
          Io.prompt_input io ~msg:"  Statement of theorem: "
            ~history_file:Option.none (fun location line ->
              let typ =
                read_harpoon_theorem_typ disambiguation_state location line
              in
              elaborate_typ indexing_state LF.Empty typ)
        in
        let order =
          let totality_declaration_opt =
            Io.prompt_input io ~msg:"  Induction order (empty for none): "
              ~history_file:Option.none (fun location input ->
                read_harpoon_totality_declaration_opt disambiguation_state
                  location input)
          in
          match totality_declaration_opt with
          | Option.Some declaration ->
              elaborate_totality_declaration tau declaration
          | Option.None -> `not_recursive
        in
        let conf =
          Theorem.Conf.make (Name.make_from_identifier name) order tau k
        in
        conf :: do_prompts ~theorem_number:(theorem_number + 1)
  in
  let confs = do_prompts ~theorem_number:1 in
  Theorem.configure_set (Io.formatter io) automation_state confs

let add_theorems_to_disambiguation_state disambiguation_state theorems =
  Disambiguation_state.iter_list disambiguation_state
    (fun disambiguation_state theorem ->
      let theorem_name = Theorem.get_name theorem in
      let theorem_identifier = Name.to_identifier theorem_name in
      Disambiguation_state.add_program_constant disambiguation_state
        theorem_identifier)
    theorems

let add_theorems_to_indexing_state indexing_state theorems =
  Indexing_state.iter_list indexing_state
    (fun indexing_state theorem ->
      let theorem_name = Theorem.get_name theorem in
      let theorem_identifier = Name.to_identifier theorem_name in
      let theorem_cid = Theorem.get_cid theorem in
      Indexing_state.add_program_constant indexing_state theorem_identifier
        theorem_cid)
    theorems

let configuration_wizard disambiguation_state indexing_state io
    automation_state : t option =
  let mutual_group, thms =
    configuration_wizard' disambiguation_state indexing_state io
      automation_state
  in
  (* c will be populated with theorems; if there are none it's because the
     session is over. *)
  match thms with
  | _ :: _ ->
      add_theorems_to_disambiguation_state disambiguation_state thms;
      add_theorems_to_indexing_state indexing_state thms;
      Option.some
        (make disambiguation_state indexing_state mutual_group thms)
  | [] -> Option.none

let fmt_ppr_theorem_list ppf c =
  let theorem_list = full_theorem_list c in
  let fmt_ppr_theorem_completeness ppf t =
    if Theorem.is_complete t then Format.fprintf ppf " (finished)" else ()
  in
  let fmt_ppr_indexed_theorem ppf (i, t) =
    Format.fprintf ppf "%d. %a%a" (i + 1) Name.pp (Theorem.get_name t)
      fmt_ppr_theorem_completeness t
  in
  let fmt_ppr_indexed_theorems =
    Format.pp_print_list ~pp_sep:Format.pp_print_cut fmt_ppr_indexed_theorem
  in
  (* It may be better to add the current session name to this message *)
  Format.fprintf ppf "@[<v>%a@]" fmt_ppr_indexed_theorems
    (List.index theorem_list)
