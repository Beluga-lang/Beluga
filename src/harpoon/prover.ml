open Support

module B = Beluga
module Check = B.Check
module Command = B.Syntax.Ext.Harpoon
module Context = B.Context
module Comp = B.Syntax.Int.Comp
module HoleId = B.HoleId
module Holes = B.Holes
module Id = B.Id
module Interactive = B.Interactive
module LF = B.Syntax.Int.LF
module Logic = B.Logic
module P = B.Pretty.Int.DefaultPrinter
module Total = B.Total
module Whnf = B.Whnf
module S = B.Substitution
module Debug = B.Debug
module F = Misc.Function
module CompS = B.Store.Cid.Comp
module Loc = B.Location

module DynArray = Misc.DynArray

let dprintf, _, dprnt = Debug.(makeFunctions' (toFlags [13]))
open Debug.Fmt

type error =
  | NoSuchVariable of Id.name * [ `meta | `comp ]
  | EndOfInput

exception Error of error

let throw e = raise (Error e)

let format_error ppf =
  let open Format in
  function
  | NoSuchVariable (name, level) ->
     let format_variable_kind ppf = function
       | `meta -> fprintf ppf "metavariable"
       | `comp -> fprintf ppf "computational variable"
     in
     fprintf ppf "No such %a %a."
       format_variable_kind level
       Id.print name
  | EndOfInput -> fprintf ppf "End of input."

let _ =
  B.Error.register_printer'
    begin fun e ->
    match e with
    | Error e -> Some (B.Error.print (fun ppf -> format_error ppf e))
    | _ -> None
    end

(** High-level elaboration from external to internal syntax. *)
module Elab = struct
  (** Elaborates a synthesizable expression in the given contexts. *)
  let exp' cIH cD cG mfs t =
    let (hs, (i, tau)) =
      Holes.catch
        begin fun _ ->
        let (i, (tau, theta)) =
          Interactive.elaborate_exp' cD cG t
        in
        dprintf
          begin fun p ->
          p.fmt "[elaborate_exp'] @[<v>done:@,\
                 i = @[%a@] (internal)@]"
            P.(fmt_ppr_cmp_exp_syn cD cG l0) i
          end;
        let i = Whnf.(cnormExp' (i, m_id)) in
        let _ = Check.Comp.syn ~cIH: cIH cD cG mfs i in  (* (tau, theta); *)
        (i, Whnf.cnormCTyp (tau, theta))
        end
    in
    (hs, i, tau)

  (** Elaborates a checkable expression in the given contexts against the given type. *)
  let exp cIH cD cG mfs t ttau =
    Holes.catch
      begin fun _ ->
      let e = Interactive.elaborate_exp cD cG t (Pair.lmap Total.strip ttau) in
      let e = Whnf.(cnormExp (e, m_id)) in
      Check.Comp.check ~cIH: cIH cD cG mfs e ttau;
      e
      end

  let typ cD tau =
    let (tau, k) = Interactive.elaborate_typ cD tau in
    tau

  (** Elaborates a metavariable. *)
  let mvar cD loc name =
    (* This is kind of sketchy since we don't parse a head, but rather
       just a name (or a hash_name), and we do all the elaboration "by
       hand" here instead of using Lfrecon and Index.
     *)
    let p (d, _) = Id.equals name (LF.name_of_ctyp_decl d) in
    match Context.find_with_index_rev' cD p with
    | None -> B.Lfrecon.(throw loc (UnboundName name))
    | Some LF.(Decl (_, cT, dep), k) ->
       let cT = Whnf.cnormMTyp (cT, LF.MShift k) in
       dprintf
         begin fun p ->
         p.fmt "[harpoon] [Elab.mvar] @[<v>found index %d for metavariable@,\
                @[<hov 2>%a :@ @[%a@]@]@]"
           k
           Id.print name
           P.(fmt_ppr_cmp_meta_typ cD) cT
         end;
       let mF =
         let open LF in
         match cT with
         | ClTyp (mT, cPsi) ->
            let psi_hat = Context.dctxToHat cPsi in
            let obj =
              match mT with
              | MTyp _ -> MObj (MVar (Offset k, S.LF.id) |> head)
              | PTyp _ -> PObj (PVar (k, S.LF.id))
              | STyp _ -> SObj (SVar (k, 0, S.LF.id)) (* XXX not sure about 0 -je *)
            in
            ClObj (psi_hat, obj)
         | LF.CTyp _ ->
            let cPsi = LF.(CtxVar (CtxOffset k)) in
            CObj cPsi
       in
       let i =
         Comp.AnnBox ( (loc, mF), cT )
       in
       let tau =
         Comp.TypBox (loc, cT)
       in
       (i, tau)
    | _ -> B.Error.violation "[harpoon] [Elab] [mvar] cD decl has no type"

end

(**
 * TODO: Move this util into a dedicated module
 * TODO: Add more abstraction layers for system level operations
 *)
let replace_locs (replacees : (Loc.t * (Format.formatter -> unit -> unit)) list) : unit =
  replacees
  |> Misc.Hashtbl.group_by F.(Loc.filename ++ fst)
  (* iterate over replacee groups
   (* open file stream *)
   (* sort items in the group *)
   (* iterate over the items
   (* iterate over file stream and print uchars until it meets the item hole *)
   (* print the item value *)
   *)
   *)
  |> Hashtbl.iter
       begin fun file_name replacees ->
       dprintf begin fun p ->
         p.fmt "[replace_locs] opening file %s" file_name
         end;
       Files.with_in_channel file_name
         begin fun in_ch ->
         let in_lexbuf = Sedlexing.Utf8.from_channel in_ch in
         let read_length = ref 0 in
         let indentation = ref 0 in
         let raise_edited_error () =
           B.Error.violation "[harpoon] [serialize] original file is edited"
         in
         let with_uchar n f =
           match Sedlexing.next in_lexbuf with
           | None -> n ()
           | Some v ->
              incr read_length;
              if v != Uchar.of_char '\n'
              then incr indentation
              else indentation := 0;
              f v
         in
         dprintf (fun p -> p.fmt "[replace_locs] opening temp file beluga_harpoon");
         Filename.(Files.with_temp_file (dirname file_name) (basename file_name))
           begin fun temp_file_name out_ch ->
           dprintf (fun p -> p.fmt "[replace_locs] opened %s" temp_file_name);
           let outbuf = Buffer.create 4 in
           replacees
           |> List.sort (Misc.on fst Loc.compare_start)
           |> List.iter
                begin fun (loc, printer) ->
                let start_offset = Loc.start_offset loc in
                let stop_offset = Loc.stop_offset loc in
                Misc.Function.until
                  begin fun _ ->
                  if !read_length < start_offset
                  then
                    with_uchar raise_edited_error
                      begin fun v ->
                      Buffer.clear outbuf;
                      Buffer.add_utf_8_uchar outbuf v;
                      Buffer.output_buffer out_ch outbuf;
                      true
                      end
                  else
                    false
                  end;
                let ppf = Format.formatter_of_out_channel out_ch in
                Format.pp_open_vbox ppf !indentation;
                printer ppf ();
                Format.pp_close_box ppf ();
                Format.pp_print_flush ppf ();
                Misc.Function.until
                  begin fun _ ->
                  if !read_length < stop_offset
                  then
                    with_uchar raise_edited_error (Misc.const true)
                  else
                    false
                  end
                end;
           Misc.Function.until
             begin fun _ ->
             with_uchar (Misc.const false)
               begin fun v ->
               Buffer.clear outbuf;
               Buffer.add_utf_8_uchar outbuf v;
               Buffer.output_buffer out_ch outbuf;
               true
               end
             end;
           close_in in_ch;
           close_out out_ch;
           dprintf begin fun p ->
             p.fmt "[replace_locs] moving %s -> %s" temp_file_name file_name
             end;
           Sys.rename temp_file_name file_name
           end
         end
       end

let update_existing_holes existing_holes =
  let open Maybe in
  existing_holes
  |> List.map (fun (loc, (_, ps)) -> (loc, ps))
  |> filter_map
       begin fun (loc, ps) ->
       let open Comp in
       !(ps.solution)
       $> fun p ->
          ( loc
          , fun fmt _ -> P.fmt_ppr_cmp_proof ps.context.cD ps.context.cG fmt p
          )
       end
  |> replace_locs

let add_new_mutual_rec_thmss target_file_name new_mutual_rec_thmss =
  let out_ch = open_out_gen [Open_append; Open_text] 0o600 target_file_name in
  let out_ppf = Format.formatter_of_out_channel out_ch in
  let printf_out fmt = Format.fprintf out_ppf fmt in
  new_mutual_rec_thmss
  |> List.iter
       begin fun thms ->
       printf_out "@.";
       printf_out "@[<v>";
       thms
       |> List.iteri
            begin fun i thm ->
            if i != 0
            then printf_out "and@,";
            Format.fprintf out_ppf "%a" Theorem.serialize thm
            end;
       printf_out ";@]@."
       end;
  close_out out_ch

let get_existing_holes () =
  let has_file_loc = F.(not ++ Loc.is_ghost ++ fst) in
  Holes.get_harpoon_subgoals ()
  |> List.filter has_file_loc

(** Contains a family a functions for rewriting references to program
    functions.

    This is used after translation to replace all references for
    recursive calls with calls to the translated functions.
 *)
module CidProgRewrite = struct
  open Comp

  let rec exp_chk f = function
    | Syn (loc, i) -> Syn (loc, exp_syn f i)
    | Fn (loc, x, e) -> Fn (loc, x, exp_chk f e)
    | Fun (loc, fbs) -> Fun (loc, fun_branches f fbs)
    | MLam (loc, u, e, plicity) -> MLam (loc, u, exp_chk f e, plicity)
    | Pair (loc, e1, e2) -> Pair (loc, exp_chk f e1, exp_chk f e2)
    | LetPair (loc, i, (x1, x2, e)) ->
       LetPair (loc, exp_syn f i, (x1, x2, exp_chk f e))
    | Let (loc, i, (x, e)) -> Let (loc, exp_syn f i, (x, exp_chk f e))
    | Box (loc, cM, cU) -> Box (loc, cM, cU)
    | Case (loc, prag, i, bs) ->
       Case (loc, prag, exp_syn f i, List.map (branch f) bs)
    | Impossible (loc, i) -> Impossible (loc, exp_syn f i)
    | Hole (loc, id, name) -> Hole (loc, id, name)

  and exp_syn f = function
    | Var (loc, k) -> Var (loc, k)
    | DataConst (loc, cid) -> DataConst (loc, cid)
    | Obs (loc, e, t, cid) -> Obs (loc, exp_chk f e, t, cid)
    | Const (loc, cid) -> Const (loc, f cid)
    | Apply (loc, i, e) -> Apply (loc, exp_syn f i, exp_chk f e)
    | MApp (loc, i, cM, cU, plicity) ->
       MApp (loc, exp_syn f i, cM, cU, plicity)
    | AnnBox (cM, cU) -> AnnBox (cM, cU)
    | PairVal (loc, i1, i2) ->
       PairVal (loc, exp_syn f i1, exp_syn f i2)

  and branch f (Branch (loc, cD_pref, (cD_b, cG_b), pat, t, e)) =
      Branch (loc, cD_pref, (cD_b, cG_b), pat, t, exp_chk f e)

  and fun_branches f = function
    | NilFBranch loc -> NilFBranch loc
    | ConsFBranch (loc, (cD, cG, patS, e), bs) ->
       ConsFBranch
         (loc, (cD, cG, patS, exp_chk f e), fun_branches f bs)
end

module Prover = struct
  module Session = struct
    type t =
      { theorems : Theorem.t DynArray.t
      ; finished_theorems: (Theorem.t * Comp.exp_chk option) DynArray.t
      ; mutual_group : CompS.mutual_group_id
      }

    let make mutual_group thms =
      { theorems = thms
      ; finished_theorems = DynArray.make 32
      ; mutual_group
      }

    (** Gets the list of mutual declarations corresponding to the
        currently loaded theorems in the active session.
     *)
    let get_mutual_decs (s : t) : Comp.total_dec list option =
      CompS.lookup_mutual_group s.mutual_group

    (** Unhides cids for all theorems in this session. *)
    let enter (s : t) : unit =
      DynArray.iter (F.flip Theorem.set_hidden false) s.theorems

    (** Hides cids for all theorems in this session. *)
    let suspend (s : t) : unit =
      DynArray.iter (F.flip Theorem.set_hidden true) s.theorems

    let remove_current_theorem s =
      DynArray.delete s.theorems 0

    (** Moves the current theorem from the incomplete theorem stack to
        the finished theorem stack, and associates it to the given
        checkable term that is its translation.
     *)
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
      Misc.DynArray.head s.theorems

    (** Decides whether a given `cid` is in among the currently being
        proven theorems. *)
    let cid_is_in_current_theorem_set s c =
      List.exists (F.flip Theorem.has_cid_of c) (DynArray.to_list s.theorems)

    (** Infer invocation kind based on `exp_syn` and the current theorem
     *)
    let infer_invocation_kind s (i : Comp.exp_syn) : Comp.invoke_kind =
      match Comp.head_of_application i with
      | Comp.Const (_, c) when cid_is_in_current_theorem_set s c -> `ih
      | _ -> `lemma

    (** Selects a theorem by name in the current session.
        Returns whether the selection succeeded. (A theorem by such name could be found.)
     *)
    let select_theorem c name =
      match
        Misc.DynArray.rfind_opt_idx
          c.theorems
          (F.flip Theorem.has_name_of name)
      with
      | None -> false
      | Some (i, t) ->
         DynArray.delete c.theorems i;
         DynArray.insert c.theorems 0 t;
         true

    (** Constructs a list of all theorems in this session, both
        incomplete and finished.
     *)
    let full_theorem_list c =
      DynArray.to_list c.theorems
      @ List.map fst (DynArray.to_list c.finished_theorems)

    let get_session_kind c : [`introduced | `loaded] =
      let existing_holes = get_existing_holes () in
      (* If the theorems in the session do not have
       * any predefined holes in the loaded files,
       * that session is newly defined in this harpoon process,
       *)
      let is_loaded =
        full_theorem_list c
        |> List.exists
             begin fun thm ->
             existing_holes
             |> List.map F.(fst ++ snd)
             |> List.exists (Theorem.has_cid_of thm)
             end
      in
      if is_loaded
      then `loaded
      else `introduced

    type translation_check_result =
      [ `some_translations_failed
      | `check_error of exn
      | `ok
      ]

    let prepare_translated_proofs tes total_decs =
      let trans_name name =
        Id.(mk_name (SomeString ("_" ^ render_name name ^ "_trans")))
      in
      (* create the totality declarations for the translated
         proofs, and allocate the mutual group with them. *)
      let total_decs =
        Maybe.map
          (List.map
             (fun dec ->
               let open Comp in
               { dec with name = trans_name dec.name }))
          total_decs
      in
      let mutual_group_id =
        CompS.add_mutual_group total_decs
      in
      (* map from old cids to new cids *)
      let h = Hashtbl.create 8 in
      let es =
        List.map
          begin fun (t, e) ->
          let open CompS in
          let cid, entry = Theorem.get_entry' t in
          let tau = entry.Entry.typ in
          let _ =
            add
              begin fun cid' ->
              (* associate the cid of this theorem to the newly allocated
                 cid for the translated proof *)
              Hashtbl.add h cid cid';
              mk_entry
                (trans_name entry.Entry.name)
                tau
                entry.Entry.implicit_arguments
                mutual_group_id
                None
              end
          in
          (e, tau)
          end
          tes
      in
      (* Now h is populated, so we can rewrite the programs with the
         new cids.
         First, convert the hashtable to a function sending unmapped
         entries to themselves.
       *)
      let cid_map k =
        Hashtbl.find_opt h k |> Maybe.get_default k
      in
      let es =
        List.map
          (fun (e, ttau) -> (CidProgRewrite.exp_chk cid_map e, ttau))
          es
      in
      (es, total_decs)

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
        |> Maybe.(traverse (fun (t, e) -> e $> fun e -> (t, e)))
      with
      | None -> `some_translations_failed
      | Some tes ->
         let ettaus, total_decs =
           prepare_translated_proofs tes (get_mutual_decs c)
         in
         let total_decs = Maybe.get_default [] total_decs in
         try
           List.iter
             (fun (e, tau) ->
               B.Check.Comp.check LF.Empty LF.Empty total_decs
                 e (tau, Whnf.m_id))
             ettaus;
           `ok
         with
         | exc -> `check_error exc
  end

  module State = struct
    type t =
      { sessions : Session.t DynArray.t
      (* ^ The theorem sets currently being proven. *)

      ; automation_state : Automation.State.t
      ; prompt : InputPrompt.t
      ; prompt_number : int ref (* used to number the prompts to the user *)
      ; ppf : Format.formatter
      ; save_back: bool
      ; stop : [ `stop | `go_on ]
      ; sig_path : string (* path to the signature that was loaded *)
      ; all_paths : string list (* paths to the resolved loaded files *)
      }

    let next_prompt_number s = incr s.prompt_number; !(s.prompt_number)

    (** Constructs a Theorem.t for the given cid with the given
        subgoals. *)
    let recover_theorem ppf hooks (cid, gs) =
      let open Comp in
      let e = CompS.get cid in
      let initial_state =
        let s =
          make_proof_state SubgoalPath.start
            ( e.CompS.Entry.typ, Whnf.m_id )
        in
        let prf =
          match e.CompS.Entry.prog with
          | Some (ThmValue (_, Proof p, _, _)) -> p
          | _ -> B.Error.violation "recovered theorem not a proof"
        in
        dprintf begin fun p ->
          p.fmt "[recover_theorem] @[<v>proof =@,@[%a@]@]"
            P.(fmt_ppr_cmp_proof LF.Empty LF.Empty) prf
          end;
        s.solution := Some prf;
        s
      in
      Theorem.configure
        cid
        ppf
        hooks
        initial_state
        (Nonempty.to_list gs)

    let recover_session ppf hooks (mutual_group, thm_confs) =
      let theorems =
        let open Nonempty in
        let f =
          (* after recovering the theorem, set it hidden.
             later, we enter the session, which will bring it into
             scope. *)
          F.((fun t -> Theorem.set_hidden t true; t) ++ recover_theorem ppf hooks)
        in
        (* XXX to_list -> of_list later is inefficient
           It would be best to add a function to obtain a Seq.t from
           an Nonempty.t, lazily map the sequence, and the force the
           sequence with DynArray.of_seq
         *)
        map f thm_confs |> to_list
      in
      dprintf begin fun p ->
        p.fmt "[recover_session] @[<v>recovered a session with the following theorems:\
               @,  @[<hv>%a@]@]"
          (Format.pp_print_list ~pp_sep: Fmt.comma
             (fun ppf t -> Format.fprintf ppf "%a" Id.print (Theorem.get_name t)))
          theorems
        end;
      { Session.theorems = DynArray.of_list theorems
      ; finished_theorems = DynArray.make 32
      ; mutual_group
      }

    (** Constructs a list of sessions from a list of open subgoals.
        Subgoals are grouped into theorems according to their
        associated cid, and theorems are grouped into sessions
        according to their mutual group.

        WARNING: all recovered theorems are hidden (out of scope).
        It is necessary to enter the session that ends up selecteed to
        bring its theorems into scope.
     *)
    let recover_sessions ppf hooks (gs : Comp.open_subgoal list) =
      (* idea:
         - first group subgoals by theorem
         - group theorems by mutual group
         - construct a session for each mutual group
       *)
      Nonempty.(
        group_by fst gs
        |> List.map (Pair.rmap (map snd))
        |> group_by F.(CompS.mutual_group ++ fst)
      )
      |> List.map (recover_session ppf hooks)

    (** Drops all sessions from the prover, replacing with the given
        list.
     *)
    let replace_sessions s ss =
      DynArray.(clear s.sessions; append_list s.sessions ss)

    let printf s x = Format.fprintf s.ppf x

    (** Moves the current session to the back of the session list,
        making (what was) the second session the active session. *)
    let defer_session s =
      let c = DynArray.get s.sessions 0 in
      DynArray.delete s.sessions 0;
      DynArray.add s.sessions c

    let next_session s = Misc.DynArray.head s.sessions

    let remove_current_session s =
      DynArray.delete s.sessions 0

    (** Runs proof automation on a given subgoal. *)
    let run_automation auto_state (t : Theorem.t) (g : Comp.proof_state) =
      ignore (Automation.execute auto_state t g)

    (** Creates a prover state with sessions recovered from the given
        list of open subgoals.
        Use an empty list to generate a prover state with no sessions.
     *)
    let make
          save_back
          stop
          (sig_path : string)
          (all_paths : string list)
          (ppf : Format.formatter)
          (prompt : InputPrompt.t)
          (gs : Comp.open_subgoal list)
        : t =
      let automation_state = Automation.State.make () in
      let hooks = [run_automation automation_state] in
      let sessions = recover_sessions ppf hooks gs in
      let _ =
        (* since all recovered sessions are suspended, we must
           explicitly enter the first one *)
        let open Maybe in
        Misc.List.hd_opt sessions
        $> Session.enter
      in

      F.flip List.iter sessions
        begin fun c ->
        dprintf begin fun p ->
          let open Format in
          p.fmt "[harpoon State.make] @[<v>%a@]"
            (pp_print_list ~pp_sep: pp_print_cut
               (fun ppf t ->
                 fprintf ppf "@[%a: hidden = %b@]"
                   Id.print (Theorem.get_name t)
                   (Theorem.get_entry t).CompS.Entry.hidden))
            (DynArray.to_list c.Session.theorems)
          end
        end;

      { sessions = DynArray.of_list sessions
      ; prompt_number = ref 0
      ; automation_state
      ; prompt
      ; ppf
      ; save_back
      ; stop
      ; sig_path
      ; all_paths
      }

    (** Displays the given prompt `msg` and awaits a line of input from the user.
        The line is parsed using the given parser.
        In case of a parse error, the prompt is repeated.
        The user can abort the prompt by giving an empty string.
     *)
    let rec prompt_with s msg use_history (p : 'a B.Parser.t) : 'a option =
      match s.prompt msg use_history () with
      | None -> throw EndOfInput
      | Some "" -> None
      | Some line ->
         B.Runparser.parse_string
           (Loc.(move_line (next_prompt_number s) (initial "<prompt>")))
           line
           (B.Parser.only p)
         |> snd
         |> B.Parser.handle
              begin fun err ->
              printf s "@[%a@]@."
                B.Parser.print_error err;
              prompt_with s msg use_history p
              end
              Maybe.pure

    (** Repeats the prompt even if the user gives an empty response. *)
    let rec prompt_forever_with s msg use_history p =
      match prompt_with s msg use_history p with
      | None -> prompt_forever_with s msg use_history p
      | Some x -> x

    (** Runs the theorem configuration prompt to construct a mutual
        group of theorems.
     *)
    let session_configuration_wizard' s : CompS.mutual_group_id * Theorem.t list =
      let rec do_prompts i : Theorem.Conf.t list =
        printf s "Configuring theorem #%d@." i;
        (* prompt for name, and allow using empty to signal we're done. *)
        match
          prompt_with s "  Name of theorem (:quit or empty to finish): "
            None
            B.Parser.next_theorem
        with
        | None | Some `quit -> []
        | Some (`next name) ->
           let tau, k =
             (* XXX These calls are sketchy as hell.
                There must be a better place to put them -je
              *)
             B.Reconstruct.reset_fvarCnstr ();
             B.Store.FCVar.clear ();
             (* Now prompt for the statement, and disallow empty to signal we're done. *)
             prompt_forever_with s "  Statement of theorem: " None
               B.Parser.(cmp_typ $> Interactive.elaborate_typ LF.Empty)
           in
           dprintf begin fun p ->
             p.fmt "@[<v 2>[harpoon] [session_configuration] elaborated type\
                    @,@[%a@]\
                    @,with %d implicit parameters@]"
               P.(fmt_ppr_cmp_typ LF.Empty l0) tau
               k
             end;
           let order =
             let p =
               Misc.Function.flip B.Parser.map
                 B.Parser.(numeric_total_order |> span)
                 begin fun (loc, o) ->
                   let order = B.Reconstruct.numeric_order tau o in
                   dprintf begin fun p ->
                     p.fmt "[session_configuration] @[<v>elaborated numeric order\
                            @,  @[%a@]\
                            @,considering %d implicit arguments.@]"
                       P.(fmt_ppr_cmp_numeric_order) order
                       k
                     end;
                   order
                     (* TODO we should check that the order is legit
                        here so that we can right away prompt the user
                        for a correct one; currently this check only
                        happens very late when the theorem set is
                        configured. *)
                 end
             in
             prompt_with s "  Induction order (empty for none): " None
               p
           in
           printf s "@]";
           let total_dec_kind =
             match order with
             | Some order -> `inductive order
             | None -> `not_recursive
           in
           let conf = Theorem.Conf.make name total_dec_kind tau k in
           conf :: do_prompts (i + 1)
      in

      let confs = do_prompts 1 in
      Theorem.configure_set s.ppf [run_automation s.automation_state] confs

    (** Given that session `c` is at index `i` in the sessions list,
        `select_session s i c` moves it to the front, thus activating
        it.Takes care of suspending the active session and entering
        `c`. *)
    let select_session s i c =
      (* get the active session *)
      let c' = DynArray.get s.sessions 0 in
      (* remove the target session (i.e. c) from the list *)
      DynArray.delete s.sessions i;
      (* suspend the current session and enter the target session *)
      Session.suspend c';
      Session.enter c;
      (* make the target session the active session by moving it to position 0 *)
      DynArray.insert s.sessions 0 c

    (** Adds a session to the prover and selects it.
        If another session was selected before, it is suspended, and
        the new session is entered.
     *)
    let add_session s c =
      let k = DynArray.length s.sessions in
      DynArray.add s.sessions c;
      (* newly added session is at index k *)
      select_session s k c
                        (*
    let remove_current_session s = DynArray.delete s.sessions 0
                         *)

    let session_configuration_wizard s =
      let mutual_group, thms = session_configuration_wizard' s in
      (* c will be populated with theorems; if there are none it's
         because the session is over. *)
      match thms with
      | _ :: _ ->
         `ok (Session.make mutual_group (DynArray.of_list thms))
      | [] -> `aborted

    (** Finds a session containing a theorem with the given name and
        selects that session and that theorem.
        Returns false when no theorem by such name could be found.
     *)
    let select_theorem s name =
      match
        Misc.DynArray.rfind_opt_idx
          s.sessions
          begin fun c ->
          List.exists
            F.(Id.equals name ++ Theorem.get_name)
            (DynArray.to_list c.Session.theorems)
          end
      with
      | None -> false
      | Some (i, c) ->
         select_session s i c;
         (* select the desired theorem within the session;
            this should be guaranteed to succeed due to the
            List.exists call in the match. *)
         if not (Session.select_theorem c name) then
           B.Error.violation
             "[select_theorem] selected session does not contain the theorem";
         true

    (** Gets the next state triple from the prover. *)
    let next_triple (s : t) =
      match next_session s with
      | None -> Either.Left `no_session
      | Some c ->
         match Session.next_theorem c with
         | None -> Either.Left (`no_theorem c)
         | Some t ->
            match Theorem.next_subgoal t with
            | None -> Either.Left (`no_subgoal (c, t))
            | Some g -> Either.Right (c, t, g)

    (** Drops all state and reloads from the signature.
        Typically, this is called after serialization reflects the
        state into the signature.
        Note that the current state triple is not preserved by this
        call, and that after it, the prover may be focussing on a
        different subgoal, possibly in a different session/theorem.
        To preserve focus, combine this with `keeping_focus`.
     *)
    let reset s : unit =
      let _ = B.Load.load s.ppf s.sig_path in
      let gs = B.Holes.get_harpoon_subgoals () |> List.map snd in
      let hooks = [run_automation s.automation_state] in
      let ss = recover_sessions s.ppf hooks gs in
      dprintf begin fun p ->
        p.fmt "[reset] recovered %d sessions from %d subgoals"
          (List.length ss)
          (List.length gs)
        end;
      replace_sessions s ss

    (** Takes note of the currently selected theorem and subgoal, runs
        the given function, and then reselects the theorem and subgoal.
        This is used by the serialize function to make sure that after
        serializing the Harpoon state, we're back in the same subgoal
        we were in before.
     *)
    let keeping_focus s c t g f =
      let curr_thm_name = Theorem.get_name t in
      let curr_sg_label = g.Comp.label in
      f ();
      if not (select_theorem s curr_thm_name) then
        B.Error.violation
          "[reset] reloaded signature does not contain the theorem \
           we were working on";
      let t =
        match next_triple s with
        | Either.Right (_, t, _) -> t
        | _ ->
           B.Error.violation
             "[reset] next_triple didn't give a triple."
      in
      match
        Theorem.select_subgoal_satisfying t
          begin fun g ->
          Whnf.conv_subgoal_path_builder g.Comp.label curr_sg_label
          end
      with
      | None ->
         B.Error.violation
           "[reset] select_subgoal_satisfying returned None"
      | Some _ -> ()

    (** Reflects the current prover state back into the loaded
        signature file.
        You should reset the prover state after doing this by calling
        `reset`.
     *)
    let save s =
      let existing_holes = get_existing_holes () in
      let new_mutual_rec_thmss =
        DynArray.to_list s.sessions
        |> List.filter
             begin fun sess ->
             match Session.get_session_kind sess with
             | `introduced -> true
             | `loaded -> false
             end
        |> List.map Session.full_theorem_list
        |> List.filter Misc.List.nonempty
      in
      update_existing_holes existing_holes;
      add_new_mutual_rec_thmss
        (ExtList.List.last s.all_paths)
        new_mutual_rec_thmss
  end

    (*
  (** Removes the theorem with a given name from the list of theorems. *)
  let remove_theorem s name =
    let n = DynArray.length s.theorems in
    let rec loop = function
      | i when i >= n -> ()
      | i when Id.equals name (DynArray.get s.theorems i).Theorem.name ->
         DynArray.delete s.theorems i
      | i -> loop (i + 1)
    in
    loop 0
     *)

  let translate s { CompS.Entry.prog; typ = tau; name; _ } =
    let prog =
      Maybe.get'
        (B.Error.Violation
           ("The body of theorem "
            ^ Id.render_name name ^ " is unknown."))
        prog
    in
    let thm =
      match prog with
      | Comp.ThmValue (cid', thm, t, rho) ->
         assert (match rho with Comp.Empty -> true | _ -> false);
         assert (match t with LF.MShift 0 -> true | _ -> false);
         thm
      | _ ->
         B.Error.violation
           "Looked up theorem is not a theorem value."
    in
    Translate.(trap (fun _ -> theorem thm tau))

  let dump_proof t path =
    let out = open_out path in
    let ppf = Format.formatter_of_out_channel out in
    Theorem.dump_proof ppf t;
    Format.pp_print_newline ppf ();
    close_out out

  let prompt s =
    (* The lambda character (or any other UTF-8 characters)
       does not work with linenoise.
       See https://github.com/ocaml-community/ocaml-linenoise/issues/13
       for detail.
     *)
    s.State.prompt "> " None ()
    |> Maybe.get' (Error EndOfInput)

  let process_command
        (s : State.t)
        (c : Session.t)
        (t : Theorem.t)
        (g : Comp.proof_state)
        (cmd : Command.command)
      : unit =
    let mfs =
      lazy
        begin
          let ds = Session.get_mutual_decs c |> Maybe.get_default [] in
          dprintf
            begin fun p ->
            p.fmt "[harpoon] [mfs] @[<v>got mutual decs:\
                   @,-> @[<v>%a@]@]"
              (Format.pp_print_list ~pp_sep: Format.pp_print_cut
                 P.fmt_ppr_cmp_total_dec)
              ds
            end;
          ds
        end
    in

    let open Comp in

    let solve_hole (id, Holes.Exists (w, h)) =
      let open Holes in
      dprintf
        begin fun p ->
        p.fmt "[harpoon] [solve_hole] processing hole %s"
          (HoleId.string_of_name_or_id (h.Holes.name, id))
        end;
      let { name; Holes.cD = cDh; info; _ } = h in
      match w with
      | Holes.CompInfo -> failwith "computational holes not supported"
      | Holes.LFInfo ->
         let { lfGoal; cPsi; lfSolution } = h.info in
         assert (lfSolution = None);
         let typ = Whnf.normTyp lfGoal in
         dprintf
           begin fun p ->
           p.fmt "[harpoon] [solve] [holes] @[<v>goal: @[%a@]@]"
             (P.fmt_ppr_lf_typ cDh cPsi P.l0) typ
           end;
         Logic.prepare ();
         let (query, skinnyTyp, querySub, instMVars) =
           Logic.Convert.typToQuery cPsi cDh (typ, 0)
         in
         try
           Logic.Solver.solve cDh cPsi query
             begin fun (cPsi, tM) ->
             State.printf s "found solution: @[%a@]@,@?"
               (P.fmt_ppr_lf_normal cDh cPsi P.l0) tM;
             h.info.lfSolution <- Some (tM, LF.Shift 0);
             raise Logic.Frontend.Done
             end
         with
         | Logic.Frontend.Done ->
            State.printf s "logic programming finished@,@?";
            ()
    in

    let { cD; cG; cIH } = g.context in

    match cmd with
    (* Administrative commands: *)
    | Command.Theorem cmd ->
       begin match cmd with
       | `list ->
          let theorem_list = DynArray.to_list c.Session.theorems in
          let theorem_indexed_name_list =
            List.mapi (fun i thm -> (i, Theorem.get_name thm)) theorem_list
          in
          let fmt_ppr_indexed_theorem ppf (i, sName) =
            Format.fprintf ppf "%d. %a" i Id.print sName
          in
          let fmt_ppr_indexed_theorems =
            Format.pp_print_list ~pp_sep: Format.pp_print_cut fmt_ppr_indexed_theorem
          in
          (* It may be better to add the current session name to this message *)
          State.printf s
            "@[<v>Theorems in the current session:@,  @[<v>%a@]@,Current theorem: 1.@]"
            fmt_ppr_indexed_theorems theorem_indexed_name_list
       | `defer -> Session.defer_theorem c
       | `show_ihs ->
          let f i =
            State.printf s "%d. @[%a@]@,"
              (i + 1)
              (P.fmt_ppr_cmp_ih g.context.cD g.context.cG)
          in
          State.printf s "@[<v>There are %d IHs:@,"
            (Context.length g.context.cIH);
          Context.to_list g.context.cIH |> List.iteri f;
          State.printf s "@]"
       | `dump_proof path ->
          dump_proof t path
       | `show_proof ->
          Theorem.show_proof t
       end
    | Command.Session cmd ->
       begin match cmd with
       | `list ->
          let open Format in
          let session_list = DynArray.to_list s.State.sessions in
          let index l = List.mapi Pair.left l in
          let print_list f ppf x =
            pp_print_list ~pp_sep: pp_print_cut f ppf x
          in
          let print_indexed_session ppf (i, s) =
            let thms = DynArray.to_list s.Session.theorems in
            let print_indexed_theorem ppf (i, t) =
              fprintf ppf "%d. %a" (i + 1) Id.print (Theorem.get_name t)
            in
            fprintf ppf "%d. @[<v>%a@]"
              (i + 1)
              (print_list print_indexed_theorem) (index thms)
          in
          State.printf s "@[<v>Sessions:@,  @[<v>%a@]@,Current session: 1.@]"
            (print_list print_indexed_session) (index session_list)
       | `defer -> State.defer_session s
       | `create ->
          begin match State.session_configuration_wizard s with
          | `ok c -> State.add_session s c
          | `aborted -> ()
          end
       | `serialize ->
          State.(keeping_focus s c t g (fun _ -> save s; reset s))
       end
    | Command.Subgoal cmd ->
       begin match cmd with
       | `list -> Theorem.show_subgoals t
       | `defer -> Theorem.defer_subgoal t
       end

    | Command.SelectTheorem name ->
       if not (State.select_theorem s name) then
         State.printf s
           "There is no theorem by name %a."
           Id.print name

    | Command.Rename (x_src, x_dst, level) ->
       if not (Theorem.rename_variable x_src x_dst level t g) then
         throw (NoSuchVariable (x_src, level))

    | Command.ToggleAutomation (automation_kind, automation_change) ->
       Automation.toggle
         s.State.automation_state
         automation_kind
         automation_change

    | Command.Type i ->
       let (hs, i, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       State.printf s
         "- @[<hov 2>@[%a@] :@ @[%a@]@]"
         P.(fmt_ppr_cmp_exp_syn cD cG l0) i
         P.(fmt_ppr_cmp_typ cD l0) tau

    | Command.Info (k, n) ->
       begin match k with
       | `prog ->
          let open Maybe in
          begin match CompS.(index_of_name_opt n $> get) with
          | None ->
             State.printf s
               "- No such theorem by name %a" Id.print n
          | Some e ->
             State.printf s
               "- @[%a@]"
               P.fmt_ppr_cmp_comp_prog_info e
          end
       end

    | Command.Translate n ->
       let open Maybe in
       begin match CompS.(index_of_name_opt n $> get) with
       | Some entry ->
          State.printf s "%a"
            Translate.fmt_ppr_result (translate s entry)
       | None ->
          State.printf s "No such theorem by name %a defined."
            Id.print n
       end

    (* Real tactics: *)
    | Command.Unbox (i, name) ->
       let (hs, m, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       Tactic.unbox m tau name t g

    | Command.Intros names ->
       Tactic.intros names t g

    | Command.Split (split_kind, i) ->
       let (hs, m, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       Tactic.split split_kind m tau (Lazy.force mfs) t g
    | Command.MSplit (loc, name) ->
       let i, tau = Elab.mvar cD loc name in
       Tactic.split `split i tau (Lazy.force mfs) t g
    | Command.By (i, name) ->
       let (hs, i, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       dprintf
         begin fun p ->
         p.fmt "@[<v>[harpoon-By] elaborated invocation:@,%a@ : %a@]"
           (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
           (P.fmt_ppr_cmp_typ cD P.l0) tau
         end;
       if Whnf.closedExp' i then
         (List.iter solve_hole hs; Tactic.invoke i tau name t g)
       else
         State.printf s
           "@[<v>Elaborated expression\
            @,  @[%a@]\
            @,of type\
            @,  @[%a@]\
            @,is not closed.\
            @,Both the expression and its type must be closed for use with `by`.@]"
           P.(fmt_ppr_cmp_exp_syn cD cG l0) i
           P.(fmt_ppr_cmp_typ cD l0) tau

    | Command.Suffices (i, tau_list) ->
       let (hs, i, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       begin match Session.infer_invocation_kind c i with
       | `ih ->
          State.printf s "inductive use of `suffices by ...` is not currently supported"
       | `lemma ->
          begin match hs with
          | _ :: _ ->
             Theorem.printf t "holes are not supported for `suffices by _ ...`"
          | [] ->
             let tau_list = List.map (Elab.typ cD) tau_list in
             Tactic.suffices i tau_list tau t g
          end
       end

    | Command.Solve e ->
       let (hs, e) = Elab.exp cIH cD cG (Lazy.force mfs) e g.goal in
       dprnt "[harpoon] [solve] elaboration finished";
       (* State.printf s "Found %d hole(s) in solution@." (List.length hs); *)
       List.iter solve_hole hs;
       dprnt "[harpoon] [solve] double-check!";
       Check.Comp.check cD cG (Lazy.force mfs) ~cIH: cIH e g.goal;
       dprnt "[harpoon] [solve] double-check DONE";
       (Comp.solve e |> Tactic.solve) t g
end

(** A computed value of type 'a or a function to print an error. *)
type 'a e = (Format.formatter -> unit -> unit, 'a) Either.t

(** Parses the given string to a Syntax.Ext.Harpoon.command or an
    error-printing function.
 *)
let parse_input k (input : string) : Command.command list e =
  let open B in
  Runparser.parse_string Loc.(move_line k (initial "<prompt>")) input
    Parser.(only interactive_harpoon_command_sequence)
  |> snd
  |> Parser.to_either
  |> Either.lmap (fun e ppf () -> Parser.print_error ppf e)

(** Runs the given function, trapping exceptions in Either.t
    and converting the exception to a function that prints the
    error with a given formatter.
 *)
let run_safe (f : unit -> 'a) : 'a e =
  try
    Either.Right (f ())
  with
  | Error e ->
     Either.Left
       begin fun ppf () ->
       Format.fprintf ppf "@[<v>%a@]@."
         format_error e
       end
  | e ->
     let s = Printexc.to_string e in
     let bt = Printexc.get_backtrace () in
     Either.Left
       begin fun ppf () ->
       Format.fprintf ppf "@[<v>Internal error. (State may be undefined.)@,%s@,%s@]"
         s bt
       end

(** Parses the user input string and executes it in the given state
    triple.
    The input command sequence must be fully executable in the
    current theorem.
    Returns:
    - `ok: all commands were executed in the current theorem
    - `stopped_short: some commands were not executed because the
      current theorem is over.
    - `error: an error occurred. Commands beyond the failed one were
      not executed.
 *)
let process_input s (c, t, g) input =
  let printf x = Prover.State.printf s x in
  let e =
    let open Either in
    parse_input (Prover.State.next_prompt_number s) input
    $ fun cmds ->
      (* Idea:
         - count the commands to run
         - count the commands we were able to process
       *)
      let n = List.length cmds in
      run_safe
        begin fun () ->
        let (k, _) =
          List.fold_left
            begin fun (k, g) cmd ->
            match g with
            | None -> (k, g)
            | Some g ->
               Prover.process_command s c t g cmd;
               (k + 1, Theorem.next_subgoal t)
            end
            (0, Some g)
            cmds
        in
        n = k
        end
  in
  Either.eliminate
    begin fun f ->
    printf "%a" f ();
    if s.Prover.State.stop = `stop then
      exit 1;
    `error
    end
    (function
     | true -> `ok
     | false -> `stopped_short)
    e

let rec loop (s : Prover.State.t) : unit =
  let printf x = Prover.State.printf s x in
  match Prover.State.next_triple s with
  | Either.Left `no_session ->
     begin match Prover.State.session_configuration_wizard s with
     | `ok c ->
        Prover.State.add_session s c;
        loop s
     | `aborted ->
        printf "@,Harpoon terminated.@,"
     end
  | Either.Left (`no_theorem c) ->
     printf "@,@[<v>Proof complete! (No theorems left.)@,";
     begin match Prover.Session.check_translated_proofs c with
     | `ok ->
        printf "- Translated proofs successfully checked.@,"
     | `some_translations_failed ->
        printf "- @[%a@]@,"
          Format.pp_print_string
          "Skipped checking translated proofs because some translations failed."
     | `check_error e ->
        printf "- @[<v>An error occurred when checking the translated proofs.\
                @,@[%s@]@]@,"
          (Printexc.to_string e)
     end;
     printf "@]";
     begin
       if s.Prover.State.save_back
       then Prover.State.(save s; reset s)
       else Prover.State.remove_current_session s
     end;
     loop s
  | Either.Left (`no_subgoal (c, t)) ->
     (* TODO: record the proof into the Store *)
     let e_trans = Prover.translate s (Theorem.get_entry t) in
     printf
       "@[<v>Subproof complete! (No subgoals left.)\
        @,Full proof script:\
        @,  @[<v>%a@]\
        @,@[<v>%a@]@]"
       Theorem.dump_proof t
       Translate.fmt_ppr_result e_trans;
     Prover.Session.mark_current_theorem_as_proven c (Either.to_option e_trans);
     loop s
  | Either.Right (c, t, g) ->
    (* Show the proof state and the prompt *)
    printf "@,@[<v>@,%a@,@]@?"
      P.fmt_ppr_cmp_proof_state g;
    (*
      printf "@,@[<v>@,%a@,There are %d IHs.@,@]@?"
      P.fmt_ppr_cmp_proof_state g
      (Context.length Comp.(g.context.cIH));
     *)

    (* Parse the input and run the command *)
    let input = Prover.prompt s in
    match process_input s (c, t, g) input with
    | `ok | `error -> loop s
    | `stopped_short ->
       printf "@,Warning: theorem proven before all commands were processed.@,";
       loop s

type interaction_mode = [ `stop | `go_on ]

let start_toplevel
      (save_back : bool)
      (stop : interaction_mode)
      (sig_path : string)
      (all_paths : string list)
      (gs : Comp.open_subgoal list)
      (input_prompt : InputPrompt.t)
      (ppf : Format.formatter) (* The formatter used to display messages *)
    : unit =
  let open Prover in
  let s = State.make save_back stop sig_path all_paths ppf input_prompt gs in
  (* If no sessions were created by loading the subgoal list
     then (it must have been empty so) we need to create the default
     session and configure it. *)
  B.Gensym.reset ();
  if DynArray.empty s.State.sessions then
    match State.session_configuration_wizard s with
    | `ok c ->
       State.add_session s c;
       loop s
    | `aborted -> ()
  else
    loop s
