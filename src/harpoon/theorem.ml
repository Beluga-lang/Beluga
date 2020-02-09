(* open Support *)
open Support
open Beluga
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp
open Id
module CompS = Store.Cid.Comp
module Loc = Location

module P = Pretty.Int.DefaultPrinter

let (dprintf, _, _) = Debug.(makeFunctions' (toFlags [13]))
open Debug.Fmt

module Conf = struct
  type t = Comp.total_dec * int

  let make name order tau implicit_parameters =
    ({ Comp.name; order; tau}, implicit_parameters)
end

type 'a subgoal_hook = Comp.proof_state -> 'a

(** A single theorem. *)
type t =
  { (* The Store entry for the theorem. *)
    cid : cid_prog

  (* It's important to remember the initial proof state, since it
     gives us a way to track the original full statement of the theorem
     to prove as well as a handle on the whole (partial) proof.
   *)
  ; initial_state : Comp.proof_state

  (* The remaining subgoals for this theorem. *)
  ; remaining_subgoals : Comp.proof_state DynArray.t

  (* A list of hooks to run on every new subgoal that is added to this theorem. *)
  ; subgoal_hooks : unit subgoal_hook DynArray.t

  (* So tactics can print messages. *)
  ; ppf : Format.formatter
  }

(** Alias to be used when this module is open. *)
type theorem = t

let printf t x = Format.fprintf t.ppf x

let get_name t = (CompS.get t.cid).CompS.name
let has_name_of t name = equals (get_name t) name
let has_cid_of t cid = t.cid = cid

(** Gets the statement of the given theorem. *)
let theorem_statement (t : t) =
  Whnf.cnormCTyp t.initial_state.Comp.goal

let serialize ppf (t : t) =
  let s = t.initial_state in
  let fmt_ppr_order =
    Maybe.print
      begin fun ppf ->
      function
      | `inductive order ->
         Format.fprintf ppf "/ @[<hov 2>total@ @[%a@]@] /"
           P.fmt_ppr_cmp_numeric_order order
      | `not_recursive -> Format.fprintf ppf "/ total /"
      | `partial -> ()
      | `trust -> Format.fprintf ppf "/ trust /"
      end
  in
  let name = CompS.name t.cid in
  let order =
    let open Maybe in
    Total.lookup_dec name (CompS.total_decs t.cid |> get_default [])
    $> fun o -> o.Comp.order
  in
  Format.fprintf ppf "@[<v>proof %a : %a =@,%a@,%a@,@]"
    Id.print name
    Comp.(P.fmt_ppr_cmp_typ s.context.cD P.l0) Comp.(Whnf.cnormCTyp s.goal)
    fmt_ppr_order order
    Comp.(P.fmt_ppr_cmp_proof s.context.cD s.context.cG) (Comp.incomplete_proof Loc.ghost s)

(** Computes the index of the current subgoal we're working on. *)
let current_subgoal_index gs = 0

(** Gets the next subgoal from the given theorem.
    Returns `None` if there are no subgoals remaining in the theorem,
    i.e. the theorem has been proven.
 *)
let next_subgoal (t : t) : Comp.proof_state option =
  match t.remaining_subgoals with
  | gs when DynArray.empty gs -> None
  | gs -> Some (DynArray.get gs (current_subgoal_index gs))

(** Finds the first subgoal in this theorem statisfying a given
    predicate and makes it the active subgoal.
 *)
let select_subgoal_satisfying (t : t) (p: Comp.proof_state -> bool) : Comp.proof_state option =
  let open Maybe in
  t.remaining_subgoals
  |> DynArray.to_list
  |> Misc.List.index_of p
  $> begin fun idx ->
     let sg = DynArray.get t.remaining_subgoals idx in
     DynArray.delete t.remaining_subgoals idx;
     DynArray.insert t.remaining_subgoals 0 sg;
     sg
     end

let dump_proof ppf t =
  let s = t.initial_state in
  Format.fprintf ppf "%a"
    Comp.(P.fmt_ppr_cmp_proof s.context.cD s.context.cG) (Comp.incomplete_proof Loc.ghost s)

let show_proof (t : t) =
  (* This is a trick to print out the proof resulting from
     the initial state correctly. The initial state's solution
     might be None or Some; we don't know. Rather than handle
     that distinction here, we can wrap the state into a proof
     that immediately ends with Incomplete. The proof
     pretty-printer will then deal with the None/Some for us by
     printing a `?` if the initial state hasn't been solved
     yet.
   *)
  printf t "@[<v>Proof so far:@,%a@,@]"
    dump_proof t

let show_subgoals (t : t) =
  let f ppf i g =
    printf t "%2d. @[%a@]@,"
      (i + 1)
      Comp.(P.fmt_ppr_cmp_typ g.context.cD P.l0) Comp.(Whnf.cnormCTyp g.goal)
  in
  let print_subgoals ppf gs =
    List.iteri (f ppf) gs
  in
  printf t "@[<v>%a@]"
    print_subgoals (DynArray.to_list t.remaining_subgoals)

(** Runs all registered subgoal hooks on the given subgoal. *)
let run_subgoal_hooks t g =
  List.iter (fun f -> f g) (DynArray.to_list t.subgoal_hooks)

(** Adds a new subgoal to this theorem.
    Will run the subgoal hooks.
 *)
let add_subgoal t g =
  DynArray.insert t.remaining_subgoals 0 g;
  run_subgoal_hooks t g

(** Adds a list of subgoals to this theorem.
    Will run the subgoal hooks.
 *)
let add_subgoals t = List.iter (add_subgoal t)

let remove_subgoal t g =
  let p g' = Comp.(Whnf.conv_subgoal_path_builder g.label g'.label) in
  let i = DynArray.index_of p t.remaining_subgoals in
  DynArray.delete t.remaining_subgoals i

let remove_current_subgoal t =
  DynArray.delete t.remaining_subgoals 0

(** Moves the current subgoal to the back of the list.
    Does not run subgoal hooks!
 *)
let defer_subgoal t =
  let g = DynArray.get t.remaining_subgoals 0 in
  remove_current_subgoal t;
  DynArray.add t.remaining_subgoals g

let replace_subgoal t g =
  remove_current_subgoal t;
  add_subgoal t g

(** Fills in the solution of the given subgoal.
    This should (ultimately) be called by tactics that solve their goal.
    It is the most primitive solving tactic.
    This doesn't remove the subgoal from the list of pending subgoals!
 *)
let solve (s : Comp.proof_state) (proof : Comp.proof) : unit =
  s.Comp.solution := Some proof

(** High-level solving tactic.
    solve_by_replacing_subgoal g' f g t
    - removes the current subgoal (which must be g)
    - fill's in g's solution with an incomplete proof for g', transformed by f.
 *)
let solve_by_replacing_subgoal t g' f g =
  replace_subgoal t g';
  f (Comp.incomplete_proof Loc.ghost g') |> solve g

(** Renames a variable from `src` to `dst` at the given level
    (`comp or `meta) in the subgoal `g`.
 *)
let rename_variable src dst level t g =
  let g' =
    let open Comp in
    { g with
      context =
        begin match level with
        | `comp ->
           { g.context with
             cG = Context.rename_gctx src dst g.context.cG
           }
        | `meta ->
           { g.context with
             cD = Context.rename_mctx src dst g.context.cD
           }
        end
    ; solution = ref None
    }
  in
  solve_by_replacing_subgoal t g' Misc.id g

(** Registers the theorem in the store.
    The statement of the theorem must be stripped of totality
    annotations.
 *)
let register name tau p mutual_group k : cid_prog =
  CompS.add Syntax.Loc.ghost
    begin fun cid ->
    let v = Comp.(ThmValue (cid, Proof p, Whnf.m_id, Empty)) in
    CompS.mk_entry name tau k
      mutual_group
      (Some v)
    end
  |> snd

(** Creates a Theorem.t
    (You need to add the theorem to the Store before trying to call
    this function to get a cid allocated.)
    The initial state of the theorem is whatever program is in the
    store associated to this theorem. (There must be an associated
    program; the prog field cannot be None.)
    If this is a brand new theorem, configured within Harpoon
    interactively, then you must construct the initial state and build
    an incomplete proof holding that state. That state should be
    passed both as the initial state parameter to this function as
    well as the only item in the list of states to work on.
 *)
let configure cid ppf hooks initial_state gs =
  let t =
    { cid
    ; initial_state
    ; remaining_subgoals = DynArray.make 16
    ; subgoal_hooks = DynArray.create ()
    ; ppf
    }
  in
  let hooks = List.map (fun h -> h t) hooks in
  Misc.DynArray.append_list t.subgoal_hooks hooks;
  add_subgoals t gs;
  t

(** Converts Theorem.Conf.t to Theorem.t by adding all the theorems
    to the store.
 *)
let configure_set ppf (hooks : (t -> Comp.proof_state -> unit) list) (confs : Conf.t list)
    : CompS.mutual_group_id * t list =
  let mutual_group =
    CompS.add_mutual_group
      (Some (List.map fst confs))
  in
  let configure ({ Comp.name; tau; order }, k) =
    let tau' =
      Comp.option_of_total_dec_kind order
      |> Maybe.map
           begin fun order ->
           Order.list_of_order order
           |> Maybe.get'
                (Error.Violation
                   "lexicographic order not supported; should \
                    have checked sooner")
           |> Total.annotate tau
           |> Maybe.get'
                (Error.Violation
                   "annotation failed; too many arguments? \
                    Check sooner.")
           end
      |> Maybe.get_default tau
    in
    dprintf begin fun p ->
      p.fmt "[configure_set] @[<v>got (possibly) annotated type\
             @,@[%a@]\
             @,from total dec\
             @,@[%a@]\
             @]"
        P.(fmt_ppr_cmp_typ LF.Empty l0) tau'
        P.fmt_ppr_cmp_total_dec_kind order
      end;
    let g =
      (* construct the initial state with the annotated type *)
      Comp.make_proof_state Comp.SubgoalPath.start
        ( tau', Whnf.m_id )
    in
    let p = Comp.incomplete_proof Loc.ghost g in
    (* add the theorem to the store to get a cid allocated
       Make sure to register with the original, un-annotated type.
       Annotating and then stripping here doesn't work, as stripping
       isn't actually the inverse of annotation.
     *)
    let cid = register name tau p mutual_group k in
    (* configure the theorem *)
    configure cid ppf hooks g [g]
  in
  (mutual_group, List.map configure confs)

let set_hidden (t : t) b =
  Store.Cid.Comp.set_hidden t.cid (Misc.const b)

(* Invokes the translation procedure on a given theorem *)
let translate (thm : t) : Comp.exp_chk =
  let open Comp in
  let state = thm.initial_state in
  let cD = state.context.cD in
  let cG = state.context.cG in
  let (tau, _) = state.goal in
  Translate.translate_proof cD cG (Option.get !(state.solution)) tau
