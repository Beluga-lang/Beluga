open Support
open Beluga
open Beluga_syntax
module LF = Synint.LF
module Comp = Synint.Comp
open Id

module P = Prettyint.DefaultPrinter

let (dprintf, _, _) = Debug.(makeFunctions' (toFlags [13]))
open Debug.Fmt

module Conf = struct
  type t = Comp.total_dec * int

  let make name order tau implicit_parameters =
    ({ Comp.name; order; tau}, implicit_parameters)
end

type subgoal_hook = Comp.proof_state -> unit

module Action = struct
  (** An invertible action applied to a theorem. Used to implement
      history/undo. *)
  type t =
    { target : Comp.proof_state
    ; children : Comp.proof_state list
    ; solution : Comp.proof
    ; name : string
    }

  let make name target children solution =
    { name; target; children; solution }

  let name_of_action a = a.name
end

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
  ; subgoal_hooks : subgoal_hook DynArray.t

  (* So tactics can print messages. *)
  ; ppf : Format.formatter

  (* Actions applied to this theorem. *)
  ; history : Action.t History.t
  }

let get_history_names t =
  Pair.both (List.map Action.name_of_action) (History.to_lists t.history)

let remove_subgoal t g =
  let p g' = Comp.(Whnf.conv_subgoal_path_builder g.label g'.label) in
  let i =
    try DynArray.index_of p t.remaining_subgoals
    with
    | Not_found ->
        Error.raise_violation "[remove_subgoal] no such subgoal"
  in
  DynArray.delete t.remaining_subgoals i

let remove_subgoals t = List.iter (remove_subgoal t)

(** Runs all registered subgoal hooks on the given subgoal. *)
let run_subgoal_hooks t g =
  DynArray.iter (fun f -> f g) t.subgoal_hooks

(** Adds a new subgoal to this theorem.
    This does not run subgoal hooks, and should be used in contexts
    where automation must not be run.
 *)
let add_subgoal' t g =
  DynArray.insert t.remaining_subgoals 0 g

(** Adds a list of subgoals to this theorem.
    Will run the subgoal hooks, but only after adding *all* the
    subgoals to the theorem.
 *)
let add_subgoals t gs =
  List.iter (add_subgoal' t) gs;
  List.iter (run_subgoal_hooks t) gs

(** Fills in the solution of the given subgoal. *)
let solve (s : Comp.proof_state) (proof : Comp.proof) : unit =
  s.Comp.solution := Some proof

(** Clears the solution of the given subgoal. *)
let unsolve g =
  g.Comp.solution := None

(** Raises Violation if any preconditions of an action are not
    satisfied. *)
let validate_action t a : unit =
  (* - the solution of the target subgoal is None
     - the target subgoal is among the list of remaining subgoals
     - the child subgoals are not in the list of remaining subgoals
   *)
  () (* TODO *)

let validate_action_inverse t a : unit =
  (* - the solution of the target subgoal is not None
     - the target subgoal is not among the list of remaining subgoals
     - the child subgoals are among the list of remaining subgoals
   *)
  () (* TODO *)

let apply_forward theorem_state action =
  validate_action theorem_state action;
  solve action.Action.target action.Action.solution;
  remove_subgoal theorem_state action.Action.target;
  add_subgoals theorem_state action.Action.children

let apply_backward theorem_state action =
  validate_action_inverse theorem_state action;
  unsolve action.Action.target;
  remove_subgoals theorem_state action.Action.children;
  add_subgoal' theorem_state action.Action.target

let record_action theorem_state action =
  History.add theorem_state.history action

let apply theorem_state action =
  apply_forward theorem_state action;
  record_action theorem_state action

let history_step_backward theorem_state =
  match History.step_backward theorem_state.history with
  | Option.Some x -> apply_backward theorem_state x; true
  | Option.None -> false

let history_step_forward theorem_state =
  match History.step_forward theorem_state.history with
  | Option.Some x -> apply_forward theorem_state x; true
  | Option.None -> false

(** Alias to be used when this module is open. *)
type theorem = t

let printf t x = Format.fprintf t.ppf x

let get_entry' t =
  let cid = t.cid in
  (cid, Store.Cid.Comp.get cid)

let get_cid t = t.cid
let get_entry t = get_entry' t |> Pair.snd
let get_name t = (get_entry t).Store.Cid.Comp.Entry.name
let has_name_of t name = Name.(get_name t = name)
let has_cid_of t cid = t.cid = cid

let get_statement t = t.initial_state.Comp.goal

let serialize ppf (t : t) =
  let name = Store.Cid.Comp.name t.cid in
  dprintf begin fun p ->
    p.fmt "[theorem] [serialize] begin serialization of theorem '%a'"
      Name.pp name
    end;
  let s = t.initial_state in
  let goal = Whnf.cnormCTyp s.Comp.goal in
  let fmt_ppr_order =
    Option.print
      begin fun ppf ->
      function
      | `inductive order ->
         Format.fprintf ppf "/ @[<hov 2>total@ @[%a@]@] /"
           P.fmt_ppr_cmp_numeric_order (Erase.numeric_order goal order)
      | `not_recursive -> Format.fprintf ppf "/ total /"
      | `partial -> ()
      | `trust -> Format.fprintf ppf "/ trust /"
      end
  in
  let order =
    let open Option in
    Total.lookup_dec name (Store.Cid.Comp.total_decs t.cid)
    $> fun o -> o.Comp.order
  in
  Printer.with_implicits false
    begin fun _ ->
    Format.fprintf ppf "@[<v>proof %a : %a =@,%a@,%a@,@]"
      Name.pp name
      Comp.(P.fmt_ppr_cmp_typ s.context.cD P.l0) goal
      fmt_ppr_order order
      Comp.(P.fmt_ppr_cmp_proof s.context.cD s.context.cG) (Comp.incomplete_proof Beluga_syntax.Location.ghost s)
    end

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
  let open Option in
  t.remaining_subgoals
  |> DynArray.to_list
  |> List.index_of p
  $> begin fun idx ->
     let sg = DynArray.get t.remaining_subgoals idx in
     DynArray.delete t.remaining_subgoals idx;
     DynArray.insert t.remaining_subgoals 0 sg;
     sg
     end

let dump_proof ppf t =
  let s = t.initial_state in
  Format.fprintf ppf "%a"
    Comp.(P.fmt_ppr_cmp_proof s.context.cD s.context.cG) (Comp.incomplete_proof Beluga_syntax.Location.ghost s)

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
  printf t "@[<v>%a@]"
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

let remove_current_subgoal t =
  DynArray.delete t.remaining_subgoals 0

(** Moves the current subgoal to the back of the list.
    Does not run subgoal hooks!
 *)
let defer_subgoal t =
  let g = DynArray.get t.remaining_subgoals 0 in
  remove_current_subgoal t;
  DynArray.add t.remaining_subgoals g

(** High-level solving tactic.
    apply_subgoal_replacement t g' f g
    - removes the current subgoal (which must be g)
    - fill's in g's solution with an incomplete proof for g', transformed by f.
 *)
let apply_subgoal_replacement t name g' f g =
  let p = f (Comp.incomplete_proof Beluga_syntax.Location.ghost g') in
  apply t (Action.make name g [g'] p)

(** Renames a variable from `src` to `dst` at the given level
    (`comp or `meta) in the subgoal `g`.
 *)
let rename_variable src dst level t g =
  let open Option in
  let open Comp in
  begin match level with
  | `comp ->
     Context.rename_gctx src dst g.context.cG
     $> fun cG -> { g.context with cG }
  | `meta ->
     Context.rename_mctx src dst g.context.cD
     $> fun cD -> { g.context with cD }
  end
  $> (fun context -> { g with context; solution = ref None })
  $> (fun g' -> apply_subgoal_replacement t "rename" g' Fun.id g)
  |> is_some

(** Registers the theorem in the store.
    The statement of the theorem must be stripped of totality
    annotations.
 *)
let register name tau p mutual_group k : cid_prog =
  Store.Cid.Comp.add
    begin fun cid ->
    let v = Comp.(ThmValue (cid, Proof p, Whnf.m_id, Empty)) in
    Store.Cid.Comp.mk_entry name tau k
      mutual_group
      (Some v)
    end

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
  dprintf begin fun p ->
    p.fmt "[theorem] configuring theorem %a"
      Name.pp (Store.Cid.Comp.name cid)
    end;
  let t =
    { cid
    ; initial_state
    ; remaining_subgoals = DynArray.make 16
    ; subgoal_hooks = DynArray.create ()
    ; ppf
    ; history = History.create ()
    }
  in
  let hooks = List.map (fun h -> h t) hooks in
  DynArray.append_list t.subgoal_hooks hooks;
  add_subgoals t gs;
  t

(** Converts Theorem.Conf.t to Theorem.t by adding all the theorems
    to the store.
 *)
let configure_set ppf (hooks : (t -> Comp.proof_state -> unit) list) (confs : Conf.t list)
    : Id.cid_mutual_group * t list =
  let mutual_group =
    Store.Cid.Comp.add_mutual_group
      (List.map Pair.fst confs)
  in
  let configure ({ Comp.name; tau; order }, k) =
    let tau' = Total.annotate Beluga_syntax.Location.ghost order tau in
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
    let p = Comp.incomplete_proof Beluga_syntax.Location.ghost g in
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

let is_complete t =
  DynArray.length t.remaining_subgoals = 0

let subgoals t = DynArray.to_list t.remaining_subgoals

let count_subgoals t = DynArray.length t.remaining_subgoals
