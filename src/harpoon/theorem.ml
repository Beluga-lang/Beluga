(* open Support *)
open Support
open Beluga
module Comp = Syntax.Int.Comp
open Id

module P = Pretty.Int.DefaultPrinter

module Conf = struct
  type t = Comp.total_dec * int

  let make name order tau implicit_parameters =
    ({ Comp.name; order; tau}, implicit_parameters)
end

(** A single theorem. *)
type t =
  { (* The name of the theorem. *)
    name : name

  (* The Store entry for the theorem. *)
  ; cid : cid_prog

  (* The induction order for this theorem. *)
  ; order : Comp.order option

  (* It's important to remember the initial proof state, since it
     gives us a way to track the original full statement of the theorem
     to prove as well as a handle on the whole (partial) proof.
   *)
  ; initial_state : Comp.proof_state

  (* The remaining subgoals for this theorem. *)
  ; remaining_subgoals : Comp.proof_state DynArray.t

  (* A list of hooks to run on every new subgoal that is added to this theorem. *)
  ; subgoal_hooks : (Comp.proof_state -> unit) DynArray.t

  (* So tactics can print messages. *)
  ; ppf : Format.formatter
  }

(** Alias to be used when this module is open. *)
type theorem = t

let printf t x = Format.fprintf t.ppf x

let get_name t = t.name
let has_name_of t name = equals (get_name t) name
let has_cid_of t cid = t.cid = cid

(** Gets the statement of the given theorem. *)
let theorem_statement (t : t) =
  Whnf.cnormCTyp t.initial_state.Comp.goal

let serialize ppf (t : t) =
  let s = t.initial_state in
  let fmt_ppr_order ppf =
    function
    | Some (Arg o) -> Format.fprintf ppf "/ total %d /" o
    | None -> ()
    | _ -> failwith "Invalid order"
  in
  Format.fprintf ppf "@[<v>proof %a : %a =@,%a@,%a@,;@,@]"
    Id.print t.name
    (P.fmt_ppr_cmp_typ s.context.cD P.l0) (Whnf.cnormCTyp s.goal)
    fmt_ppr_order t.order
    (P.fmt_ppr_cmp_proof s.context.cD s.context.cG) (incomplete_proof s)

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
  let s = t.initial_state in
  printf t "@[<v>Proof so far:@,%a@,@]"
    Comp.(P.fmt_ppr_cmp_proof s.context.cD s.context.cG) (Comp.incomplete_proof s)

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

let remove_subgoal t g =
  let i = DynArray.index_of (fun g' -> g = g') t.remaining_subgoals in
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
  s.Comp.solution <- Some proof

(** High-level solving tactic.
    solve_by_replacing_subgoal g' f g t
    - removes the current subgoal (which must be g)
    - fill's in g's solution with an incomplete proof for g', transformed by f.
 *)
let solve_by_replacing_subgoal t g' f g =
  replace_subgoal t g';
  f (Comp.incomplete_proof g') |> solve g

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
    ; solution = None
    }
  in
  solve_by_replacing_subgoal t g' Misc.id g

let register { Comp.name; tau; order } total_decs implicit_parameters : cid_prog =
  let open Store.Cid.Comp in
  add Syntax.Loc.ghost
    begin fun _ ->
    mk_entry name (Total.strip tau) implicit_parameters
      total_decs (* all Harpoon theorems are total *)
      None (* we don't have an evaluated form *)
    end
  |> snd

(** Creates the theorem from the configuration and a cid.
    (You need to add the theorem to the Store before trying to call
    this function to get a cid allocated.)
    This function will
    - construct the initial state;
    - allocate & populate the array of subgoal hooks;
    - construct the array of pending subgoals;
    - add the initial state to the subgoal array.
      (This will run the subgoal hooks.)
 *)
let configure { Comp.name; tau; order } cid ppf hooks =
  let initial_state =
    Comp.make_proof_state
      [Id.render_name name]
      (tau, Whnf.m_id)
  in
  let t =
    { cid
    ; order
    ; name
    ; initial_state
    ; remaining_subgoals = DynArray.make 16
    ; subgoal_hooks = DynArray.create ()
    ; ppf
    }
  in
  let hooks = List.map (fun h -> h t) hooks in
  Misc.DynArray.append_list t.subgoal_hooks hooks;
  add_subgoal t initial_state;
  t

(** Converts Theorem.Conf.t to Theorem.t by adding all the theorems
    to the store.
 *)
let configure_set ppf (hooks : (t -> Comp.proof_state -> unit) list) (confs : Conf.t list) : t list =
  let configure ({ Comp.name; tau; order } as conf, k) =
    (* add the theorem to the store to get a cid allocated *)
    let cid = register conf (Some (List.map fst confs)) k in
    (* configure the theorem *)
    configure conf cid ppf hooks
  in
  List.map configure confs

let total_dec (t : t) =
  Comp.make_total_dec
    t.name
    Comp.(Whnf.cnormCTyp t.initial_state.goal |> Total.strip)
    t.order

let set_hidden (t : t) b =
  Store.Cid.Comp.set_hidden t.cid (Misc.const b)

(* Invokes the translation procedure on a given theorem *)
let translate (thm : t) : Comp.exp_chk =
  let open Comp in
  let state = thm.initial_state in
  let cD = state.context.cD in
  let cG = state.context.cG in
  let (tau, _) = state.goal in
  Translate.translate_proof cD cG (Option.get state.solution) tau
