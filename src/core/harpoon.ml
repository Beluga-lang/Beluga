(* module Harpoon *)

module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

(** Gives a more convenient way of writing complex proofs by using list syntax. *)
let prepend_statements (stmts : 'a Comp.statement list) (proof : 'a Comp.proof)
    : 'a Comp.proof =
  List.fold_right Comp.proof_cons stmts proof

(** All the high-level proof tactics.
 * In general, a tactic has inputs
 * 1. Some tactic-specific parameters
 * 2. A `proof_state` to act on
 * 3. An action to perform for each subgoal introduced.
 *
 * Each tactic is expected to _solve_ the input `proof_state`,
 * i.e. fill its `solution` field.
 *)
module Tactic = struct
  type t = unit Comp.proof_state -> (unit Comp.proof_state -> unit) -> unit

  (** Fill the hole with the given proof. *)
  let solve (proof : Comp.incomplete_proof) : t =
    fun s _ ->
    s.Comp.solution <- Some proof

  (** `solve` with the arguments switched around to make it more
      convenient to call from other tactics.
   *)
  let solve' (s : unit Comp.proof_state) (proof : Comp.incomplete_proof) : unit =
    solve proof s (fun _ -> ())

  (** Introduces all assumptions present in the current goal.
      Solves the input proof state.
   *)
  let intros : t =
    let genVarName tA = Store.Cid.Typ.gen_var_name tA in
    let gen_var_for_typ =
      function
      | Comp.TypBox (l, LF.ClTyp (LF.MTyp tA, psi)) ->
         Id.mk_name (Id.BVarName (genVarName tA))
      | Comp.TypBox (l, LF.ClTyp (LF.PTyp tA, psi)) ->
         Id.mk_name (Id.PVarName (genVarName tA))
      | _ ->
         Id.mk_name Id.NoName
    in
    (* Walks a type and collects assumptions into cD and cG,
       returning the conclusion type.
     *)
    let rec intro' (cD : LF.mctx) (cG : Comp.gctx) (t : Comp.typ)
            : LF.mctx * Comp.gctx * Comp.typ =
      match t with
      | Comp.TypArr (t1, t2) ->
         let name = gen_var_for_typ t1 in
         intro' cD (LF.Dec (cG, Comp.CTypDecl (name, t1, false))) t2
      | Comp.TypPiBox (tdec, t2) ->
         intro' (LF.Dec (cD, tdec)) cG t2
      | _ -> cD, cG, t
    in
    (* Main body of `intros`: *)
    fun s callback ->
    let open Comp in
    let (t, sigma) = s.goal in
    let cD, cG, t' = intro' LF.Empty LF.Empty t in
    let goal' = (t', sigma) in
    let context =
      { cG = Context.append s.context.cG cG
      ; cD = Context.append s.context.cD cD
      }
    in
    let new_state = { context; goal = goal'; solution = None } in
    (* Invoke the callback on the subgoal that we created *)
    callback new_state;
    (* Solve the current goal with the subgoal. *)
    prepend_statements
      [ Comp.intros context (Comp.incomplete_proof new_state)
      ; Comp.claim s.context.cD s.goal
      ]
      Comp.QED
    |> solve' s

           (* let split : Comp.meta_obj -> t = Misc.not_implemented "Tactic.split" *)
end

module Prover = struct
  module P = Pretty.Int.DefaultPrinter

  type interpreter_state =
    { initial_state : unit Comp.proof_state
    ; remaining_subgoals : unit Comp.proof_state DynArray.t
    }

  let make_prover_state (s : unit Comp.proof_state) : interpreter_state =
    { initial_state = s
    ; remaining_subgoals = DynArray.of_list [s]
    }

  (** Gets the next subgoal from the interpreter state.
      Returns `None` if there are no subgoals remaining.
   *)
  let next_subgoal (s : interpreter_state) : unit Comp.proof_state option =
    let a = s.remaining_subgoals in
    if DynArray.empty a then
      None
    else
      Some (DynArray.get a 0)

  let process_command
        (ppf : Format.formatter)
        (s : interpreter_state) (g : unit Comp.proof_state)
        (cmd : Syntax.Ext.Harpoon.command)
      : unit =
    let module Command = Syntax.Ext.Harpoon in
    let add_subgoal = DynArray.add s.remaining_subgoals in
    let remove_current_subgoal () = DynArray.delete s.remaining_subgoals 0 in
    let open Comp in
    let { cD; cG } = g.context in
    match cmd with
    (* Administrative commands: *)
    | Command.ShowProof ->
       (* This is a trick to print out the proof resulting from
          the initial state correctly. The initial state's solution
          might be None or Some; we don't know. Rather than handle
          that distinction here, we can wrap the state into a proof
          that immediate ends with Incomplete. The proof
          pretty-printer will then deal with the None/Some for us by
          printing a `?` if the initial state hasn't been solved
          yet.
        *)
       let s = s.initial_state in
       Format.fprintf ppf "Proof so far:@,%a"
         (P.fmt_ppr_cmp_proof cD cG) (incomplete_proof s)

    (* Real tactics: *)
    | Command.Intros ->
       Tactic.intros g add_subgoal;
       remove_current_subgoal ()
  let rec loop ppf (s : interpreter_state) : unit =
    (* Get the next subgoal *)
    match next_subgoal s with
    | None -> () (* we're done; proof complete *)
    | Some g ->
       (* Show the proof state and the prompt *)
       Format.fprintf ppf "@.Current state:@.%a@.@.\xCE\xBB> @?" P.fmt_ppr_cmp_proof_state g;

       (* Parse the input.*)
       let input = read_line () in
       let cmd = Parser.parse_string ~name: "command line" ~input: input Parser.harpoon_command in
       process_command ppf s g cmd;
       loop ppf s

  let start_toplevel (ppf : Format.formatter) (name : string) (stmt : Comp.tclo) : unit =
    let initial_state = stmt |> Comp.make_proof_state |> make_prover_state in
    loop ppf initial_state
end
