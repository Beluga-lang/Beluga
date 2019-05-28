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
  let intros (names : string list option) : t =
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
    let rec intro'
              (names : string list option)
              (cD : LF.mctx) (cG : Comp.gctx) (t : Comp.typ)
            : LF.mctx * Comp.gctx * Comp.typ =
      let next_name : (string * string list) option =
        let open Maybe in
        names
        $ function
          | [] -> None
          | x :: xs -> Some (x , xs)
      in
      match t with
      | Comp.TypArr (t1, t2) ->
         let name , names =
           next_name
           |> Maybe.eliminate
                (fun _ -> gen_var_for_typ t1 , None)
                (fun (name, names) -> Id.mk_name (Id.SomeString name), Some names)
         in
         intro' names cD (LF.Dec (cG, Comp.CTypDecl (name, t1, false))) t2
      | Comp.TypPiBox (tdec, t2) ->
         intro' names (LF.Dec (cD, tdec)) cG t2
      | _ -> cD, cG, t
    in
    (* Main body of `intros`: *)
    fun s callback ->
    let open Comp in
    let (t, sigma) = s.goal in
    let cD, cG, t' = intro' names LF.Empty LF.Empty t in
    let goal' = (t', sigma) in
    let context =
      { cG = Context.append s.context.cG cG
      ; cD = Context.append s.context.cD cD
      ; cIH = s.context.cIH
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

  let split (m : Comp.exp_syn) (tau : Comp.typ) : t =
    let open Comp in
    fun s callback ->
    (* Compute the coverage goals for the type to split on *)
    let cgs =
      Coverage.genPatCGoals
        s.context.cD
        (Coverage.gctx_of_compgctx s.context.cG)
        tau
        []
    in
    (* We will map f over the coverage goals that were generated.
       f computes the subgoal for the given coverage goal, invokes the
       callback on the computed subgoal (to register it), and
       constructs the Harpoon syntax for this split branch.
     *)
    let f (cD, cov_goal, ms) =
      match cov_goal with
      (* Because we called genPatCGoals, I'm pretty sure that the
         CovCtx and CovGoal constructors are impossible here,
         but I could be wrong.
       *)
      | Coverage.CovCtx cPsi -> Misc.not_implemented "split on context variables"
      | Coverage.CovGoal (cPsi, tR, (tau', ms')) -> Misc.not_implemented "bar"
      | Coverage.CovPatt (cG, patt, tau) ->
         let cG = Coverage.compgctx_of_gctx cG in
         let open Comp in
         let h = { cD; cG; cIH = s.context.cIH } in
         let goal_type, goal_sub = s.goal in
         let new_state =
           { context = h
           ; goal = (goal_type, Whnf.mcomp goal_sub ms)
           (* ^ our goal already has a delayed msub, so we compose the
              one we obtain from the split (the refinement substitution)
              with the one we have (eagerly).
            *)
           ; solution = None
           }
         in
         callback new_state;
         split_branch h (incomplete_proof new_state)
    in
    let bs = List.map f cgs in
    (* Assemble the split branches computed in `bs` into the Harpoon
       Split syntax.
     *)
    prepend_statements
      [ Comp.split m tau bs ]
      Comp.QED
    |> solve' s
end

module Prover = struct
  module P = Pretty.Int.DefaultPrinter

  type interpreter_state =
    { initial_state : unit Comp.proof_state
    (* ^ it's important to remember the initial proof state, since it
       gives us a way to track the original full statement of the theorem
       to prove as well as a handle on the whole (partial) proof.
     *)
    ; remaining_subgoals : unit Comp.proof_state DynArray.t
    ; theorem_name : Id.name
    ; order : Order.order
    }

  let make_prover_state
        (name : Id.name)
        (order : Order.order)
        (s : unit Comp.proof_state)
      : interpreter_state =
    { initial_state = s
    ; remaining_subgoals = DynArray.of_list [s]
    ; theorem_name = name
    ; order = order
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
    let { cD; cG; cIH } = g.context in
    match cmd with
    (* Administrative commands: *)
    | Command.ShowProof ->
       (* This is a trick to print out the proof resulting from
          the initial state correctly. The initial state's solution
          might be None or Some; we don't know. Rather than handle
          that distinction here, we can wrap the state into a proof
          that immediately ends with Incomplete. The proof
          pretty-printer will then deal with the None/Some for us by
          printing a `?` if the initial state hasn't been solved
          yet.
        *)
       let s = s.initial_state in
       Format.fprintf ppf "@[<v>Proof so far:@.%a@]"
         (P.fmt_ppr_cmp_proof cD cG) (incomplete_proof s)
    | Command.Defer ->
       (* Remove the current subgoal from the list (it's in head position)
        * and then add it back (on the end of the list) *)
       remove_current_subgoal ();
       add_subgoal g

    (* Real tactics: *)
    | Command.Intros names ->
       Tactic.intros names g add_subgoal;
       remove_current_subgoal ()
    | Command.Split t ->
       let (m, tau) =
         let (m, (tau, ms)) = Interactive.elaborate_exp' cD cG t in
         (Whnf.cnormExp' (m, ms), Whnf.cnormCTyp (tau, ms))
       in
       (*
       Format.fprintf ppf "@[Elaborated term:@;%a : %a@,"
         (P.fmt_ppr_cmp_exp_syn g.context.cD g.context.cG Pretty.std_lvl) m
         (P.fmt_ppr_cmp_typ g.context.cD Pretty.std_lvl) tau;
        *)
       Tactic.split m tau g add_subgoal;
       remove_current_subgoal ()
    | Command.UseIH (t, name, typ) ->
       let cG' =
         (* We elaborate the IH in an extended context with the
            theorem already defined.
            This is just to make sure that the appeal to the IH is
            well-typed; we check well-foundededness separately
            after.
            It's worth noting that because of this, all the
            indices will be off-by-one compared to the smaller
            context, so we will need to shift them down.
          *)
         LF.Dec
           ( cG
           , Comp.CTypDecl
               ( s.theorem_name
               , Whnf.cnormCTyp s.initial_state.Comp.goal |> Total.strip
               (* In command.ml, when we enter Harpoon, we pass
                  the theorem to prove *with* induction
                  annotations. Sadly, elaboration does *not* play
                  nice with these annotations, so we need to strip
                  them off when we elaborate the IH.
                *)
               , false
               )
           )
       in
       let (m, tau) =
         let (m, (tau, ms)) = Interactive.elaborate_exp' cD cG' t in
         (Whnf.cnormExp' (m, ms), Whnf.cnormCTyp (tau, ms))
       in
       Format.fprintf ppf "Elaborated IH: %a : %a@."
         (P.fmt_ppr_cmp_exp_syn cD cG' Pretty.std_lvl) m
         (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) tau;
    (*  Misc.not_implemented "UseIH" *)

    | Command.Solve m ->
       let m = Interactive.elaborate_exp cD cG m g.goal in
       try
         Check.Comp.check cD cG m g.goal;
         prepend_statements
           [ Comp.claim ~term: (Some m) cD g.goal ]
           Comp.QED
         |> Tactic.solve' g;
         remove_current_subgoal ()
       with
         Check.Comp.Error (_l, _e) ->
          Printexc.print_backtrace stderr

  (** A computed value of type 'a or a function to print an error. *)
  type 'a error = (Format.formatter -> unit, 'a) Either.t

  (** Parses the given string to a Syntax.Ext.Harpoon.command or an
      error-printing function.
   *)
  let parse_input (input : string) : Syntax.Ext.Harpoon.command error =
    try
      Parser.parse_string
        ~name: "command line"
        ~input: input
        Parser.harpoon_command
      |> Either.pure
    with
    | Parser.Grammar.Loc.Exc_located (_, _) as e ->
       Either.Left
         (fun ppf ->
           Format.fprintf ppf
             "@[<v>Parse error.@.%s@]"
             (Printexc.to_string e))

  (** Runs the given function, trapping exceptions in Either.t
      and converting the exception to a function that prints the
      error with a given formatter.
   *)
  let run_safe (f : unit -> 'a) : 'a error =
    let show_error e ppf =
      Format.fprintf ppf
        "@[<v>Internal error. (State may be undefined.)@.%s@]"
        (Printexc.to_string e)
    in
    Either.trap f |> Either.lmap show_error

  (* UTF-8 encoding of the lowercase Greek letter lambda. *)
  let lambda : string = "\xCE\xBB"

  let rec loop ppf (s : interpreter_state) : unit =
    (* Get the next subgoal *)
    match next_subgoal s with
    | None ->
       Format.fprintf ppf "@.Proof complete! (No subgoals left.)@.";
       () (* we're done; proof complete *)
    | Some g ->
       (* Show the proof state and the prompt *)
       Format.fprintf ppf
         "@.@[<v>Current state:@.%a@]@.@.%s> @?"
         P.fmt_ppr_cmp_proof_state g
         lambda;

       (* Parse the input and run the command *)
       let input = read_line () in
       let e =
         let open Either in
         parse_input input
         $ fun cmd ->
           run_safe (fun () -> process_command ppf s g cmd)
       in
       Either.eliminate
         (fun f -> f ppf)
         (Misc.const ())
         e;
       loop ppf s

  let start_toplevel
        (ppf : Format.formatter) (* The formatter used to display messages *)
        (name : Id.name) (* The name of the theorem to prove *)
        (stmt : Comp.tclo) (* The statement of the theorem *)
        (order : Order.order) (* The induction order of the theorem *)
      : unit =
    Comp.make_proof_state stmt
    |> make_prover_state name order
    |> loop ppf
end
