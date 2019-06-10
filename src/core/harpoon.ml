(* module Harpoon *)

module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

module P = Pretty.Int.DefaultPrinter

let dprint, _ = Debug.makeFunctions (Debug.toFlags [11])

(** Gives a more convenient way of writing complex proofs by using list syntax. *)
let prepend_commands (cmds : Comp.command list) (proof : 'a Comp.proof)
    : 'a Comp.proof =
  List.fold_right Comp.proof_cons cmds proof

(** Decides whether something we're splitting on is inductive.
    Either:
    * it's a computational variable whose type is TypInd or with a WF
      flag
    * or it's a metavariable such that when you look it up in the
      context cD it's marked Inductive.

    This is similar to the logic used in check.ml to determine the
    kind of a branch: [Ind]DataObj or [Ind]IndexObj.
 *)
let is_inductive (cG : Comp.gctx) (cD : LF.mctx) (m : Comp.exp_syn) : bool =
  let open Comp in
  let open Id in
  let is_inductive_comp_variable (k : offset) : bool =
    Context.lookup' cG k
    |> Maybe.get' (Failure "Computational variable out of bounds")
    |> function
      (* Either it's a TypInd or the WF flag is true *)
      | CTypDecl (u, tau, true) -> true
      | CTypDecl (u, TypInd _, _) -> true
      | _ -> false
  in
  let is_inductive_meta_variable (k : offset) : bool =
    Context.lookup_dep cD k
    |> Maybe.get' (Failure "Metavariable out of bounds or missing type")
    |> fun (_, dep) -> dep = LF.Inductive
  in
  let open Maybe in
  variable_of_exp m $> is_inductive_comp_variable $ of_bool |> is_some
  || metavariable_of_exp m $> fst $> is_inductive_meta_variable $ of_bool |> is_some


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
      ; cIH = s.context.cIH (* TODO shift any IHs *)
      }
    in
    let new_state = { context; goal = goal'; solution = None } in
    (* Invoke the callback on the subgoal that we created *)
    callback new_state;
    (* Solve the current goal with the subgoal. *)
    Comp.intros context (Comp.incomplete_proof new_state)
    |> solve' s

  let split (m : Comp.exp_syn) (tau : Comp.typ) : t =
    let open Comp in
    fun s callback ->
    (* Compute the coverage goals for the type to split on *)
    dprint
      (fun _ ->
        "[harpoon-split] splitting on "
        ^ P.expSynToString s.context.cD s.context.cG m);
    let cgs =
      Coverage.genPatCGoals
        s.context.cD
        (Coverage.gctx_of_compgctx s.context.cG)
        (* We need to strip off the inductivity annotations as the
           coverage checker generally pretends they don't exist
         *)
        (Total.strip tau)
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
      | Coverage.CovCtx cPsi ->
         Format.eprintf "OH NO 1\n";
         Misc.not_implemented "CovCtx impossible"
      | Coverage.CovGoal (cPsi, tR, (tau', ms')) ->
         Format.eprintf "OH NO 2\n";
         Misc.not_implemented "CovGoal impossible"
      | Coverage.CovPatt (cG, p, tau) ->
         match p with
         | PatMetaObj (_, patt) ->
            let open Comp in
            let refine_ctx ctx = Whnf.cnormCtx (Whnf.normCtx ctx, ms) in
            let cG = refine_ctx s.context.cG in
            let cIH = refine_ctx s.context.cIH in
            dprint
              (fun _ ->
                "[harpoon-split] got pattern " ^ P.patternToString cD cG p);
            let (cD, cIH') =
              if is_inductive cG cD m && Total.struct_smaller p
              then
                (* mark subterms in the context as inductive *)
                let cD1 = Check.Comp.mvars_in_patt cD p in
                (* Compute the well-founded recursive calls *)
                let cIH = Total.wf_rec_calls cD1 LF.Empty (Misc.not_implemented "mfs") in
                dprint
                  (fun _ ->
                    "[harpoon-split] computed WF rec calls "
                    ^ P.gctxToString cD cIH);

                (cD1, cIH)
              else
                (cD, LF.Empty)
            in
            let cD = Check.Comp.id_map_ind cD ms s.context.cD in
            let cIH0 = Total.wf_rec_calls cD cG (Misc.not_implemented "mfs") in

            let h =
              { cD
              ; cG
              ; cIH =
                  Context.append cIH
                    (Context.append cIH0 cIH')
              }
            in

            let new_state =
              { context = h
              ; goal = Pair.rmap (fun s -> Whnf.mcomp s ms) s.goal
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
    Comp.split m tau bs
    |> solve' s

  let useIH (m : Comp.exp_syn) (tau : Comp.typ) (name : Id.name) : t =
    fun g callback ->
    let open Comp in
    let new_state =
      { g with
        context =
          { g.context with
            cG =
              LF.Dec
                ( g.context.cG
                , CTypDecl (name, tau, false)
                )
          }
      ; solution = None
      }
    in
    callback new_state;
    prepend_commands
      [ Comp.IH (m, name) ]
      (Comp.incomplete_proof new_state)
    |> solve' g

end

module Prover = struct
  type interpreter_state =
    { initial_state : unit Comp.proof_state
    (* ^ it's important to remember the initial proof state, since it
       gives us a way to track the original full statement of the theorem
       to prove as well as a handle on the whole (partial) proof.
     *)
    ; remaining_subgoals : unit Comp.proof_state DynArray.t
    ; theorem_name : Id.name
    ; order : Comp.order
    }

  let make_prover_state
        (name : Id.name)
        (order : Comp.order)
        (s : unit Comp.proof_state)
      : interpreter_state =
    { initial_state = s
    ; remaining_subgoals = DynArray.of_list [s]
    ; theorem_name = name
    ; order = order
    }

  (** Computes the index of the current subgoal we're working on. *)
  let current_subgoal_index gs =
    DynArray.length gs - 1

  (** Gets the next subgoal from the interpreter state.
      Returns `None` if there are no subgoals remaining.
   *)
  let next_subgoal (s : interpreter_state) : unit Comp.proof_state option =
    let gs = s.remaining_subgoals in
    if DynArray.empty gs then
      None
    else
      Some (DynArray.get gs (current_subgoal_index gs))

  let process_command
        (ppf : Format.formatter)
        (s : interpreter_state) (g : unit Comp.proof_state)
        (cmd : Syntax.Ext.Harpoon.command)
      : unit =
    let module Command = Syntax.Ext.Harpoon in
    let add_subgoal = DynArray.insert s.remaining_subgoals 0 in
    let remove_current_subgoal () =
      let gs = s.remaining_subgoals in
      DynArray.delete gs (current_subgoal_index gs)
    in
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
    | Command.ShowIHs ->
       let f i =
         Format.fprintf ppf "%d. %a@."
           (i + 1)
           (P.fmt_ppr_cmp_ctyp_decl g.context.cD Pretty.std_lvl)
       in
       Format.fprintf ppf "There are %d IHs:@."
         (Context.length g.context.cIH);
       Context.to_list g.context.cIH |> List.iteri f

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
    | Command.UseIH (t, name (* , typ *)) ->
       let cG' =
         (* We elaborate the IH in an extended context with the
            theorem already defined.
            This is just to make sure that the appeal to the IH is
            well-typed; we check well-foundedness after.
            It's worth noting that because of this, all the
            (computational) indices will be off-by-one compared to the
            smaller context, so we will need to shift them down.
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
       dprint
         (fun _ ->
           "[harpoon-UseIH] elaborated IH: "
           ^ P.expSynToString cD cG' m
           ^ " : "
           ^ P.compTypToString cD tau
           ^ " in cIH = " ^ P.gctxToString cD cIH);
       (* This will verify that the IH is well-founded
          (Ignoring thepresence of bugs)
        *)
       let _ = Check.Comp.syn cD cG' (Misc.not_implemented "mfs") m in
       Tactic.useIH m tau name g add_subgoal;
       remove_current_subgoal ()

    | Command.Solve m ->
       let m = Interactive.elaborate_exp cD cG m g.goal in
       try
         Check.Comp.check cD cG (Misc.not_implemented "mfs") m g.goal;
         Comp.solve m
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
         "@.@[<v>Current state:@.%a@]@.There are %d IHs.@.%s> @?"
         P.fmt_ppr_cmp_proof_state g
         (Context.length g.Comp.context.Comp.cIH)
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
        (order : Comp.order) (* The induction order of the theorem *)
      : unit =
    Comp.make_proof_state stmt
    |> make_prover_state name order
    |> loop ppf
end
