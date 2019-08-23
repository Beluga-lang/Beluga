(* module Harpoon *)

open Support
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp
module Command = Syntax.Ext.Harpoon
module P = Pretty.Int.DefaultPrinter

let dprintf, dprint, _ = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

(** Gives a more convenient way of writing complex proofs by using list syntax. *)
let prepend_commands (cmds : Comp.command list) (proof : 'a Comp.proof)
    : 'a Comp.proof =
  List.fold_right Comp.proof_cons cmds proof

(** Decides whether a data object is something we're doing induction
    on, i.e. it's a computational variable whose type is TypInd or
    with a WF flag

    This is similar to the logic used in check.ml to determine the
    kind of a branch: [Ind]DataObj or [Ind]IndexObj.
 *)
let is_comp_inductive (cG : Comp.gctx) (m : Comp.exp_syn) : bool =
  let open Id in
  let open Comp in
  let is_inductive_comp_variable (k : offset) : bool =
    Context.lookup' cG k
    |> Maybe.get' (Failure "Computational variable out of bounds")
    |> function
      (* Either it's a TypInd or the WF flag is true *)
      | CTypDecl (u, tau, true) -> true
      | CTypDecl (u, TypInd _, _) -> true
      | _ -> false
  in
  let open Maybe in
  variable_of_exp m
  $> is_inductive_comp_variable
  $ of_bool
  |> is_some

  (*
(** Decides whether an index object is something we're doing
    induction on, i.e. it's a metavariable with the Inductive flag set
    when we look it up in the meta-context.
 *)
let is_meta_inductive (cD : LF.mctx) (mf : LF.mfront) : bool =
  let open Id in
  let open LF in
  let is_inductive_meta_variable (k : offset) : bool =
    Context.lookup_dep cD k
    |> Maybe.get' (Failure "Metavariable out of bounds or missing type")
    |> fun (_, dep) -> dep = LF.Inductive
  in
  let open Maybe in
  variable_of_mfront mf
  $> fst
  $> is_inductive_meta_variable
  $ of_bool
  |> is_some
   *)

(** Given an initial context cDl and a refined context cDl', compute the
    list of all declarations in cD' that are either new variables (not
    present in cD) or have different types in the new context
    (refined).
    The contexts cDl and cDl' should have been converted to lists using
    Context.to_list.
 *)
let filter_mctx_refinement
      (cDl : LF.ctyp_decl list) (cDl' : LF.ctyp_decl list)
    : LF.ctyp_decl list =
  let f d =
    match List.find_opt (fun d' -> Whnf.convCTypDecl d d') cDl with
    | Some _ ->
       false
    | None ->
       (* if we cannot find a convertible declaration in the original
          context, then we keep the current declaration d.
        *)
       true
  in
  List.filter f cDl'

module type TacticContext = sig
  val add_subgoal : unit Comp.proof_state -> unit
  val remove_current_subgoal : unit -> unit

  (** Shows a message to the user. *)
  val printf : ('a, Format.formatter, unit) format -> 'a
end

(** All the high-level proof tactics.
 * In general, a tactic has inputs
 * 1. Some tactic-specific parameters
 * 2. A `proof_state` to act on
 *
 * Tactics are parameterized by a TacticContext that gives them
 * certain capabilities, such as manipulating the subgoal list or
 * showing messages to the user.
 *
 * Tactics are not obligated to solve the current subgoal!
 *)
module Tactic (T : TacticContext) = struct
  type t = unit Comp.proof_state -> unit

  (** `solve` with the arguments switched around to make it more
      convenient to call from other tactics.
   *)
  let solve' (s : unit Comp.proof_state) (proof : Comp.incomplete_proof) : unit =
    s.Comp.solution <- Some proof

  (** Fill the hole with the given proof.
      This will solve the current subgoal.
   *)
  let solve (proof : Comp.incomplete_proof) : t =
    fun s ->
    solve' s proof;
    T.remove_current_subgoal ()

  (** Walks a type and collects assumptions into cD and cG,
      returning the conclusion type.
   *)
  let intros' : string list option -> LF.mctx -> Comp.gctx -> Comp.typ ->
                LF.mctx * Comp.gctx * Comp.typ =
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
    let rec go names cD cG t =
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
         go names cD (LF.Dec (cG, Comp.CTypDecl (name, t1, false))) t2
      | Comp.TypPiBox (tdec, t2) ->
         go names (LF.Dec (cD, tdec)) cG t2
      | _ -> cD, cG, t
    in
    go


  (** Introduces all assumptions present in the current goal.
      Solves the input proof state.
   *)
  let intros (names : string list option) : t =
    (* Main body of `intros`: *)
    fun s ->
    let open Comp in
    let (t, sigma) = s.goal in
    let cD, cG, t' = intros' names LF.Empty LF.Empty t in
    let goal' = (t', sigma) in
    let local_context = {cD; cG; cIH = LF.Empty} in
    let context = Context.append_hypotheses s.context local_context in
    let local_context =
      let c = Context.to_local_context local_context in
      { c with
        cDl = List.mapi (fun i d -> Whnf.cnormCDecl (d, LF.MShift (i + 1))) c.cDl
      }
    in
    let new_state =
      { context
      ; local_context
      ; goal = goal'
      ; solution = None
      }
    in
    (* Invoke the callback on the subgoal that we created *)
    (* Solve the current goal with the subgoal. *)
    T.remove_current_subgoal ();
    T.add_subgoal new_state;
    Comp.intros context local_context (Comp.incomplete_proof new_state)
    |> solve' s

  (** Calls the coverage checker to compute the list of goals for a
      given type in the contexts of the given proof state.
   *)
  let generate_pattern_coverage_goals
        (k : Command.split_kind) (m : Comp.exp_syn) (tau : Comp.typ) (g : unit Comp.proof_state)
      : (LF.mctx * Coverage.cov_goal * LF.msub) list option =
    let open Comp in
    let cgs =
      Coverage.genPatCGoals g.context.cD (Coverage.gctx_of_compgctx g.context.cG) tau []
                            (* XXX should be Total.strip tau? *)
    in
    let n = List.length cgs in
    match k with
    | `invert when n <> 1 ->
       T.printf "Can't invert %a. (Not a unique case.)@,"
         (P.fmt_ppr_cmp_exp_syn g.context.cD g.context.cG Pretty.std_lvl) m;
       None
    | _ -> Some cgs

  let split (k : Command.split_kind) (m : Comp.exp_syn) (tau : Comp.typ) mfs : t =
    let open Comp in
    fun s ->
    (* Compute the coverage goals for the type to split on. *)
    dprintf
      (fun p ->
        p.fmt
          "[harpoon-split] split on %a with type %a"
          (P.fmt_ppr_cmp_exp_syn s.context.cD s.context.cG Pretty.std_lvl) m
       (P.fmt_ppr_cmp_typ s.context.cD Pretty.std_lvl) tau
      );
    match generate_pattern_coverage_goals k m tau s with
    | None -> ()
    (* splitting failed, so we do nothing *)
    | Some cgs ->
       (* We will map f over the coverage goals that were generated.
          f computes the subgoal for the given coverage goal, invokes the
          add_subgoal callback on the computed subgoal (to register it),
          invokes the remove_current_subgoal callback, and constructs the
          Harpoon syntax for this split branch.
        *)
       let f (cD, cov_goal, ms) =
         match cov_goal with
         (* Because we called genPatCGoals, I'm pretty sure that the
            CovCtx and CovGoal constructors are impossible here,
            but I could be wrong.
          *)
         | Coverage.CovCtx _
           | Coverage.CovGoal (_, _, _) ->
            Misc.not_implemented "CovCtx impossible"
         | Coverage.CovPatt (cG, p, tau) ->
            let open Comp in
            let refine_ctx ctx = Whnf.cnormCtx (Whnf.normCtx ctx, ms) in
            let cG = refine_ctx s.context.cG in
            let cIH = refine_ctx s.context.cIH in
            dprint
              (fun _ ->
                "[harpoon-split] got pattern " ^ P.patternToString cD cG p);
            let (cDext, cIH') =
              if is_comp_inductive cG m && Total.struct_smaller p
              then
                (* mark subterms in the context as inductive *)
                let cD1 = Check.Comp.mvars_in_patt cD p in
                (* Compute the well-founded recursive calls *)
                let cIH = Total.wf_rec_calls cD1 LF.Empty mfs in
                dprintf
                  (fun p ->
                    p.fmt "[harpoon-split] @[<v>computed WF rec calls:@,@[<hov>%a@]@]"
                      (P.fmt_ppr_cmp_gctx cD Pretty.std_lvl) cIH);

                (cD1, cIH)
              else
                let _ =
                  dprint
                    (fun _ ->
                      "[harpoon-split] skipped computing WF calls; splitting on non-inductive variable")
                in
                (cD, LF.Empty)
            in
            (* propagate inductive annotations *)
            let cD = Check.Comp.id_map_ind cDext ms s.context.cD in
            dprintf
              (fun p ->
                let open Format in
                p.fmt "[harpoon-split] @[<v 2>id_map_ind@,%a@,ms@,%a@,=@,%a@]"
                  (P.fmt_ppr_lf_mctx ~sep: pp_print_cut Pretty.std_lvl) cDext
                  (P.fmt_ppr_lf_mctx ~sep: pp_print_cut Pretty.std_lvl) s.context.cD
                  (P.fmt_ppr_lf_mctx ~sep: pp_print_cut Pretty.std_lvl) cD);
            let cIH0 = Total.wf_rec_calls cD cG mfs in
            let local_context =
              { no_local_hypotheses with
                cDl =
                  filter_mctx_refinement
                    (Whnf.mctx_to_list_shifted s.context.cD)
                    (Whnf.mctx_to_list_shifted cDext)
              }
            in
            let context =
              { cD
              ; cG
              ; cIH =
                  Context.append cIH
                    (Context.append cIH0 cIH')
              }
            in
            let new_state =
              { context
              ; local_context
              ; goal = Pair.rmap (fun s -> Whnf.mcomp s ms) s.goal
              (* ^ our goal already has a delayed msub, so we compose the
                 one we obtain from the split (the refinement substitution)
                 with the one we have (eagerly).
               *)
              ; solution = None
              }
            in
            (* compute the head of the pattern to be the case label *)
            let patt =
              match p with
              | PatMetaObj (_, patt) -> patt
              | _ -> failwith "splitting on non computation-level types not supported yet"
            in
            let c =
              head_of_meta_obj patt
              |> Maybe.get
              |> Pair.lmap Context.hatToDCtx
            in
            T.add_subgoal new_state;
            meta_branch c context local_context (incomplete_proof new_state)
       in
       T.remove_current_subgoal ();
       let bs = List.map f cgs in
       (* Assemble the split branches computed in `bs` into the Harpoon
          Split syntax.
        *)
       Comp.meta_split m tau bs
       |> solve' s

  let useIH (m : Comp.exp_syn) (tau : Comp.typ) (name : Id.name) : t =
    fun g ->
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
    T.remove_current_subgoal ();
    T.add_subgoal new_state;
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
  let current_subgoal_index gs = 0

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
    let module TCtx : TacticContext =
      struct
        let add_subgoal = DynArray.add s.remaining_subgoals
        let remove_current_subgoal () =
          let gs = s.remaining_subgoals in
          DynArray.delete gs (current_subgoal_index gs)
        let printf x = Format.fprintf ppf x
      end
    in
    let module T = Tactic (TCtx) in
    let open Comp in
    let { cD; cG; cIH } = g.context in
    let mfs =
      (* this should probably directly be a part of interpreter_state,
         or perhaps a part of a larger state for the collection of
         mutually inductive theorems being defined.
       *)
      [ Total.make_total_dec
          s.theorem_name
          (Whnf.cnormCTyp s.initial_state.goal |> Total.strip)
          (Some s.order)
      ]
    in
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
       Format.fprintf ppf "@[<v>Proof so far:@,%a@]"
         (P.fmt_ppr_cmp_proof s.context.cD s.context.cG) (incomplete_proof s)
    | Command.Defer ->
       (* Remove the current subgoal from the list (it's in head position)
        * and then add it back (on the end of the list) *)
       TCtx.remove_current_subgoal ();
       TCtx.add_subgoal g
    | Command.ShowIHs ->
       let f i =
         Format.fprintf ppf "%d. %a@,"
           (i + 1)
           (P.fmt_ppr_cmp_ctyp_decl g.context.cD Pretty.std_lvl)
       in
       Format.fprintf ppf "There are %d IHs:@,"
         (Context.length g.context.cIH);
       Context.to_list g.context.cIH |> List.iteri f

    (* Real tactics: *)
    | Command.Intros names ->
       T.intros names g;
    | Command.Split (split_kind, t) ->
       let (m, tau) =
         let (m, (tau, ms)) = Interactive.elaborate_exp' cD cG t in
         (Whnf.cnormExp' (m, ms), Whnf.cnormCTyp (tau, ms))
       in
       begin
         match tau with
         | TypInd tau | tau ->
            T.split split_kind m tau mfs g
       end
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
               (* ^ In command.ml, when we enter Harpoon, we pass
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
       dprintf
         (fun p ->
           p.fmt
             "@[<v 2>[harpoon-UseIH] elaborated IH:@,%a@ : %a@,in cIH = @[<v>%a@]"
             (P.fmt_ppr_cmp_exp_syn cD cG' Pretty.std_lvl) m
             (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) tau
             (P.fmt_ppr_cmp_gctx cD Pretty.std_lvl) cIH);
       let _ = Check.Comp.syn cD cG' ~cIH: cIH mfs m in
       T.useIH m tau name g;

    | Command.Solve m ->
       let m = Interactive.elaborate_exp cD cG m g.goal in
       try
         Check.Comp.check cD cG mfs m g.goal;
         ( Comp.solve m
           |> T.solve
         ) g ;
       with
         Check.Comp.Error (_l, _e) ->
          Printexc.print_backtrace stderr

  (** A computed value of type 'a or a function to print an error. *)
  type 'a error = (Format.formatter -> unit, 'a) Either.t

  (** Parses the given string to a Syntax.Ext.Harpoon.command or an
      error-printing function.
   *)
  let parse_input (input : string) : Syntax.Ext.Harpoon.command error =
    Runparser.parse_string "<prompt>" input Parser.(only harpoon_command)
    |> snd |> Parser.to_either
    |> Either.lmap (fun e ppf -> Parser.print_error ppf e)

  (** Runs the given function, trapping exceptions in Either.t
      and converting the exception to a function that prints the
      error with a given formatter.
   *)
  let run_safe (f : unit -> 'a) : 'a error =
    let show_error e ppf =
      Format.fprintf ppf
        "@[<v>Internal error. (State may be undefined.)@,%s@]"
        (Printexc.to_string e)
    in
    Either.trap f |> Either.lmap show_error

  (* UTF-8 encoding of the lowercase Greek letter lambda. *)
  let lambda : string = "\xCE\xBB"

  let rec loop ppf (s : interpreter_state) : unit =
    (* Get the next subgoal *)
    match next_subgoal s with
    | None ->
       Format.fprintf ppf "@,Proof complete! (No subgoals left.)@,";
       () (* we're done; proof complete *)
    | Some g ->
       (* Show the proof state and the prompt *)
       Format.fprintf ppf
         "@,@[<v>Current state:@,%a@,There are %d IHs.@,@]%s> @?"
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
