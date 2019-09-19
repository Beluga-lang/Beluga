open Support

module B = Beluga
module Abstract = B.Abstract
module Check = B.Check
module Command = B.Syntax.Ext.Harpoon
module Context = B.Context
module HoleId = B.HoleId
module Holes = B.Holes
module Id = B.Id
module Interactive = B.Interactive
module Loc = B.Location
module Logic = B.Logic
module P = B.Pretty.Int.DefaultPrinter
module Total = B.Total
module Whnf = B.Whnf
module Debug = B.Debug

let dprintf, _, dprnt = Debug.(makeFunctions' (toFlags [13]))
open Debug.Fmt

module Comp = B.Syntax.Int.Comp

type interpreter_state =
  { initial_state : unit Comp.proof_state
  (* ^ it's important to remember the initial proof state, since it
     gives us a way to track the original full statement of the theorem
     to prove as well as a handle on the whole (partial) proof.
   *)
  ; remaining_subgoals : unit Comp.proof_state DynArray.t
  ; automation_state : Automation.automation_state
  ; theorem_name : Id.name
  ; cid : Id.cid_prog
  ; order : Comp.order option
  }

let make_prover_state
      (cid : Id.cid_prog)
      (theorem_name : Id.name)
      (order : Comp.order option)
      (initial_state : unit Comp.proof_state)
    : interpreter_state =
  { initial_state
  ; remaining_subgoals = DynArray.of_list []
  ; automation_state = Automation.make_automation_state ()
  ; theorem_name
  ; order
  ; cid
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

let show_proof s tctx =
  let open Comp in
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
  Tactic.(tctx.printf) "@[<v>Proof so far:@,%a@]"
    (P.fmt_ppr_cmp_proof s.context.cD s.context.cG) (incomplete_proof s)

let add_subgoal_hook s g tctx =
  let auto_st = s.automation_state in
  ignore
    (List.exists
       (fun f -> f g tctx)
       [ Automation.get_automation auto_st `auto_solve_trivial
       ; Automation.get_automation auto_st `auto_intros
       ]
    )

let process_command
      (s : interpreter_state) (g : unit Comp.proof_state)
      (cmd : Command.command)
      (tctx : Tactic.tactic_context)
    : unit =
  let printf x = Tactic.(tctx.printf) x in
  let open Comp in
  let mfs =
    (* this should probably directly be a part of interpreter_state,
       or perhaps a part of a larger state for the collection of
       mutually inductive theorems being defined.
     *)
    [ Total.make_total_dec
        s.theorem_name
        (Whnf.cnormCTyp s.initial_state.goal |> Total.strip)
        s.order
    ]
  in
  (** Checks that the given term corresponds to the given kind of invocation.
      Without this, it is possible to invoke lemmas using `by ih`.
   *)
  let check_invocation (k : invoke_kind) cD cG (i : exp_syn) f =
    match k with
    | `lemma -> f ()
    | `ih ->
       match head_of_application i with
       | Const (_, c) when c = s.cid -> f ()
       | _ ->
          Tactic.(tctx.printf) "@[<v>The expression@,  @[%a@]@,\
                                is not an appeal to an induction hypothesis.@]"
            (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
  in
  let elaborate_exp' cIH cD cG t =
    let (hs, (i, tau)) =
      Holes.catch
        (fun _ ->
          let (i, (tau, theta)) =
            Interactive.elaborate_exp' cD cG t
          in
          let _ = Check.Comp.syn ~cIH: cIH cD cG mfs i in  (* (tau, theta); *)
          (i, Whnf.cnormCTyp (tau, theta)))
    in
    (hs, i, tau)
  in
  let elaborate_exp cIH cD cG t ttau =
    Holes.catch
      (fun _ ->
        let e = Interactive.elaborate_exp cD cG t ttau in
        Check.Comp.check ~cIH: cIH cD cG mfs e ttau;
        e
      )
  in
  let { cD; cG; cIH } = g.context in
  match cmd with
  (* Administrative commands: *)
  | Command.ShowProof ->
     show_proof s tctx
  | Command.Defer ->
     (* Remove the current subgoal from the list (it's in head position)
      * and then add it back (on the end of the list) *)
     Tactic.(tctx.defer ())
  | Command.ShowIHs ->
     let f i =
       Tactic.(tctx.printf) "%d. %a@,"
         (i + 1)
         (P.fmt_ppr_cmp_ctyp_decl g.context.cD P.l0)
     in
     Tactic.(tctx.printf) "There are %d IHs:@,"
       (Context.length g.context.cIH);
     Context.to_list g.context.cIH |> List.iteri f
  | Command.ShowSubgoals ->
     let f ppf i g =
       let open Comp in
       Tactic.(tctx.printf) "%2d. @[%a@]@,"
         (i + 1)
         (P.fmt_ppr_cmp_typ g.context.cD P.l0) (Whnf.cnormCTyp g.goal)
     in
     let print_subgoals ppf gs =
       List.iteri (f ppf) gs
     in
     Tactic.(tctx.printf) "@[<v>%a@]"
       print_subgoals (DynArray.to_list s.remaining_subgoals)

  | Command.ToggleAutomation (automation_kind, automation_change) ->
     Automation.toggle_automation s.automation_state automation_kind automation_change

  (* Real tactics: *)
  | Command.Unbox (t, name) ->
     let (hs, m, tau) = elaborate_exp' cIH cD cG t in
     Tactic.unbox m tau name g tctx

  | Command.Intros names ->
     Tactic.intros names g tctx;
  | Command.Split (split_kind, t) ->
     let (hs, m, tau) = elaborate_exp' cIH cD cG t in
     Tactic.split split_kind m tau mfs g tctx
  | Command.By (k, t, name) ->
     let (hs, m, tau) = elaborate_exp' cIH cD cG t in
     dprintf
       begin fun p ->
       p.fmt "@[<v>[harpoon-By] elaborated invocation:@,%a@ : %a@]"
         (P.fmt_ppr_cmp_exp_syn cD cG P.l0) m
         (P.fmt_ppr_cmp_typ cD P.l0) tau
       end;
     (* validate the invocation and call the suspension if it passes. *)
     check_invocation k cD cG m
       (fun () -> Tactic.invoke k m tau name g tctx);

  | Command.Solve m ->
     let (hs, m) = elaborate_exp cIH cD cG m g.goal in
     dprnt "[harpoon] [solve] elaboration finished";
     printf "Found %d hole(s) in solution@." (List.length hs);
     let open Holes in
     let f (id, Exists (w, h)) =
       dprintf
         begin fun p ->
         p.fmt "[harpoon] [solve] [holes] processing hole %s"
           (HoleId.string_of_name_or_id (h.name, id))
         end;
       let { name; Holes.cD = cDh; info; _ } = h in
       match w with
       | Holes.CompInfo -> failwith "computational holes not supported"
       | Holes.LFInfo ->
          let { lfGoal; cPsi; lfSolution } = h.info in
          let typ = Whnf.normTyp lfGoal in
          let (ti, k) = Abstract.typ typ in
          dprintf
            begin fun p ->
            p.fmt "[harpoon] [solve] [holes] @[<v>goal: @[%a@]@,abstracted: @[%a@]@]"
              (P.fmt_ppr_lf_typ cDh cPsi P.l0) typ
              (P.fmt_ppr_lf_typ cDh cPsi P.l0) ti
            end;
          Logic.prepare ();
          let (query, skinnyTyp, querySub, instMVars) =
            Logic.Convert.typToQuery cPsi cDh (ti, k)
          in
          try
            let n = ref 0 in
            Logic.Solver.solve cDh cPsi query
              begin
                fun (cPsi, tM) ->
                Tactic.(tctx.printf) "found solution: @[%a@]@,@?"
                  (P.fmt_ppr_lf_normal cDh cPsi P.l0) tM;
                incr n;
                if !n >= 10 then raise Logic.Frontend.Done
              end
          with
          | Logic.Frontend.Done ->
             printf "logic programming finished@,@?";
             ()
     in
     List.iter f hs;
     Check.Comp.check cD cG mfs m g.goal;
     ( Comp.solve m
       |> Tactic.solve
     ) g tctx ;




     (*
     let (hs, m) = elaborate_exp cIH cD cG m g.goal in
     printf "Found %d holes in solution@," (List.length hs);
     let f (id, h) =
       let open Holes in
       let { name; Holes.cD = cDh; info; _ } = h in
       match info with
       | CompHoleInfo _ -> failwith "computational holes not supported"
       | LfHoleInfo { lfGoal; cPsi; lfSolution } ->
          let typ = Whnf.normTyp lfGoal in
          let ti = Abstract.typ typ in
          Logic.prepare ();
          let (query, skinnyTyp, querySub, instMVars) =
            Logic.Convert.typToQuery cPsi cDh ti
          in
          try
            let n = ref 0 in
            Logic.Solver.solve cDh cPsi query
              begin
                fun (cPsi, tM) ->
                Tactic.(tctx.printf) "found solution: @[%a@]@,@?"
                  (P.fmt_ppr_lf_normal cDh cPsi P.l0) tM;
                incr n;
                if !n >= 10 then raise Logic.Frontend.Done
              end
          with
          | Logic.Frontend.Done -> ()
     in
     List.iter f hs;
     Check.Comp.check cD cG mfs m g.goal;
     ( Comp.solve m
       |> Tactic.solve
     ) g tctx ;
      *)

(** A computed value of type 'a or a function to print an error. *)
type 'a error = (Format.formatter -> unit, 'a) Either.t

(** Parses the given string to a Syntax.Ext.Harpoon.command or an
    error-printing function.
 *)
let parse_input (input : string) : Command.command error =
  let open B in
  Runparser.parse_string "<prompt>" input Parser.(only harpoon_command)
  |> snd |> Parser.to_either
  |> Either.lmap (fun e ppf -> Parser.print_error ppf e)

(** Runs the given function, trapping exceptions in Either.t
    and converting the exception to a function that prints the
    error with a given formatter.
 *)
let run_safe (f : unit -> 'a) : 'a error =
  let show_error e ppf =
    Format.fprintf ppf "@[<v>Internal error. (State may be undefined.)@,%s@]"
      (Printexc.to_string e)
  in
  Either.trap f |> Either.lmap show_error

let build_tactic_context ppf s =
  let open Tactic in
  let printf x = Format.fprintf ppf x in
  let rec tctx =
    { add_subgoal
    ; remove_subgoal
    ; remove_current_subgoal
    ; printf
    ; defer
    }
  and add_subgoal g =
    (*
      dprintf
      begin fun p ->
      p.fmt "@[<v>[tactic context] add the following subgoal@,%a@]"
      P.fmt_ppr_cmp_proof_state g
      end;
     *)
    DynArray.insert s.remaining_subgoals 0 g;
    add_subgoal_hook s g tctx
  and remove_subgoal g =
    (*
      dprintf
      begin fun p ->
      p.fmt "@[<v>[tactic context] remove the following subgoal@,%a@]"
      P.fmt_ppr_cmp_proof_state g
      end;
     *)
    let idx = DynArray.index_of (fun g' -> g = g') s.remaining_subgoals in
    DynArray.delete s.remaining_subgoals idx
  and remove_current_subgoal () =
    let gs = s.remaining_subgoals in
    let csg_index = current_subgoal_index gs in
    (*
      dprintf
      begin fun p ->
      p.fmt "@[<v>[tactic context] remove the goal %d of the following@,%a@]"
      csg_index
      P.fmt_ppr_cmp_proof_state (DynArray.get gs csg_index)
      end;
     *)
    DynArray.delete gs csg_index
  and defer () =
    let g = DynArray.get s.remaining_subgoals 0 in
    remove_current_subgoal ();
    DynArray.add s.remaining_subgoals g
  in
  tctx

(* UTF-8 encoding of the lowercase Greek letter lambda. *)
let lambda : string = "\xCE\xBB"

let rec loop ppf (s : interpreter_state) tctx : unit =
  (* Get the next subgoal *)
  match next_subgoal s with
  | None ->
     Tactic.(tctx.printf) "@,Proof complete! (No subgoals left.)@,";
     show_proof s tctx;
     () (* we're done; proof complete *)
  | Some g ->
     (* Show the proof state and the prompt *)
     Tactic.(tctx.printf) "@,@[<v>@,%a@,There are %d IHs.@,@]%s> @?"
       P.fmt_ppr_cmp_proof_state g
       (Context.length g.Comp.context.Comp.cIH)
       lambda;

     (* Parse the input and run the command *)
     let input = read_line () in
     let e =
       let open Either in
       parse_input input
       $ fun cmd ->
         run_safe (fun () -> process_command s g cmd tctx)
     in
     Either.eliminate
       (fun f -> f ppf)
       (Misc.const ())
       e;
     loop ppf s tctx

let start_toplevel
      (ppf : Format.formatter) (* The formatter used to display messages *)
      (name : Id.name) (* The name of the theorem to prove *)
      (stmt : Comp.tclo) (* The statement of the theorem *)
      (order : Comp.order option) (* The induction order of the theorem *)
    : unit =
  let module S = B.Store.Cid.Comp in
  (* maybe we should actually say the correct number of implicits
     here instead of zero.
     -je
   *)
  let _, cid =
    S.add Loc.ghost
      (fun _ -> S.mk_entry name (Whnf.cnormCTyp stmt |> Total.strip) 0 true None [name])
  in
  let g = Comp.make_proof_state stmt in
  let s = make_prover_state cid name order g in
  let tctx = build_tactic_context ppf s in
  Tactic.(tctx.add_subgoal g);
  loop ppf s tctx
