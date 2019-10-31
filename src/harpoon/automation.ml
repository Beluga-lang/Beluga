open Support

module B = Beluga

module P = B.Pretty.Int.DefaultPrinter
module Command = B.Syntax.Ext.Harpoon
module Comp = B.Syntax.Int.Comp
module LF = B.Syntax.Int.LF
module Loc = B.Syntax.Loc
module Context = B.Context
module Whnf = B.Whnf
module S = B.Substitution

open Comp

let (dprintf, _, _) = B.Debug.(makeFunctions' (toFlags [11]))
open B.Debug.Fmt

type t = proof_state -> Tactic.tactic_context -> bool

let auto_intros : t =
  fun g tctx ->
  let (t, _) = g.goal in
  dprintf
    begin fun p ->
    p.fmt "[auto_intros]: invoked on %a"
      (P.fmt_ppr_cmp_typ g.context.cD P.l0) t
    end;
  match t with
  | TypArr _ | TypPiBox _ ->
     Tactic.intros None g tctx;
     true
  | _ -> false

(** Solve {v ... -> P -> ... -> P v} case automatically.
    For example,
    this function will resolve

    x: [|- a]
    -------------
    [|- a]
 *)
let auto_solve_trivial : t =
  fun g tctx ->
  let { cD; cG; _ } = g.context in
  let m_is_witness ((m, idx) : LF.ctyp_decl * int) =
    dprintf
      begin fun p ->
      p.fmt "@[<v>[auto_solve_trivial] witness candidate = %a@]"
        (P.fmt_ppr_lf_ctyp_decl cD P.l0) m
      end;
    match m with
    | LF.Decl (_, mtyp, _) ->
       Whnf.convCTyp g.goal (TypBox (Loc.ghost, mtyp), LF.MShift idx)
    | LF.DeclOpt _ ->
       B.Error.violation "[auto_solve_trivial] Unexpected DeclOpt"
  in
  let build_mwitness (m : LF.ctyp_decl * int) =
    match m with
    | (LF.Decl (_, LF.ClTyp (_, dctx), _), idx) ->
       let open LF in
       let open Loc in
       let head = MVar (Offset idx, S.LF.id) in
       let clobj = MObj (Root (ghost, head, Nil)) in
       let psi_hat = Context.dctxToHat dctx in
       Box (ghost, (ghost, ClObj (psi_hat, clobj)))
    (* The following case is impossible because m_is_witness
       will never return true for a DeclOpt.
     *)
    | _ ->
       B.Error.violation "[auto_solve_trivial] Impossible case"
  in
  let c_is_witness ((c, _) : ctyp_decl * int) =
    dprintf
      begin fun p ->
      p.fmt "@[<v>[auto_solve_trivial] witness candidate = %a@]"
        (P.fmt_ppr_cmp_ctyp_decl cD P.l0) c
      end;
    match c with
    | CTypDecl (_, typ, _) ->
       Whnf.convCTyp g.goal (typ, Whnf.m_id)
    | CTypDeclOpt _ ->
       B.Error.violation "[auto_solve_trivial] Unexpected CTypDeclOpt"
    | WfRec _ ->
       B.Error.violation "[auto_solve_trivial] Unexpected WfRec"
  in
  let build_cwitness (c : ctyp_decl * int) =
    match c with
    | (_, idx) ->
       let open Loc in
       Syn (ghost, Var (ghost, idx))
  in
  let open Maybe in
  let opt_mwitness =
    lazy
      (Context.find_with_index' cD m_is_witness
       $> build_mwitness
      )
  in
  let opt_cwitness =
    lazy
      (Context.find_with_index' cG c_is_witness
       $> build_cwitness
      )
  in
  let opt_witness = opt_mwitness <|> opt_cwitness in
  match opt_witness with
  | lazy None ->
     dprintf
       begin fun p ->
       p.fmt "@[<v>[auto_solve_trivial] There are no witness in@,%a@,@]"
         P.fmt_ppr_cmp_proof_state g
       end;
     false
  | lazy (Some w) ->
     Tactic.(
      tctx.printf "@[<v>@,A goal %a is automatically solved.@,@]"
        (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp g.goal)
     );
     (solve w
      |> Tactic.solve
     ) g tctx;
     true

type automation_info = bool ref * t

type automation_state =
  (Command.automation_kind, automation_info) Hashtbl.t

let make_automation_state () : automation_state =
  let hashtbl = Hashtbl.create 2 in
  let open List in
  [ (`auto_intros, auto_intros)
  ; (`auto_solve_trivial, auto_solve_trivial)
  ]
  |> iter (fun (k, f) -> Hashtbl.add hashtbl k (ref true, f));
  hashtbl

let get_automation_info auto_st (k : Command.automation_kind) : automation_info =
  (* find here is guaranteed to succeed by the external invariant
     that the hashtable has been populated with all the keys of the
     polymorphic variant `automation_kind`.
   *)
  Hashtbl.find auto_st k

let toggle_automation auto_st (k : Command.automation_kind) (state : Command.automation_change) : unit =
  let (b, _) = get_automation_info auto_st k in
  let s =
    match state with
    | `on -> true
    | `off -> false
    | `toggle -> not !b
  in
  b := s

let exec_automation auto_st : t =
  fun g tctx ->
  let open List in
  (* The order of automation kinds is important,
     because it is the order in which automations are executed.
   *)
  [ `auto_solve_trivial
  ; `auto_intros
  ]
  |> map (fun k -> get_automation_info auto_st k)
  |> filter (fun (b, _) -> !b)
  |> exists (fun (_, auto) -> auto g tctx)
