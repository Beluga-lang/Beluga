open Support

module B = Beluga

module P = B.Pretty.Int.DefaultPrinter
module Command = B.Syntax.Ext.Harpoon
module Comp = B.Syntax.Int.Comp
module Coverage = B.Coverage
module LF = B.Syntax.Int.LF
module Loc = B.Syntax.Loc
module Context = B.Context
module Total = B.Total
module Whnf = B.Whnf
module S = B.Substitution

open Comp

let (dprintf, _, _) = B.Debug.(makeFunctions' (toFlags [11]))
open B.Debug.Fmt

type t = Total.dec list Lazy.t -> Theorem.t -> proof_state -> bool

let auto_intros : t =
  fun _ t g ->
  let (tau, _) = g.goal in
  dprintf
    begin fun p ->
    p.fmt "[auto_intros]: invoked on %a"
      (P.fmt_ppr_cmp_typ g.context.cD P.l0) tau
    end;
  match tau with
  | TypArr _ | TypPiBox _ ->
     Tactic.intros None t g;
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
  fun _ t g ->
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
     Theorem.printf t "@[<v>@,A goal %a is automatically solved.@,@]"
       (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp g.goal);
     (solve w |> Tactic.solve) t g;
     true

(** Solve a goal with an impossible hypothesis automatically.
    Be more precise, this automation solves a goal which has
    a hypothesis spliting into 0 cases.
 *)
let auto_impossible : t =
  fun mfs t g ->
  let { cD; cG; _ } = g.context in
  let m_is_impossible ((m, idx) : LF.ctyp_decl * int) =
    dprintf
      begin fun p ->
      p.fmt "@[<v>[auto_impossible] witness candidate = %a@]"
        (P.fmt_ppr_lf_ctyp_decl cD P.l0) m
      end;
    match m with
    (* Fix the following two cases after
     * fixing genPatCGoals (and related functions) to
     * emit an error for illegal cases and
     * return appropriate coverage goals
     *)
    | LF.Decl (_, LF.ClTyp (LF.STyp _, _), _) -> false
    | LF.Decl (_, LF.ClTyp (LF.PTyp _, _), _) -> false
    | LF.Decl (_, mtyp, _) ->
      let typ = Whnf.cnormCTyp (TypBox (Loc.ghost, mtyp), LF.MShift idx) in
      let cgs = Coverage.genPatCGoals cD (Coverage.gctx_of_compgctx cG) (Total.strip typ) [] in
      cgs == []
    | LF.DeclOpt _ ->
      B.Error.violation "[auto_impossible] Unexpected DeclOpt"
  in
  let build_mimpossible ((m, idx) : LF.ctyp_decl * int) =
    match m with
    | LF.Decl (_, mtyp, _) ->
      let exp = Comp.Var (Loc.ghost, idx) in
      let typ = Whnf.cnormCTyp (TypBox (Loc.ghost, mtyp), LF.MShift idx) in
      (exp, typ)
    (* The following case is impossible because m_is_impossible
       will never return true for a DeclOpt.
     *)
    | LF.DeclOpt _ ->
      B.Error.violation "[auto_impossible] Impossible case"
  in
  let c_is_impossible ((c, idx) : ctyp_decl * int) =
    dprintf
      begin fun p ->
      p.fmt "@[<v>[auto_impossible] witness candidate = %a@]"
        (P.fmt_ppr_cmp_ctyp_decl cD P.l0) c
      end;
    match c with
    | CTypDecl (_, typ, _) ->
      let cgs = Coverage.genPatCGoals cD (Coverage.gctx_of_compgctx cG) (Total.strip typ) [] in
      cgs == []
    | CTypDeclOpt _ ->
       B.Error.violation "[auto_impossible] Unexpected CTypDeclOpt"
    | WfRec _ ->
       B.Error.violation "[auto_impossible] Unexpected WfRec"
  in
  let build_cimpossible ((c, idx) : ctyp_decl * int) =
    match c with
    | CTypDecl (_, typ, _) ->
       let open Loc in
       (Var (ghost, idx), typ)
    | CTypDeclOpt _ ->
       B.Error.violation "[auto_impossible] Impossible case"
    | WfRec _ ->
       B.Error.violation "[auto_impossible] Impossible case"
  in
  let open Maybe in
  let opt_mimpossible =
    lazy
      (Context.find_with_index' cD m_is_impossible
       $> build_mimpossible)
  in
  let opt_cimpossible =
    lazy
      (Context.find_with_index' cG c_is_impossible
       $> build_cimpossible)
  in
  let opt_impossible =
    opt_mimpossible <|> opt_cimpossible
  in
  match opt_impossible with
  | lazy None ->
     dprintf
      begin fun p ->
        p.fmt "@[<v>[auto_impossible] There are no impossible hypotheses in@,%a@,@]"
          P.fmt_ppr_cmp_proof_state g
      end;
     false
  | lazy (Some (exp, typ)) ->
     Theorem.printf t "@[<v>@,A goal %a is automatically solved for an impossible hypothesis %a.@,@]"
       (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp g.goal)
       (P.fmt_ppr_cmp_typ cD P.l0) typ;
     Tactic.split `impossible exp typ (Lazy.force mfs) t g;
     true

type automation_info = bool ref * t

type automation_state =
  (Command.automation_kind, automation_info) Hashtbl.t

let make_automation_state () : automation_state =
  let hashtbl = Hashtbl.create 2 in
  let open List in
  [ (`auto_intros, auto_intros)
  ; (`auto_solve_trivial, auto_solve_trivial)
  ; (`auto_impossible, auto_impossible)
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
  fun mfs t g ->
  let open List in
  (* The order of automation kinds is important,
     because it is the order in which automations are executed.
   *)
  [ `auto_solve_trivial
  ; `auto_intros
  ; `auto_impossible
  ]
  |> map (fun k -> get_automation_info auto_st k)
  |> filter (fun (b, _) -> !b)
  |> exists (fun (_, auto) -> auto mfs t g)
