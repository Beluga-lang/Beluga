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

type t = Theorem.t -> proof_state -> bool
type automation = t

let auto_intros : t =
  fun t g ->
  let (tau, theta) = g.goal in
  dprintf
    begin fun p ->
    p.fmt "[auto_intros]: invoked on %a"
      (P.fmt_ppr_cmp_typ g.context.cD P.l0) tau
    end;
  match Tactic.intros' t None LF.Empty LF.Empty tau with
  | Either.Right (cD, cG, tau') ->
     let fmt_ppr_ctx f ppf ctx = Context.iter ctx (f ppf) in
     let fmt_ppr_lf_ctx ppf =
       function
       | LF.Empty -> ()
       | cD ->
          Format.fprintf ppf "@,  @[<v 2>Meta-assumptions:";
          fmt_ppr_ctx (fun ppf cD v -> Format.fprintf ppf "@,@[<hov 2>%a@]" (P.fmt_ppr_lf_ctyp_decl cD P.l0) v) ppf cD;
          Format.fprintf ppf "@]"
     in
     let fmt_ppr_cmp_ctx ppf =
       function
       | LF.Empty -> ()
       | cG ->
          Format.fprintf ppf "@,  @[<v 2>Computational assumptions:";
          fmt_ppr_ctx (fun ppf _ v -> Format.fprintf ppf "@,@[<hov 2>%a@]" (P.fmt_ppr_cmp_ctyp_decl cD P.l0) v) ppf cG;
          Format.fprintf ppf "@]"
     in
     let fmt_ppr_assumptions ppf () =
       fmt_ppr_lf_ctx ppf cD;
       fmt_ppr_cmp_ctx ppf cG
     in
     Theorem.printf t
       "@[<v>@,Assumptions%a\
        @,are automatically introduced for the subgoal of type\
        @,  @[<v>%a@]\
        @,@]"
       fmt_ppr_assumptions ()
       (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp g.goal);
     let goal = (tau', theta) in
     let local_context = {cD; cG; cIH = LF.Empty} in
     let context = Whnf.append_hypotheses g.context local_context in
     let new_state =
       { context
       ; goal
       ; solution = None
       ; label = g.label
       }
     in
     ignore (Theorem.solve_by_replacing_subgoal t new_state (Comp.intros context) g);
     true
  | Either.Left _ ->
     false

(** Solve {v ... -> P -> ... -> P v} case automatically.
    For example,
    this function will resolve

    x: [|- a]
    -------------
    [|- a]
 *)
let auto_solve_trivial : t =
  fun t g ->
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
     Theorem.printf t
       "@[<v>@,The subgoal\
        @,  @[<hov 2>%a@]\
        @,of type\
        @,  @[<hov 2>%a@]\
        @,has been automatically solved.\
        @,\
        @,@]"
       ( Format.pp_print_list
           ~pp_sep: (fun ppf () -> Format.fprintf ppf " <-@ ")
           (fun ppf l -> Format.fprintf ppf "%s" l)
       ) g.label
       (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp g.goal);
     (solve w |> Tactic.solve) t g;
     true

module State : sig
  type t
  val make : unit -> t
  val toggle : t -> Command.automation_kind -> Command.automation_change -> unit
  val execute : t -> automation
end = struct
  type info = bool ref * automation

  type t =
    (Command.automation_kind, info) Hashtbl.t

  let make () : t =
    let hashtbl = Hashtbl.create 2 in
    let open List in
    [ (`auto_intros, auto_intros)
    ; (`auto_solve_trivial, auto_solve_trivial)
    ]
    |> iter (fun (k, f) -> Hashtbl.add hashtbl k (ref true, f));
    hashtbl

  let get_info st (k : Command.automation_kind) : info =
    (* find here is guaranteed to succeed by the external invariant
       that the hashtable has been populated with all the keys of the
       polymorphic variant `automation_kind`.
     *)
    Hashtbl.find st k

  let toggle st (k : Command.automation_kind) (inst : Command.automation_change) : unit =
    let (b, _) = get_info st k in
    let v =
      match inst with
      | `on -> true
      | `off -> false
      | `toggle -> not !b
    in
    b := v

  let execute st : automation =
    fun t g ->
    let open List in
    (* The order of automation kinds is important,
       because it is the order in which automations are executed.
     *)
    [ `auto_solve_trivial
    ; `auto_intros
    ]
    |> map (fun k -> get_info st k)
    |> filter (fun (b, _) -> !b)
    |> exists (fun (_, auto) -> auto t g)
end

let toggle = State.toggle
let execute = State.execute
