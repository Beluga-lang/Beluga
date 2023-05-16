open Support.Equality
(* module Logic *)
(* author:
   Costin Badescu
   Jacob Thomas Errington
   Johanna Schwartzentruber
 *)

open Support
open Beluga_syntax
module S = Substitution.LF
open Format
open Synint

let (dprintf, _, _) = Debug.makeFunctions' (Debug.toFlags [11])
open! Debug.Fmt

module Options = struct
  (* Enable the logic programming engine (disabled by default). *)
  let enableLogic = ref true

  (* Control verbosity level:
       0 => No output.
       1 => Query and success notification.
       2 => + Error messages.
       3 => + Solutions and proof terms.
       4 => + LF signature & Comp Sig.
  *)
  let chatter = ref 3

  (* Ask before giving more solutions (à la Prolog). *)
  let askSolution = ref false

  (* Type check the proof terms. *)
  let checkProofs = ref true
end


exception NotImplementedYet


(* Naming conventions:
     g : goal
   Goal.
     r : res
   Residual goal.
     cPsi : LF.dctx
   Universal typing context.
     tD : typ_decl
   LF type declaration.
     dPool : dPool
   Pool of dynamic assumptions.
     cG : conjunction
   Conjunction of goals.
     eV : LF.dctx
   Context with TypDecl's of existential variables belonging to a clause.
     dCl : clause
   Dynamic clause.
     sCl : clause
   Clause from LF signature.
     sCCl : clause
   Clause from Signature of computation type.
     cS : int
   Constant shift for BVar indices bound to existential variables.
     dS : int
   Dynamic shift for indices of variables in dynamic clauses.
     dR : int
   Range of de Bruijn indices in the dynamic scope.
*)

type lfTyp =  (* Used to classify the kind of LF object an LF type represents *)
  | M | P

type goal =                             (* Goals            *)
  | Atom of LF.typ                      (* g ::= A          *)
  | Impl of (res * LF.typ_decl) * goal  (*     | r => g'    *)
  | All of LF.typ_decl * goal           (*     | ∀x:A. g'   *)

and res =                               (* Residual Goals   *)
  | Head of LF.typ                      (* r ::= A          *)
  | And of goal * res                   (*     | g ∧ r'     *)
  | Exists of LF.typ_decl * res         (*     | ∃x:T. r'   *)

type conjunction =                       (* Subgoals         *)
  | True                                 (* cG ::= True      *)
  | Conjunct of conjunction * goal       (*      | cG' ∧ g   *)

let rec list_of_conjunction : conjunction -> goal list =
  function
  | True -> []
  | Conjunct (c, x) -> x :: list_of_conjunction c

type bound = int option                 (* b ::= '*' | nat  *)

type query = goal * LF.sub              (* q ::= (g, s)     *)

type clause =                    (* Horn Clause ::= eV |- A :- cG   *)
  { tHead : LF.typ               (* Head A : LF.Atom                *)
  ; eVars : LF.dctx              (* Context eV : EV's bound in A/cG *)
  ; subGoals : conjunction       (* Subgoals cG : solv. cG => A     *)
  }

(* Naming conventions:

  cg : comp_goal (computation-level goal)
  mq : mquery    (a query for a cg)

 *)

type comp_goal =                                (* Comp Goal cg :=       *)
  | Box of LF.dctx  * goal * lfTyp option       (*     | Box (cPsi , g)  *)
  | Implies of (comp_res * Comp.ctyp_decl)      (*     | r -> cg'        *)
               * comp_goal
  | Forall of  LF.ctyp_decl * comp_goal         (*     | ∀x:U. cg        *)
  | Atomic of Id.cid_comp_typ * atomic_spine    (*     | a meta_spine    *)

and atomic_spine =
  | End
  | Spine of atomic_spine * (Comp.meta_typ
                             * LF.mfront
                             * Plicity.t) (* For recreating type*)

and comp_res =                          (* Residual Comp Goals   *)
  | Base of Comp.typ                    (* cr ::= A              *)
  | CAnd of comp_goal * comp_res        (*     | cg ∧ r'         *)
  | CExists of LF.ctyp_decl * comp_res  (*     | ∃x:T. r'        *)

type subgoals =                     (* Subgoals         *)
  | Proved                          (* sg ::= Proved    *)
  | Solve of subgoals * comp_goal   (*      | sg ∧ cg   *)

let rec list_of_subgoals : subgoals -> comp_goal list =
  function
  | Proved -> []
  | Solve (c, x) -> x :: list_of_subgoals c

type mquery = comp_goal * LF.msub       (* mq := (cg, ms)  *)


(*  bp : modelling the computation level clause following the LF clause definition *)
type cclause =                       (* Comp. Horn Clause ::= cD |- tau_atomic  :- subgoals   *)
  { cHead : Comp.typ                 (* Head tau_atomic := TypBox U | TypBase (c, S) *)
  ; cMVars : LF.mctx                 (* Context cD : meta-vars  bound in compTyp     *)
  ; cSubGoals : subgoals             (* Subgoals that need to be solved              *)
  }


module Shift : sig
  val shiftAtom : LF.typ -> int * int * int -> LF.typ
end = struct
  (* NB.

     Only BVar's in LF.Atom's are affected.
     Enclosed substitutions are not shifted.

     i: De Bruijn index.
     k: Shifting measure.

     Algorithm:

     BV bound by λ remain invariant.
      - i < lR |- BV(i) -> BV(i)

     BV bound by a dynamic scope are shifted by dS.
      - lR < i <= dR |- BV(i) -> BV(i + dS)

     BV bound to EV are shifted by k.
      - i > lR && i > dR |- BV(i) -> BV(i + k)
  *)

  let lR = ref 0               (* Range of Lambda Scope *)
  let dR = ref 0               (* Range of Dynamic Scope *)
  let dS = ref 0               (* Dynamic Shift *)

  let rec shiftTyp tM k =
    match tM with
    | LF.Atom (l, c, tS) ->
       LF.Atom (l, c, shiftSpine tS k)
    | x -> x

  and shiftSpine tS k =
    match tS with
    | LF.App (tN, tS) ->
       LF.App (shiftNormal tN k, shiftSpine tS k)
    | LF.SClo (tS, s) ->
       LF.SClo (shiftSpine tS k, s)
    | LF.Nil -> LF.Nil

  and shiftNormal tN k =
    match tN with
    | LF.Lam (l, n, tN') ->
       begin
         incr lR;
         let tM = LF.Lam (l, n, shiftNormal tN' k) in
         decr lR;
         tM
       end
    | LF.Root (l, tH, tS, plicity) ->
       LF.Root (l, shiftHead tH k, shiftSpine tS k, plicity)
    | LF.Clo (tN, s) ->
       LF.Clo (shiftNormal tN k, s)
    | LF.Tuple (l, tP) ->
       LF.Tuple (l, shiftTuple tP k)

  and shiftHead tH k =
    match tH with
    | LF.BVar i ->
       if i > !lR && i > !dR
       then LF.BVar (i + k)
       else if i > !lR && i <= !dR
       then LF.BVar (i + !dS)
       else LF.BVar i
    | LF.AnnH (tH, tM) ->
       LF.AnnH (shiftHead tH k, tM)
    | LF.Proj (tH, n) ->
       LF.Proj (shiftHead tH k, n)
    | x -> x

  and shiftTuple tP k =
    match tP with
    | LF.Last tN ->
       LF.Last (shiftNormal tN k)
    | LF.Cons (tN, tP') ->
       LF.Cons (shiftNormal tN k, shiftTuple tP' k)

  let shiftAtom tM (cS, dS', dR') =
    dR := dR';
    dS := dS';
    shiftTyp tM cS
end


module Convert = struct

  (* typToClause' eV cG tA (cS, dS, dR) = clause
     Invariants:
       If BV(i) is free in tA, then BV(i) is bound in (eV |- tA).
       If tA = PiTyp (x:A, No), then tA ~ cG (i.e. conjunction representing the subgoals).
  *)
  let rec typToClause' eV cG tA (cS, dS, dR) =
    match tA with
    | LF.PiTyp ((tD, _, Plicity.Implicit), tA') ->
       typToClause' (LF.DDec (eV, tD)) cG tA' (cS, dS, dR)
    | LF.PiTyp ((LF.TypDecl (_, tA), _, Plicity.Explicit), tB) ->
       typToClause' eV (Conjunct (cG, typToGoal tA (cS, dS, dR)))
         tB (cS + 1, dS, dR)
    | LF.Atom _ ->
       { tHead = (Shift.shiftAtom tA (-cS, -dS, dR))
       ; eVars = eV
       ; subGoals = cG
       }


  (* comptypToCClause' cD tau subgoals  = cclause
     Invariants:

       cD |- tau
       cD |- subgoals

       If tau = TypPiBox (u:U, tau) then cD := cD, u:U
       If tau = TypArr tau1 tau2 then subgoals := Solve (subgoals, tau1)


   To do:
   - add other types (such as codata, etc. ) abort gracefull
  *)

  and comptypToCClause' cD tau subgoals  =
    match tau with
    | Comp.TypBox (_, _U) ->
       { cHead = tau
       ; cMVars = cD
       ; cSubGoals = subgoals
       }
    | Comp.TypPiBox (l, tdecl, tau') ->
       let cD' = Whnf.extend_mctx cD (tdecl, LF.MShift 0) in
       comptypToCClause' cD' tau' subgoals
    | Comp.TypArr (_, t1, t2) ->
       let cg = comptypToCompGoal t1 in
       comptypToCClause' cD t2 (Solve (subgoals, cg))
    | Comp.TypBase (_) ->
       { cHead = tau
       ; cMVars = cD
       ; cSubGoals = subgoals
       }
    | _  ->
       { cHead = tau
       ; cMVars = cD
       ; cSubGoals = subgoals
       }


  (* Write out invariant / comment
     in particular: what is cS, dS, dR
   *)
  and typToGoal tA (cS, dS, dR) =
    match tA with
    | LF.PiTyp ((tdec, _, Plicity.Implicit), tA') ->
       All (tdec, typToGoal tA' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (x, tA) as tdec, _, Plicity.Explicit), tB) ->
       Impl ((typToRes tA (cS, dS, dR), tdec), typToGoal tB (cS, dS, dR + 1))
    | LF.Atom _ ->
       Atom (Shift.shiftAtom tA (-cS, -dS, dR))
    | LF.TClo (tA, s) ->
       dprintf begin fun p -> p.fmt "[typToGoal] TClo" end;
       raise NotImplementedYet

  and typToRes tM (cS, dS, dR) =
    match tM with
    | LF.PiTyp ((tD, _, Plicity.Implicit), tM') ->
       Exists (tD, typToRes tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (_, tA), _, Plicity.Explicit), tB) ->
       And (typToGoal tA (cS, dS, dR), typToRes tB (cS + 1, dS + 1, dR + 1))
    | LF.Atom _ ->
       Head (Shift.shiftAtom tM (-cS, -dS, dR))


  and comptypToCompGoal tau  =
    (* convert spine into the required shape (atomic_spine) *)
    let rec msToAs s =
      match s with
      | Comp.MetaNil -> End
      | Comp.MetaApp ((_loc, mf), ctyp, s', plicity) ->
         Spine  (msToAs s', (ctyp, mf, plicity))
    in
    match tau with
    | Comp.TypBox (_loc, LF.ClTyp (LF.MTyp tA, cPsi)) ->
       (* Invariant: tA will always be atomic in our implementation *)
       Box (cPsi, Atom tA, Some M)
       (* possibly needs to have PiBox variables shifted;
          note: Pibox variables are indexed with respect to cD (Delta)
                LF Pi variables are indexed with respect to LF context
                (hence one cannot simply re-use the module Shift, but would need a module MShift)
        *)
    | Comp.TypBox (_loc, LF.ClTyp (LF.PTyp tA, cPsi)) ->
       Box (cPsi, Atom tA, Some P)
    | Comp.TypBox (_loc, LF.ClTyp (LF.STyp (svar_class, range), dom)) ->
       raise NotImplementedYet
    | Comp.TypPiBox (loc, ctyp_decl , tau') ->
       Forall(ctyp_decl, comptypToCompGoal tau' )
    | Comp.TypArr (loc, tau1, tau2) ->
       let cr1 = comptypToCompRes tau1 in
       let cg2 = comptypToCompGoal tau2 in
       let name = Name.mk_name Name.NoName in
       let typ_dec = Comp.CTypDecl (name, tau1 , true) in
       Implies ((cr1, typ_dec), cg2)
    | Comp.TypBase (_, comp_cid, s) ->
       Atomic (comp_cid, msToAs s)

  and comptypToCompRes tau =
    match tau with
    | Comp.TypBox (_) | Comp.TypBase(_) ->
       Base tau
    | Comp.TypArr (_, tau1, tau2) ->
       CAnd (comptypToCompGoal tau1, comptypToCompRes tau2)
    | Comp.TypPiBox (_, typ_dec, tau') ->
       CExists (typ_dec, comptypToCompRes tau')
    | Comp.TypInd tau' -> comptypToCompRes tau'

  let rec resToClause' eV cG (r, s) =
    match r with
    | Exists (tD, r') ->
       resToClause' (LF.DDec (eV, tD)) cG (r', S.dot1 s)
    | And (g, r') ->
       resToClause' eV (Conjunct (cG, g)) (r', s)
    | Head tA ->
       let (tA', _) = Whnf.whnfTyp (tA, s) in
       { tHead = tA'; eVars = eV; subGoals = cG }

  let resToClause (r, s) =
    resToClause' LF.Null True (r, s)

  let rec cResToCClause' mV sg (cr, ms) =
    match cr with
    | Base tau ->
       let (tau', _) = Whnf.cwhnfCTyp(tau, ms) in
       { cHead = tau'; cMVars = mV; cSubGoals = sg }
    | CAnd (cg, cr') ->
       cResToCClause' mV (Solve (sg, cg)) (cr', ms)
    | CExists (tdec, cr') ->
       cResToCClause' (LF.Dec (mV, tdec)) sg (cr', ms)

  let cResToCClause (cr, ms) =
    cResToCClause' LF.Empty Proved (cr, ms)

  let typToClause tA =
    typToClause' LF.Null True tA (0, 0, 0)

  let comptypToCClause tau =
    comptypToCClause' LF.Empty tau Proved

  (* Converts a box comp goal to a Comp.TypBox *)
  let boxToTypBox box =
    match box with
    | Box (cPsi, Atom tA, Some M) ->
       let loc = Location.ghost in
       let ctyp = LF.ClTyp (LF.MTyp tA, cPsi) in
       Comp.TypBox (loc, ctyp)
    | Box (cPsi, Atom tA, Some P) ->
       let loc = Location.ghost in
       let ctyp = LF.ClTyp (LF.PTyp tA, cPsi) in
       Comp.TypBox (loc, ctyp)

  (* Converts an atomic comp goal to a Comp.TypBase *)
  let atomicToBase atomic =
    let rec asToMs aS =
      match aS with
      | End -> Comp.MetaNil
      | Spine (aS', (mt, mf, pl)) ->
         Comp.MetaApp ((Location.ghost, mf), mt, asToMs aS', pl)
    in
    match atomic with
    | Atomic (cid, aS) ->
       let loc = Location.ghost in
       let mS = asToMs aS in
       Comp.TypBase (loc, cid, mS)


  (* etaExpand Psi (A, s) = normal
     Invariants:
       Psi |- s : Phi
       Phi |- A : LF.typ

     Effects:
       None.

    Example: tA = \x. X[x] : nat -> nat
        meta-variable X generated by newMMVar at type nat in a context cPsi := x:nat
        (instead of a meta-variable of type nat -> nat)

  *)
  let rec etaExpand cD cPsi sA =
    let (tA, s) = Whnf.whnfTyp sA in
    match tA with
    | LF.Atom _ ->
       let u = LF.Inst (Whnf.newMMVar None (cD, cPsi, LF.TClo (tA, s)) Plicity.implicit Inductivity.not_inductive) in
       LF.Root (Location.ghost, LF.MVar (u, S.id), LF.Nil, Plicity.explicit)
    | LF.PiTyp ((LF.TypDecl (x, tA) as tD, _, _), tB) ->
       LF.Lam
         ( Location.ghost
         , x
         , etaExpand cD (LF.DDec (cPsi, S.decSub tD s)) (tB, S.dot1 s)
         )


  (* dctxToSub Delta Psi (eV, s) fS = sub * (spine -> spine)
     Invariants:
       eV = Null | ((Null, Dec (x, M)), ...)
       Psi |- s : Phi
       Phi |- M
       fS : spine -> spine

     Effects:
       None.

     Create MVars for all the TypDecl's in eV. Accumulate them
     in a substitution, performing eta-expansion if necessary,
     and add them to the spine of a proof-term through fS.
  *)
  let rec dctxToSub cD cPsi (eV, s) fS =
    dprintf begin fun p -> p.fmt "[dctxToSub]" end;
    match eV with
    | LF.DDec (eV', LF.TypDecl (_, tA)) ->
       let (s', fS') = dctxToSub cD cPsi (eV', s) fS in
       let tM' = etaExpand cD cPsi (tA, s') in
       (LF.Dot (LF.Obj tM', s'), (fun tS -> fS' (LF.App (tM', tS))))
    | LF.Null -> (s, fS)
    | LF.CtxVar _ ->
       invalid_arg
         "Logic.Convert.dctxToSub: Match conflict with LF.CtxVar _."

  (* Convert eV to a substitution *)
  let rec dctxToSub' cD cPsi (eV, s) fS =
    dprintf begin fun p -> p.fmt "[dctxToSub']" end;
    match eV with
    | LF.DDec (eV', LF.TypDecl (_, tA)) ->
       let (s', fS') = dctxToSub' cD cPsi (eV', s) fS in
       let tM' = etaExpand cD cPsi (tA, s') in
       (LF.Dot (LF.Obj tM', s'), (fun tS -> fS' (LF.App (tM', tS))))
    | LF.Null -> (s, fS)
    | LF.CtxVar _ -> (s, fS)

  (* Convert mV to a meta-substitution *)
  let mctxToMSub cD (mV, ms) fS =
    let etaExpand' cD cPsi (tA, ms) name plic ind =
      let cvar = Whnf.newMMVar (Some name) (cD, cPsi, tA) plic ind in
       LF.Root (Location.ghost, LF.MMVar((cvar, ms), S.id), LF.Nil, plic)
    in
    let rec rev_ms ms ms_ret =
      match ms with
      | LF.MShift k -> ms_ret
      | LF.MDot (mf, ms') -> rev_ms ms' (LF.MDot (mf, ms_ret))
    in
    let rec shift lst i =
      match lst with
      | [] -> lst
      | (cPsi, k) :: lst' -> (cPsi, k+i) :: (shift lst' i)
    in
    let rmLst lst =
      match lst with
      | (cPsi, k) :: lst' -> (shift lst' (-1), cPsi)
    in
    let rec find_cPsi lst k =
      match lst with
      | (dctx, k') :: lst' when k = k' -> dctx
      | x :: lst' -> find_cPsi lst' k
      | _ -> raise NotImplementedYet
    in
    let rec find_ctxvar_offset dctx =
      match dctx with
      | LF.DDec (dctx', _) -> find_ctxvar_offset dctx'
      | LF.CtxVar (LF.CtxOffset k) -> k
      | LF.Null -> 0
    in
    let rec adjust_offset cPsi ctx_var =
      match cPsi with
      | LF.DDec (cPsi', td) -> LF.DDec (adjust_offset cPsi' ctx_var, td)
      | LF.CtxVar (_) -> ctx_var
      | _ -> invalid_arg
         "Logic.Convert.mctxToMSub.adjust_offset"
    in
    let rev_mctx cD =
      let rec rev cD cD_ret =
      match cD with
      | LF.Empty -> cD_ret
      | LF.Dec(cD', cdecl) ->
         rev cD' (LF.Dec(cD_ret, cdecl))
      in
      rev cD LF.Empty
    in
    let rec create_psiList mV psiLst =
      match mV with
      | LF.Empty -> shift psiLst (-1)
      | LF.Dec (mV',
                LF.Decl (name, LF.CTyp (Some cid), plic ,ind)) ->
         let dctx = LF.CtxVar(Whnf.newCVar (Some name) cD (Some cid) plic ind) in
         let psiLst' = (dctx, 1) :: (shift psiLst 1) in
         create_psiList mV' psiLst'
      | LF.Dec (mV', _) ->
         create_psiList mV' (shift psiLst 1)
    in
    let rec mctxToMSub' cD (mV, ms) psiLst =
      match mV with
      | LF.Empty -> ms
      | LF.Dec (mV',
                LF.Decl (name, LF.CTyp (Some cid), plic, ind)) ->
         let (psiLst', dctx) = rmLst psiLst in
         let mfront = LF.CObj dctx in
         let ms' = mctxToMSub' cD (mV', ms) psiLst' in
         LF.MDot (mfront, ms')
      | LF.Dec (mV',
                LF.Decl (name, LF.ClTyp (LF.MTyp tA,
                                         LF.CtxVar (LF.CtxOffset k)), plic, ind)) ->
         let dctx = find_cPsi psiLst k in
         let dctx_hat = Context.dctxToHat dctx in
         let psiLst' = shift psiLst (-1) in
         let ms' = mctxToMSub' cD (mV', ms) psiLst' in
         let tA = Whnf.cnormTyp (tA, ms') in
         let tM = etaExpand' cD dctx (tA, LF.MShift 0) name plic ind in
         let mfront = LF.ClObj (dctx_hat, LF.MObj tM) in
         LF.MDot (mfront, ms')
      | LF.Dec (mV',
                LF.Decl (name, LF.ClTyp (LF.PTyp tA,
                                         LF.CtxVar (LF.CtxOffset k)), plic, ind)) ->
         let dctx = find_cPsi psiLst k in
         let dctx_hat = Context.dctxToHat dctx in
         let psiLst' = shift psiLst (-1) in
         let ms' = mctxToMSub' cD (mV', ms) psiLst' in
         let tA = Whnf.cnormTyp (tA, ms') in
         let cvar = Whnf.newMPVar (Some name) (cD, dctx, tA) plic ind in
         let tM = LF.MPVar((cvar, ms), S.id) in
         let mfront = LF.ClObj (dctx_hat, LF.PObj tM) in
         LF.MDot (mfront, ms')
      | LF.Dec (mV',
                LF.Decl (name, LF.ClTyp (LF.MTyp tA, cPsi), plic, ind)) ->
         let k = find_ctxvar_offset cPsi in
         let dctx = match k with
           | 0 -> cPsi
           | _ -> adjust_offset cPsi (find_cPsi psiLst k)
         in
         let dctx_hat = Context.dctxToHat dctx in
         let psiLst' = shift psiLst (-1) in
         let ms' = mctxToMSub' cD (mV', ms) psiLst' in
         let tA = Whnf.cnormTyp (tA, ms') in
         let tM = etaExpand' cD dctx (tA, LF.MShift 0) name plic ind in
         let mfront = LF.ClObj (dctx_hat, LF.MObj tM) in
         LF.MDot (mfront, ms')
      | LF.Dec (mV',
                LF.Decl (name, LF.ClTyp (LF.PTyp tA, cPsi), plic, ind)) ->
         let k = find_ctxvar_offset cPsi in
         let dctx = match k with
           | 0 -> cPsi
           | _ -> adjust_offset cPsi (find_cPsi psiLst k)
         in
         let dctx_hat = Context.dctxToHat dctx in
         let psiLst' = shift psiLst (-1) in
         let ms' = mctxToMSub' cD (mV', ms) psiLst' in
         let tA = Whnf.cnormTyp (tA, ms') in
         let cvar = Whnf.newMPVar (Some name) (cD, dctx, tA) plic ind in
         let tM = LF.MPVar((cvar, ms), S.id) in
         let mfront = LF.ClObj (dctx_hat, LF.PObj tM) in
         LF.MDot (mfront, ms')
      | _ -> raise NotImplementedYet
    in
    let rec msToSpine ms fS =
      let loc = Location.ghost in
      match ms with
      | LF.MShift k -> fS
      | LF.MDot (LF.CObj ((LF.CtxVar(LF.CInst
                                      ({ LF.name ; instantiation ; cD ; mmvar_id ;
                                         typ ; constraints ; plicity ; inductivity }, _))) as dctx),
                 ms') ->
         let mfront = LF.CObj dctx in
         msToSpine ms' (fun s ->
             (Comp.MApp (loc, fS s, (loc, mfront), typ, plicity)))
      | LF.MDot (LF.ClObj (dctx_hat, LF.MObj ((LF.Root (_,LF.MMVar (({ LF.name ; instantiation ; cD ; mmvar_id ; typ ; constraints ; plicity ; inductivity },_),_), _ ,_)) as tM)), ms') ->
         let mfront = LF.ClObj (dctx_hat, LF.MObj tM) in
         msToSpine ms' (fun s ->
             (Comp.MApp (loc, fS s, (loc, mfront), typ, plicity)))
      | LF.MDot (LF.ClObj (dctx_hat, LF.PObj (LF.MPVar (({ LF.name ; instantiation ; cD ; mmvar_id ; typ ; constraints ; plicity ; inductivity }, _), _) as tM)), ms') ->
         let mfront = LF.ClObj (dctx_hat, LF.PObj tM) in
         msToSpine ms' (fun s ->
             (Comp.MApp (loc, fS s, (loc, mfront), typ, plicity)))
      | _ -> raise NotImplementedYet
    in
    let rev_cD = rev_mctx mV in
    let psiLst = create_psiList rev_cD [] in
    let ms' = mctxToMSub' cD (mV, ms) psiLst in
    let ms_rev = (rev_ms ms' (LF.MShift 0)) in
    let fS = msToSpine ms_rev (fun s -> s) in
    (ms_rev, fS)

  (** typToQuery (M, i)  = ((g, s), xs)
      Transform a reconstructed LF.typ into a query, accumulating all
      the abstracted existential variables into a substitution while
      storing the MVars into a list `xs' for immediate access.

      `i` is the count of abstracted existential variables in the
      type.
  *)
  let typToQuery cD cPsi (tA, i) =
    let rec typToQuery' (tA, i) s xs =
      match tA with
      | LF.PiTyp ((LF.TypDecl (x, tA), _, Plicity.Implicit), tB) when i > 0 ->
         let tN' = etaExpand cD cPsi (tA, s) in
         typToQuery' (tB, i - 1) (LF.Dot (LF.Obj tN', s)) ((x, tN') :: xs)
      | _ -> ((typToGoal tA (0, 0, 0), s), tA, s, xs)
    in    typToQuery' (tA, i) S.id []

  let rec solToSub xs =
    match xs with
    | [] -> S.id
    | (x, tN) :: xs -> LF.Dot (LF.Obj tN, solToSub xs)

  let rec solToMSub xs =
    match xs with
    | [] -> LF.MShift 0
    | (x, tN) :: xs ->
       LF.MDot (tN, solToMSub xs)



(*
  comptypToMQuery (tau, i) = comp_goal

   Precondition:

     . |- tau : ctyp  (i.e. tau is a closed computation-level type)
          i  = # Pibox quantified variables in tau that denote existential variables,
               i.e. we want to find instantiation for those variables during proof search.

   Postcondition (result)
      comp_goal is a the representation of the computation-level type tau as a computation-level goal


 *)
let comptypToMQuery (tau, i) =
  let rec comptypToMQuery' (tau, i) ms xs =
    (*
     Invariant:

       cD' |- tau
       .   |- ms : cD'     ms is a meta-substitution that provides existential variables (refs that will instantiated)
                              for all the bound meta-variables in cD'
       .   |- [ms]tau

     *)
      match tau with
      | Comp.TypBox (_loc, LF.ClTyp (LF.MTyp _tA, _cPsi)) ->
          (((comptypToCompGoal tau), ms), tau, ms, xs)
      | Comp.TypBox (_loc, LF.ClTyp (LF.PTyp _tA, _cPsi)) ->
         (((comptypToCompGoal tau), ms), tau, ms, xs)
      | Comp.TypBox (loc, LF.ClTyp (LF.STyp (_svar_c, _cPhi),  _cPsi)) ->
          raise NotImplementedYet
      | Comp.TypPiBox (loc, mdecl, tau')  when i > 0 ->
         let LF.Decl(x, mtyp, plicity, inductivity) = mdecl in
         (match mtyp with
         | LF.ClTyp (LF.MTyp _, _) ->
            let mmV = Whnf.newMMVar' (Some x) (LF.Empty, mtyp) plicity inductivity in
            let mfront = Whnf.mmVarToMFront loc mmV mtyp in
            comptypToMQuery' (tau', i-1) (LF.MDot (mfront, ms))
              ((x, (loc, mfront)) :: xs)
         | LF.ClTyp (LF.PTyp tA, cPsi) ->
            let mmV = Whnf.newMPVar (Some x) (LF.Empty, cPsi, tA) plicity inductivity in
            let mfront = Whnf.mmVarToMFront loc mmV mtyp in
            comptypToMQuery' (tau', i-1) (LF.MDot (mfront, ms))
              ((x, (loc, mfront)) :: xs)
         | LF.CTyp cid_opt ->
            comptypToMQuery' (tau', i-1) ms xs)
      | Comp.TypPiBox (_, _, tau') when i = 0 ->
         (((comptypToCompGoal tau), ms), tau, ms, xs)
      | Comp.TypArr (loc, tau1, tau2) ->
         (((comptypToCompGoal tau), ms), tau, ms, xs)
      | Comp.TypBase (_) ->
         (((comptypToCompGoal tau), ms), tau, ms, xs)
      | _ -> raise NotImplementedYet
    in
    comptypToMQuery' (tau, i) (LF.MShift 0) []

end


module Index = struct
  let types = Hashtbl.create 0          (* typConst Hashtbl.t          *)

  let compITypes = Hashtbl.create 0     (* compTypConst Hashtbl.t      *)

  let compTTypes = Hashtbl.create 0     (* comp theorem Hashtbl.t      *)

  type inst = (Name.t *  LF.normal)    (* I ::= (x, Y[s]) where Y is an MVar        *)
                                        (* where mf contains an MMVar *)
  type sgnQuery =
    { query : query                   (* Query ::= (g, s)            *)
    ; typ : LF.typ                    (* Query as LF.typ.            *)
    ; skinnyTyp : LF.typ              (* Query stripped of E-vars.   *)
    ; optName : Name.t option         (* Opt. name of proof term.    *)
    ; cD : LF.mctx                    (* Meta context.               *)
    ; expected : bound                (* Expected no. of solutions.  *)
    ; tries : bound                   (* No. of tries to find soln.  *)
    ; instMVars : inst list           (* MVar instantiations.        *)
    }

  let queries = DynArray.create ()      (* sgnQuery DynArray.t         *)

  let querySub = ref S.id

  (* addTyp c = sgnClause DynArray.t
     Create a new entry for a type constant, c, in the `types' table and
     return its mapping, i.e. an empty DynArray.
  *)
  let addTyp cidTyp =
    Hashtbl.add types cidTyp (DynArray.create ());
    Hashtbl.find types cidTyp

  (* addCompTyp c = sgnCClause DynArray.t
     Create new entry for a compTyp constant c in the `compITypes' table
     and return its mapping
  *)

  let addCompTyp cidTyp =
    Hashtbl.add compITypes cidTyp (DynArray.create ());
    Hashtbl.find compITypes cidTyp

  let addComp cidTyp =
    Hashtbl.add compTTypes cidTyp (DynArray.create ());
    Hashtbl.find compTTypes cidTyp

  (* addSgnClause tC, sCl = ()
     Add a new sgnClause, sCl, to the DynArray tC.
  *)
  let addSgnClause typConst sgnClause =
    DynArray.add typConst sgnClause

  (* addSgnQuery (p, (g, s), cD, xs, e, t)  = ()
     Add a new sgnQuery to the `queries' DynArray.
  *)
  let addSgnQuery (p, a, a', q, cD, xs, e, t) =
    DynArray.add queries
      { query = q
      ; typ = a
      ; skinnyTyp = a'
      ; optName = p
      ; cD = cD
      ; expected = e
      ; tries = t
      ; instMVars = xs
      }

  (* compile _ Clause c = (c, sCl)
     Retrieve type for term constant c, clausify it, and
     return the respective clause (c, sCl).
   *)

  (* LF Constants  *)
  let compileSgnClause cidTerm =
    let { Store.Cid.Term.Entry.typ = tA; _ } = Store.Cid.Term.get cidTerm in
    (cidTerm, Convert.typToClause tA)

  (* Computation Theorem Constants  *)
  let compileSgnCClause cidTerm =
    let { Store.Cid.Comp.Entry.typ = tau; _ } = Store.Cid.Comp.get cidTerm in
    (cidTerm, Convert.comptypToCClause tau)

  (* Computation Inductive Constants *)
  let compileSgnConstClause cidCompTerm =
    let { Store.Cid.CompConst.Entry.typ = tau; _ } = Store.Cid.CompConst.get cidCompTerm in
    (cidCompTerm, Convert.comptypToCClause tau)


  (* termName c = Name.t
     Get the string representation of term constant c.
  *)
  let termName cidTerm =
    (Store.Cid.Term.get cidTerm).Store.Cid.Term.Entry.name

  let compName cidTerm =
    (Store.Cid.Comp.get cidTerm).Store.Cid.Comp.Entry.name

  let compConstName cidTerm =
    (Store.Cid.CompConst.get cidTerm).Store.Cid.CompConst.Entry.name

  (* storeTypConst c = ()
     Add a new entry in `types' for type constant c and fill the DynArray
     with the clauses corresponding to the term constants associated with c.
     The revIter function serves to preserve the order of term constants
     intrinsic to the Beluga source file, since the constructors for c are
     listed in reverse order.
  *)
  let storeTypConst (cidTyp, typEntry) =
    let typConstr = !(typEntry.Store.Cid.Typ.Entry.constructors) in
    let typConst = addTyp cidTyp in
    let regSgnClause cidTerm =
      addSgnClause typConst (compileSgnClause cidTerm)
    in
    let rec revIter f =
      function
      | [] -> ()
      | h :: l' ->
         revIter f l';
         f h
    in
    revIter regSgnClause typConstr

  (* storeCompValue c = ()
     Add a new entry in `compTTypes' for comptype constant c and fill the
     DynArray with the clause corresponding to the comp. theorem
     associated  with c.
   *)

  let storeCompValue (cidTyp, typEntry) =
    let typConst = addComp cidTyp in
    addSgnClause typConst (compileSgnCClause cidTyp)


  (* storeCompConst c = ()
     Add a new entry in `Comptypes' for computation level constructor c and fill the
     DynArray with the clauses corresponding to the constructor
     (defined by keywords `Stratified' and `Inductive') associated  with c.
   *)


  let storeCompConst (cidCompTyp, compTypEntry) =
    let ctypConstr = !(compTypEntry.Store.Cid.CompTyp.Entry.constructors) in
    let ctypConst = addCompTyp cidCompTyp in
    let regSgnCClause cidCompTerm =
      addSgnClause ctypConst (compileSgnConstClause cidCompTerm)
    in
    let rec revIter f =
      function
      | [] -> ()
      | h :: l' ->
         revIter f l';
         f h
    in
    revIter regSgnCClause ctypConstr

  (* storeQuery (p, (tA, i), cD, e, t) = ()
     Invariants:
       i = # of abstracted EVars in tA
  *)
  let storeQuery (p, (tA, i), cD,  e, t) =
    let (q, tA', s, xs) = (Convert.typToQuery LF.Empty LF.Null (tA, i)) in
    querySub := s;
    addSgnQuery (p, tA, tA', q, cD, xs, e, t)

  (* rob_LF_Store () = ()
     Store all type constants in the `types' table.
  *)
  let rob_LF_Store () =
    try
      List.iter storeTypConst (Store.Cid.Typ.current_entries ())
    with
    | _ -> ()

  (* rob_CompValue_Store () = ()
     Store all computation level constant in the `compTTypes' table.
  *)
  let rob_CompValue_Store () =
    try
      List.iter storeCompValue (Store.Cid.Comp.current_entries ())
    with
    | _ -> ()

  (* rob_CompConst_Store () = ()
     Store all computation level constructors from
     inductive and stratified data types in the `compITypes' table.
  *)
  let rob_CompConst_Store () =
    try
      List.iter storeCompConst (Store.Cid.CompTyp.current_entries ())
    with
    | _ -> ()

  (* Store all signature constants in their respective tables *)
  let robStore () =
    rob_LF_Store ();
    rob_CompValue_Store ();
    rob_CompConst_Store ()

  (* iterSClauses f c = ()
     Iterate over all signature clauses associated with c.
  *)
  let iterSClauses f cidTyp =
    DynArray.iter f (Hashtbl.find types cidTyp)

  let iterAllSClauses f =
    Hashtbl.iter (fun k v -> DynArray.iter f v) types

  let iterISClauses f cidTyp =
    DynArray.iter f (Hashtbl.find compITypes cidTyp)

  let iterAllISClauses f =
    Hashtbl.iter (fun k v -> DynArray.iter f v) compITypes

  let iterAllTSClauses f =
    Hashtbl.iter (fun k v -> DynArray.iter f v) compTTypes

  let iterQueries f =
    DynArray.iter (fun q -> f q) queries

  (* clearIndex () = ()
     Empty the local storage.
  *)
  let clearIndex () =
    DynArray.clear queries;
    Hashtbl.clear types;
    Hashtbl.clear compITypes;
    Hashtbl.clear compTTypes



  let singleQuery (p, (tA, i), cD, e, t) f =
    let (q, tA', s, xs) = (Convert.typToQuery LF.Empty LF.Null (tA, i)) in
    querySub := s;
    robStore ();
    let bchatter = !Options.chatter in
    Options.chatter := 0;
    let sgnQ =
      { query = q
      ; typ = tA
      ; skinnyTyp = tA'
      ; optName = p
      ; cD = cD
      ; expected = e
      ; tries = t
      ; instMVars = xs
      }
    in
    f sgnQ;
    Options.chatter := bchatter;
    Hashtbl.clear types;
    Hashtbl.clear compITypes;
    Hashtbl.clear compTTypes
end



module Printer = struct
  module P = Prettyint.DefaultPrinter
  open Index

  let fmt_ppr_dctx cD ppf cPsi =
    P.fmt_ppr_lf_dctx cD P.l0 ppf cPsi

  let fmt_ppr_gctx cD ppf cG =
    P.fmt_ppr_cmp_gctx cD P.l0 ppf cG

  let fmt_ppr_mctx ppf cD =
    P.fmt_ppr_lf_mctx P.l0 ppf cD

  let fmt_ppr_cmp_ihctx cD cG ppf cIH =
    P.fmt_ppr_cmp_ihctx cD cG ppf cIH

  let fmt_ppr_typ cD cPsi ppf sA =
    P.fmt_ppr_lf_typ cD cPsi P.l0 ppf (Whnf.normTyp sA)

  let fmt_ppr_cmp_typ cD ppf sA =
    P.fmt_ppr_cmp_typ cD P.l0 ppf sA

  let fmt_ppr_normal cD cPsi ppf sM =
    P.fmt_ppr_lf_normal cD cPsi P.l0 ppf (Whnf.norm sM)

  let fmt_ppr_decl cD cPsi ppf (tD, s) =
    match tD with
    | LF.TypDeclOpt x ->
       fprintf ppf "%a : _"
         Name.pp x
    | LF.TypDecl (x, tA) ->
       fprintf ppf "%a : %a"
         Name.pp x
         (fmt_ppr_typ cD cPsi) (tA, s)

  let fmt_ppr_lf_ctyp_decl cD ppf ctdec =
    P.fmt_ppr_lf_ctyp_decl cD ppf ctdec

  (* goalToString Psi (g, s) = string
     Invariants:
       Psi |- s : Phi
       Phi |- g : goal
       Psi |- g[s] : goal

     Effects:
       None.
  *)
  let rec fmt_ppr_goal cD cPsi ppf (g, s) =
    match g with
    | Atom tA ->
       fmt_ppr_typ cD cPsi ppf (tA, s)
    | Impl ((r, tD), g') ->
       fprintf ppf "%a -> %a"
         (fmt_ppr_res cD cPsi) (r, s)
         (fmt_ppr_goal cD (LF.DDec (cPsi, S.decSub tD s))) (g', S.dot1 s)
    | All (tD, g') ->
       fprintf ppf "(∀%a. %a)"
         (fmt_ppr_decl cD cPsi) (tD, s)
         (fmt_ppr_goal cD (LF.DDec (cPsi, S.decSub tD s))) (g', S.dot1 s)

  and fmt_ppr_cmp_goal cD ppf (cg, s) =
    match cg with
    | Box (cPsi, _g, lfTy) ->
       let tau = Convert.boxToTypBox cg in
       fprintf ppf " %a "
         (fmt_ppr_cmp_typ cD) (tau)
    | Atomic (cid, aSpine) ->
       let tau = Convert.atomicToBase cg in
       fprintf ppf " %a "
         (fmt_ppr_cmp_typ cD) (tau)
    | Forall (ctdec, cg') ->
       let cD' = Whnf.extend_mctx cD (ctdec, LF.MShift 0) in
       fprintf ppf "(∀%a. %a)"
         (fmt_ppr_lf_ctyp_decl cD) ctdec
         (fmt_ppr_cmp_goal cD') (cg', S.dot1 s)
    | Implies ((cr, ctdec), cg') ->
       fprintf ppf "%a -> %a"
         (fmt_ppr_cmp_res cD) (cr, s)
         (fmt_ppr_cmp_goal cD) (cg', s)

  (* resToString cPsi (r, s) = string
     Invariants:
       Psi |- s: Phi
       Phi |- r : res
       Psi |- r[s] : res

     Effects:
       None.
   *)

  and fmt_ppr_cmp_res cD ppf (cr, s) =
    match cr with
    | Base (tau) ->
       fprintf ppf "%a"
         (fmt_ppr_cmp_typ cD) tau
    | CAnd (cg', cr') ->
       fprintf ppf "%a -> %a"
         (fmt_ppr_cmp_goal cD) (cg', s)
         (fmt_ppr_cmp_res cD) (cr', s)
    | CExists (ctdec, cr') ->
       fprintf ppf "(∃%a. %a)"
         (fmt_ppr_lf_ctyp_decl cD) (ctdec)
         (fmt_ppr_cmp_res cD) (cr', s)


  and fmt_ppr_res cD cPsi ppf (r, s) =
    match r with
    | Head tH ->
       fmt_ppr_typ cD cPsi ppf (tH, s)
    | And (g, r') ->
       fprintf ppf "%a -> %a"
         (fmt_ppr_goal cD cPsi) (g, s)
         (fmt_ppr_res cD cPsi) (r', s)
    | Exists (LF.TypDecl (_, _tA) as tD, r') ->
       fprintf ppf "(∃%a. %a)"
         (fmt_ppr_decl cD cPsi) (tD, s)
         (fmt_ppr_res cD (LF.DDec (cPsi, S.decSub tD s))) (r', S.dot1 s)


  let fmt_ppr_cmp_exp cD cG ppf eChk =
    P.fmt_ppr_cmp_exp cD cG P.l0 ppf eChk


  (** Prints each subgoal with a leading `<-`. *)
  let fmt_ppr_subgoals cD cPsi ppf (cG, s) =
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut
         (fun ppf g ->
           fprintf ppf "<- %a"
             (fmt_ppr_goal cD cPsi) (g, s)))
      (list_of_conjunction cG)

  (** Prints each comp. subgoal with a trailing `->`. *)
  let fmt_ppr_csubgoals cD ppf subgoals =
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut
         (fun ppf sg ->
           fprintf ppf "%a ->"
             (fmt_ppr_cmp_goal cD) (sg, S.id)))
         (List.rev (list_of_subgoals subgoals))

  (* sgnClauseToString (c, sCl) = string
     String representation of signature clause.
  *)
  let fmt_ppr_sgn_clause ppf (cidTerm, sCl) =
    fprintf ppf "@[<v 2>@[%a@] : @[%a@]@,%a@]"
      Name.pp (termName cidTerm)
      (fmt_ppr_typ LF.Empty sCl.eVars) (sCl.tHead, S.id)
      (fmt_ppr_subgoals LF.Empty sCl.eVars) (sCl.subGoals, S.id)

  (** Prints a Computation Type clause *)
  let fmt_ppr_sgn_cclause ppf (cidTerm, sCCl) =
    fprintf ppf "@[<v 2>@[%a@] : @[%a@]@,%a@]"
      Name.pp (compName cidTerm)
      (fmt_ppr_cmp_typ sCCl.cMVars) (sCCl.cHead)
      (fmt_ppr_csubgoals sCCl.cMVars) (sCCl.cSubGoals)

   (** Prints clausal form of a Computation Constant *)
  let fmt_ppr_sgn_compclause ppf (cidTerm, sCCl) =
    fprintf ppf "@[<v 2>@[%a@] : @[%a@]@,%a@]"
      Name.pp (compConstName cidTerm)
      (fmt_ppr_cmp_typ sCCl.cMVars) (sCCl.cHead)
      (fmt_ppr_csubgoals sCCl.cMVars) (sCCl.cSubGoals)


  let fmt_ppr_bound ppf =
    function
    | Some i -> fprintf ppf "%d" i
    | None -> fprintf ppf "*"

  let fmt_ppr_sgn_query ppf q =
    fprintf ppf "--query %a %a %a."
      fmt_ppr_bound q.expected
      fmt_ppr_bound q.tries
      (fmt_ppr_typ LF.Empty LF.Null) (q.typ, S.id)

  (* instToString xs = string
     Return string representation of existential variable
     instantiations in the query.
   *)
  let fmt_ppr_inst ppf =
    function
    | [] -> fprintf ppf "^."
    | xs ->
       fprintf ppf "@[<v>%a@]."
         (pp_print_list ~pp_sep: pp_print_cut
            (fun ppf (x, tA) ->
              fprintf ppf "%a = %a;"
                Name.pp x
                (fmt_ppr_normal LF.Empty LF.Null) (tA, S.id)))
         xs

  let printQuery q =
    fprintf std_formatter "%a.@\n@\n"
      fmt_ppr_sgn_query q

  (* Prints all LF signatures *)
  let printSignature () =
    iterAllSClauses
      (fun w ->
        fprintf std_formatter "%a@\n"
          fmt_ppr_sgn_clause w)

  (* Prints all the computation theorems *)
  let printCompSignature () =
    iterAllTSClauses
      (fun w ->
        fprintf std_formatter "%a@\n"
          fmt_ppr_sgn_cclause w)

  (* Prints all Inductive type signatures *)
  let printCompConstSignature () =
    iterAllISClauses
      (fun w ->
        fprintf std_formatter "%a@\n"
          fmt_ppr_sgn_compclause w)


  let printAllSig () =
    printSignature ();
    printCompSignature ();
    printCompConstSignature ()

end

module Solver = struct
  module P = Printer.P
  module U = Unify.StdTrail
  module C = Convert
  module I = Index

  exception DepthReached of bound
  exception End_Of_Search
  exception NoSolution

  (* Dynamic Assumptions *)
  type dPool =                           (* dP ::=                  *)
    | Empty                              (*      | Empty            *)
    | DynCl of (dPool * (clause * int))  (*      | (dP', (dCl, k))  *)

  (* unify Psi (A, s) (B, s') sc = ()
     Invariants:
       sc : unit -> unit

     Effects:
       Instatiation of MVars in s and s'.
       Any effect of (sc ()).
  *)
  let unify cD cPsi sA sB sc =
    U.unifyTyp cD cPsi sA sB;
    sc ()

  (* trail f = ()
     Trail a function. If an exception is raised, unwind the trail and
     propagate the exception.
  *)
  let trail f =
    U.mark ();
    try
      f ();
      U.unwind ()
    with
    | e ->
       U.unwind ();
       raise e

  (* trail' f = ()
    Trail a function. If an exception is raised, unwind the trail and
    propagate the exception. Do not unwind if f () succesful. *)

  let trail' f =
    U.mark ();
    try
      f ()
    with
    | e ->
       U.unwind ();
       raise e

  (* eqHead A dCl = bool
     Compare the cid_typ's of A and the head of dCl.
  *)
  let eqHead tA dCl =
    match (tA, dCl.tHead) with
    | (LF.Atom (_, i, _), LF.Atom (_, j, _)) -> Id.cid_typ_equal i j
    | _ -> false

  (* cidFromAtom A = cid_typ *)
  let cidFromAtom =
    function
    | LF.Atom (_, i, _) -> i
    | _ ->
       invalid_arg
         "Logic.Solver.cidFromAtom: Match failure against LF.Atom (_, _, _)."

  (* shiftSub k = ^k
     Invariants:
       Psi, x1:_, x2:_, ... xk:_ |- ^k : Psi
  *)
  let shiftSub k = LF.Shift k

  let succ x =
    match x with
    | None -> (Some 1)
    | (Some i) -> (Some (i + 1))

  let checkDepth x y =
      match (x, y) with
      | (Some i, Some j) -> i > j
      | (Some i, None) -> false
      | (None, _) -> false

  let uninstantiated hd =
      match hd with
    | LF.MMVar ((mmvar, ms'), s)
         when Option.is_none !(mmvar.LF.instantiation) ->
       true
    | LF.MVar (LF.Inst mmvar, s)
         when Option.is_none !(mmvar.LF.instantiation) ->
       true
    | LF.MPVar ((mmvar, ms'), s)
         when Option.is_none !(mmvar.LF.instantiation) ->
       true
    | _ -> false

  (* Returns true if there are no uninstantiated mvars in the sub. *)
  let rec check_sub s =
    match s with
    | LF.Shift _ -> true
    | LF.Dot (LF.Head (((LF.MMVar ((mmvar, ms'), s)) as hd)), s') ->
       if uninstantiated hd then false
       else check_sub s'
    | LF.Dot (LF.Head (((LF.MPVar ((mmvar, ms'), s)) as hd)), s') ->
       if uninstantiated hd then false
       else check_sub s'
    | LF.Dot (LF.Head (((LF.MVar (LF.Inst mmvar, s)) as hd)), s') ->
       if uninstantiated hd then false
       else check_sub s'
    | LF.Dot (LF.Obj (LF.Root (loc,
                               ((LF.MVar (LF.Inst mmvar, s)) as hd), sP, pl))
            , s') ->
       if uninstantiated hd then false
       else check_sub s'
    | LF.Dot (LF.Obj (LF.Root (loc,
                               ((LF.MMVar ((mmvar, ms'), s)) as hd), sP, pl))
            , s') ->
       if uninstantiated hd then false
       else check_sub s'
    | LF.Dot (LF.Obj (LF.Root (loc,
                               ((LF.MPVar ((mmvar, ms'), s)) as hd), sP, pl))
            , s') ->
       if uninstantiated hd then false
       else check_sub s'
    | LF.Dot (_, s') ->
       check_sub s'

  (* Correct the plicity tags on the mmvars in the sub *)
  let rec fix_sub s cD =
    let rec get_plicity cD k =
      match cD with
      | LF.Dec (_, LF.Decl (_, _, plic, _)) when k = 1 -> plic
      | LF.Dec (cD', _) -> get_plicity cD' (k-1)
    in
    match s with
    | LF.Dot (LF.Obj (LF.Root (loc,
                               ((LF.MVar (LF.Inst mmvar, s)) as hd), sP, _1))
            , s') ->
       let plicity =
         match !(mmvar.LF.instantiation) with
         | Some (LF.INorm (LF.Root (_, LF.MVar (LF.Offset k, _), _, _))) ->
            get_plicity cD k
         | Some (LF.IHead (LF.MVar (LF.Offset k, _))) -> get_plicity cD k
         | _ -> _1
       in
       LF.Dot (LF.Obj (LF.Root (loc, hd, sP, plicity)), fix_sub s' cD)
    | LF.Dot (_1, s') ->
       dprintf begin fun p -> p.fmt "[fix_sub] skipping fixing sub" end;
       LF.Dot (_1, fix_sub s' cD)
    | _ -> s

  (* Instantiate the nth position of sub s with the front ft. *)
  let rec instantiate_sub (n, s) ft curr =
    match s with
    | LF.Dot (_, s') when n = curr ->
       LF.Dot (ft, s')
    | LF.Dot (ft', s') -> LF.Dot (ft', instantiate_sub (n, s) ft (curr + 1))
    | _ -> s

  (* gSolve dPool (Psi, k) (g, s) sc = ()
     Invariants:
       dPool ~ Psi
       k = |Psi|
       Psi |- s : Phi
       Phi |- g : Goal
       sc : proof -> unit
       If G |- M : g[s], then (sc M) is evaluated.

     Effects:
       Instantiation of MVars in s and dPool.
       Any effect (sc M) might have.

     Comments:
       In the arguments to 'sc', 'u' refers to the universal
       context and 't' refers to a proof term.
  *)
  let rec gSolve dPool cD (cPsi, k) (g, s) sc (currDepth, maxDepth) =
    if (checkDepth currDepth maxDepth)
    then
      begin
        dprintf
          begin fun p ->
          p.fmt "[logic] [gSolve] DEPTH REACHED"
          end;
        raise (DepthReached currDepth)
      end
    else
    match g with
    | Atom tA ->
       matchAtom dPool cD (cPsi, k) (tA, s) sc (currDepth, maxDepth)

    | Impl ((r, (LF.TypDecl (x, _) as tD)), g') ->
       (* extend the dynamic pool with the new assumption and prove the conclusion *)
       let dPool' =
         DynCl (dPool, (C.resToClause (r, s), k))
       in
       gSolve dPool' cD (LF.DDec (cPsi, S.decSub tD s), k + 1) (g', S.dot1 s)
         (fun (u, tM) -> sc (u, LF.Lam (Location.ghost, x, tM)))
         (currDepth, maxDepth)

    | All (LF.TypDecl (x, _) as tD, g') ->
       (* we *don't* get an assumption from a forall; it's just a parameter.
          So we just prove the conclusion in an extended context. *)
       gSolve dPool cD (LF.DDec (cPsi, S.decSub tD s), k + 1) (g', S.dot1 s)
         (fun (u, tM) -> sc (u, LF.Lam (Location.ghost, x, tM)))
         (currDepth, maxDepth)

  (* Overall goal...
     cD ; cPsi         |- X <= u
     cD ; cPhi ~ dPool |- goal[s_goal]
     cD ; cPhi         |- s_all : cPsi
     want to instantiate s s.t. [s_all]u == [s_goal]goal

     solve_sub:
     s_all = s, ?M/x, s' <= cPhi', x:?tA. cPhi''
     find M:tA' s.t. cD ; cPhi' |- M <= [s]tA *)
  and solve_sub_delta (cD_all, cD, k, cPhi, dPool) (tA, s, curr_sub) (u, s_all)
(goal, s_goal) =
    dprintf begin fun p ->
      p.fmt "[solve_sub_delta] looking for term of type %a"
      (Printer.fmt_ppr_typ cD_all cPhi) (tA, LF.Shift 0) end;
    let tA = match tA with
      | LF.TClo (tA, _) | tA -> tA in

    let rec strengthen (dctx, n) =
      match dctx with
      | LF.DDec (dctx', td) when n > 0 -> strengthen (dctx, (n-1))
      | _ -> dctx
    in

    (* remove first curr_sub entries from cPhi *)
    let cPhi' = strengthen (cPhi, curr_sub) in
    match cD with
    | LF.Empty -> raise NoSolution
    | LF.Dec (cD', LF.Decl (_, LF.CTyp (_), _, _)) ->
       solve_sub_delta (cD_all, cD', k+1, cPhi, dPool) (tA, s, curr_sub) (u, s_all) (goal, s_goal)
    | LF.Dec (cD', LF.Decl (_, LF.ClTyp (cltyp, cPsi), plicity, _)) ->
       let tA' = match cltyp with
         | LF.MTyp tau -> tau
         | LF.PTyp tau -> tau
       in
       try
         trail'
           begin fun () ->
           try
           (* Check if the assumption matches our goal *)
           U.unifyTyp cD_all cPhi'
             (tA, LF.Shift 0)
             (Whnf.cnormTyp(tA', LF.MShift k), LF.Shift 0);

           dprintf begin fun p ->
            p.fmt "[solve_sub_delta] s = %a, s_all = %a"
              (P.fmt_ppr_lf_sub cD' cPhi' P.l0) s
              (P.fmt_ppr_lf_sub cD_all cPhi P.l0) s_all
            end;

           (* If the assumption matches the desired type, we make sure we're
              on the right track by
              unifying our current goal and sub_goal [s_goal]goal with
              the assumption from cD and its sub [s_all]u              *)
           U.unifyTyp cD_all cPhi (goal, s_goal) (u, s_all);

           (* Instantiate the correct sub in s_all with the front *)
           instantiate_sub (curr_sub, s_all) (LF.Obj (LF.Root (Location.ghost, LF.MVar(LF.Offset k, LF.Shift 0), LF.Nil, plicity))) 1

           with
           | U.Failure _ ->
                U.unifyTyp cD_all cPhi'
                  (Whnf.cnormTyp(tA, LF.MShift k), LF.Shift 0)
                  (Whnf.cnormTyp(tA', LF.MShift k), LF.Shift 0);
                U.unifyTyp cD_all cPhi (goal, s_goal) (LF.TClo(u, s_all), LF.Shift 0);
                (* Instantiate the correct sub in s_all with the front *)
           instantiate_sub (curr_sub, s_all) (LF.Obj (LF.Root (Location.ghost, LF.MVar(LF.Offset k, LF.Shift 0), LF.Nil, plicity))) 1
           end
       with
       | U.Failure _ ->
     solve_sub_delta (cD_all, cD', k+1, cPhi, dPool) (tA, s, curr_sub) (u, s_all) (goal, s_goal)

  (* Attempts to complete a branch of the proof tree by solving the
     simultaneuos substitution.

     cD ; cPsi         |- X <= u      where X : U = (cPsi, u) is in cD
     cD ; cPhi ~ dPool |- goal[s_goal]
     cD ; cPhi         |- s_all : cPsi
     want to instantiate s_all s.t. [s_all]u == [s_goal]goal           *)
  and trivially_prove s s_all cD (goal, cPhi, s_goal) dPool u curr_sub =
    dprintf begin fun p -> p.fmt "[trivially_prove] s = %a"
                             (P.fmt_ppr_lf_sub cD cPhi P.l0) s
                             end;
    match s with
    | LF.Shift _ ->
dprintf begin fun p ->
            p.fmt "[trivially_prove] s_all = %a"
              (P.fmt_ppr_lf_sub cD cPhi P.l0) s_all
            end;
       if (* Check if all mvars have been instantiated *)
         check_sub (Whnf.normSub s_all)
       then (* Correct plicity tags on mvars *)
         fix_sub s_all cD
       else raise NoSolution
    | LF.Dot (LF.Head (((LF.MMVar ((mmvar, ms'), s)) as hd)), s')
         when (uninstantiated hd) ->
         let ctyp = mmvar.LF.typ in
         let tA = match ctyp with
           | LF.ClTyp (LF.MTyp tA, _) | LF.ClTyp (LF.PTyp tA, _) -> tA
           | _ -> raise NotImplementedYet
         in
         (try
            let s_all' = solve_sub_delta (cD, cD, 1, cPhi, dPool) (tA, s', curr_sub) (u, s_all) (goal, s_goal) in
            let s' = Whnf.normSub s' in
            trivially_prove s' s_all' cD (goal, cPhi, s_goal) dPool u
              (curr_sub+1)
         with
         | U.Failure _ | NoSolution -> raise NoSolution)

    | LF.Dot (LF.Head (((LF.MPVar ((mmvar, ms'), s)) as hd)), s')
         when (uninstantiated hd) ->
         let ctyp = mmvar.LF.typ in
         let tA = match ctyp with
           | LF.ClTyp (LF.MTyp tA, _) | LF.ClTyp (LF.PTyp tA, _) -> tA
           | _ -> raise NotImplementedYet
         in
         (try
            let s_all' = solve_sub_delta (cD, cD, 1, cPhi, dPool) (tA, s', curr_sub)
                           (u, s_all) (goal, s_goal) in
            let s' = Whnf.normSub s' in
            trivially_prove s' s_all' cD (goal, cPhi, s_goal) dPool u (curr_sub+1)
         with
         | U.Failure _ | NoSolution -> raise NoSolution)

    | LF.Dot (LF.Head (((LF.MVar (LF.Inst mmvar, s)) as hd)), s')
         when (uninstantiated hd) ->
         let ctyp = mmvar.LF.typ in
         let tA = match ctyp with
           | LF.ClTyp (LF.MTyp tA, _) | LF.ClTyp (LF.PTyp tA, _) -> tA
           | _ -> raise NotImplementedYet
         in
         (try
            let s_all' = solve_sub_delta (cD, cD, 1, cPhi, dPool) (tA, s', curr_sub)
                           (u, s_all) (goal, s_goal) in
            let s' = Whnf.normSub s' in
            trivially_prove s' s_all' cD (goal, cPhi, s_goal) dPool u (curr_sub+1)
         with
         | U.Failure _ | NoSolution -> raise NoSolution)
    | LF.Dot (LF.Obj
                (LF.Root
                   (loc, ((LF.MVar (LF.Inst mmvar, s)) as hd), sP, pl)), s')
         when (uninstantiated hd) ->
         let ctyp = mmvar.LF.typ in
         let tA = match ctyp with
           | LF.ClTyp (LF.MTyp tA, _) | LF.ClTyp (LF.PTyp tA, _) -> tA
           | _ -> raise NotImplementedYet
         in
         (try
            let s_all' = solve_sub_delta (cD, cD, 1, cPhi, dPool) (tA, s', curr_sub)
                           (u, s_all) (goal, s_goal) in
            let s' = Whnf.normSub s' in
            trivially_prove s' s_all' cD (goal, cPhi, s_goal) dPool u (curr_sub+1)
         with
         | U.Failure _ | NoSolution -> raise NoSolution)
    | LF.Dot (LF.Obj
                (LF.Root
                   (loc, ((LF.MMVar ((mmvar, ms'), s)) as hd), sP, pl)), s')
         when (uninstantiated hd) ->
         let ctyp = mmvar.LF.typ in
         let tA = match ctyp with
           | LF.ClTyp (LF.MTyp tA, _) | LF.ClTyp (LF.PTyp tA, _) -> tA
           | _ -> raise NotImplementedYet
         in
         (try
            let s_all' = solve_sub_delta (cD, cD, 1, cPhi, dPool) (tA, s', curr_sub)
                           (u, s_all) (goal, s_goal) in
            let s' = Whnf.normSub s' in
            trivially_prove s' s_all' cD (goal, cPhi, s_goal) dPool u (curr_sub+1)
         with
         | U.Failure _ | NoSolution -> raise NoSolution)
    | LF.Dot (LF.Obj
                (LF.Root
                   (loc, ((LF.MPVar ((mmvar, ms'), s)) as hd), sP, pl)), s')
         when (uninstantiated hd) ->
         let ctyp = mmvar.LF.typ in
         let tA = match ctyp with
           | LF.ClTyp (LF.MTyp tA, _) | LF.ClTyp (LF.PTyp tA, _) -> tA
           | _ -> raise NotImplementedYet
         in
         (try
            let s_all' = solve_sub_delta (cD, cD, 1, cPhi, dPool) (tA, s', curr_sub)
                           (u, s_all) (goal, s_goal) in
            let s' = Whnf.normSub s' in
            trivially_prove s' s_all' cD (goal, cPhi, s_goal) dPool u (curr_sub+1)
         with
         | U.Failure _ | NoSolution -> raise NoSolution)
    | LF.Dot (_, s') ->
       trivially_prove s' s_all cD (goal, cPhi, s_goal) dPool u (curr_sub+1)

  (* matchAtom dPool Delta (Psi, k) (A, s) sc = ()
     Invariants:
       dPool ~ Psi, k = |Psi|
       Delta; Psi |- s : Phi
       Delta; Phi |- A : Atom
       sc : proof -> unit
       If Delta; Psi |- M : A[s], then (sc M) is evaluated.

     Effects:
       Instatiation of MVars in s and dPool.
       Any effect (sc M) might have.
  *)
  and matchAtom dPool cD (cPsi, k) (tA, s) sc (currDepth, maxDepth) =
    (* some shorthands for creating syntax *)
    let root x = LF.Root (Location.ghost, x, LF.Nil, Plicity.explicit) in
    let pvar k = LF.PVar (k, LF.Shift 0) in
    let mvar k = LF.MVar (LF.Offset k, LF.Shift 0) in
    let proj x k = LF.Proj (x, k) in

    (* matchDProg dPool = ()
       Try all the dynamic clauses in dPool starting with the most
       recent one. If dPool is empty, try the signatures.
    *)
    let rec matchDProg = function
      | DynCl (dPool', (dCl, k')) ->
         (if (eqHead tA dCl)
         then
           begin
             let (s', fS) =
               C.dctxToSub cD cPsi (dCl.eVars, shiftSub (k - k'))
                 (fun tS -> tS) in
             (* Trail to undo MVar instantiations. *)
             (try
               trail
                 begin fun () ->
                 unify cD cPsi (tA, s) (dCl.tHead, s')
                   begin fun () ->
                   solveSubGoals dPool cD (cPsi, k) (dCl.subGoals, s')
                     begin fun (u, tS) ->
                     let tM =
                       LF.Root
                         ( Location.ghost
                         , LF.BVar (k - k')
                         , fS (spineFromRevList tS)
                         , Plicity.explicit
                         )
                     in
                     sc (u, tM)
                     end
                   (currDepth, maxDepth)
                   end
                 end
             with
             | U.Failure _ | End_Of_Search | DepthReached _ -> ());
             matchDProg dPool'
           end
          else
            matchDProg dPool')

      | Empty ->
         matchSig (cidFromAtom tA);
         raise End_Of_Search

    (* Decides whether the given Sigma type can solve the
     * goal type by trying all the projections.
     * Calls the success continuation with the found index.
     *
     * pv: the pattern variable whose sigma type we are analyzing
     * cD, psi: the contexts in which pv makes sense
     * typs: the sigma type of pv that we are analyzing
     * ts: the substitution we build up for past projections.
     * Since typs is a dependent pair, later projections can depend on
     * earlier projections. Hence, when we try to unify a later
     * projection with the goal type, we need to eliminate its bound
     * variables by substituting in the appropriate earlier projections.
     *)
    and matchSigma (pv : LF.head) (cD : LF.mctx) (psi : LF.dctx) (tRec : LF.typ_rec) sc : unit =
      let rec loop (typs, ts) k =
        let check typ =
          try
            trail
              begin fun () ->
              U.unifyTyp cD psi (typ, ts) (tA, s);
              dprintf
                begin fun p ->
                p.fmt "[logic] [matchSigma] \
                       @[<v>Found solution with projection %d of sigma-type:\
                       @,@[%a@]@]"
                  k
                  (P.fmt_ppr_lf_typ_rec cD psi P.l0) tRec
                end;
              sc k
              end
          with
          | U.Failure s -> ()
        in
        match typs with
        | LF.SigmaLast (name, typ) ->
           check typ
        | LF.SigmaElem (name, typ, typs) ->
           check typ;
           (* extend the substitution to use on subsequent entries of the sigma.
            *)
           loop
             (typs, LF.Dot (LF.Head (proj pv k), ts))
             (k + 1)
      in
      loop (tRec, LF.Shift 0) 1

    (* Try to find a solution in the meta-context.
     * The index `k` is the position we're looking at currently,
       and is used to appropriately weaken the meta-context type
       so that it is in the same context as the goal.
     * The initial value for `k` is 1.
     * If the context entry fails to unify with the target type,
       then this function will check whether the context entry is
       a Sigma type, meaning that it is a pattern or bound
       variable.
     * In that case, it will call matchSigma to figure out the
       appropriate projection to use on the variable, if any.
     *)
    (* cD0 ; cPsi |- tA[s]
       cD'', cdecl, cD_ ; cPsi |- tA[s]
       unify cdecl[s'] with tA[s]                                *)
    and matchDelta (cD0 : LF.mctx) =
      (* Extract the ctx_var (if any) from the dctx *)
      let rec get_ctx_var cPsi =
        match cPsi with
        | LF.DDec (cPsi', _) -> get_ctx_var cPsi'
        | _ -> cPsi
      in
      let rec loop cD' k =
        match cD' with
        | LF.Empty -> matchDProg dPool
        | LF.Dec (cD'', LF.Decl (n, LF.ClTyp (cltyp, cPsi0), _, _)) ->
           begin
             let cPsi' = Whnf.cnormDCtx (cPsi0, LF.MShift k) in
             let cltyp' = Whnf.cnormClTyp (cltyp, LF.MShift k) in
             let (s', _) =
               try
                 U.unifyDCtx cD0 cPsi' cPsi;
                 (LF.Shift 0, fun i -> i)
               with
               | U.Failure _ ->
                  C.dctxToSub' cD0 cPsi (cPsi', LF.Shift 0) (fun tS -> tS)
             in

             try
               trail
                 begin fun () ->
                 (* U.unifyDCtx cD psi' cPsi; *)

                 (* We look to see whether we're dealing with a sigma type.
                    In this case, we must consider the projections of the sigma.
                    If it isn't a sigma then we can just try to unify the types.
                  *)
                 match cltyp' with
                 | LF.PTyp (LF.Sigma typs) ->
                    matchSigma (pvar k) cD0 cPsi' typs
                      (fun k' ->
                        (* recall: k is the index of the variable in the _context_ *)
                        (* k' is the index of the projection into the _sigma_ *)
                        sc (cPsi', LF.Clo (root (proj (pvar k) k'),
                                           LF.Shift 0)))

                 | LF.PTyp typ' ->
                    (* I don't think this case ever happens; I'm pretty
                     * sure that whenever we have a PTyp, its type is a
                     * Sigma, so we can probably remove this case or assert
                     * that it's impossible.
                     * -jake
                     *)

                    U.unifyTyp cD0 cPsi' (typ', LF.Shift 0) (tA, s);

                    (* We need to create the syntax to refer to this _pattern_ variable *)
                    sc (cPsi', LF.Clo (root (pvar k), LF.Shift 0))

                 | LF.MTyp typ' ->
                    let s'' = trivially_prove s' s' cD0 (tA, cPsi, s) dPool typ' 1 in
                    U.unifyTyp cD0 cPsi (typ', s'') (tA, s);
                    dprintf
                      begin fun p ->
                      p.fmt "[logic] [matchDelta] found solution: variable %d" k
                      end;

                    if check_sub s''
                    then
                    let psi = get_ctx_var cPsi' in
                      sc (psi, LF.Clo (root (mvar k), s''))
                    else raise NoSolution

                 | LF.STyp _ ->
                    (* ignore substitution variables for now *)
                    ()
                 end
             with
             | U.Failure _ | U.Error _ | NotImplementedYet | NoSolution
               | DepthReached _ | End_Of_Search -> ()
           end;
           loop cD'' (k + 1)
        | LF.Dec (cD'', _dec) ->
           loop cD'' (k + 1)
      in
      loop cD0 1

    (* matchSig c = ()
       Try all the clauses in the static signature with head matching
       type constant c.                                               *)
    and matchSig cidTyp =
      dprintf begin fun p -> p.fmt "[matchSig]" end;
      I.iterSClauses (fun w -> matchSgnClause w sc) cidTyp

    (* matchSgnClause (c, sCl) sc = ()
       Try to unify the head of sCl with A[s]. If unification succeeds,
       attempt to solve the subgoals of sCl.                            *)
    and matchSgnClause (cidTerm, sCl) sc =
      begin
        let (s', fS) =
          C.dctxToSub cD cPsi (sCl.eVars, shiftSub (Context.dctxLength cPsi))
            (fun tS -> tS)
        in
      (* Trail to undo MVar instantiations. *)
        try
          trail
            begin fun () ->
            U.unifyTyp cD cPsi (tA, s) (sCl.tHead, s');
            solveSubGoals dPool cD (cPsi, k) (sCl.subGoals, s')
              begin fun (u, tS) ->
              let tM =
                LF.Root
                  ( Location.ghost
                  , LF.Const (cidTerm)
                  , fS (spineFromRevList tS)
                  , Plicity.explicit
                  )
              in
              sc (u, tM)
              end
              (currDepth, maxDepth)
            end
        with
        | U.Failure _ | End_Of_Search | DepthReached _ -> ()
      end

    in
    (* ^ end of the gigantic let of all the helpers for matchAtom;
      Now here's the actual body of matchAtom: *)
    matchDelta cD

  (* spineFromRevList : LF.normal list -> LF.spine
     build an LF.spine out of a list of LF.normal, reversing the order of the elements*)
  and spineFromRevList lS =
    List.fold_left (fun tSc tMc -> LF.App (tMc, tSc)) LF.Nil lS

  (* solveSubGoals dPool (Psi, k) (G, s) sc = ()
     Invariants:
       dPool ~ Psi
       G = (G', g) | T
       Psi |- s : Phi
       Phi |- g : goal
       sc : (dctx * spine) -> unit
       If Psi |- M : g[s], then (sc App (M, S)) is evaluated.
       If Psi |- G = T, then (sc Nil) is evaluated, ending the
       spine of proof-terms for the goals in G.

     Effects:
       Instatiation of MVars in dPool and g[s].
       Any effect of (sc S).                                  *)
  and solveSubGoals dPool cD (cPsi, k) (cG, s) sc (currDepth, maxDepth) =
    match cG with
    | True -> sc (cPsi, [])
    | Conjunct (cG', g) ->
       gSolve dPool cD (cPsi, k) (g, s)
         (fun (u, tM) ->
           solveSubGoals dPool cD (cPsi, k) (cG', s)
             (fun (v, tS) ->  sc (v, tM :: tS))
             (currDepth, maxDepth))
         (succ currDepth, maxDepth)

  (* solve (g, s) sc = ()
     Invariants:
       Empty |- g[s] : goal
       sc : dctx * normal -> unit

     Effects:
       Same as gSolve.
  *)
  let solve cD cPsi (g, s) sc d =
    gSolve Empty cD (cPsi, Context.dctxLength cPsi) (g, s) sc
      (None, d)

end

module CSolver = struct
  module U = Unify.StdTrail
  module C = Convert
  module I = Index
  module P = Printer
  module DP = Prettyint.DefaultPrinter

  (* Unboxed status of assumptions in Gamma *)
  (* We use this tag to tell us when a boxed assumption from Gamma has
     been unboxed (and thus no longer considered to be in Gamma). Once
     unboxed, the assumption is not able to be unboxed again or focused on.
     All assumptions begin tagged 'Boxed'.
   *)
  type status =
    | Boxed
    | Unboxed

    (* Dynamic Computation Assumptions *)
  type cPool =                             (* cP ::=                     *)
    | Emp                                  (*   | Emp                    *)
    | Full of
        (cPool * (cclause * int * status)) (*   | Full (cP', (cc, k, s)) *)
                                           (*      where k denotes the
                                                   postion of the
                                                   correspoding type
                                                   declaration in cG    *)
  (* Whether or not to blur on this iteration *)
  type blur_it =
    | Blur
    | No_Blur

  let noLoc = Location.ghost

  (* Exceptions raised during Proof Search *)
  exception DepthReached of bound  (* Max depth of search tree reached      *)
  exception End_Of_Search          (* All branches of search tree attempted *)

  (* unify (tau, ms) (tau', ms') sc = ()
     Invariants:
       sc : unit -> unit

     Effects:
       Instatiation of MMVars in ms and ms'.
       Any effect of (sc ()).
    *)
  let unify cD ttau ttau' sc =
    U.unifyCompTyp cD ttau ttau';
    sc ()

  let isBox cg =
    match cg with
    | Box (_) -> true
    | _ -> false

  let succ x =
    match x with
    | None -> (Some 1)
    | (Some i) -> (Some (i + 1))

  let checkDepth x y =
    match (x, y) with
    | (Some i, Some j) -> i > j
    | (Some i, None) -> false
    | (None, _) -> false

  (* If the first entry of cG is of box-type, checks if it's in rest of cG
     This is used to ensure the proofs we find are unique *)
  let in_cG cG cG_all cD =
    let ctyp, cG' =
      match cG_all with
      | LF.Dec (cG', Comp.CTypDecl (_, Comp.TypBox (_, ctyp), _)) ->
         ctyp, cG'
      | _ -> raise NotImplementedYet
    in
    let rec in_cG' cG cD =
      match cG with
      | LF.Empty -> false
      | LF.Dec (cG', Comp.CTypDecl (_, Comp.TypBox (_, ctyp'), _)) ->
         begin
           try
             (Solver.trail
               (fun () ->
                 U.unifyMetaTyp cD (ctyp, LF.MShift 0) (ctyp', LF.MShift 0)));
             true
           with
           | U.Failure _ -> in_cG' cG' cD
         end
      | LF.Dec (cG', _) -> in_cG' cG' cD
    in
    in_cG' cG' cD

  (* Check to see if the cid of the head of an assumption
     matches the cid of the comp_goal                         *)
  let rec matchHead assump cg =
    match (assump, cg) with
    | (Comp.TypBox (_, LF.ClTyp (LF.MTyp tA, cPsi))),
       Box (cPsi', Atom tA', Some M) ->
       Id.cid_typ_equal (Solver.cidFromAtom tA) (Solver.cidFromAtom tA')
    | (Comp.TypBox (_, LF.ClTyp (LF.PTyp tA, cPsi))),
       Box (cPsi', Atom tA', Some P) ->
       Id.cid_typ_equal (Solver.cidFromAtom tA) (Solver.cidFromAtom tA')
    | (Comp.TypBase (_, cid, _meta_spine), Atomic (cid', _atomic_spine)) ->
       Id.cid_comp_typ_equal cid cid'
    | (Comp.TypArr (_, tau1, tau2), cg) ->
       matchHead tau2 cg
    | (Comp. TypPiBox (_, ctdec, tau), cg) ->
       matchHead tau cg
    | _ -> false

  let rev_cPool cPool =
    let rec rev cPool cPool_ret =
      match cPool with
      | Emp -> cPool_ret
      | Full(cPool', cc) -> rev cPool' (Full (cPool_ret, cc))
    in
    rev cPool Emp

  let rev_mctx cD =
    let rec rev cD cD_ret =
      match cD with
      | LF.Empty -> cD_ret
      | LF.Dec(cD', cdecl) ->
         rev cD' (LF.Dec(cD_ret, cdecl))
    in
    rev cD LF.Empty

  (* prepend a clause to cPool *)
  let rec prependToCPool x cPool =
    match cPool with
    | Emp -> Full (Emp, x)
    | Full (cPool', c) ->
       Full (prependToCPool x cPool', c)

  (* shifts the index of the cPool by k
     ex) shift_cPool (Full (Full (Emp, (A, 4)), (B, 3))) 1 =
                      Full (Full (Emp, (A, 5)), (B, 4))

         shift_cPool (Full (Full (Emp, (A, 4)), (B, 3))) (-2) =
                      Full (Full (Emp, (A, 2)), (B, 1))       *)
  let rec shift_cPool cPool k =
    match cPool with
    | Full (cPool', (cc, k', s)) ->
       Full (shift_cPool cPool' k, (cc, k'+k, s))
    | _ -> cPool

  (* Applies the msub to hd only if it is not an uninstantiated mvar/mmvar *)
  let cnormHd (hd, ms) =
    match hd with
    | LF.MMVar ((mmvar, ms'), s)
         when Option.is_none !(mmvar.LF.instantiation) ->
       hd
    | LF.MPVar ((mmvar, ms'), s)
         when Option.is_none !(mmvar.LF.instantiation) ->
       hd
    | LF.MVar (LF.Inst mmvar, s)
         when Option.is_none !(mmvar.LF.instantiation) ->
       hd
    | _ -> Whnf.cnormHead (hd, ms)

  (* Applies msub to all heads excluding uninstantiated mvars/mmvars *)
  let rec cnormSpine (spine, ms) =
    match spine with
    | LF.Nil -> LF.Nil
    | LF.App (norm, spine') ->
       LF.App (cnormNorm (norm, ms), cnormSpine (spine', ms))
    | _ -> dprintf
             begin fun p ->
             p.fmt "[cnormSpine]"
             end;
           raise NotImplementedYet

  (* Applies msub to all heads excluding uninstantiated mvars/mmvars *)
  and cnormNorm (norm, ms) =
    match norm with
    | LF.Root (loc, hd, spine, pl) ->
       (try
         (let hd' = cnormHd (hd, ms) in
       let spine' = cnormSpine (spine, ms) in
       LF.Root (loc, hd', spine', pl))
       with
       | _ -> Whnf.cnorm (norm, ms))
    | LF.Lam (loc, name, norm') ->
       LF.Lam (loc, name, cnormNorm (norm', ms))
    | _ -> dprintf
             begin fun p ->
             p.fmt "[cnormNorm]"
             end;
           raise NotImplementedYet

  (* Applies msub to all heads excluding uninstantiated mvars/mmvars *)
  let cnormTyp (tA, ms) =
    match tA with
    | LF.Atom (loc, cid, spine) ->
       LF.Atom (loc, cid, cnormSpine (spine, ms))
    | _ -> dprintf
             begin fun p ->
             p.fmt "[cnormTyp]"
             end;
           raise NotImplementedYet

  (* Applies msub to all heads excluding uninstantiated mvars/mmvars *)
  let cnormMetaObj ((loc, mf), ms) =
    match mf with
    | LF.ClObj (dctx_hat, clobj) ->
       let clobj' =
         match clobj with
         | LF.MObj norm -> LF.MObj (cnormNorm (norm, ms))
         | LF.PObj hd -> LF.PObj (cnormHd (hd, ms))
         | _ -> dprintf
             begin fun p ->
             p.fmt "[cnormMetaObj]"
             end;
                raise NotImplementedYet
       in
       (loc, LF.ClObj (Whnf.cnorm_psihat dctx_hat ms, clobj'))
    | LF.CObj dctx ->
       (loc, LF.CObj (Whnf.cnormDCtx (dctx, ms)))
    | _ -> (loc, mf)

  (* Applies msub to all heads excluding uninstantiated mvars/mmvars *)
  let cnormMTyp (mtyp, ms) =
    match mtyp with
    | LF.ClTyp (LF.MTyp tA, cPsi) ->
       let tA' = cnormTyp (tA, ms) in
       LF.ClTyp (LF.MTyp tA', Whnf.normDCtx (Whnf.cnormDCtx (cPsi, ms)))
    | LF.ClTyp (LF.PTyp tA, cPsi) ->
       let tA' = cnormTyp (tA, ms) in
       LF.ClTyp (LF.PTyp tA', Whnf.normDCtx (Whnf.cnormDCtx (cPsi, ms)))
    | LF.CTyp sW -> LF.CTyp sW
    | _ -> dprintf
             begin fun p ->
             p.fmt "[cnormMTyp]"
             end;
           raise NotImplementedYet

  (* Applies msub to all heads excluding uninstantiated mvars/mmvars *)
  let rec cnormMetaSpine (mS, ms) =
    match mS with
    | Comp.MetaNil -> Comp.MetaNil
    | Comp.MetaApp (mO, mT, mS, plicity) ->
       Comp.MetaApp
         ( cnormMetaObj (mO, ms)
         , cnormMTyp (mT, ms)
         , cnormMetaSpine (mS, ms)
         , plicity
         )

  (* Applies the msub to the ctyp (excluding the mmvars and mvars) *)
  let rec cnormCTyp (tau, ms) =
    match (tau, ms) with
    | (Comp.TypBase (loc, a, mS), t) ->
        let mS' = cnormMetaSpine (mS, t) in
        Comp.TypBase (loc, a, mS')
    | (Comp.TypBox (loc, cT), t) ->
        Comp.TypBox (loc, cnormMTyp (cT, t))
    | (Comp.TypArr (loc, tT1, tT2), t) ->
        Comp.TypArr (loc, cnormCTyp (tT1, t), cnormCTyp (tT2, t))
    | (Comp.TypPiBox (loc, cdecl, tau), t) ->
        let cdecl' = Whnf.cnormCDecl (cdecl, t) in
        Comp.TypPiBox (loc, cdecl', cnormCTyp (tau, Whnf.mvar_dot1 t))
    | _ -> dprintf
             begin fun p ->
             p.fmt "[cnormCTyp]"
             end;
           raise NotImplementedYet

  (* Applies the msub to the comp goal. excludes applying sub to mvars *)
  (* Invariant:
     if cD ; cG  |- cg
     cD'  |- ms <= cD
     then
     [|ms|] cg = cg'
     cD' ; cG |- cg'                     *)

  let rec normCompGoal (cg, ms) =
    let rec normCompRes ms r =
      match r with
      | Base tau -> Base (Whnf.cnormCTyp (tau, ms))
      | CAnd (cg', r') ->
         let cg'' = normCompGoal (cg', ms) in
         let r'' = normCompRes ms r' in
         CAnd (cg'', r'')
      | CExists (td, r') ->
         let td' = Whnf.cnormCDecl (td, ms) in
         let r'' = normCompRes ms r' in
         CExists (td', r'')
    in
    let rec normAtomicSpine ms aS =
      match aS with
      | End -> aS
      | Spine (aS', (mt, mf, pl)) ->
         let aS'' = normAtomicSpine ms aS' in
         let (_, mf') = cnormMetaObj ((noLoc, mf), ms) in
         let mt' = cnormMTyp (mt, ms) in
         Spine (aS'', (mt', mf',pl))
    in
    match cg with
    | Box (cPsi, Atom tA, _lfTyp) ->
       let tA' = cnormTyp (tA, ms) in
       let cPsi' = Whnf.cnormDCtx (cPsi, ms) in
       Box (cPsi', Atom tA', _lfTyp)
    | Implies ((r, td), cg') ->
       let cg'' = normCompGoal (cg', ms) in
       let r' = normCompRes ms r in
       let td' = Whnf.cnormCCDecl (td, ms) in
       Implies ((r', td'), cg'')
    | Forall (td, cg') ->
       let td' = Whnf.cnormCDecl (td, ms) in
       let cg'' = normCompGoal (cg', ms) in
       Forall (td', cg'')
    | Atomic (cid, aS) ->
       let aS' = normAtomicSpine ms aS in
       Atomic (cid, aS')
    | _ -> raise NotImplementedYet

  (* Applies the msub to the sub goals (as above). *)
  let rec normSubGoals (sg, ms) =
    match sg with
    | Proved -> sg
    | Solve (sg', cg) ->
       let cg' = normCompGoal (cg, ms) in
       Solve (normSubGoals (sg', ms), cg')

  (* Applies the msub to the ihctx (excluding the mmvars and mvars) *)
  let cnormIHCtx' (ihctx, ms) =
    let cnormIHArg (a, t) =
      match a with
      | Comp.M (cM, cT) ->
         Comp.M (cnormMetaObj (cM, t), cnormMTyp (cT, t))
      | Comp.DC ->
         dprintf
          begin fun p ->
          p.fmt
          "[cnormIHArg]"
          end;
         raise NotImplementedYet
      | _ -> a
    in
    let cnormIHDecl (Comp.WfRec (name, ih_args, tau)) =
      let ih_args' = List.map (fun a -> cnormIHArg (a, ms)) ih_args in
      let tau' = cnormCTyp (tau, ms) in
      Comp.WfRec (name, ih_args', tau')
    in
    Context.map (fun d -> cnormIHDecl d) ihctx

  let rec cnormMCtx (cD, ms) =
    match cD with
    | LF.Empty -> cD
    | LF.Dec (cD', cdecl) ->
       LF.Dec (cnormMCtx (cD', ms), Whnf.cnormCDecl (cdecl, ms))

  (* Applies the msub to cPool (as above). *)
  let rec cnormCPool (cPool, ms) =
    match cPool with
    | Emp -> cPool
    | Full (cPool', ({cHead = hd; cMVars = mV; cSubGoals = sg}, _k, _s)) ->
       let cPool'' = cnormCPool (cPool', ms) in
       let hd' = Whnf.cnormCTyp (hd, ms) in
       let sg' = normSubGoals (sg, ms) in
       let mV' = cnormMCtx (mV, ms) in
       Full (cPool'', ({cHead = hd'; cMVars = mV'; cSubGoals = sg'}, _k, _s))

  (* Returns the name of the variable declaration at position k in cG *)
  let rec get_name k cG =
    match cG with
    | LF.Dec (cG', Comp.CTypDecl (name, _, _)) when k = 1 -> name
    | LF.Dec (cG', Comp.CTypDecl (name, _, _)) ->
       get_name (k-1) cG'

  let printCPool cD cG ppf cPool =
    let rec full_cD cD' cD_ret =
      match cD' with
      | LF.Empty -> cD_ret
      | LF.Dec (cD'', decl) -> full_cD cD'' (LF.Dec (cD_ret, decl))
    in
    let rec list_of_cPool =
      function
        | Emp -> []
        | Full (cPool', (cc, k, Boxed)) ->
           (get_name k cG, cc) :: list_of_cPool cPool'
        | Full (cPool', (cc, _, Unboxed)) ->
           list_of_cPool cPool'
    in
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut
         (fun ppf (x, sCCl) ->
           fprintf ppf " @[%a : %a %a@]@,%a@]"
             Name.pp x
             (P.fmt_ppr_mctx) (sCCl.cMVars)
             (P.fmt_ppr_csubgoals (full_cD (rev_mctx sCCl.cMVars) cD))
             (sCCl.cSubGoals)
             (P.fmt_ppr_cmp_typ (full_cD (rev_mctx sCCl.cMVars) cD))
             (sCCl.cHead)))
      (list_of_cPool (rev_cPool cPool))

  (* Prints the current state of proof loop
    (used for debugging) *)
  let printState cD cG cPool cIH cg ppf ms =
    let ms = Whnf.cnormMSub ms in
    let cg' = normCompGoal (cg, ms) in
    match cIH with
    | LF.Empty ->
       fprintf ppf
         "Current State: @;\
          @[<h 0> %a@] @; @[<h 0> ;  %a@] @; @[<h 0> |-  %a@] @\n\
          @[<h 2> ms = %a@]  @\n"
         (P.fmt_ppr_mctx) cD
         (printCPool cD cG) cPool
         (P.fmt_ppr_cmp_goal cD) (cg', S.id)
         (DP.fmt_ppr_lf_msub cD DP.l0) ms
    | _ ->
       fprintf ppf
         "Current State WITH IH: \n\
          @[<h 0> %a@] @; @[<h 0> ;  %a@] @; @[<h 0> |-  %a@] @\n\
          @[<h 2> cIH = %a@] @\n\
          @[<h 2> ms = %a@] @\n"
         (P.fmt_ppr_mctx) cD
         (printCPool cD cG) cPool
         (P.fmt_ppr_cmp_goal cD) (cg', S.id)
         (P.fmt_ppr_cmp_ihctx cD cG) cIH
         (DP.fmt_ppr_lf_msub cD DP.l0) ms

  (* reverses ms with head MShift k *)
  let rev_ms ms k =
    let rec rev ms ms_ret =
      match ms with
      | LF.MShift k' -> ms_ret
      | LF.MDot (mf, ms') -> rev ms' (LF.MDot (mf, ms_ret))
    in
    rev ms (LF.MShift k)

  let rev_cG cG =
    let rec rev cG cG_ret =
      match cG with
      | LF.Empty -> cG_ret
      | LF.Dec(cG', cdecl) -> rev cG' (LF.Dec(cG_ret, cdecl))
    in
    rev cG LF.Empty

  (* Clausify a computational contextual declaration *)
  let decToCC cdecl k =
    match cdecl with
    | Comp.CTypDecl (_, tau, _) ->
       let cc = {cHead = tau; cMVars = LF.Empty; cSubGoals = Proved} in
       (cc, k, Boxed)

  (* Removes those I.H. which refer to the computation context (i.e. have a
     Comp.V argument in their args. This is because those I.H. have been found
     to cause issues. In particular, it is possible to make calls to such
     schemas which aren't smaller. Since we currently have no way of checking
     the validity of the terms we build, it is best to omit those. *)
  let rec remove_IH cIH =
    let rec refers_to_cG args =
      match args with
      | Comp.V _ :: xs -> true
      | _ :: xs -> refers_to_cG xs
      | [] -> false
    in
    match cIH with
    | LF.Empty -> cIH
    | LF.Dec (cIH', ((Comp.WfRec (name, args, tau)) as dec)) ->
       if refers_to_cG args then remove_IH cIH'
       else LF.Dec (remove_IH cIH', dec)

  (* Generates, from cIH, a new cIH where each entry is unique. *)
  let unique_IH cIH cD =
    dprintf begin fun p -> p.fmt "[unique_IH]" end;
    let rec not_in ((Comp.WfRec (name, ih_arg_lst, tau)) as ih) cIH =
      let different_type tau2 =
        try
          Solver.trail
            (fun () ->
          U.unifyCompTyp cD (tau, LF.MShift 0) (tau2, LF.MShift 0));
          false
        with
        | _ -> true
      in
      let check (Comp.WfRec (name2, ih_arg_lst2, tau2)) =
        (different_type tau2)
      in
      match cIH with
      | LF.Empty -> true
      | LF.Dec (cIH', ihdecl) ->
         (check ihdecl) && (not_in ih cIH')
    in

    let rec unique cIH ret =
      match cIH with
      | LF.Empty -> ret
      | LF.Dec (cIH', ihdecl) ->
         if not_in ihdecl ret then unique cIH' (LF.Dec (ret, ihdecl))
         else unique cIH' ret
    in
    unique cIH LF.Empty

  (* extends the cPool with the assumptions from the pattern

     cD'; cG' (cPool) |- cg
     cD; [ref_ms]cG', cG_pat (= cG (cPool')) |- [ref_ms]cg
     returns cPool' which is the cPool corresponding to cG *)
  let updateCPool cPool cG pos ms cD =
    let rec lenCPool cPool =
      match cPool with
      | Emp -> 0
      | Full (cP', cc) -> 1 + (lenCPool cP')
    in
    let unbox (cc, k, status) = (cc, k, Unboxed) in
    let revP = rev_cPool cPool in
    let revG = rev_cG cG in
    let pos' = (lenCPool cPool) - pos + 1 in
    let rec update cP cG cP_ret k =
      match (cP, cG) with
      | (Emp, LF.Dec(cG', cdecl)) ->
         let cc = decToCC cdecl 1 in
         let cP_ret' = shift_cPool cP_ret 1 in
         update cP cG' (prependToCPool cc cP_ret') (k+1)
      | (Full(cP', cc), LF.Dec(cG', _)) ->
         let cc = (* If the assumption we're at was just split on, "unbox"
                     it so it's no longer considered in gamma              *)
           if pos' = k then unbox cc else cc in
         let (Full (Emp, cc')) = cnormCPool (Full (Emp, cc), ms) in
         update cP' cG' (prependToCPool cc' cP_ret) (k+1)
      | (Emp, LF.Empty) -> cP_ret
    in
    let revP' = update revP revG Emp 1 in
    rev_cPool revP'

  let remove_mvar_subs cIH =
    dprintf begin fun p -> p.fmt "[remove_mvar_subs]" end;
    let remove_hd hd =
      match hd with
      | LF.MMVar ((mmvar, _), _) ->
         LF.MMVar ((mmvar, LF.MShift 0), LF.Shift 0)
      | LF.MPVar ((mmvar, _), _) ->
         LF.MPVar ((mmvar, LF.MShift 0), LF.Shift 0)
      | _ -> hd
    in
    let rec remove_norm norm =
      match norm with
      | LF.Root (loc, hd, sp, p) ->
         LF.Root (loc, remove_hd hd, remove_sp sp, p)
      | LF.Lam (loc, name, norm) ->
         LF.Lam (loc, name, remove_norm norm)
      | LF.Clo (norm, s) ->
         LF.Clo (remove_norm norm, s)
      | _ -> norm
    and remove_sp sp =
      match sp with
      | LF.App (norm, sp') ->
         LF.App (remove_norm norm, remove_sp sp')
      | LF.SClo (sp', s) -> LF.SClo (remove_sp sp', s)
      | _ -> sp
    in
    let remove_ctx_var cv =
      match cv with
      | LF.CInst (mm_var, _) -> LF.CInst (mm_var, LF.MShift 0)
      | _ -> cv
    in
    let rec remove_dctx dctx =
      match dctx with
      | LF.CtxVar cv -> LF.CtxVar (remove_ctx_var cv)
      | LF.DDec (dctx', td) -> LF.DDec (remove_dctx dctx', td)
      | _ -> dctx
    in
    let remove_mf mf =
      match mf with
      | LF.ClObj (cPsi_hat, LF.MObj norm) ->
         LF.ClObj (cPsi_hat, LF.MObj (remove_norm norm))
      | LF.ClObj (cPsi_hat, LF.PObj hd) ->
         LF.ClObj (cPsi_hat, LF.PObj (remove_hd hd))
      | LF.CObj dctx -> LF.CObj (remove_dctx dctx)
      | _ -> mf
    in
    let rec remove_typ tA =
      match tA with
      | LF.Atom (l, cid, sp) ->
         LF.Atom (l, cid, remove_sp sp)
      | LF.PiTyp ((td, depend, plicity), tA') ->
         LF.PiTyp ((td, depend, plicity), remove_typ tA)
      | LF.TClo (tA', s) ->
         LF.TClo (remove_typ tA', s)
    in
    let remove_mT ctyp =
      match ctyp with
      | LF.ClTyp (LF.MTyp tA, cPsi) ->
         LF.ClTyp (LF.MTyp (remove_typ tA), cPsi)
      | LF.ClTyp (LF.PTyp tA, cPsi) ->
         LF.ClTyp (LF.PTyp (remove_typ tA), cPsi)
      | _ -> ctyp
    in
    let rec remove_mS mS =
      match mS with
      | Comp.MetaApp ((loc, mf), mT, mS', p) ->
         let mf' = remove_mf mf in (* mfront *)
         let mT' = remove_mT mT in (* ctyp *)
         Comp.MetaApp ((loc, mf'), mT', remove_mS mS', p)
      | _ -> mS
    in
    let rec remove_tau tau =
      match tau with
      | Comp.TypBase (l, cid, mS) ->
         Comp.TypBase (l, cid, remove_mS mS)
      | Comp.TypBox (l, mT) ->
         (match mT with
         | LF.ClTyp (LF.MTyp tA, cPsi) ->
            Comp.TypBox (l, LF.ClTyp (LF.MTyp (remove_typ tA), cPsi))
         | LF.ClTyp (LF.PTyp tA, cPsi) ->
            Comp.TypBox (l, LF.ClTyp (LF.PTyp (remove_typ tA), cPsi))
         | _ -> tau)
      | Comp.TypArr (l, tau1, tau2) ->
         Comp.TypArr (l, remove_tau tau1, remove_tau tau2)
      | Comp.TypPiBox (l, cdec, tau') ->
         Comp.TypPiBox (l, cdec, remove_tau tau')
    in
    let remove_arg arg =
      match arg with
      | Comp.M ((loc, mf), mt) -> Comp.M ((loc, remove_mf mf), remove_mT mt)
      | _ -> arg
    in
    Context.map (fun (Comp.WfRec (name, ih_arg_lst, tau)) ->
        (Comp.WfRec (name, List.map remove_arg ih_arg_lst,
                     remove_tau tau))) cIH

  (* Replaces the DC argument of each I.H. with the correct mmvar.  *)
  let fix_IH_args ihctx cD =
    dprintf
      begin fun p ->
        p.fmt "[fix_IH_args] Fixing %d hypotheses"
        (Context.length ihctx)
      end;

    (* Returns a list of the mvars and mmvars in tau
       (unique elements only)                        *)
    let get_list_of_mvars tau =

      let rec list_of_mvars_norm normal =
        match normal with
        | LF.Root (_, LF.MVar (LF.Inst mmvar,_), spine, _) ->
           if Option.is_none !(mmvar.LF.instantiation)
           then
             normal :: (list_of_mvars_spine spine)
           else
             list_of_mvars_spine spine
        | LF.Root(_, LF.MMVar ((mmvar,_),_), spine, _) ->
           if Option.is_none !(mmvar.LF.instantiation)
           then
             normal :: (list_of_mvars_spine spine)
           else
             list_of_mvars_spine spine
        | LF.Root(_, LF.MPVar ((mmvar,_),_), spine, _) ->
           if Option.is_none !(mmvar.LF.instantiation)
           then
             normal :: (list_of_mvars_spine spine)
           else
             list_of_mvars_spine spine
        | LF.Root(_,_, spine, _) ->
           list_of_mvars_spine spine
        | LF.Lam (_, _, normal') -> list_of_mvars_norm normal'
        | LF.Clo (normal', _) -> list_of_mvars_norm normal'
        | _ -> dprintf
             begin fun p ->
             p.fmt "[list_of_mvars_norm]"
             end;
               raise NotImplementedYet

      and list_of_mvars_spine spine =
        match spine with
        | LF.Nil -> []
        | LF.App (normal, spine') ->
          (list_of_mvars_norm normal) @ (list_of_mvars_spine spine')
        | LF.SClo (spine', _) -> list_of_mvars_spine spine'
      in

      let rec list_of_mvars_mspine mS =
        match mS with
        | Comp.MetaNil -> []
        | Comp.MetaApp (mO, mT, mS', _) ->
           match mO with
           | (_, LF.ClObj (_, LF.MObj norm)) ->
              (list_of_mvars_norm norm) @ (list_of_mvars_mspine mS')
           | (_, LF.ClObj (_, LF.PObj hd)) -> (* TODO:: correct?? *)
              (list_of_mvars_norm (LF.head hd)) @ (list_of_mvars_mspine mS')
           | _ -> []
      in

      let rec list_of_mmvars tau =
        match tau with
        | Comp.TypBox (_, LF.ClTyp(LF.MTyp (LF.Atom (_, _, spine)), _)) ->
           list_of_mvars_spine spine
        | Comp.TypBox (_, LF.ClTyp(LF.PTyp (LF.Atom (_, _, spine)), _)) ->
           list_of_mvars_spine spine
        | Comp.TypArr (_, tau1, tau2) ->
           (list_of_mmvars tau1) @ (list_of_mmvars tau2)
        | Comp.TypPiBox (_, _, tau) ->
           list_of_mmvars tau
        | Comp.TypBase (_, _, mS) ->
           list_of_mvars_mspine mS
        | _ -> dprintf
             begin fun p ->
             p.fmt "[list_of_mmvars]"
             end;
               raise NotImplementedYet
      in

      let is_in mm_var lst =
        let cid =
          match mm_var with
          | LF.Root(_, LF.MMVar(((mmvar, _),_)), _, _) -> mmvar.LF.mmvar_id
          | LF.Root(_, LF.MPVar(((mmvar, _),_)), _, _) -> mmvar.LF.mmvar_id
          | LF.Root(_, LF.MVar(LF.Inst mmvar,_), _, _) -> mmvar.LF.mmvar_id
          | _ -> dprintf
             begin fun p ->
             p.fmt "[is_in - cid]"
             end;
                 raise NotImplementedYet
        in
        let rec is_in_lst cid lst =
          match lst with
          | (LF.Root(_, LF.MMVar(((mmvar, _),_)), _, _)) :: xs
               when mmvar.LF.mmvar_id = cid -> true
          | (LF.Root(_, LF.MPVar(((mmvar, _),_)), _, _)) :: xs
               when mmvar.LF.mmvar_id = cid -> true
          | (LF.Root(_, LF.MVar(LF.Inst mmvar,_), _, _)) :: xs
               when mmvar.LF.mmvar_id = cid -> true
          | x :: xs -> is_in_lst cid xs
          | [] -> false
        in
        is_in_lst cid lst

      in
      let rec get_unique_mvars lst unq_lst =
        match lst with
        | x :: xs ->
           if is_in x unq_lst
           then
             get_unique_mvars xs unq_lst
           else
             get_unique_mvars xs (x::unq_lst)
        | [] -> List.rev unq_lst
      in
      let mmvars = list_of_mmvars tau in
      get_unique_mvars mmvars []

    in

    let fix_ihctx (Comp.WfRec (name, ih_args, tau)) =
      let unq_mmvars = get_list_of_mvars tau in
      let rec fix_args ih_args mvars =
        match (ih_args, mvars) with
        | (Comp.DC :: xs, x :: mvars') ->
           (match x with
           | LF.Root (_, ((LF.MPVar ((mmvar,_), _)) as hd), _, _) ->
              let dctx_hat = match mmvar.LF.typ with
                | LF.ClTyp (_, dctx) -> Context.dctxToHat dctx
                | _ -> raise NotImplementedYet
              in
              (Comp.M ((noLoc, LF.ClObj (dctx_hat, LF.PObj hd)),
                       mmvar.LF.typ))
              :: (fix_args xs mvars')
           | LF.Root (_, LF.MMVar ((mmvar,_), _), _, _) ->
              let dctx_hat = match mmvar.LF.typ with
                | LF.ClTyp (_, dctx) -> Context.dctxToHat dctx
                | _ -> raise NotImplementedYet
              in
              (Comp.M ((noLoc, LF.ClObj (dctx_hat, LF.MObj x)), mmvar.LF.typ))
              :: (fix_args xs mvars')
           | LF.Root (_, LF.MVar (LF.Inst mmvar, _), _, _) ->
              let dctx_hat = match mmvar.LF.typ with
                | LF.ClTyp (_, dctx) -> Context.dctxToHat dctx
                | _ -> raise NotImplementedYet
              in
              (Comp.M ((noLoc, LF.ClObj (dctx_hat, LF.MObj x)), mmvar.LF.typ))
              :: (fix_args xs mvars')
           | _ -> dprintf begin fun p -> p.fmt "[fix_ihctx]" end;
                  raise NotImplementedYet)
        | (x :: xs, _) ->
           x :: (fix_args xs mvars)
        | ([], _) -> []
      in
      let args' = fix_args ih_args unq_mmvars in
      Comp.WfRec (name, args', tau)

    in
    Context.map (fun d -> fix_ihctx d) ihctx

  (* Creates an identical I.H. with the original uninstantiated mvars
     replaced with new uninstantiated mvars.
     This is so we can reuse the I.H.
     (i.e. the original mvars in the original I.H. do not get instantiated) *)
  let generate_new_IH (Comp.WfRec (name, ih_arg_lst, tau)) =
    (* Returns list of mvars in ih_arg_lst *)
    let rec get_mvars ih_arg_lst =
      match ih_arg_lst with
      | Comp.M ((
          _, LF.ClObj
               (dctx_hat, LF.MObj
                            (((LF.Root
                               (_, LF.MVar
                                     (LF.Inst mmvar,_), _, _)))
                             as norm))), _) :: lst'
           when Option.is_none !(mmvar.LF.instantiation) ->
         let xs = get_mvars lst' in
         norm :: xs
      | Comp.M ((
          _, LF.ClObj
               (dctx_hat, LF.MObj
                            (((LF.Root
                                 (_, LF.MMVar ((mmvar,_),_), _, _))
                              as norm)))), _) :: lst'
           when Option.is_none !(mmvar.LF.instantiation) ->
         let xs = get_mvars lst' in
         norm :: xs
      | Comp.M ((
          _, LF.ClObj
               (dctx_hat, LF.PObj
                            (((LF.MPVar ((mmvar,_),_))
                              as hd)))), _) :: lst'
           when Option.is_none !(mmvar.LF.instantiation) ->
         let xs = get_mvars lst' in
         (LF.head hd) :: xs
      | _ :: lst' -> get_mvars lst'
      | [] -> []
    in
    (* Generate the new ih_arg_lst with new mvars along with the
       substitution                                              *)
    let rec gen_new_ih_args ih_args mvar_lst =
      match (ih_args, mvar_lst) with
      | (Comp.M ((
          _, LF.ClObj
               (dctx_hat, LF.MObj
                            (LF.Root
                               (_, LF.MVar
                                     (LF.Inst mmvar,_), _, plicity)))), mT)
         :: lst'
        , y :: ys) when Option.is_none !(mmvar.LF.instantiation) ->
         let LF.ClTyp (LF.MTyp tA, cPsi) = mmvar.LF.typ in
         let mmvar' =
           Whnf.newMMVar None (mmvar.LF.cD, cPsi, tA) mmvar.LF.plicity
             mmvar.LF.inductivity in
         let norm = LF.Root (noLoc,
                             LF.MMVar ((mmvar', LF.MShift 0), LF.Shift 0),
                             LF.Nil, plicity) in
         let mf = LF.ClObj (dctx_hat, LF.MObj norm) in
         let x = Comp.M ((noLoc, mf), mT) in
         let (xs, sub) = gen_new_ih_args lst' ys in
         (x :: xs, (mmvar.LF.mmvar_id, norm) :: sub)

      | (Comp.M ((
          _, LF.ClObj
               (dctx_hat, LF.MObj
                            (LF.Root
                               (_, LF.MMVar
                                     ((mmvar, _),_), _, plicity)))), mT)
         :: lst'
        , y :: ys)
           when Option.is_none !(mmvar.LF.instantiation) ->
         let LF.ClTyp (LF.MTyp tA, cPsi) = mmvar.LF.typ in
         let mmvar' =
           Whnf.newMMVar None (mmvar.LF.cD, cPsi, tA) mmvar.LF.plicity
             mmvar.LF.inductivity in
         let norm = LF.Root (noLoc, LF.MMVar
                                      ((mmvar', LF.MShift 0), LF.Shift 0),
                             LF.Nil, plicity) in
         let mf = LF.ClObj (dctx_hat, LF.MObj norm) in
         let x = Comp.M ((noLoc, mf), mT) in
         let (xs, sub) = gen_new_ih_args lst' ys in
         (x :: xs, (mmvar.LF.mmvar_id, norm) :: sub)

      | (Comp.M ((
          _, LF.ClObj
               (dctx_hat, LF.PObj
                            (LF.MPVar
                                     ((mmvar, _),_)))), mT) :: lst'
        , y :: ys)
           when Option.is_none !(mmvar.LF.instantiation) ->
         let LF.ClTyp (LF.PTyp tA, cPsi) = mmvar.LF.typ in
         let mmvar' =
           Whnf.newMPVar None (mmvar.LF.cD, cPsi, tA) mmvar.LF.plicity
             mmvar.LF.inductivity in
         let hd = LF.MPVar ((mmvar', LF.MShift 0), LF.Shift 0) in
         let mf = LF.ClObj (dctx_hat, LF.PObj hd) in
         let x = Comp.M ((noLoc, mf), mT) in
         let (xs, sub) = gen_new_ih_args lst' ys in
         (x :: xs, (mmvar.LF.mmvar_id, LF.head hd) :: sub)

      | (x :: lst', ys) ->
         let (xs, sub) = gen_new_ih_args lst' ys in
         (x :: xs, sub)
      | (lst', []) ->
         (lst', [])
      | _ ->
         dprintf
             begin fun p ->
             p.fmt "[gen_new_ih_args]"
             end;
         raise NotImplementedYet
    in
    let rec generate_new_typ tau sub =
      let rec find_sub id sub =
        match sub with
        | (id', norm) :: _ when id' = id -> norm
        | _ :: xs -> find_sub id xs
        | _ ->
           dprintf
             begin fun p ->
             p.fmt "[find_sub]"
             end;
           raise NotImplementedYet
      in
      let rec sub_norm norm sub =
        match norm with
        | LF.Root (_, LF.MVar (LF.Inst mmvar,_), spine, _)
             when Option.is_none !(mmvar.LF.instantiation) ->
           find_sub mmvar.LF.mmvar_id sub
        | LF.Root(_, LF.MMVar ((mmvar,_),_), spine, _)
             when Option.is_none !(mmvar.LF.instantiation) ->
           find_sub mmvar.LF.mmvar_id sub
        | LF.Root(_, LF.MPVar ((mmvar,_),_), spine, _)
             when Option.is_none !(mmvar.LF.instantiation) ->
           find_sub mmvar.LF.mmvar_id sub
        | LF.Root (loc, hd, spine, plicity) ->
           LF.Root (loc, hd, sub_spine spine sub, plicity)
        | LF.Lam (loc, name, norm') ->
           LF.Lam(loc, name, sub_norm norm' sub)
        | _ ->
           dprintf
             begin fun p ->
             p.fmt "[sub_norm]"
             end;
           raise NotImplementedYet

      and sub_spine spine sub =
        match spine with
        | LF.Nil -> LF.Nil
        | LF.SClo (spine', s) -> LF.SClo (sub_spine spine' sub, s)
        | LF.App (norm, spine') ->
           let norm' = sub_norm norm sub in
           LF.App (norm', sub_spine spine' sub)
      in

      let sub_metaObj mO sub =
        match mO with
        | (loc, LF.ClObj (dh, LF.MObj norm)) ->
           let norm' = sub_norm norm sub in
           (loc, LF.ClObj (dh, LF.MObj norm'))
        | (loc, LF.ClObj (dh, LF.PObj hd)) ->
           let (LF.Root(_, hd',_,_)) = sub_norm (LF.head hd) sub in
           (loc, LF.ClObj (dh, LF.PObj hd'))
        | (_, LF.MV k) -> mO
        | (_, LF.CObj _) -> mO
        | _ -> dprintf
             begin fun p ->
             p.fmt "[sub_metaObj]"
             end;
               raise NotImplementedYet
      in

      let sub_typ mT sub =
        match mT with
        | LF.ClTyp (LF.MTyp (LF.Atom (loc, cid, spine)), cPsi) ->
           let spine' = sub_spine spine sub in
           LF.ClTyp (LF.MTyp (LF.Atom (loc, cid, spine')), cPsi)
        | LF.ClTyp (LF.PTyp (LF.Atom (loc, cid, spine)), cPsi) ->
           let spine' = sub_spine spine sub in
           LF.ClTyp (LF.PTyp (LF.Atom (loc, cid, spine')), cPsi)
        | LF.CTyp _ -> mT
        | _ -> dprintf
             begin fun p ->
             p.fmt "[sub_typ]"
             end;
               raise NotImplementedYet
      in

      let rec sub_mspine mS sub =
        match mS with
        | Comp.MetaApp (mO, mT, mS', plicity) ->
           let mO' = sub_metaObj mO sub in
           let mT' = sub_typ mT sub in
           let mS'' = sub_mspine mS' sub in
           Comp.MetaApp (mO', mT', mS'', plicity)
        | _ -> mS
      in

      match tau with
      | Comp.TypBox (loc, LF.ClTyp (LF.MTyp (LF.Atom (loc2, cid, spine)),
                                    cPsi)) ->
         let spine' = sub_spine spine sub in
         Comp.TypBox (loc, LF.ClTyp (LF.MTyp (LF.Atom (loc2, cid, spine')),
                                     cPsi))
      | Comp.TypBox (loc, LF.ClTyp (LF.PTyp (LF.Atom (loc2, cid, spine)),
                                    cPsi)) ->
         let spine' = sub_spine spine sub in
         Comp.TypBox (loc, LF.ClTyp (LF.PTyp (LF.Atom (loc2, cid, spine')),
                                     cPsi))
      | Comp.TypBase (loc, cid, mS) ->
         let mS' = sub_mspine mS sub in
         Comp.TypBase (loc, cid, mS')
      | Comp.TypArr (loc, tau1, tau2) ->
         let tau1' = generate_new_typ tau1 sub in
         let tau2' = generate_new_typ tau2 sub in
         Comp.TypArr (loc, tau1', tau2')
      | Comp.TypPiBox (loc, cdecl, tau) ->
         let tau' = generate_new_typ tau sub in
         Comp.TypPiBox (loc, cdecl, tau')
      | _ -> dprintf
             begin fun p ->
             p.fmt "[generate_new_typ]"
             end;
             raise NotImplementedYet
    in
    let mvar_list = get_mvars ih_arg_lst in
    let (args, sub) = gen_new_ih_args ih_arg_lst mvar_list in
    let tau' = generate_new_typ tau sub in
    (args, tau')

  (* Machinery for annotated contexts. *)
  (* cD_a : (LF.ctyp_decl, Comp.exp_syn Option, int, int, int option, bool)
            (mvar decl, Beluga term, no. of constructors of mvar, position in cD, position in theorem (if applicable), split status)
     Similarly for cG_a.
   *)

  (* When a var is added to cG, positions in cG_a get shifted by 1. *)
  let rec shift_cG_a cG_a =
    let shift_I i =
      match i with
      | Comp.Var(l, k) -> Comp.Var(l, k+1)
    in
    match cG_a with
    | [] -> []
    | (tdecl, Some i, con, pos, thm_var, bool) :: cG_a' ->
       (tdecl, Some (shift_I i), con, pos+1, thm_var, bool)
       :: (shift_cG_a cG_a')
    | x :: cG_a' ->
       x :: (shift_cG_a cG_a')

  (* When a var is added to cD, positions in cD_a get shifted by 1. *)
  let rec shift_cD_a cD_a =
    let shift_I i =
      match i with
      | Comp.AnnBox(loc,
                     (loc2, LF.ClObj(cPsi_hat,
                              LF.MObj(LF.Root (loc3,
                                               LF.MVar(LF.Offset x, s),
                                               spine, dep)))),
                    ctyp) ->
         Comp.AnnBox(loc,
                      (loc2, LF.ClObj(Whnf.cnorm_psihat cPsi_hat (LF.MShift 1),
                               LF.MObj (LF.Root (loc3,
                                                 LF.MVar(LF.Offset (x + 1),
                                                         s),
                                                 spine, dep)))),
                     Whnf.cnormMTyp (ctyp, (LF.MShift 1)))
      | Comp.AnnBox(loc, (loc2, LF.ClObj(cPsi_hat,
                                   LF.PObj(LF.PVar(x, s)))), ctyp) ->
         Comp.AnnBox(loc,
                      (loc2, LF.ClObj(Whnf.cnorm_psihat cPsi_hat (LF.MShift 1),
                               LF.PObj (LF.PVar(x + 1, s)))),
                     Whnf.cnormMTyp (ctyp, (LF.MShift 1)))
      | Comp.AnnBox(loc, (loc2, clobj), ctyp) ->
         Comp.AnnBox(loc, (loc2, Whnf.cnormMFt clobj (LF.MShift 1)),
                     Whnf.cnormMTyp (ctyp, (LF.MShift 1)))
      | _ ->
         dprintf
      begin fun p ->
      p.fmt
        "[shift_I] NOT IMPLEMENTED YET"
      end;
         raise NotImplementedYet
    in
    match cD_a with
      | [] -> []
      | (tdecl, Some i, no, pos, thm_var, bool) :: cD_a' ->
         let tdecl' = Whnf.cnormCDecl (tdecl, LF.MShift 1) in
         (tdecl', Some (shift_I i), no, pos + 1, thm_var, bool)
         :: (shift_cD_a cD_a')
      | x :: cD_a' ->
         x :: (shift_cD_a cD_a')

  (* Returns the number of type constructors for a type *)
  let consOfLFTyp cltyp =
    let typ =
      match cltyp with
      | LF.MTyp tA | LF.PTyp tA -> tA
    in
    let cid = Solver.cidFromAtom typ in
    let typEntry = Store.Cid.Typ.get cid in
    let typConstructors = !(typEntry.Store.Cid.Typ.Entry.constructors) in
    List.length typConstructors

  (* Returns the number of type constructors for a type *)
  let consOfTyp cid =
    let typEntry = Store.Cid.CompTyp.get cid in
    let typConstructors =
      !(typEntry.Store.Cid.CompTyp.Entry.constructors) in
    List.length typConstructors

  (* Updates the cG_a for the branch case. *)
  let update_branch_cG_a (cG, cPool, cG_a) =

    let var = Comp.Var (noLoc, 1) in

    let rec old_split name cG_a =
      match cG_a with
      | [] -> false
      | (Comp.CTypDecl (name2, _ ,_), _, _, _, _, _) :: cG_a' ->
         (Name.equal name name2) || (old_split name cG_a')
    in

    let rec find_split name cG_a =
      match cG_a with
      | (Comp.CTypDecl (name2, _ ,_), _, con, _, thm, bool) :: cG_a'
           when Name.equal name name2 ->
         (con, thm, bool)
      | x :: xs -> find_split name xs
    in

    let rec update (cG, cPool, ret) =
      match (cG, cPool) with
      | (LF.Dec(cG',
                ((Comp.CTypDecl (name, Comp.TypBox
                                         (_, LF.ClTyp (cltyp, cPsi)), _wf))
                 as cdecl)),
         Full (cPool', ({cHead = hd; cMVars; cSubGoals = sg}, k', Boxed))) ->

         let (con, thm, bool) =
           if old_split name cG_a
           then find_split name cG_a
           else
             try
               (consOfLFTyp cltyp, None, true)
             with
             | _ -> (0, None, false)
         in
         let ret' = shift_cG_a ret in
         let x = (cdecl, Some var, con, 1, None, bool) in
         update (cG', cPool', x :: ret')

      | (LF.Dec(cG',
                ((Comp.CTypDecl (name, Comp.TypInd(Comp.TypBox
                                         (_, LF.ClTyp (cltyp, cPsi))), _wf))
                 as cdecl)),
         Full (cPool', ({cHead = hd; cMVars; cSubGoals = sg}, k', Boxed))) ->

         let (con, thm, bool) = (0, None, false)
         in
         let ret' = shift_cG_a ret in
         let x = (cdecl, Some var, con, 1, None, bool) in
         update (cG', cPool', x :: ret')

      | (LF.Dec(cG', (Comp.CTypDecl (name, Comp.TypBase (_, cid,_mS), _wf)
                      as cdecl)),
         Full (cPool', _))->

         let (con, thm, bool) =
           if old_split name cG_a
           then find_split name cG_a
           else
             try
               (consOfTyp cid, None, true)
             with
             | _ -> (0, None, false)
         in
         let ret' = shift_cG_a ret in
         let x = (cdecl, Some var, con, 1, None, bool) in
         update (cG', cPool', x :: ret')

      | (LF.Dec (cG', _), Full (cPool', _)) ->
         update (cG', cPool', ret)

      | (LF.Empty, Emp) -> ret

    in
     (update (rev_cG cG, rev_cPool cPool, []))

  (* Updates the cD_a for the branch case. *)
  let update_branch_cD_a (cD, cD_a) =
    dprintf
      begin fun p ->
      p.fmt "[update_branch_cD_a]"
      end;
    let rec is_in n l =
      match l with
      | [] -> false
      | (LF.Decl (name, _, _, _), Some i, no, pos, thm_var, bool) :: cD_a'
           when Name.equal name n -> true
      | _ :: cD_a' -> is_in n cD_a'
    in
    let rec retrieve n cD_a =
      match cD_a with
      | (LF.Decl (name, ctyp, plic, ind), Some i, no, pos, thm_var, bool) :: cD_a'
           when Name.equal name n ->
         (LF.Decl (name, ctyp, plic, ind), Some i, no, pos, thm_var, bool)
      | _ :: cD_a' -> retrieve n cD_a'
    in
    let rec update cD ret =
      match cD with
      | LF.Dec (cD', ((LF.Decl (name, ((LF.ClTyp (cltyp, cPsi)) as ctyp),
                                Plicity.Explicit, ind)) as tdecl))
           when is_in name cD_a ->
         let (LF.Decl (_, tau2, _, induc), _, con, pos, thm, bool) =
           retrieve name cD_a in
         let (con', bool') =
           if bool then
              try
                (consOfLFTyp cltyp, true)
              with
              | _ -> (0, false)
           else (con, false) in
         let clobj = match cltyp with
           | LF.MTyp tA ->
              LF.MObj (LF.Root (noLoc, LF.MVar (LF.Offset 1, S.id),
                                LF.Nil, Plicity.explicit))
           | LF.PTyp tA ->
              LF.PObj (LF.PVar (1, S.id))
         in
         let mf = LF.ClObj (Whnf.cnorm_psihat (Context.dctxToHat cPsi)
                            (LF.MShift 1), clobj) in
         let ctyp' = Whnf.cnormMTyp (ctyp, LF.MShift 1) in
         let mobj = (noLoc, mf) in
         let i = Comp.AnnBox(noLoc, mobj, ctyp') in
         let tdecl' = Whnf.cnormCDecl (tdecl, LF.MShift 1) in
         let x = (tdecl', Some i, con', 1, thm, bool') in
         let ret' = shift_cD_a ret in
         update cD' (x :: ret')
      | LF.Dec (cD', ((LF.Decl (name, ((LF.ClTyp (cltyp, cPsi)) as ctyp),
                                Plicity.Explicit, induc)) as tdecl)) ->
         let (con', bool') =
            try
              (consOfLFTyp cltyp, true)
            with
            | _ -> (0, false) in
         let clobj = match cltyp with
           | LF.MTyp tA ->
              LF.MObj (LF.Root (noLoc, LF.MVar (LF.Offset 1, S.id),
                                LF.Nil, Plicity.explicit))
           | LF.PTyp tA ->
              LF.PObj (LF.PVar (1, S.id))
         in
         let mf = LF.ClObj (Whnf.cnorm_psihat (Context.dctxToHat cPsi)
                             (LF.MShift 1), clobj) in
         let ctyp' = Whnf.cnormMTyp (ctyp, LF.MShift 1) in
         let mobj = (noLoc, mf) in
         let i = Comp.AnnBox(noLoc, mobj, ctyp') in
         let tdecl' = Whnf.cnormCDecl (tdecl, LF.MShift 1) in
         let x = (tdecl', Some i, con', 1, None, bool') in
         let ret' = shift_cD_a ret in
         update cD' (x :: ret')
      | LF.Dec (cD', ((LF.Decl (name, LF.ClTyp (cltyp, cPsi),
                                Plicity.Implicit, induc)) as tdecl)) ->
         (* Do not split on implict vars *)
         let (con, bool) = (0, false) in
         let tdecl' = Whnf.cnormCDecl (tdecl, LF.MShift 1) in
         let x = (tdecl', None, con, 1, None, bool) in
         let ret' = shift_cD_a ret in
         update cD' (x :: ret')
      | LF.Dec(cD', ((LF.Decl (name, (LF.CTyp cid_schema), _, _)) as tdecl)) ->
         (* Do not currently split on context schemas *)
         let (con, bool) = (0, false) in
         let tdecl' = Whnf.cnormCDecl (tdecl, LF.MShift 1) in
         let x = (tdecl', None, con, 1, None, bool) in
         let ret' = shift_cD_a ret in
         update cD' (x :: ret')
      | LF.Empty -> ret
    in
    update (rev_mctx cD) []

  (* Returns true if there are vars or mvars left to split on, else false *)
  let vars_left (cD_a, cG_a) =
    let rec var cG_a =
      match cG_a with
      | [] -> false
      | (_,_,_,_,_,true)::xs -> true
      | x :: xs -> var xs
    in
    let rec mvar cD_a =
      match cD_a with
      | [] -> false
      | (_,_,_,_,_,true)::xs -> true
      | x :: xs -> mvar xs
    in
    (var cG_a || mvar cD_a)

  (* If ind is given, return the variable corresponding to its location in
     either cD or cG, otherwise, return the variable with the lowest rating
     where rating =
        #constructors * position_in_the_theorem *
           (1 if var is inductive, otherwise 2)                           *)
  let choose_split (cD_a, cG_a) (cD, cG) ind =

    let (l1, l2) = (List.length cD_a, List.length cG_a) in

    (* Get the ratings of each mvar *)
    let rec cD_rating cD_a =
      match cD_a with
      | [] -> []
      | (LF.Decl (name, mtyp, _, _), Some i, n, pos, _, true)
        :: cD_a' ->
         (match n with
            | 0 -> (cD_rating cD_a')
            | 1 -> (name, 1) :: (cD_rating cD_a')
            | _ ->
               let t = if Total.is_inductive_split cD cG i then 1 else 2 in
               (name, n * (l1 - pos + 1) * t) :: (cD_rating cD_a'))
      | x :: cD_a' -> cD_rating cD_a'
    in

    (* Get the ratings of each var *)
    let rec cG_rating cG_a =
      match cG_a with
      | (Comp.CTypDecl (_, Comp.TypInd(_), _), _, _, _, _, _) :: cG_a' ->
         cG_rating cG_a'
      | (Comp.CTypDecl (name, tau, _wf), Some i, n, pos, _, true) :: cG_a' ->
         (match n with
          | 0 -> (cG_rating cG_a')
          | 1 -> (name, 1) :: (cG_rating cG_a')
          | _ ->
             let t = if Total.is_inductive_split cD cG i then 1 else 2 in
             (name, n * (l2 - pos + 1) * t) :: (cG_rating cG_a'))
      | [] -> []
      | x :: cG_a' -> cG_rating cG_a'
    in

    (* Get the mvar with the lowest rating *)
    let rec get_cD_min cD_tot =
      match cD_tot with
      | [] -> (None, 1000000)
      | (name, tot) :: cD_tot' ->
         let (name', tot') = get_cD_min cD_tot' in
         if tot' < tot then
           (name', tot')
         else
           (Some name, tot)
    in

    (* Get the var with the lowest rating *)
    let rec get_cG_min cG_tot =
      match cG_tot with
      | [] -> (None, 100000)
      | (name, tot) :: cG_tot' ->
         let (name', tot') = get_cG_min cG_tot' in
         if tot' < tot then
           (name', tot')
         else
           (Some name, tot)
    in

    (* Remove var from the split list cG_a (i.e. set bool to false) *)
    let rec remove_var name cG_a =
      match cG_a with
      | (Comp.CTypDecl (n, tau, _wf), Some i, no, k, thm_var, true) :: cG_a'
           when Name.equal name n ->
         (tau, i, thm_var,
          (Comp.CTypDecl (n, tau, _wf), Some i, no, k, thm_var, false)
          :: cG_a', k)
      | x :: cG_a' ->
         let (tau, i, thm_var, cG_a'', pos) = remove_var name cG_a' in
         (tau, i, thm_var, x :: cG_a'', pos)
    in

    (* Remove mvar from the msplit list cD_a (i.e. set bool to false) *)
    let rec remove_mvar name cD_a =
      match cD_a with
      | (LF.Decl (n, mtyp, pl, induc), Some i, no, k, thm_var, true)
        :: cD_a' when Name.equal name n ->
         let tau = Comp.TypBox(noLoc, mtyp) in
         (tau, i, thm_var, (LF.Decl (n, mtyp, pl, induc), Some i, no, k, thm_var, false)
                     :: cD_a')
      | x :: cD_a' ->
         let (tau, i, thm_var, cD_a'') = remove_mvar name cD_a' in
         (tau, i, thm_var, x :: cD_a'')
    in

    (* If the split (m)var given is a var, returns the name of the var. *)
    let rec find_var k cG_a =
      match cG_a with
      | (Comp.CTypDecl (name, _, _), _, _, _, Some k', true) :: cG_a' ->
         dprintf
      begin fun p ->
      p.fmt
        "[choose_split] Searching for var at Index = %d, on index %d"
        k
      k'
      end;
         if k = k' then Some name else  find_var k cG_a'
      | x :: cG_a' ->
         find_var k cG_a'
      | [] -> None
    in

    (* If the split (m)var given is an mvar, returns the name of the mvar. *)
    let rec find_mvar k cD_a =
      match cD_a with
      | (LF.Decl (name, _, _, _), _, _, _, Some k', true) :: cD_a'
           when k = k' ->
         Some name
      | c :: cD_a' -> find_mvar k cD_a'
      | [] -> None
    in
    let (cD_tot, cG_tot) = (cD_rating cD_a, cG_rating cG_a) in
    match ind with
    | None | Some 0 -> (* No split (m)var given explicitly *)
       (match (get_cD_min cD_tot, get_cG_min cG_tot) with
        | ((Some name, k), (Some name2, k2)) ->
          if k2 < k then
            (* In this case we split on a var from cG *)
            let (tau, i, thm_var, cG_a', pos) = remove_var name2 cG_a in
            (tau, i, thm_var, cD_a, cG_a', pos)
          else
            (* In this case we split on an mvar from cD *)
            let (tau, i, thm_var, cD_a') = remove_mvar name cD_a in
            (tau, i, thm_var, cD_a', cG_a, 0)
       | ((None, _), (Some name, _)) ->
          (* In this case we split on a var from cG *)
          let (tau, i, thm_var, cG_a', pos) = remove_var name cG_a in
          (tau, i, thm_var, cD_a, cG_a', pos)
       | ((Some name, k), (None, _)) ->
          (* In this case we split on an mvar from cD *)
          let (tau, i, thm_var, cD_a') = remove_mvar name cD_a in
          (tau, i, thm_var, cD_a', cG_a, 0)
       | ((None, _), (None, _)) -> raise End_Of_Search)

    | Some k -> (* Split (m)var given explicitly *)
       dprintf
      begin fun p ->
      p.fmt
        "[choose_split] Split (m)var given explicitly. Index = %d"
         k
      end;
       match find_var k cG_a with
       | Option.None ->
         (dprintf
           begin fun p ->
           p.fmt
             "[choose_split] mvar to split."
           end;
         let (Some n) = find_mvar k cD_a in
         let (tau, i, thm_var, cD_a') = remove_mvar n cD_a in
         (tau, i, thm_var, cD_a', cG_a, 0))
       | Option.Some name ->
         (dprintf
           begin fun p ->
           p.fmt
             "[choose_split] var to split."
           end;
         let (tau, i, thm_var, cG_a', pos) = remove_var name cG_a in
         (tau, i, thm_var, cD_a, cG_a', pos))

  (* Shifts the tdecls in cG_a by 1 *)
  let rec mshift_cG_a cG_a =
    match cG_a with
    | [] -> []
    | (decl, Some i, n, k, thm_var, true) :: cG_a' ->
       let decl' = Whnf.cnormCCDecl (decl, LF.MShift 1) in
       let i' = Whnf.cnormExp (i, LF.MShift 1) in
       (decl', Some i', n, k, thm_var, true) :: (mshift_cG_a cG_a')
    | x :: cG_a' -> x :: (mshift_cG_a cG_a')

  (* Move a boxed var to the mctx and apply change
     to cD_a and cG_a *)
  let update_annotations (cD_a, cG_a) name =
    let remove_from_cG_a cG_a =
      let cG_a' = mshift_cG_a cG_a in
      let rec remove cG_a =
        match cG_a with
        | (((Comp.CTypDecl (name2, _ ,_)) as cdecl), _, con, _, thm, bool)
          :: cG_a' when Name.equal name name2 ->
           (cdecl, con, thm, bool, cG_a')
        | x :: xs ->
           let (tdecl, num, thm_var, bool, cG_a') =
             remove xs in
           (tdecl, num, thm_var, bool, x :: cG_a')
      in
      remove cG_a'
    in
    let (tdecl, num_con, thm_var, bool, cG_a') =
      remove_from_cG_a cG_a in
    match tdecl with
    | Comp.CTypDecl
      (name, Comp.TypBox (_, ((LF.ClTyp (cltyp, cPsi)) as ctyp)), wf) ->
       (match cltyp with
       | LF.MTyp tA ->
          let tdecl' = LF.Decl (name, ctyp, Plicity.explicit, Inductivity.not_inductive) in
          let norm =
            LF.Root (noLoc, LF.MVar (LF.Offset 1, S.id), LF.Nil, Plicity.explicit) in
          let clobj = LF.MObj norm in
          let mf = LF.ClObj
                     (Context.dctxToHat cPsi
                     , clobj) in
          let mobj = (noLoc, mf) in
          let i = Comp.AnnBox(noLoc, mobj, ctyp) in
          let cD_a' = (tdecl', Some i, num_con, 1, thm_var, bool)
                      :: (shift_cD_a cD_a) in
          (cD_a', cG_a')
       | LF.PTyp tA ->
          let tdecl' = LF.Decl (name, ctyp, Plicity.explicit, Inductivity.not_inductive) in
          let hd = LF.PVar (1, S.id) in
          let clobj = LF.PObj hd in
          let mf = LF.ClObj
                     (Context.dctxToHat cPsi
                     , clobj) in
          let mobj = (noLoc, mf) in
          let i = Comp.AnnBox(noLoc, mobj, ctyp) in
          let cD_a' = (tdecl', Some i, num_con, 1, thm_var, bool)
                      :: (shift_cD_a cD_a) in
          (cD_a', cG_a'))
    | Comp.CTypDecl (name,
                     Comp.TypInd (Comp.TypBox (_, ((LF.ClTyp (cltyp, cPsi))
                                                   as ctyp))), wf) ->
       (match cltyp with
       | LF.MTyp _ ->
          let tdecl' = LF.Decl (name, ctyp, Plicity.explicit, Inductivity.inductive) in
          let norm =
            LF.Root (noLoc, LF.MVar (LF.Offset 1, S.id), LF.Nil, Plicity.explicit) in
          let clobj = LF.MObj norm in
          let mf = LF.ClObj
                     (Context.dctxToHat cPsi
                     , clobj) in
          let mobj = (noLoc, mf) in
          let i = Comp.AnnBox(noLoc, mobj, ctyp) in
          let cD_a' = (tdecl', Some i, num_con, 1, thm_var, bool)
                      :: (shift_cD_a cD_a) in
          (cD_a', cG_a')
       | LF.PTyp _ ->
          let tdecl' = LF.Decl (name, ctyp, Plicity.explicit, Inductivity.inductive) in
          let hd = LF.PVar (1, S.id) in
          let clobj = LF.PObj hd in
          let mf = LF.ClObj
                     (Context.dctxToHat cPsi
                     , clobj) in
          let mobj = (noLoc, mf) in
          let i = Comp.AnnBox(noLoc, mobj, ctyp) in
          let cD_a' = (tdecl', Some i, num_con, 1, thm_var, bool)
                      :: (shift_cD_a cD_a) in
          (cD_a', cG_a'))
    | _ -> dprintf
             begin fun p ->
             p.fmt "[update_annotations]"
             end;
           raise NotImplementedYet

  (* Add a split var onto cG_a *)
  let add_split pos tdecl cG_a var_in_thm =
    dprintf
      begin fun p ->
      p.fmt "[add_split]"
      end;
    match tdecl with
    | Comp.CTypDecl (name, Comp.TypBase (_, cid,_mS), _wf) ->
       let i = Comp.Var (noLoc, 1) in
       let thm_var =
         match var_in_thm with
         | true -> Some pos
         | false -> None
       in
       (tdecl, Some i, consOfTyp cid, 1, thm_var, true)
       :: (shift_cG_a cG_a)
    | Comp.CTypDecl (name, Comp.TypInd (Comp.TypBase (_, cid,_ms)), _wf) ->
       let i = Comp.Var (noLoc, 1) in
       let thm_var =
         match var_in_thm with
         | true -> Some pos
         | false -> None
       in
       (tdecl, Some i, consOfTyp cid, 1, thm_var, true)
       :: (shift_cG_a cG_a)
    | Comp.CTypDecl (name, Comp.TypBox (_, LF.ClTyp (cltyp, cPsi)), _wf) ->
       let i = Comp.Var (noLoc, 1) in
       let thm_var =
         match var_in_thm with
         | true -> Some pos
         | false -> None
       in
       (tdecl, Some i, consOfLFTyp cltyp, 1, thm_var, true)
       :: (shift_cG_a cG_a)
    | Comp.CTypDecl (name, Comp.TypInd (Comp.TypBox (_, LF.ClTyp (cltyp, cPsi))), _wf) ->
       let i = Comp.Var (noLoc, 1) in
       let thm_var =
         match var_in_thm with
         | true -> Some pos
         | false -> None
       in
       (tdecl, Some i, consOfLFTyp cltyp, 1, thm_var, true)
       :: (shift_cG_a cG_a)
    | _ -> shift_cG_a cG_a

  (* Add an msplit var onto cD_a *)
  let add_msplit pos tdecl cD_a var_in_thm =
    dprintf
      begin fun p ->
      p.fmt
        "[add_msplit]"
      end;
    match tdecl with
    | LF.Decl (_, ((LF.ClTyp (cltyp, cPsi)) as ctyp), plic, _) ->
       (match cltyp with
        | LF.MTyp _ ->
          let norm =
            LF.Root (noLoc, LF.MVar (LF.Offset 1, S.id),
                     LF.Nil, plic) in
          let clobj = LF.MObj norm in
          let mf = LF.ClObj
                     (Whnf.cnorm_psihat (Context.dctxToHat cPsi) (LF.MShift 1)
                     , clobj) in
          let mobj = (noLoc, mf) in
          let ctyp' = Whnf.cnormMTyp (ctyp, LF.MShift 1) in
          let i = Comp.AnnBox(noLoc, mobj, ctyp') in
          let tdecl' = Whnf.cnormCDecl (tdecl, LF.MShift 1) in
          let thm_var =
            match var_in_thm with
            | true -> Some pos
            | false -> None
          in
          (tdecl', Some i, consOfLFTyp cltyp, 1, thm_var, true)
          :: (shift_cD_a cD_a)
        | LF.PTyp _ ->
          let hd = LF.PVar (1, S.id) in
          let clobj = LF.PObj hd in
          let mf = LF.ClObj
                     (Whnf.cnorm_psihat (Context.dctxToHat cPsi) (LF.MShift 1)
                     , clobj) in
          let mobj = (noLoc, mf) in
          let ctyp' = Whnf.cnormMTyp (ctyp, LF.MShift 1) in
          let i = Comp.AnnBox(noLoc, mobj, ctyp') in
          let tdecl' = Whnf.cnormCDecl (tdecl, LF.MShift 1) in
          let thm_var =
            match var_in_thm with
            | true -> Some pos
            | false -> None
          in
          (tdecl', Some i, consOfLFTyp cltyp, 1, thm_var, true)
          :: (shift_cD_a cD_a))
    | LF.Decl (_, LF.CTyp (Some cid), _, _) ->
       (* For now we do not split on contexts *)
          let mf = LF.CObj (LF.CtxVar(LF.CtxName (Store.Cid.Schema.get_name cid))) in
          let mobj = (noLoc, mf) in
          let ctyp' = Whnf.cnormMTyp (LF.CTyp (Some cid), LF.MShift 1) in
          let i = Comp.AnnBox(noLoc, mobj, ctyp') in
          let tdecl' = Whnf.cnormCDecl (tdecl, LF.MShift 1) in
          let thm_var =
            match var_in_thm with
            | true -> Some pos
            | false -> None
          in
          (* We hardcode the number of cases for a ctx schema to 2 *)
          (tdecl', Some i, 2, 1, thm_var, true)
          :: (shift_cD_a cD_a)
    | LF.Decl (_, LF.CTyp None, _, _) ->
       (* For now we do not split on contexts *)
          let tdecl' = Whnf.cnormCDecl (tdecl, LF.MShift 1) in
          let thm_var =
            match var_in_thm with
            | true -> Some pos
            | false -> None
          in
          (tdecl', None, 0, 1, thm_var, true)
          :: (shift_cD_a cD_a)
    | _ -> shift_cD_a cD_a

  (* Generate the annotated cD_a for cD *)
  let gen_cD_a cD thm =
    dprintf
      begin fun p ->
      p.fmt
        "[gen_cD_a]"
      end;
    let get_name tdecl =
      match tdecl with
      | LF.Decl (name, _, _, _) | LF.DeclOpt (name, _) -> name
    in
    let check_in_thm name =
      let rec iter_thm k thm =
        match thm with
        | Comp.TypInd (tau') -> iter_thm k tau'
        | Comp.TypArr (_,_,tau) -> iter_thm (k+1) tau
        | Comp.TypPiBox (_, tdecl, tau) ->
           if Name.equal (get_name tdecl) name
           then (k, true)
           else iter_thm (k+1) tau
        | _ -> (0, false)
      in
      iter_thm 1 thm
    in
    let rec gen cD cD_a =
      match cD with
      | LF.Empty -> cD_a
      | LF.Dec (cD', tdecl) ->
         let (pos, bool) = check_in_thm (get_name tdecl) in
         gen cD' (add_msplit pos tdecl cD_a bool)
    in
    gen cD []

  (* Generate the annotated cG_a for cG *)
  let gen_cG_a cG thm cD =
    dprintf
      begin fun p ->
      p.fmt
        "[gen_cG_a]"
      end;
    let get_typ tdecl =
      match tdecl with
      | Comp.CTypDecl (_, tau, _) -> tau
      | _ -> raise NotImplementedYet
    in
    let unifies tau1 tau2 =
      try
        U.unifyCompTyp cD (tau1, LF.MShift 0) (tau2, LF.MShift 0);
        true
      with
      | _ -> false
    in
    let check_in_thm tau =
      let rec iter_thm tau thm k =
        match thm with
        | Comp.TypArr (_, tau1, tau2) ->
           if unifies tau tau1
           then (k, true)
           else iter_thm tau tau2 (k+1)
        | Comp.TypPiBox (_, _, thm') ->
           iter_thm tau thm' (k+1)
        | Comp.TypInd (tau') -> iter_thm tau' thm k
        | _ -> (0, false)
      in
      iter_thm tau thm 1
    in
    let rec gen cG cG_a =
      match cG with
      | LF.Empty -> dprintf
      begin fun p ->
      p.fmt
        "[gen_cG_a] length of generated cG_a = %d"
        (List.length cG_a)
      end; cG_a
      | LF.Dec (cG', tdecl) ->
         let (pos, bool) = check_in_thm (get_typ tdecl) in
         dprintf
      begin fun p ->
      p.fmt
        "[gen_cG_a] check_in_thm pos = %d, bool = %b"
        pos
          bool
      end;
         gen cG' (add_split pos tdecl cG_a bool)
    in
    gen cG []

  let rec lengthCPool cPool =
    match cPool with
    | Emp -> 0    | Full (cPool', cc) -> 1 + (lengthCPool cPool')

  let rec gen_cPool cG cPool =
    match cG with
    | LF.Empty -> cPool
    | LF.Dec (cG', Comp.CTypDecl (_, tau, _)) ->
       let clause = {cHead = tau; cMVars = LF.Empty; cSubGoals = Proved} in
       let cc = (clause, (lengthCPool cPool) + 1, Boxed) in
       gen_cPool cG' (prependToCPool cc cPool)

  let fix_psi mtyp mf =
    let rec merge_names psi_names psi_types =
      dprintf
      begin fun p ->
      p.fmt
        "[merge_names] names_psi = %a, types_psi = %a"
        (P.fmt_ppr_dctx LF.Empty) psi_names
      (P.fmt_ppr_dctx LF.Empty) psi_types
      end;
      match psi_names, psi_types with
      | LF.DDec (p1, LF.TypDecl (n, _)), LF.DDec (p2, LF.TypDecl (_, tA)) ->
         LF.DDec (merge_names p1 p2, LF.TypDecl (n, tA))
      | LF.Null, LF.Null -> LF.Null
      | LF.CtxVar (LF.CtxName n), LF.DDec (LF.Null, LF.TypDecl (_, tA)) ->
         LF.DDec (LF.Null, LF.TypDecl (n, tA))
      | LF.CtxVar (LF.CtxOffset k),  _ ->
         psi_types
      | LF.DDec (p1,td1), LF.DDec (p2,LF.TypDeclOpt _) ->
         LF.DDec (merge_names p1 p2, td1)
      | _ -> dprintf
      begin fun p ->
      p.fmt
        "[merge_names] ERROR"
      end; raise NotImplementedYet
    in
    let new_psi psi = match mf with
      | LF.ClObj (dctx_hat, _) ->
         merge_names psi (Context.hatToDCtx dctx_hat)
      | LF.CObj p -> p
      | _ -> raise NotImplementedYet
    in
    match mtyp with
    | LF.ClTyp (c, psi') -> LF.ClTyp (c, new_psi psi')
    | _ -> mtyp

  (* Given the arguments of the IH, build the respective Beluga term. *)
  let create_IH_args (thm, args, tau) cD =

    let rec create (thm, args) f k len ms =
      dprintf
             begin fun p ->
             p.fmt "[create]"
             end;
      match (args, thm) with
      | (Comp.M ((loc, mf), _) :: xs,
         Comp.TypPiBox (noLoc, LF.Decl (_, ctyp, plic, ind), tau)) ->
         let ctyp' = (* a bit sketchy... this is done bc during the check
                          the ctyp is only used for the dctx.             *)
           fix_psi (cnormMTyp (ctyp,ms)) mf in
         let ms' = LF.MDot (mf, ms) in
         create (tau, xs) (fun s ->
             Comp.MApp (noLoc, f s, (noLoc, mf), ctyp', plic))
           k (len-1) ms'
      | (Comp.M ((loc, mf), _) :: xs,
         Comp.TypArr(_, Comp.TypBox (l, mt), tau)) ->
         let mt' = fix_psi (cnormMTyp (mt,ms)) mf in
         let ms' = LF.MDot (mf, ms) in
         let syn = Comp.AnnBox (noLoc, (noLoc, mf), mt') in
         create (tau, xs) (fun s ->
             Comp.Apply (noLoc, f s, syn)) k (len-1) ms'
      | (Comp.M ((loc, mf), _) :: xs,
         Comp.TypArr(_, Comp.TypInd (Comp.TypBox (l, mt)), tau)) ->
         let mt' = fix_psi (cnormMTyp (mt,ms)) mf in
         let ms' = LF.MDot (mf, ms) in
         let syn = Comp.AnnBox (noLoc, (noLoc, mf), mt') in
         create (tau, xs) (fun s ->
             Comp.Apply (noLoc, f s, syn)) k (len-1) ms'
      | ((Comp.V k) :: xs,
         Comp.TypArr(_,_,tau)) ->
         create (tau, xs) (fun s ->
             Comp.Apply (noLoc, f s, Comp.Var (noLoc, k))) k (len-1) ms
      | (Comp.DC :: xs,
         Comp.TypPiBox (noLoc, LF.Decl (_, ctyp, plic, ind), tau)) ->
         (* If this case happens, it usually means there is a meta-variable
            not being used in the theorem. To make the prover more robust we
            can implement this case, it will just choose a random meta-var
            from Delta to be the argument. *)
         dprintf
             begin fun p ->
             p.fmt "[create_IH_args] Invalid I.H. Unused mvar"
             end;
         raise NotImplementedYet
      | (Comp.DC :: xs,
         Comp.TypArr(_,tau1,tau)) ->
         dprintf
             begin fun p ->
             p.fmt "[create_IH_args] Invalid I.H. DC"
             end;
         raise NotImplementedYet
      | ([], _) -> f
      | (Comp.E :: xs, _) ->
         dprintf
             begin fun p ->
             p.fmt "[create_IH_args] Invalid I.H. E"
             end;
         raise NotImplementedYet
      | (_, Comp.TypInd tau') -> create (tau', args) f k len ms
      | _ -> dprintf
             begin fun p ->
             p.fmt "[create_IH_args] Invalid I.H. Other"
             end; raise NotImplementedYet
    in
    create (thm, args) (fun s -> s) 0 (Context.length cD) (LF.MShift 0)

  (* Calls the coverage checker to compute the list of goals for a
    given type in the contexts of the given proof state.             *)
  let generate_pattern_coverage_goals tau cD cG :
        (LF.mctx * (Comp.gctx * Comp.pattern * Comp.tclo) * LF.msub) list =
    let names = Context.(names_of_mctx cD @ names_of_gctx cG) in
    Coverage.(genPatCGoals names withPatVar cD (Total.strip tau))

  (* Get the cases for current cD and cG *)
  let get_cases (cD, cG) (cD_a, cG_a) =
      let rec update_mvar_case_count cD_a =
        match cD_a with
        | [] -> []
        | (((LF.Decl (_, mtyp, _, _)) as tdecl), i, _, pos, thm_var, true)::xs ->
           let tau = Comp.TypBox(noLoc, mtyp) in
           let cases =
             try
               generate_pattern_coverage_goals tau cD cG
             with
             | _ -> []
           in
           let n = List.length cases in
           (tdecl, i, n, pos, thm_var, true):: (update_mvar_case_count xs)
        | x :: xs ->
           x :: (update_mvar_case_count xs)
      in
      let rec update_var_case_count cG_a =
        match cG_a with
        | [] -> []
        | (((Comp.CTypDecl (_, tau, _)) as tdecl), i, _, pos, thm_var, true)
          ::xs ->
           let cases =
             try
               generate_pattern_coverage_goals tau cD cG
             with
             | _ -> []
           in
           let n = List.length cases in
           (tdecl, i, n, pos, thm_var, true):: (update_var_case_count xs)
        | x :: xs ->
           x :: (update_var_case_count xs)
      in
      let cD_a' = update_mvar_case_count cD_a in
      let cG_a' = update_var_case_count cG_a in
      (cD_a', cG_a')

  (* Returns the plicity of the mvar from the cD at position k *)
  let rec get_plicity cD k =
    match cD with
    | LF.Dec (_, LF.Decl (_, _, plicity, _))
      | LF.Dec (_, LF.DeclOpt (_, plicity))
         when k = 1 -> plicity
    | LF.Dec (cD', _) -> get_plicity cD' (k-1)
    | _ ->
       dprintf begin fun p -> p.fmt "[get_plicity] INDEX OUT OF BOUNDS" end;
       raise NotImplementedYet

  (* Given a Beluga expression and corresponding cD, correct the plicities
     of the mvar references (LF.MVar (LF.Offset ...))                         *)
  let rec fix_plicities e cD =
    match e with
    | Comp.Fn (_1, _2, e') ->
       Comp.Fn (_1, _2, fix_plicities e' cD)
    | Comp.MLam (_1, name, e', _3) ->
       Comp.MLam (_1, name,
                  fix_plicities e' (LF.Dec(cD, LF.DeclOpt (name, Plicity.explicit))),
                  _3)
    | Comp.Box (_1, (_2, mft), _3) ->
       Comp.Box (_1, (_2, fix_plicities_mf mft cD), _3)
    | Comp.Case (_1, _2, e', lst) ->
       Comp.Case (_1, _2, fix_plicities e' cD, fix_branches lst)
    | Comp.Apply (_1, e1, e2) ->
       Comp.Apply (_1, fix_plicities e1 cD, fix_plicities e2 cD)
    | Comp.MApp (_1, e', (_2, mft), _3, _4) ->
       Comp.MApp (_1, fix_plicities e' cD,
                  (_2, fix_plicities_mf mft cD), _3, _4)
    | Comp.AnnBox (_1, (_2, mft), _3) ->
       Comp.AnnBox (_1, (_2, fix_plicities_mf mft cD), _3)
    | _ -> e

  and fix_branches lst =
    match lst with
    | (Comp.Branch (_1, _2, (cD, _3), _4, _5, e)) :: lst' ->
       (Comp.Branch (_1, _2, (cD, _3), _4, _5, fix_plicities e cD))
       :: (fix_branches lst')
    | [] -> []

  and fix_plicities_mf mft cD =
    match mft with
    | LF.ClObj (_1, LF.MObj (LF.Root (_2, LF.MVar (LF.Offset k, _3),
                                      spine, _4))) ->
       LF.ClObj (_1, LF.MObj (LF.Root (_2, LF.MVar (LF.Offset k, _3),
                                       spine, get_plicity cD k)))
    | LF.ClObj (_1, LF.MObj (LF.Root (_2, LF.MMVar ((mmvar, _3), _4),
                                      spine, _5))) ->
       let plicity =
       match !(mmvar.LF.instantiation) with
       | Some (LF.INorm (LF.Root (_2, LF.MVar (LF.Offset k, _3),
                                  spine, _4))) ->
          get_plicity cD k
       | Some (LF.IHead (LF.MVar (LF.Offset k, _1))) -> get_plicity cD k
       | _ -> _5
       in
       LF.ClObj (_1, LF.MObj (LF.Root (_2, LF.MMVar ((mmvar, _3), _4),
                                       spine, plicity)))
    | LF.ClObj (_1, LF.MObj norm) ->
       LF.ClObj (_1, LF.MObj (fix_plicities_norm norm cD))
    | _ -> mft

  and fix_plicities_norm norm cD =
    match norm with
    | LF.Lam (_1, _2, norm') ->
       LF.Lam (_1, _2, fix_plicities_norm norm' cD)
    | LF.Root (_1, hd, LF.Nil, _2) ->
       let plicity = match hd with
         | LF.MVar (LF.Offset k, _) -> get_plicity cD k
         | _ -> _2
       in
       LF.Root (_1, hd, LF.Nil, plicity)
    | LF.Root (_1, hd, spine, _2) ->
       LF.Root (_1, hd, fix_plicities_spine spine cD, _2)
    | _ -> norm

  and fix_plicities_spine spine cD =
    match spine with
    | LF.App (norm, spine') ->
       LF.App (fix_plicities_norm norm cD,
               fix_plicities_spine spine' cD)
    | _ -> spine

  (* Used for splitting operations. Beluga doesn't correctly give the plicity
     of the mvars after a split so this fixes it. Given the original cD
     (cD_old) and pattern, and newly generated cD (cD_fix) for the branch, fix the
     plicities of its declarations *)
  let gen_explicit_cD cD_old pat cD_fix =
    dprintf begin fun p ->
      p.fmt "[gen_explicit] cD_old = %a, cD_fix = %a, pat = %a"
        (P.fmt_ppr_mctx) cD_old
        (P.fmt_ppr_mctx) cD_fix
        (DP.fmt_ppr_cmp_pattern cD_fix LF.Empty DP.l0) pat
      end;
    let rec find_name cD k =
      match cD with
      | LF.Dec (_, LF.Decl (name, _, _, _)) when k = 1 -> name
      | LF.Dec (cD', _) -> find_name cD' (k-1)
    in
    let collect_explicit_mvars =
      let rec collect_from_cD cD =
        match cD with
        | LF.Dec (cD', LF.Decl (name, _, Plicity.Explicit, _)) ->
           name :: (collect_from_cD cD')
        | LF.Dec (cD', LF.DeclOpt (name, Plicity.Explicit)) ->
           name :: (collect_from_cD cD')
        | LF.Dec (cD', _) ->
           collect_from_cD cD'
        | LF.Empty -> []
      in
      let rec collect_from_norm norm =
        match norm with
        | LF.Lam (_, _, norm') | LF.Clo (norm', _) ->
           collect_from_norm norm'
        | LF.Root (_, LF.Const cid, spine, Plicity.Explicit) ->
           let tau = (Store.Cid.Term.get cid).Store.Cid.Term.Entry.typ in
           find_explicit tau spine
        | LF.Root (_, hd, LF.Nil, Plicity.Explicit) ->
           collect_from_hd hd
        | LF.Root (_1, hd, LF.SClo (spine, _), Plicity.Explicit) ->
           collect_from_norm (LF.Root (_1, hd, spine, Plicity.explicit))
        | LF.Root (_1, hd, LF.App (norm', spine), Plicity.Explicit) ->
           List.append
             (collect_from_norm norm')
             (collect_from_norm (LF.Root (_1, hd, spine, Plicity.explicit)))
        | _ -> []

      and collect_from_hd hd =
        match hd with
        | LF.MMVar ((mm_var, _), _)
          | LF.MPVar ((mm_var, _), _)
          | LF.MVar (LF.Inst mm_var, _) ->
           [mm_var.LF.name]
        | LF.MVar (LF.Offset k, _) ->
           [find_name cD_fix k]
        | _ -> []

      and find_explicit tau spine =
        match (tau, spine) with
        | (LF.PiTyp ((LF.TypDecl (name, _), depend, Plicity.Explicit), tau'),
           LF.App (norm, spine')) ->
           List.append (collect_from_norm norm) (find_explicit tau' spine')
        | (LF.PiTyp ((LF.TypDeclOpt name, depend, Plicity.Explicit), tau'),
           LF.App (norm, spine')) ->
           List.append (collect_from_norm norm) (find_explicit tau' spine')
        | (LF.PiTyp ((_, _, _), tau'), LF.App (_, spine')) ->
           find_explicit tau' spine'
        | _ -> []

      and collect_from_pat pat =
        match pat with
        | Comp.PatMetaObj (_, (_, LF.ClObj (_, LF.MObj norm))) ->
           collect_from_norm norm
        | Comp.PatMetaObj (_, (_, LF.ClObj (_, LF.PObj hd))) ->
           collect_from_hd hd
        | Comp.PatMetaObj (_, (_, LF.CObj (LF.CtxVar (LF.CtxOffset k)))) ->
           [find_name cD_fix k]
        | Comp.PatMetaObj (_,
                           (_, LF.CObj (LF.CtxVar (LF.CInst (mm_var, _))))) ->
          [mm_var.LF.name]
        | Comp.PatMetaObj (_1, (_2, LF.CObj (LF.DDec (dctx', _)))) ->
           collect_from_pat (Comp.PatMetaObj (_1, (_2, LF.CObj (dctx'))))
        | Comp.PatMetaObj (_, (_, LF.MV k)) ->
           [find_name cD_fix k]
        | Comp.PatConst (_1, _2, Comp.PatApp (_, pat', pat_spine)) ->
           List.append
             (collect_from_pat pat')
             (collect_from_pat (Comp.PatConst (_1, _2, pat_spine)))
        | Comp.PatConst (_1, _2, Comp.PatObs (_, _, _, pat_spine)) ->
           collect_from_pat (Comp.PatConst (_1, _2, pat_spine))
        | _ -> []
      in
      List.append (collect_from_cD cD_old) (collect_from_pat pat)
    in
    let explicit_mvars = collect_explicit_mvars in
    let rec is_explicit name ex_lst =
      match ex_lst with
      | n :: _ when Name.equal name n -> true
      | _ :: xs -> is_explicit name xs
      | [] -> false
    in
    let rec fix cD =
      match cD with
      | LF.Empty -> cD
      | LF.Dec (cD', LF.Decl (name, _1, _, _2))
           when is_explicit name explicit_mvars ->
         LF.Dec (fix cD', LF.Decl (name, _1, Plicity.explicit, _2))
      | LF.Dec (cD', LF.Decl (_1, _2, _, _3)) ->
         LF.Dec (fix cD', LF.Decl (_1, _2, Plicity.implicit, _3))
      | LF.Dec (cD', LF.DeclOpt (name, _))
           when is_explicit name explicit_mvars ->
         LF.Dec (fix cD', LF.DeclOpt (name, Plicity.explicit))
      | LF.Dec (cD', LF.DeclOpt (_1, _)) ->
         LF.Dec (fix cD', LF.DeclOpt (_1, Plicity.implicit))
    in
    fix cD_fix

  (* Find all the indices of mvars in cD whsoe type unifies with typ *)
  let rec find_assumption typ cD cD_all cG k lst =
    let rec k_in_lst k lst =
      match lst with
      | x :: xs when x = k -> true
      | x :: xs -> k_in_lst k xs
      | [] -> false
    in
    match cD with
    | LF.Dec (cD', LF.Decl (_, ctyp, plicity, _))
         when Plicity.is_explicit plicity ->
       (* We do not want to instantiate with implict mvars,
          this can cause issues when we reconstruct the type *)
       (
       try
         Solver.trail
           begin fun () ->
           U.unifyMetaTyp cD_all (ctyp, LF.MShift k) (typ, LF.MShift 0)
           end;
         if k_in_lst k lst
         then find_assumption typ cD' cD_all cG (k + 1) lst
         else (Some k, k :: lst)
       with
       | U.Failure _ ->
          find_assumption typ cD' cD_all cG (k + 1) lst)
    | LF.Dec (cD', _) ->
       find_assumption typ cD' cD_all cG (k + 1) lst
    | LF.Empty -> (None, [])

  (* Given an IH of box type with one uninstantiated mvar,
     find all occurances of it *)
  let rec find_all_occurances ((Comp.WfRec (name, ih_arg_lst, tau)) as dec)
            (cG, cPool, cG_a) sc cD thm_cid thm lst cIH cIH_all =
    let (ih_args, tau) = generate_new_IH dec in
    let {cHead=hd; cMVars; cSubGoals=sg} = C.comptypToCClause tau in
    let fS = create_IH_args (thm, ih_args, tau) cD in
    let names = Context.(names_of_mctx cD @ names_of_gctx cG) in
    let name = Name.gen_fresh_name names (Name.mk_name Name.NoName) in
    let inst mobj k = match mobj with
        | LF.MObj (LF.Root (_, LF.MMVar ((mmvar, _), _), _, _))
          | LF.MObj (LF.Root (_, LF.MPVar ((mmvar, _), _), _, _)) ->
           mmvar.LF.instantiation :=
             Some (LF.INorm (LF.Root (noLoc,
                                      LF.MVar (LF.Offset k, LF.Shift 0),
                                      LF.Nil, mmvar.LF.plicity)))
        | LF.PObj LF.MPVar ((mmvar, _), _)
          | LF.PObj LF.MMVar ((mmvar, _), _) ->
           mmvar.LF.instantiation :=
             Some (LF.IHead (LF.MVar (LF.Offset k, LF.Shift 0)))
    in
    let pattern = Comp.PatVar (noLoc, 1) in
    let rec grab ih_args =
      match ih_args with
      | (Comp.M ((_, LF.ClObj (_, ((LF.PObj hd) as mobj))), _)) :: xs ->
         if Solver.uninstantiated hd then mobj else grab xs
      | (Comp.M ((_, LF.ClObj (_, ((LF.MObj (LF.Root (_,hd,_,_))) as mobj))), _))
        :: xs->
         if Solver.uninstantiated hd then mobj else grab xs
      | _ :: xs -> grab xs
    in
    let mobj = grab ih_args in
    let typ = match mobj with
      | LF.MObj (LF.Root (_, LF.MMVar ((mmvar, _), _), _, _))
      | LF.MObj (LF.Root (_, LF.MPVar ((mmvar, _), _), _, _))
      | LF.PObj LF.MPVar ((mmvar, _), _)
      | LF.PObj LF.MMVar ((mmvar, _), _) -> mmvar.LF.typ in
    let (k, lst') = find_assumption typ cD cD cG 1 lst in
    match k with
    | Option.None -> (cG, cG_a, cPool, sc, cIH, cIH_all)
    | Option.Some k ->
      inst mobj k;
      let cPool' = Full (shift_cPool cPool 1,
                         ({cHead=hd;
                           cMVars=LF.Empty;
                           cSubGoals=Proved} , 1, Boxed)) in
      let tdecl = Comp.CTypDecl(name, hd, true) in
      let cG' = Whnf.extend_gctx cG (tdecl, LF.MShift 0) in
      let cG_a' = add_split 0 tdecl cG_a false in
      let cIH_all' = Total.shift cIH_all in
      let cIH' = Total.shift cIH in
      let Some cid = thm_cid in
      let i = Comp.Const(noLoc, cid) in
      let sc' = (fun e -> sc (Comp.Case (noLoc,
                                       Comp.PragmaNotCase,
                                       Whnf.cnormExp (fS i, LF.MShift 0),
                                       [Comp.Branch (noLoc,
                                                     LF.Empty,
                                                     (cD, cG'),
                                                     pattern,
                                                     LF.MShift 0,
                                                     e)]))) in
      find_all_occurances dec (cG', cPool', cG_a') sc' cD thm_cid thm lst' cIH' cIH_all'

  (* cD' ; cG' |- tau
     cD  |- ms : cD'       ms is a meta-substitution that provides existential
                           variables (refs that will instantiated) for all
                           the bound meta-variables in cD'

     cD  ; cG (= [ms]cG') (cPool)  |- tau[ms] (= mq)

     Mquery mq := N   (an mquery is a negative computation-level proposition)

     Schema   W
     Contextual
      Type    U := (Psi |- tA) | (Psi |-# tBlock) | (Psi |- Phi)   | (Psi |-# Phi)     | W
     Contextual
      Object  C := (Psi |- tM) | Psi |-# PVar _   | (Psi |- sigma) | (Psi |-# SVar _ ) | Psi

     Negative N := P -> N  | forall x:U. N | P
     Positive P := box (U) | Atomic Q
              Q := c C1 ... Cn     (where c is a constructor of an inductive/stratified data type)

    *)
  let rec cgSolve' (cD, cD_a) (cG, cPool, cG_a) cIH
            (mq:mquery) (sc: Comp.exp -> unit)
            (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
            (ind, thm, td, thm_cid) (blur: blur_it) =

    if (checkDepth currDepth maxDepth)
    then
      (dprintf
         begin fun p ->
         p.fmt "DEPTH REACHED"
         end;
      raise (DepthReached currDepth))
    else
      let (cg, ms) = mq in
      let (d1, d2) = match (currDepth, maxDepth) with
        | (Some k, None) -> (k, 0)
        | (Some k1, Some k2) -> (k1, k2)
      in
      dprintf
        begin fun p ->
        p.fmt
          "ENTERING LOOP- CURRENT D = %d, MAX = %d"
           d1
           d2
         end;
      try
        uniform_right (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
          (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
          (Context.length cD + 1) (ind, thm, td, thm_cid) blur
      with
       | End_Of_Search  -> raise End_Of_Search
       | DepthReached b -> raise (DepthReached b)

  (* Independently solve each subgoal coming from an assumption in cG *)
  (* |- cD'
     cD' |- sg
     cD |- ms' : cD'
     |- cD
     cD |- cG

     prove:
     cD ; cG => sg[ms']                                                *)
  and solveSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH (sg, k) ms sc fS
                      (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                        (thm, td, thm_cid) =
    match sg with
    | Proved ->
       let e' = (Comp.Var (noLoc, k)) in
       let e = fS e' in
       let e = Whnf.cnormExp (e, LF.MShift 0) in
       sc e
    | Solve (sg', cg') ->
       dprintf
         begin fun p ->
         p.fmt "Solve Assumption's sub goals, %a"
           (printState cD cG cPool cIH cg') ms
         end;
       cgSolve' (cD, cD_a) (cG, cPool, cG_a) cIH (cg', ms)
         (fun e ->
           solveSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH (sg', k) ms
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (thm, td, thm_cid))
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
         (None, thm, td, thm_cid) No_Blur

  (* Independently solve each sg coming from a comp. constant (as above) *)
  (* |- cD'
     cD' |- sg
     cD |- ms' : cD'
     |- cD
     cD |- cG

     prove:
     cD ; cG => sg[ms']                                                *)
  and solveCClauseSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH cid sg ms sc fS
                             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                             (thm, td, thm_cid) =
    match sg with
    | Proved ->
       let e' = (Comp.DataConst (noLoc, cid)) in
       let e = fS e' in
       let e = Whnf.cnormExp (e, LF.MShift 0) in
       sc e
    | Solve (sg', cg') ->
       dprintf
         begin fun p ->
         p.fmt "Solve Constant's sub goals, %a"
           (printState cD cG cPool cIH cg') ms
         end;
       cgSolve' (cD, cD_a) (cG, cPool, cG_a) cIH (cg', ms)
         (fun e ->
           solveCClauseSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH cid sg' ms
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (thm, td, thm_cid))
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
         (None, thm, td, thm_cid) No_Blur

  (* Independently solve each subgoal coming from a theorem (as above) *)
  (* |- cD'
     cD' |- sg
     cD |- ms' : cD'
     |- cD
     cD |- cG

     prove:
     cD ; cG => sg[ms']                                                *)
  and solveTheoremSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH cid sg ms sc fS
                             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                             (thm, td, thm_cid) =
    match sg with
    | Proved ->
       let e' = (Comp.Const (noLoc, cid)) in
       let e = fS e' in
       let e = Whnf.cnormExp (e, LF.MShift 0) in
       sc e
    | Solve (sg', cg') ->
       dprintf
         begin fun p ->
         p.fmt "Solve Theorem's sub goals, %a"
           (printState cD cG cPool cIH cg') ms
         end;
       cgSolve' (cD, cD_a) (cG, cPool, cG_a) cIH (cg', ms)
         (fun e ->
           solveTheoremSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH cid sg' ms
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (thm, td, thm_cid))
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
         (None, thm, td, thm_cid) No_Blur

  and solveIhSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH i sg ms sc fS
                        (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                        (thm, td, thm_cid) =
    match sg with
    | Proved ->
       let e' = i in
       let e = fS e' in
       let e = Whnf.cnormExp (e, LF.MShift 0) in
       sc e
    | Solve (sg', cg') ->
       dprintf
         begin fun p ->
         p.fmt "Solve I.H.'s sub goals, %a"
           (printState cD cG cPool cIH cg') ms
         end;
       cgSolve' (cD, cD_a) (cG, cPool, cG_a) cIH (cg', ms)
         (fun e ->
           solveIhSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH i sg' ms
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (thm, td, thm_cid))
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
         (None, thm, td, thm_cid) No_Blur

  (* We focus on one of the computation assumptions in the Induction Hypotheses  *)
  and focusIH (cD, cD_a) (cG, cPool, cG_a) (cIH, cIH_all) cg ms sc
                (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                  (thm, td, thm_cid) =
    dprintf
      begin fun p ->
      p.fmt
        "Foc. on some I.H., %a"
        (printState cD cG cPool cIH_all cg) ms
      end;
    match cIH with
    | LF.Empty -> ()
    | LF.Dec (cIH', ((Comp.WfRec (name, ih_arg_lst, tau)) as dec)) ->
       (* Generate a new I.H. with fresh mvars so we do not instantiate
          the template I.H.                                              *)
       let (ih_args, tau) = generate_new_IH dec in
       let {cHead=hd; cMVars; cSubGoals=sg} = C.comptypToCClause tau in
       if (* Check to see if the comp goal is the head of the assumption *)
         matchHead hd cg
       then (* If so, try to solve the subgoals *)
         (* Create the Beluga term for the I.H. *)
         let arg_builder = create_IH_args (thm, ih_args, tau) cD in
         let Some cid = thm_cid in
         let i = arg_builder (Comp.Const(noLoc, cid)) in
         let (ms', fS) =
           C.mctxToMSub cD (cMVars, LF.MShift 0) (fun s -> s) in
         let ms'' = rev_ms ms' 0 in
         let tau' = if isBox cg then C.boxToTypBox cg
                    else C.atomicToBase cg in
         (* Trail to undo MVar instantiations. *)
         (try
           Solver.trail
             begin fun () ->
             unify cD (tau', ms) (hd, ms'')
               (fun () ->
                 solveIhSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH i sg ms''
                 (fun e' -> sc e')
                 fS (succ currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                 (thm, td, thm_cid))
             end
         with
         | U.Failure _ | DepthReached _ | End_Of_Search ->
         focusIH (cD, cD_a) (cG, cPool, cG_a) (cIH', cIH_all) cg ms sc
           (currDepth, maxDepth, currSplitDepth, maxSplitDepth) (thm, td, thm_cid))

       else (* Otherwise, try the remaining hypotheses *)
         focusIH (cD, cD_a) (cG, cPool, cG_a) (cIH', cIH_all) cg ms sc
           (currDepth, maxDepth, currSplitDepth, maxSplitDepth) (thm, td, thm_cid)

  (* We focus on one of the computation-type theorems *)
  (* |- cD0
     cD0 |- cG0
     cD0 ; cG0 |- cg
     cD |- ms : cD0
     cD ; cG |- cg[ms]   where cG = [ms]cG0

     cD ; cG > cc (={hd=tau; sg=sg; cD'=mV})  |- cg[ms]
     cD' ; sg |- hd
     cD |- ms' : cD'

     1. [ms']hd ==unified== [ms]cg   where: ms' = [^|cD'|, (cdToMSub cD')]
        --->  cD ; cG => sg[ms']

     2. [ms']hd ==NOT unified== [ms]cg
        --->  cD ; cG > cc'  |- cg[ms]                                      *)
  and focusT (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
               (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
               (thm, td, thm_cid) =
    dprintf
      begin fun p ->
      p.fmt
        "Foc. on Theorems, %a"
        (printState cD cG cPool cIH cg) ms
      end;
    let matchThm (cid, sCCl) =
      let check cid =
        match thm_cid with
        | Some cid' ->
           not (Name.equal (Store.Cid.Comp.fixed_name_of cid)
                (Store.Cid.Comp.fixed_name_of cid'))
        | _ -> true
      in
      if (* Check to see if the comp goal is the head of the assumption *)
         check cid && matchHead sCCl.cHead cg;
      then
        (let (ms', fS) =
           C.mctxToMSub cD (sCCl.cMVars, LF.MShift 0) (fun s -> s)
         in
         let ms'' = rev_ms ms' 0 in
         let tau = if isBox cg then C.boxToTypBox cg else C.atomicToBase cg in
        (try
           Solver.trail
             begin fun () ->
               unify cD (tau, ms) (sCCl.cHead, ms'')
                 (fun () ->
                   solveTheoremSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH cid
                     sCCl.cSubGoals ms'' sc fS
                     (succ currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                     (thm, td, thm_cid))
              end
         with
         | U.Failure _ | DepthReached _ | End_Of_Search -> ()))
      else
        ()
    in
    Index.iterAllTSClauses (fun w -> matchThm w)

  (* Focus on the clause in the static Comp signature with head matching
     type constant c. *)
  (* |- cD0
     cD0 |- cG0
     cD0 ; cG0 |- cg
     cD |- ms : cD0
     cD ; cG |- cg[ms]   where cG = [ms]cG0

     cD ; cG > cc (={hd=tau; sg=sg; cD'=mV})  |- cg[ms]
     cD' ; sg |- hd
     cD |- ms' : cD'

     1. [ms']hd ==unified== [ms]cg
                      where: ms' = [^|cD'|, (cdToMSub cD')]
        --->  cD ; cG => sg[ms']

     2. [ms']hd ==NOT unified== [ms]cg
        --->  cD ; cG > cc'  |- cg[ms]                         *)
  and focusS cidTyp (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
               (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                 (thm, td, thm_cid) =
    dprintf
      begin fun p ->
      p.fmt
        "Foc. on Sig., %a"
        (printState cD cG cPool cIH cg) ms
      end;
    let matchSig (cidTerm, sCCl) sc =
      let (ms', fS) = C.mctxToMSub cD (sCCl.cMVars, LF.MShift 0) (fun s -> s) in
      let ms'' = rev_ms ms' 0 in
      let tau = C.atomicToBase cg in
      (try
         Solver.trail
           begin fun () ->
           unify cD (tau, ms) (sCCl.cHead, ms'')
               (fun () ->
                 solveCClauseSubGoals (cD, cD_a) (cG, cPool, cG_a) cIH cidTerm
                   sCCl.cSubGoals ms'' sc fS
                   (succ currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                   (thm, td, thm_cid))
            end
         with
         | U.Failure _ | DepthReached _ | End_Of_Search -> ())
    in
    I.iterISClauses (fun w -> matchSig w sc) cidTyp

  (* We focus on one of the computation assumptions in cPool/Gamma          *)
  (* |- cD0
     cD0 |- cG0
     cD0 ; cG0 |- cg
     cD |- ms : cD0
     cD ; cG |- cg[ms]   where cG = [ms]cG0

     cD ; cG > cc (={hd=tau; sg=sg; cD'=mV})  |- cg[ms]
     cD, cD' ; cG, sg |- hd
     cD |- ms' : cD, cD'

     1. [ms']hd ==unified== [ms]cg   where: ms' = [^|cD'|, (cdToMSub cD')]
        --->  cD ; cG => sg[ms']

     2. [ms']hd ==NOT unified== [ms]cg
        --->  cD ; cG > cc'  |- cg[ms]                                  *)
  and focusG (cD, cD_a) (cG, cPool, cPool_all, cG_a) cIH cg ms sc
               (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                 (thm, td, thm_cid) =
    dprintf
      begin fun p ->
      p.fmt
        "Foc. on Gamma, %a"
        (printState cD cG cPool cIH cg) ms
      end;
    match cPool with
    | Emp -> ()
    | Full (cPool', ({cHead = hd; cMVars; cSubGoals = sg}, k', Boxed)) ->
       let (hd, cMVars, sg) =
         match hd with
         | Comp.TypBox _ | Comp.TypBase _ -> (hd, cMVars, sg)
         | _ -> let {cHead = hd; cMVars; cSubGoals = sg} =
                  Convert.comptypToCClause hd in
                (hd, cMVars, sg)
       in
       if (* Check to see if the comp goal is the head of the assumption *)
         matchHead hd cg
       then (* If so, try to solve the subgoals *)
         let (ms', fS) = C.mctxToMSub cD (cMVars, LF.MShift 0) (fun s -> s) in
         let ms'' = rev_ms ms' 0 in
         let tau = if isBox cg then C.boxToTypBox cg else C.atomicToBase cg in
         (* Trail to undo MVar instantiations. *)
         (try
           Solver.trail
             begin fun () ->
             unify cD (tau, ms) (hd, ms'')
               (fun () ->
                 solveSubGoals (cD, cD_a) (cG, cPool_all, cG_a) cIH (sg, k') ms''
                   sc fS (succ currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                   (thm, td, thm_cid))
             end
         with
         | U.Failure _ | DepthReached _ | End_Of_Search ->
         focusG (cD, cD_a) (cG, cPool', cPool_all, cG_a) cIH cg ms sc
           (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
           (thm, td, thm_cid))

       else (* Otherwise, try the remaining comp assumptions *)
         focusG (cD, cD_a) (cG, cPool', cPool_all, cG_a) cIH cg ms sc
           (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
           (thm, td, thm_cid)
    | Full (cPool', cc) ->
       focusG (cD, cD_a) (cG, cPool', cPool_all, cG_a) cIH cg ms sc
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
         (thm, td, thm_cid)

  (* Solve the current branch for a (m)split                               *)
  (* |- cD0
     cD0 |- cG0
     cD0 ; cG0 |- cg
     cD' |- ms' : cD0
     cD' ; cG' |- [ms']cg

     |- cD
     cD |- cG_b
     cD ; cG_b |- pat
     cD |- ms : cD'
     cD ; cG |- [ms]cg   where cG = [ms]cG', cG_b                          *)
  and solve_branch (cD_cg, cg)
                     (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                       b_list (thm, (td: Comp.total_dec list)) sc =
    match b_list with
    | [] -> sc []
    | (cD, cD_b, cD_a, cG, cG_p, cG_a, cIH_b, cPool, ms_b, pat, td_b, cid)
      :: b_list' ->
       let d =
         match currDepth with
         | Some d -> d
         | _ -> 0 in
       dprintf
         begin fun p ->
         p.fmt
           "Solve Branch pattern %a of type %a, with depth = %d \
            %a"
           (DP.fmt_ppr_cmp_pattern cD cG DP.l0) pat
           (P.fmt_ppr_cmp_goal cD_cg) (cg, S.id)
           d
           (printState cD cG cPool cIH_b cg) ms_b
         end;

       let sc = (fun e ->
           solve_branch (cD_cg, cg)
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth) b_list'
               (thm, td_b)
                 (fun bl ->
                   sc (Comp.Branch(noLoc, LF.Empty,
                     (cD, cG), pat, ms_b, e) :: bl)))
       in

       try
         (* We first see if a solution was produced trivially by the split *)
         cgSolve' (cD, cD_a) (cG, cPool, cG_a) cIH_b (cg, ms_b) sc
           (Some 0, Some 0, Some 0, Some 0)
           (None, thm, td_b, cid) No_Blur
       with
       | End_Of_Search | DepthReached _ ->
         dprintf
         begin fun p ->
         p.fmt "No trivial solution- UPDATING ASSUMPTIONS"
         end;

          try
            (* If that fails, we split on all assumptions with 1 case *)
            split (cD, cD_a) (cG, cPool, cG_a) cIH_b cg ms_b sc
              (currDepth, maxDepth, Some 1, Some 1)
              (None, thm, td, cid)
           with
           | DepthReached _ | End_Of_Search ->
              (* We then carry on with our loop *)
              dprintf
              begin fun p ->
              p.fmt "Carry on..."
              end;
              cgSolve' (cD, cD_a) (cG, cPool, cG_a) cIH_b (cg, ms_b) sc
                (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                (None, thm, td, cid) Blur

  (* Split on the given split variable in ind; if none, split on the (m)var
     that provides the least number of cases                                *)
  (* |- cD0
     cD0 |- cG0
     cD0 ; cG0 |- cg
     cD |- ms : cD0
     cD ; cG |- cg[ms]   where cG = [ms]cG0

     1. cD ; cG |- case ([X]:[U]) of
                           | case1 (: tau) ->
                                |- cD'
                                cD' |- cG_b
                                cD' ; cG_b |- tau
                                cD' |- ms1 : cD
                                cD' ; [ms1]cG, cG_b1 (=cG') |- [ms1]cg
                              ...
                           | casen -> (cD' ; [msn]cG, cG_bn (=cG') |- [msn]cg)

     2. cD ; cG |- case (X in cG) of ...                                    *)
  and split (cD, cD_ann) (cG, cPool, cG_ann) cIH cg ms sc
              (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                (ind, thm, td, cid_prog) =
    dprintf
      begin fun p ->
      p.fmt
        "Split, %a"
        (printState cD cG cPool cIH cg) ms
      end;

    let checkDepth x y =
      match (x, y) with
      | (Some i, Some j) -> i > j
      | (Some i, None) -> if i = 1 then false else true
      | (None, _) -> false
    in

    let rec find_comp_assumption cG k =
      match cG with
      | LF.Dec (_, Comp.CTypDecl (_, tau, _)) when k = 1 -> tau
      | LF.Dec (cG', _) -> find_comp_assumption cG' (k-1)
    in

    let gen_branch_list i tau ms mfs (cD', cD_a) (cG', cG_a, k) cIH' index =

      let tau =
        match i, tau with
        | Comp.AnnBox (_, (_, mC), _), Comp.TypBox (loc, mT) ->
           let _, mT', _ = Check.Comp.fixParamTyp mC mT in
           Comp.TypBox(loc, mT')
        | _ -> tau
      in

      (* Computes the subgoal for the given coverage goal *)
      let get_branch (cD_gb, (cG_gb, pat, tau_p), t) =
        let tau_p = Whnf.cnormCTyp tau_p in
        let t', t1', cD_b =
          (* Refine the pattern to compute the branch's
            meta-context, accounting for dependent pattern matching on
            `m`. *)
          Reconstruct.synPatRefine
            Location.ghost
            (Reconstruct.case_type (lazy pat) i)
            (cD', cD_gb) t (tau, tau_p) in
        let pat' = Whnf.cnormPattern (pat, t1') in
        let cG_p = Whnf.cnormGCtx (cG_gb, t1') in
        let cG_b = Context.append (Whnf.cnormGCtx (cG', t'))
                     begin
                       if Total.struct_smaller pat
                       then Total.mark_gctx cG_p
                       else cG_p
                     end
        in
        let cIH_b =
          let msub_cIH = cnormIHCtx' (cIH', t') in
          let sub_cIH = Total.shiftIH (Context.length cG_p) msub_cIH in
          sub_cIH
        in
        let (cD_b, cIH'', mfs', cid) =
          match index with
          | None ->
             let cD1 = Check.Comp.mvars_in_patt cD_b pat' in
             (cD1, LF.Empty, mfs, cid_prog)
          | Some ind ->
             if Total.is_inductive_split cD' cG' i
                && Total.struct_smaller pat'
             then
               begin
               let cD1 = Check.Comp.mvars_in_patt cD_b pat' in
               let cIH = Total.wf_rec_calls cD1 LF.Empty mfs in
               let cIH = fix_IH_args cIH cD1 in (* TODO:: correct cD? *)
               (cD1, cIH, mfs, cid_prog)
               end
             else
               (cD_b, LF.Empty, mfs, cid_prog)
        in
        let cD = Check.Comp.id_map_ind cD_b t' cD' in
        (* Fixing cD make sure the plicity of each mvar is correct *)
        let cD = gen_explicit_cD cD' pat' cD in
        let cIH_b = fix_IH_args cIH_b cD in (* TODO:: correct cD? *)
        let cG = cG_b in
        let cPool_b = updateCPool cPool cG k t' cD in
        let cIH0 = fix_IH_args (Total.wf_rec_calls cD cG_b mfs) cD in
        let cIH = unique_IH(Context.(append cIH_b (append cIH0 cIH''))) cD in
        let cG_a' = update_branch_cG_a (cG, cPool_b, cG_a) in
        let cD_a' = update_branch_cD_a (cD, cD_a) in
        dprintf
        begin fun p ->
           p.fmt "[split] new cD_a with %d mvars, new cG_a with %d possible split vars"
             (List.length cD_a)
             (List.length cG_a)
        end;
        let pat'' = match pat' with
         | Comp.PatAnn _ -> pat'
         | _ ->
            match i with
            | Comp.Var (_, k) ->
               let tau = find_comp_assumption (Whnf.cnormGCtx (cG', t')) k in
               let tau = match tau with
                 | Comp.TypInd tau' -> tau'
                 | _ -> tau
               in
               Comp.PatAnn (noLoc, pat, tau, Plicity.explicit)
            | _ -> pat'
         in
        (cD, cD_b, cD_a', cG, cG_p, cG_a', cIH, cPool_b, t', pat'', mfs', cid)
      in
      (* Compute the coverage goals for the type to split on. *)
      let cgs = generate_pattern_coverage_goals tau cD' cG' in
      dprintf
      begin fun p ->
      p.fmt
        "[split] Coverage Goals Generated"
      end;
      List.map get_branch cgs
    in
    (* Check that there is a variable left to split on *)
    if vars_left (cD_ann, cG_ann)
    then
      (
      let (cD_ann', cG_ann') = get_cases (cD, cG) (cD_ann, cG_ann) in
      dprintf
      begin fun p ->
      p.fmt "[split] CASES FOUND"
      end;

      (* Decides which var/mvar to split on, removing the chosen
         one from its respective annotated context.                 *)
      let (tau, i, index, cD_ann'', cG_ann'', k) =
        try
          choose_split (cD_ann', cG_ann') (cD, cG) ind
        with
        | End_Of_Search ->
           dprintf
             begin fun p ->
               p.fmt "[split] No more cases."
             end;
           raise End_Of_Search
      in
      let blist =
        (* Returns the branch list for the given split *)
        gen_branch_list i tau ms td (cD, cD_ann'') (cG, cG_ann'', k) cIH index
      in
      let splitDepth =
        (* Only increment split depth if split produces >1 case*)
        match List.length blist with
        | 1 -> dprintf
                 begin fun p ->
                   p.fmt "[split] INVERSION"
                 end;
               currSplitDepth
        | _ -> dprintf
                 begin fun p ->
                   p.fmt "[split] SPLIT - MULTIPLE CASES"
                 end;
               succ currSplitDepth
      in

      (* If the split depth is reached- undo the current loop. *)
      if checkDepth splitDepth maxSplitDepth
      then
        (dprintf
                           begin fun p ->
                             p.fmt "[split] NO MORE CASES"
                           end;
        raise End_Of_Search)
      else
        dprintf
          begin fun p ->
          p.fmt "[split] NUMBER OF CASES = %d"
            (List.length blist)
            end;
        try
          solve_branch (cD, (normCompGoal (cg, ms)))
            (currDepth, maxDepth, splitDepth, maxSplitDepth)
            blist (thm, td)
            (fun lst -> sc (Comp.Case (noLoc, Comp.PragmaCase, i, lst)))
         with
         | DepthReached _ | End_Of_Search ->
            split (cD, cD_ann'') (cG, cPool, cG_ann'') cIH cg ms sc
              (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
              (None, thm, td, cid_prog))
    else (* If not, we are finished proof search for this branch *)
      raise End_Of_Search

  and invert (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (ind, thm, td, cid_prog) =
    dprintf
      begin fun p ->
      p.fmt "Invert, %a"
        (printState cD cG cPool cIH cg) ms
      end;
    let gen_branch_list i tau ms mfs (cD', cD_a) (cG', cG_a, cPool, k) cIH'
          index =

      let tau =
        match i, tau with
        | Comp.AnnBox (_, (_, mC), _), Comp.TypBox (loc, mT) ->
           let _, mT', _ = Check.Comp.fixParamTyp mC mT in
           Comp.TypBox(loc, mT')
        | _ -> tau
      in

      (* Computes the subgoal for the given coverage goal *)
      let get_branch (cD_gb, (cG_gb, pat, tau_p), t) =
        let tau_p = Whnf.cnormCTyp tau_p in
        let t', t1', cD_b =
          (* Refine the pattern to compute the branch's
            meta-context, accounting for dependent pattern matching on
            `m`. *)
          Reconstruct.synPatRefine
            Location.ghost
            (Reconstruct.case_type (lazy pat) i)
            (cD', cD_gb) t (tau, tau_p) in
        let pat' = Whnf.cnormPattern (pat, t1') in
        let cG_p = Whnf.cnormGCtx (cG_gb, t1') in
        let cG_b = Context.append (Whnf.cnormGCtx (cG', t'))
                     begin
                       if Total.struct_smaller pat
                       then Total.mark_gctx cG_p
                       else cG_p
                     end
        in
        let cIH_b =
          let msub_cIH = cnormIHCtx' (cIH', t') in
          let sub_cIH = Total.shiftIH (Context.length cG_p) msub_cIH in
          sub_cIH
        in
        let (cD_b, cIH'', mfs', cid) =
          match index with
          | None ->
             let cD1 = Check.Comp.mvars_in_patt cD_b pat' in
             (cD1, LF.Empty, mfs, cid_prog)
          | Some ind ->
             if Total.is_inductive_split cD' cG' i
                && Total.struct_smaller pat'
             then
               begin
               let cD1 = Check.Comp.mvars_in_patt cD_b pat' in
               let cIH = Total.wf_rec_calls cD1 LF.Empty mfs in
               let cIH = fix_IH_args cIH cD1 in (* TODO:: correct cD? *)
               (cD1, cIH, mfs, cid_prog)
               end
             else
               (cD_b, LF.Empty, mfs, cid_prog)
        in
        dprintf
      begin fun p ->
      p.fmt "[invert cD analysis] cD = %a, cD' = %a, cD_gb = %a, cD_b = %a"
        (Printer.fmt_ppr_mctx) cD
        (Printer.fmt_ppr_mctx) cD'
        (Printer.fmt_ppr_mctx) cD_gb
      (Printer.fmt_ppr_mctx) cD_b
      end;
        let cD = Check.Comp.id_map_ind cD_b t' cD' in
        (* Fixing cD make sure the plicity of each mvar is correct *)
        let cD = gen_explicit_cD cD' pat' cD in
        let cIH_b = fix_IH_args cIH_b cD in (* TODO:: correct cD? *)
        let cG = cG_b in
        let cPool_b = updateCPool cPool cG k t' cD in
        let cIH = unique_IH(Context.(append cIH_b cIH'')) cD in
        let cG_a' = update_branch_cG_a (cG, cPool_b, cG_a) in
        let cD_a' = update_branch_cD_a (cD, cD_a) in
        (cD, cD_b, cD_a', cG, cG_p, cG_a', cIH, cPool_b, t', pat', mfs', cid)
      in
      (* Compute the coverage goals for the type to split on. *)
      let cgs = generate_pattern_coverage_goals tau cD' cG' in
      dprintf
      begin fun p ->
      p.fmt
        "[invert] Coverage Goals Generated"
      end;
      List.map get_branch cgs
    in

    let rec invert_all (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (ind, thm, td, cid_prog) =
      dprintf
      begin fun p ->
      p.fmt "Invert_all, %a"
        (printState cD cG cPool cIH cg) ms
      end;

      (* Check that there is a variable left to split on *)
      if vars_left (cD_a, cG_a)
      then
        (
        let (cD_a', cG_a') = get_cases (cD, cG) (cD_a, cG_a) in
        dprintf
        begin fun p ->
        p.fmt "[invert] CASES FOUND"
        end;

        (* Decides what to split on and updates the annotated contexts *)
        let (tau, i, index, cD_a'', cG_a'', k) =
          try
            choose_split (cD_a', cG_a') (cD, cG) ind
          with
          | End_Of_Search -> raise End_Of_Search
        in
        let blist =
          dprintf
           begin fun p ->
            p.fmt "[invert] Invert on: %a"
            (DP.fmt_ppr_cmp_exp cD cG DP.l0) i
           end;
          (* Returns the branch list for the given split *)
          gen_branch_list i tau ms td (cD, cD_a'') (cG, cG_a'', cPool, k) cIH index
        in
        dprintf
        begin fun p ->
        p.fmt "[invert] BRANCH LIST GENERATED"
        end;

        (if List.length blist = 1
        then
          let [(cD, cD_b, cD_a, cG, cG_p, cG_a, cIH_b, cPool,
                ms_b, pat, td_b, cid)] = blist in

          invert_all (cD, cD_a) (cG, cPool, cG_a) cIH_b
            (normCompGoal (cg, ms)) ms_b
            (fun e ->
              sc (Comp.Case (noLoc, Comp.PragmaCase, i,
                             [Comp.Branch(noLoc, LF.Empty, (cD, cG), pat,
                                          ms_b, e)])))
            (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
            (ind, thm, td, cid)
         else
           ((cD, cD_a), (cG, cPool, cG_a), cIH, cg, ms, sc,
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth),
             (ind, thm, td, cid_prog))
        ))
      else
        ((cD, cD_a), (cG, cPool, cG_a), cIH, cg, ms, sc,
           (currDepth, maxDepth, currSplitDepth, maxSplitDepth),
           (ind, thm, td, cid_prog))
    in

    let n =
      match currSplitDepth with
      | None -> 0
      | Some n -> n
    in

    dprintf
      begin fun p ->
        p.fmt
          "[invert] %d round(s) of inversion complete" n
      end;

    if n > 2 (* Do max 2 round of inversions. *)
    then ()
    else (* Otherwise invert all possible expressions *)
      let ((cD, cD_a), (cG, cPool, cG_a), cIH, cg, ms, sc,
           (currDepth, maxDepth, currSplitDepth, maxSplitDepth),
           (ind, thm, td, cid_prog))
      =
        invert_all (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
           (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
           (ind, thm, td, cid_prog)
      in
      try
        cgSolve' (cD, cD_a) (cG, cPool, cG_a) cIH (cg, ms) sc
          (currDepth, maxDepth, succ currSplitDepth, maxSplitDepth)
          (ind, thm, td, cid_prog) Blur
      with
      | DepthReached _ | End_Of_Search ->
         raise End_Of_Search

  (* We either focus on the right (proof search in LF to solve a TypBox) or
     focus our search on one of the available assumptions on the left     *)
  (* |- cD0
     cD0 |- cG0
     cD0 ; cG0 |- cg
     cD |- ms : cD0
     cD ; cG |- cg[ms]   where cG = [ms]cG0

     cD ; cG |- [cPsi |- tA][ms]
     cD ; cPsi |- tA'   where tA' = [ms]tA

     Else, focus on the left...                                           *)
  and focus (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
              (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                (ind, thm, td, thm_cid) =
    dprintf
      begin fun p ->
      p.fmt
        "Focus, %a"
        (printState cD cG cPool cIH cg) ms
      end;
    match cg with
    | Box (cPsi, g, Some M) ->
       (* We apply the msub here in case there are FREE MVARS that
          appear from unify   *)
       let ms = Whnf.cnormMSub ms in
       let cg' = normCompGoal (cg, ms) in
       let Box(cPsi',g',_) = cg' in
       let Atom tA = g' in
       let cltyp = LF.MTyp tA in
       let sc' =
         (fun (cPsi', tM) ->
           let dctx_hat = Context.dctxToHat cPsi' in
           let mfront = LF.ClObj (dctx_hat, LF.MObj tM) in
           let meta_obj = (noLoc, mfront) in
           let meta_typ = LF.ClTyp (cltyp, cPsi') in
           sc (Comp.Box(noLoc, meta_obj, meta_typ)))
       in
       dprintf begin fun p -> p.fmt "ENTERING [logic] [gSolve]" end;
       (try
          Solver.gSolve Solver.Empty cD (cPsi', Context.dctxLength cPsi')
            (g', S.id) sc' (Some 0, Some 3);
        with
        | Solver.End_Of_Search | Solver.DepthReached _ ->
           focusG (cD, cD_a) (cG, cPool, cPool, cG_a) cIH cg ms sc
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (thm, td, thm_cid);
           focusT (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (thm, td, thm_cid);
           focusIH (cD, cD_a) (cG, cPool, cG_a) (cIH, cIH) cg ms sc
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (thm, td, thm_cid);
           match maxSplitDepth with
           | Option.None ->
               (* If no split bound given, the most we do is invert. *)
               (invert (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
                   (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                   (ind, thm, td, thm_cid);
               raise End_Of_Search)
           | Option.Some 0 ->
               (* No splitting if explicitly told not to. *)
               raise End_Of_Search
           | Option.Some _ ->
               split (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
                 (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                 (ind, thm, td, thm_cid);
               raise End_Of_Search)

    | Box (cPsi, g, Some P) ->
       let cg' = normCompGoal (cg, ms) in
       let Box(_,g',_) = cg' in
       let Atom tA = g' in
       let cltyp = LF.PTyp tA in
       let sc' =
         (fun (cPsi', tM) ->
           let LF.Root (_,hd,_,_) = tM in
           let dctx_hat = Context.dctxToHat cPsi' in
           let mfront = LF.ClObj (dctx_hat, LF.PObj hd) in
           let meta_obj = (noLoc, mfront) in
           let meta_typ = LF.ClTyp (cltyp, cPsi') in
           sc (Comp.Box(noLoc, meta_obj, meta_typ)))
       in
       dprintf begin fun p -> p.fmt "ENTERING [logic] [gSolve]" end;
       (try
          Solver.gSolve Solver.Empty cD (cPsi, Context.dctxLength cPsi)
            (g, S.id) sc' (Some 0, Some 3)
       with
       | Solver.DepthReached _ | Solver.End_Of_Search->
          focusG (cD, cD_a) (cG, cPool, cPool, cG_a) cIH cg ms sc
            (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
            (thm, td, thm_cid);
          focusT (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
            (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
            (thm, td, thm_cid);
          focusIH (cD, cD_a) (cG, cPool, cG_a) (cIH, cIH) cg ms sc
            (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
            (thm, td, thm_cid);
          match maxSplitDepth with
          | Option.None ->
              (* If no split bound given, the most we do is invert. *)
              (invert (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
                (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                (ind, thm, td, thm_cid);
              raise End_Of_Search)
          | Option.Some 0 ->
              (* No splitting if explicitly told not to. *)
              raise End_Of_Search
          | Option.Some _ ->
              split (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
                (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                (ind, thm, td, thm_cid);
              raise End_Of_Search)

    | Atomic (name, spine) ->
       focusS name (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth) (thm, td, thm_cid);
       focusG (cD, cD_a) (cG, cPool, cPool, cG_a) cIH cg ms sc
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth) (thm, td, thm_cid);
       focusT (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth) (thm, td, thm_cid);
       focusIH (cD, cD_a) (cG, cPool, cG_a) (cIH, cIH) cg ms sc
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth) (thm, td, thm_cid);
       match maxSplitDepth with
       | Option.None ->
           (* If no split bound given, the most we do is invert. *)
           (invert (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
              (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
              (ind, thm, td, thm_cid);
           raise End_Of_Search)
       | Option.Some 0 ->
           (* No splitting if explicitly told not to. *)
           raise End_Of_Search
       | Option.Some _ ->
           split (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (ind, thm, td, thm_cid);
           raise End_Of_Search

  and solveIHblur (cD, cD_a) (cG, cPool, cG_a) cIH i sg ms sc
                    fS (cDepth, mDepth, currSplitDepth, maxSplitDepth)
                    (ind, thm, td, thm_cid)
                    (cG', cPool', cG_a') (cIH', cIH_all) cg =
    dprintf begin fun p -> p.fmt "solveIHblur" end;
    match sg with
    | Proved ->
       let cG' = Whnf.cnormGCtx (cG', LF.MShift 0) in
       let cPool' = cnormCPool (cPool', LF.MShift 0) in
       let i' = fS i in
       let i'' = Whnf.cnormExp (i', LF.MShift 0) in
       let sc = sc i'' in
       blurIH (cD, cD_a) (cG', cPool', cG_a') (cIH', cIH_all)
         cg ms sc (cDepth, mDepth, currSplitDepth, maxSplitDepth)
         (ind, thm, td, thm_cid)

    | Solve (sg', cg') ->
       let ms' = LF.MShift 0 in
       dprintf
         begin fun p ->
         p.fmt "Solve I.H's sub goals --blur, %a"
           (printState cD cG cPool cIH cg') ms'
         end;
       try
         (* NOTE:: this assumes the subgoal is an atomic type... *)
         focus (cD, cD_a) (cG, cPool, cG_a) cIH_all cg' ms'
           (fun e ->
             dprintf
         begin fun p ->
         p.fmt "[Solve Blur I.H's sub goals] SOLVED A SUBGOAL"
         end;
             try
               if (* If the thing we're solving for is already an assumption,
                     skip it. *)
                 in_cG cG' cG' cD
               then ()
               else
                 solveIHblur (cD, cD_a) (cG, cPool, cG_a) cIH i sg' ms
                   (fun i ->
                     sc (Comp.Apply (noLoc, i, e))) fS
                 (cDepth, mDepth, currSplitDepth, maxSplitDepth)
                 (ind, thm, td, thm_cid) (cG', cPool', cG_a')
                 (cIH', cIH_all) cg
             with
               | NotImplementedYet ->
                   solveIHblur (cD, cD_a) (cG, cPool, cG_a) cIH i sg' ms
                     (fun i -> sc (Comp.Apply (noLoc, i, e))) fS
                     (cDepth, mDepth, currSplitDepth, maxSplitDepth)
                     (ind, thm, td, thm_cid) (cG', cPool', cG_a')
                     (cIH', cIH_all) cg)
           (Some 0, Some 0, Some 0, Some 0) (None, thm, td, thm_cid)
       with
       | DepthReached b -> raise (DepthReached b)
       | End_Of_Search -> raise End_Of_Search

  and solveGblur (cD, cD_a) (cG, cPool, cG_a) cIH (sg, k) ms sc fS
                   (cDepth, mDepth, currSplitDepth, maxSplitDepth)
                     (ind, thm, td, thm_cid) =
    match sg with
    | Proved ->
       let i = (Comp.Var (noLoc, k)) in
       let i' = fS i in
       let i'' = Whnf.cnormExp (i', LF.MShift 0) in
       sc i''
    | Solve (sg', cg') ->
       dprintf
         begin fun p ->
         p.fmt "Solve Assumption's sub goals --blur, %a"
           (printState cD cG cPool cIH cg') ms
         end;
       focus (cD, cD_a) (cG, cPool, cG_a) cIH cg' ms
         (fun e -> solveGblur (cD, cD_a) (cG, cPool, cG_a) cIH (sg', k) ms
                   (fun i -> sc (Comp.Apply (noLoc, i, e)))
                   fS (cDepth, mDepth, currSplitDepth, maxSplitDepth)
                   (ind, thm, td, thm_cid))
         (Some 0, Some 0, Some 0, Some 0) (None, thm, td, thm_cid)

  (* Blurring/Focusing/Lemma application *)
  (* Same as focusing on the left, except here, the head doesn't have to
     match

                          cD ; . >> cG, Q' ==> Q
                          -------------------- blur
                           cD ; cG > Q' ==> Q

    We focus on an assumption, solving subgoals until we come across an
    atomic assumption (Q'). We then add it to our computation-level context
    (cG) and proceed to the uniform left phase (to unbox if necessary)     *)
  and blurIH (cD, cD_a) (cG, cPool, cG_a) (cIH, cIH_all) cg ms sc
               (cDepth, mDepth, currSplitDepth, maxSplitDepth)
               (ind, thm, td, thm_cid) =
    dprintf
      begin fun p ->
      p.fmt
        "Blur IH, %a"
        (printState cD cG cPool cIH_all cg) ms
      end;
    let is_arr tau =
      match tau with
      | Comp.TypArr (_) -> true
      | _ -> false
    in
    let is_box tau =
      match tau with
      | Comp.TypBox (_) -> true
      | _ -> false
    in
    (* Returns true if an argument of the IH is an uninstantiated mvar *)
    let rec mvars ih_args =
      match ih_args with
      | (Comp.M ((_, LF.ClObj (_, LF.PObj hd)), _)) :: xs
        | (Comp.M ((_, LF.ClObj (_, LF.MObj (LF.Root (_,hd,_,_)))), _)) :: xs->
         if Solver.uninstantiated hd then true else mvars xs
      | _ :: xs -> mvars xs
      | [] -> false
    in
    match cIH with
    | LF.Empty ->
       uniform_left (cD, cD_a) (cG, cPool, Emp, cG_a) cIH_all cg ms sc
         (cDepth, mDepth, currSplitDepth, maxSplitDepth)
         (ind, thm, td, thm_cid) No_Blur
    | LF.Dec(cIH', ((Comp.WfRec (name, ih_arg_lst, tau)) as dec))
         when (is_arr tau) ->
       let (ih_args, tau) = generate_new_IH dec in
       let {cHead=hd; cMVars; cSubGoals=sg} = C.comptypToCClause tau in
       let fS = create_IH_args (thm, ih_args, tau) cD in
       let names = Context.(names_of_mctx cD @ names_of_gctx cG) in
       let name = Name.gen_fresh_name names (Name.mk_name Name.NoName) in
       let pattern = Comp.PatVar (noLoc, 1) in
       let cPool' = Full (shift_cPool cPool 1,
                          ({cHead=hd;
                            cMVars=LF.Empty;
                            cSubGoals=Proved} , 1, Boxed)) in
       let tdecl = Comp.CTypDecl(name, hd, true) in
       let cG' = Whnf.extend_gctx cG (tdecl, LF.MShift 0) in
       let cG_a' = add_split 0 tdecl cG_a false in
       let Some cid = thm_cid in
       let cIH_all' = Total.shift cIH_all in
       let cIH'' = Total.shift cIH' in
       let i = Comp.Const(noLoc, cid) in
       (try
         solveIHblur (cD, cD_a) (cG, cPool, cG_a) cIH i sg ms
                       (fun i e ->
                         sc (Comp.Case (noLoc,
                                        Comp.PragmaNotCase,
                                        i,
                                        [Comp.Branch (noLoc,
                                                      LF.Empty,
                                                      (cD,
                                                       Whnf.cnormGCtx (cG', LF.MShift 0)),
                                                      pattern,
                                                      LF.MShift 0,
                                                      e)])))
           fS (cDepth, mDepth, currSplitDepth, maxSplitDepth)
           (ind, thm, td, thm_cid) (cG', cPool', cG_a') (cIH'', cIH_all') cg
       with
       | End_Of_Search | DepthReached _ ->
          blurIH (cD, cD_a) (cG, cPool, cG_a) (cIH', cIH_all) cg ms sc
            (cDepth, mDepth, currSplitDepth, maxSplitDepth)
            (ind, thm, td, thm_cid))

    | LF.Dec(cIH', ((Comp.WfRec (name, ih_arg_lst, tau)) as dec))
         when (is_box tau) && (not (mvars ih_arg_lst)) ->
       let (ih_args, tau) = generate_new_IH dec in
       let {cHead=hd; cMVars; cSubGoals=sg} = C.comptypToCClause tau in
       let fS = create_IH_args (thm, ih_args, tau) cD in
       let names = Context.(names_of_mctx cD @ names_of_gctx cG) in
       let name = Name.gen_fresh_name names (Name.mk_name Name.NoName) in
       let pattern = Comp.PatVar (noLoc, 1) in
       let cPool' = Full (shift_cPool cPool 1,
                          ({cHead=hd;
                            cMVars=LF.Empty;
                            cSubGoals=Proved} , 1, Boxed)) in
       let tdecl = Comp.CTypDecl(name, hd, true) in
       let cG' = Whnf.extend_gctx cG (tdecl, LF.MShift 0) in
       let cG_a' = add_split 0 tdecl cG_a false in
       let Some cid = thm_cid in
       let i = Comp.Const(noLoc, cid) in
       let cIH'' = Total.shift cIH' in
       let cIH_all' = Total.shift cIH_all in
       let exp = Whnf.cnormExp (fS i, LF.MShift 0) in
       dprintf
        begin fun p ->
        p.fmt
          "ADDING TO cG exp = %a"
          (Printer.fmt_ppr_cmp_exp cD cG') exp
        end;
       let sc' = (fun e -> sc (Comp.Case (noLoc,
                                        Comp.PragmaNotCase,
                                        exp,
                                        [Comp.Branch (noLoc,
                                                      LF.Empty,
                                                      (cD, cG'),
                                                      pattern,
                                                      LF.MShift 0,
                                                      e)])))
       in
       blurIH (cD, cD_a) (cG', cPool', cG_a') (cIH'', cIH_all') cg ms sc'
         (cDepth, mDepth, currSplitDepth, maxSplitDepth)
         (ind, thm, td, thm_cid)

    | LF.Dec(cIH', ((Comp.WfRec (name, ih_arg_lst, tau)) as dec))
         when (is_box tau) ->
       let (cG', cG_a', cPool', sc', cIH'', cIH_all') =
         find_all_occurances dec (cG, cPool, cG_a) sc cD thm_cid thm [] cIH' cIH_all in
       blurIH (cD, cD_a) (cG', cPool', cG_a') (cIH'', cIH_all') cg ms sc'
         (cDepth, mDepth, currSplitDepth, maxSplitDepth)
         (ind, thm, td, thm_cid)

    | LF.Dec(cIH', _) ->
       blurIH (cD, cD_a) (cG, cPool, cG_a) (cIH', cIH_all) cg ms sc
         (cDepth, mDepth, currSplitDepth, maxSplitDepth)
         (ind, thm, td, thm_cid)

  and blurGamma (cD, cD_a) (cG, cPool, cPool_all, cG_a) cIH cg ms sc
                  (cDepth, mDepth, currSplitDepth, maxSplitDepth)
                  (ind, thm, td, thm_cid) =
    dprintf
      begin fun p ->
      p.fmt
        "Blur Gamma, %a"
           (printState cD cG cPool cIH cg) ms
      end;
    match cPool with
    | Emp -> blurIH (cD, cD_a) (cG, cPool_all, cG_a) (cIH, cIH) cg ms sc
               (cDepth, mDepth, currSplitDepth, maxSplitDepth)
               (ind, thm, td, thm_cid)
    | Full (cPool',({cHead = hd;
                     cMVars = LF.Empty;
                     cSubGoals = (Solve (_,_)) as sg}, k', Boxed)) ->
       let fS = (fun s -> s) in
       let n = Name.mk_name Name.NoName in
       let name =
         let names = Context.(names_of_mctx cD @ names_of_gctx cG) in
         Name.gen_fresh_name names n
       in
       let pattern = Comp.PatVar (noLoc, 1) in
       let cPool_all' = Full (shift_cPool cPool_all 1, ({cHead=hd;
                                           cMVars=LF.Empty;
                                           cSubGoals=Proved} , 1, Boxed)) in
       let tdecl = Comp.CTypDecl(name, hd, true) in
       let cG' = Whnf.extend_gctx cG (tdecl, LF.MShift 0) in
       let cG_a' = add_split 0 tdecl cG_a false in
       let cIH' = Total.shift cIH in
       (try
         solveGblur (cD, cD_a) (cG, cPool_all, cG_a) cIH (sg, k') ms
           (fun i -> blurGamma (cD, cD_a) (cG', cPool', cPool_all', cG_a') cIH' cg ms
                       (fun e ->
                         sc (Comp.Case (noLoc,
                                        Comp.PragmaNotCase,
                                        i,
                                        [Comp.Branch (noLoc,
                                                      LF.Empty,
                                                      (cD, cG'),
                                                      pattern,
                                                      LF.MShift 0,
                                                      e)])))
                       (cDepth, mDepth, currSplitDepth, maxSplitDepth)
                       (ind, thm, td, thm_cid))
           fS (Some 0, Some 0, Some 0, Some 0) (ind, thm, td, thm_cid)
       with
       | End_Of_Search | DepthReached _ ->
          blurGamma (cD, cD_a) (cG, cPool', cPool_all, cG_a) cIH cg ms sc
            (cDepth, mDepth, currSplitDepth, maxSplitDepth)
            (ind, thm, td, thm_cid))

    | Full (cPool', ({cHead = hd; cMVars; cSubGoals = sg}, k', _)) ->
       blurGamma (cD, cD_a) (cG, cPool', cPool_all, cG_a) cIH cg ms sc
         (cDepth, mDepth, currSplitDepth, maxSplitDepth) (ind, thm, td, thm_cid)

  (* Unif. left phase, boxed assumptions in cG get unboxed into cD *)
  (* Preconditions:
                    |- cD0
                cD0 |- cG0
           cD0 ; cG |- cg
           cD       |- ms : cD0
            cD ; cG |- cg[ms]   where: cG = [ms]cG0
            cD      |- cG ~ (cPool,cPool_ret)

          cD        |- cIH          (context containin IHs)
          cD        |- thm          (original theorem)
     where sVar denotes the Induction Variable in thm
     ———————————————————————————————————-

     Uniform Left: unfolds eagerly positive propositions (box)
                   until we have a stable context cG containing only
                    Atomic Q and negative propositions (foral and impl).


     1. cD ; cG1, [U], cG2 |- cg[ms]
        cD, (U) |- ms' : cD0, (U)
        cD' ; cG' |- cg'[ms']   where cD' = cD, (U)
                                      cG' = [^1]cG1, (U), [^1]cG2

     2. cD ; cG1, tau, cG2 |- cg[ms]   where tau =/= [U]
        cD ; cG |- cg[ms]                                          *)
  and uniform_left (cD, cD_a) (cG, cPool, cPool_ret, cG_a) cIH cg ms sc
                     (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                       (ind, thm, td, thm_cid) blur =
    dprintf
      begin fun p ->
      p.fmt
        "Unif. Left, %a"
        (printState cD cG cPool cIH cg) ms
      end;
    let unbox cp =
      match cp with
      | (_cc, _k, Boxed) -> (_cc, _k, Unboxed)
    in
    match cPool with
    | Emp ->
       (match blur with
        (* We first see if any assumptions can be gained by burring *)
        | Blur ->
           blurGamma (cD, cD_a) (cG, cPool_ret, cPool_ret, cG_a) cIH cg ms sc
             (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
             (ind, thm, td, thm_cid)
        | _ ->
           (match ind with
           (* Once blurring is finished, we see if a split (m)var has been
              declared. If so, we save time running through the loop and
              immediatley split. *)
            | None | Some 0 ->
               focus (cD, cD_a) (cG, cPool_ret, cG_a) cIH cg ms sc
                 (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                 (ind, thm, td, thm_cid)
             | _ ->
               (try
                  split (cD, cD_a) (cG, cPool_ret, cG_a) cIH cg ms sc
                    (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                    (ind, thm, td, thm_cid)
                with
                | End_Of_Search | DepthReached _ ->
                   focus (cD, cD_a) (cG, cPool_ret, cG_a) cIH cg ms sc
                    (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                    (ind, thm, td, thm_cid)
                )))
    | Full (cPool', ((({cHead = Comp.TypBox(m, r);
                        cMVars = cmv;
                        cSubGoals = Proved }, k', Boxed)) as cP)) ->
       (* In this case, we want to "unbox" the assumption and add it to
          the cD, and will no longer consider it to be in cG. *)
       let n = get_name k' cG in
       let (cD_a', cG_a') = update_annotations (cD_a, cG_a) n in
       let name' = Name.mk_name (Whnf.newMTypName r) in
       let names = Context.(names_of_mctx cD @ names_of_gctx cG) in
       let name = Name.gen_fresh_name names name' in
       let mctx_decl = LF.Decl (name, r, Plicity.explicit, Inductivity.not_inductive) in
       let cD' = Whnf.extend_mctx cD (mctx_decl, LF.MShift 0) in
       let cG' = Whnf.cnormGCtx (cG, LF.MShift 1) in
       let cIH' = cnormIHCtx' (cIH, LF.MShift 1) in
       let box = Comp.Var (noLoc, k') in
       let pattern =
         Comp.PatMetaObj (noLoc,(noLoc,
          match r with
          | LF.ClTyp (LF.MTyp _, cPsi) ->
             let tM =
               LF.Root
                 ( noLoc
                 , LF.MVar (LF.Offset 1, S.id)
                 , LF.Nil
                 , Plicity.explicit
                 )
             in
             LF.ClObj (Context.dctxToHat (Whnf.cnormDCtx (cPsi, LF.MShift 1)),
                       LF.MObj tM)
          | LF.ClTyp (LF.PTyp _, cPsi) ->
             let hd = LF.PVar (1, S.id) in
             LF.ClObj (Context.dctxToHat (Whnf.cnormDCtx (cPsi, LF.MShift 1)),
                       LF.PObj hd)
          | LF.CTyp _ ->
             LF.CObj (LF.CtxVar (LF.CtxOffset 1))
                                )
           )
       in
       let sc' =
         (fun e ->
           sc (Comp.Case (noLoc, Comp.PragmaNotCase, box,
                          [Comp.Branch (noLoc, LF.Empty,
                                        (cD', LF.Empty),
                                        pattern, LF.MShift 1, e)]))) in
       let ms' = Whnf.mvar_dot1 ms in
       let cPool'' = cnormCPool (cPool', LF.MShift 1) in
       let cPool_ret' = prependToCPool (unbox cP) cPool_ret in
       let cPool_ret'' = cnormCPool (cPool_ret', LF.MShift 1) in
       let cg' = normCompGoal (cg, (LF.MShift 1)) in
       uniform_left (cD', cD_a') (cG', cPool'', cPool_ret'', cG_a') cIH' cg'
         ms' sc' (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
         (ind, thm, td, thm_cid) blur

    | Full (cPool', x) ->
       (* Otherwise we leave the assumption in cG *)
       let cPool_ret' = prependToCPool x cPool_ret in
       uniform_left (cD, cD_a) (cG, cPool', cPool_ret', cG_a) cIH cg ms sc
          (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
          (ind, thm, td, thm_cid) blur

  (* Unif. Right phase, computational and meta-assumptions are collected *)
  (*
      Preconditions:

               |- cD0
           cD0 |- cG0
     cD0 ; cG0 |- cg           (where cg = computation-level goal)
     cD        |- ms : cD0
     cD ; cG   |- cg[ms]   where cG = [ms]cG0

     cD        |- cIH          (context containing IHs)
     cD        |- thm          (original theorem)
     where sVar denotes the Induction Variable in thm
     ———————————————————————————————————-

     Uniform Right: unfolds eagerly negative propositions (forall, impl)
                    until we encounter a positive proposition (i.e. box U or Atomic Q)

   *)
  and uniform_right (cD, cD_a) (cG, cPool, cG_a) cIH cg ms sc
                      (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
                        k (ind, thm, td, thm_cid) blur =
    dprintf
      begin fun p ->
      p.fmt
        "Unif. Right, %a"
        (printState cD cG cPool cIH cg) ms
      end;
    match cg with
    (* Positive proposition - Synchronous *)
    | Box (_) | Atomic (_) ->
       uniform_left (cD, cD_a) (cG, cPool, Emp, cG_a) cIH cg ms sc
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth)
         (ind, thm, td, thm_cid) blur
    | Forall (tdecl, cg') ->
       (*
        cD ; cG |- (forall X:U. cg')[ms]
        cD, X:U |- ms' : cD0, X:U
        cD' ; cG' |- cg'[ms']   where: cD' = cD, X:U; cG' = [^1]cG
        *)
       (* In this case we gain an assumption in the meta-context *)
       let cD_a' =
         let var_in_theorem = Option.equal (=) (Some 0) currDepth in
         add_msplit k tdecl cD_a var_in_theorem in
       let cG_a' = mshift_cG_a cG_a in
       let cD' = Whnf.extend_mctx cD (tdecl, ms) in
       let name = LF.name_of_ctyp_decl tdecl in
       let cG' = Whnf.cnormGCtx (cG, LF.MShift 1) in
       let cIH' = cnormIHCtx' (cIH, LF.MShift 1) in
       let cPool' = cnormCPool (cPool, LF.MShift 1) in
       let sc' = (fun e -> sc (Comp.MLam (noLoc, name, e, Plicity.explicit))) in
       uniform_right (cD', cD_a') (cG', cPool', cG_a') cIH' cg'
         (Whnf.mvar_dot1 ms) sc'
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth) (k+1)
         (ind, thm, td, thm_cid) blur
    | Implies ((r, tdecl), cg') ->
       (*  cD ; cG |- (r -> cg')[ms]
        cD ; cG' |- cg'   where: cG' = cG, [ms]r            *)
       (* We gain an assumption for the computation context *)
       let cG_a' =
         let var_in_theorem = Option.equal (=) (Some 0) currDepth in
         add_split k tdecl cG_a var_in_theorem in
       let cc = C.cResToCClause (r, ms) in
       let cPool' = Full (shift_cPool cPool 1, (cc, 1, Boxed)) in
       let cG' = Whnf.extend_gctx cG (tdecl, ms) in
       let Comp.CTypDecl (name, _, _) = tdecl in
       let sc' = (fun e -> sc (Comp.Fn (noLoc, name, e))) in
       let cIH' = Total.shift cIH in
       uniform_right (cD, cD_a) (cG', cPool', cG_a') cIH' cg' ms sc'
         (currDepth, maxDepth, currSplitDepth, maxSplitDepth) (k+1)
         (ind, thm, td, thm_cid) blur

  (* cgSolve(cD                   : mctx;
             cG                   : gctx;
             cIH                  : ihctx;
             mq                   : mquery (cg, ms) where tau ~ cg;
             sc                   : exp_chk -> () success continuation;
             maxDepth             : int option   bound on iterative bounded
                                                 depth-first search;
             ind                  : int option   the position of the user-
                                                 supplied induction argument
                                                 in the theorem
                                                 the argument in tau';
             sp                   : int          indicates what kind of
                                                 automated splitting to
                                                 perform (none, only
                                                 inversions, all splits);
             thm                  : Comp.typ  = tau;
             cid                  : cid option   cid of the theorem name;
             mfs                  : total_dec list)


     cD'  |- tau
     cD   |- ms : cD'       ms is a meta-substitution that provides existential
                           variables (refs that will instantiated) for all
                           the bound meta-variables in cD'
     cD  |- [ms]tau (= mq)                                       *)
  let cgSolve cD cG cIH mq sc (maxDepth, ind, sp) (thm, thm_cid, mfs) =
    (* Populate the cPool given the cG *)
    let cPool = gen_cPool cG Emp in
    (* Populate the annotated contexts. *)
    let cD_a = gen_cD_a (rev_mctx cD) thm in
    let cG_a = gen_cG_a (rev_cG cG) thm cD in
    let maxSplitDepth = match sp with
      | 0 -> Some 0  (* No splitting.    *)
      | 1 -> None    (* Only inversions. *)
      | 2 -> Some 1  (* All splitting.   *)
    in
    try
      cgSolve' (cD, cD_a) (cG, cPool, cG_a) cIH mq sc
        (Some 0, maxDepth, Some 0, maxSplitDepth) (ind, thm, mfs, thm_cid)
        Blur
    with
    | DepthReached _ -> raise End_Of_Search

end

module Frontend = struct
  module P = Printer
  open Index

  exception Done                        (* Solved query successfully. *)
  exception AbortQuery of string        (* Abort solving the query.   *)

  (* exceeds B1 B2 = b
     True if B1 = * or B1 >= B2.
  *)
  let exceeds x y =
    match (x, y) with
    | (Some i, Some j) -> i >= j
    | (Some i, None) -> false
    | (None, _) -> true

  (* boundEq B1 B2 = b
     Equality function for bounds.
  *)
  let boundEq x y = Option.equal (=) x y

  (* lowerBound B1 B2 = min (B1, B2) *)
  let lowerBound x y =
    match (x, y) with
    | (Some i, Some j) -> Some (min i j)
    | (x, None) -> x
    | (None, y) -> y

  (* Abort query. *)
  let abort f =
    let s =
      f str_formatter ();
      flush_str_formatter ()
    in
    raise (AbortQuery s)

  (* checkSolutions e t s = () *)
  let checkSolutions e t s =
    match (e, t) with
    | (None, None) ->
       raise (AbortQuery "Query error: Wrong number of solutions -- \
              expected infinite, but found finite.")
    | _ ->
       if Bool.not (boundEq (lowerBound e t) (Some s))
       then
         abort
           begin fun ppf () ->
           fprintf ppf
             "Query error: Wrong number of solutions -- \
              expected %a in %a tries, but found %d."
             P.fmt_ppr_bound e
             P.fmt_ppr_bound t
             s
           end

  (* moreSolutions () = () *)
  let moreSolutions () =
    printf "More? ";
    match read_line () with
    | "y" | "Y" | ";" -> true
    | "q" | "Q" ->
       abort (fun ppf () -> fprintf ppf "Query error -- explicit quit.")
    | _ -> false

  (* solve q = () *)
  let solve sgnQuery =

    (* Keep track of no. of solutions found. *)
    let solutions = ref 0 in

    (* Type checking function. *)
    let check cPsi tM s =
      Check.LF.check LF.Empty
        cPsi (tM, S.id) (sgnQuery.skinnyTyp, s)
    in


    (* Initial success continuation. *)
    let scInit (cPsi, tM) =
      incr solutions;

      (* Rebuild the substitution and type check the proof term. *)
      if !Options.checkProofs
      then check cPsi tM (Convert.solToSub sgnQuery.instMVars); (* !querySub *)

      (* Print MVar instantiations. *)
      if !Options.chatter >= 3
      then
        begin
          fprintf std_formatter "@[<v>---------- Solution %d ----------@,[%a]@,%a@,@]"
            (!solutions)
            (P.fmt_ppr_dctx LF.Empty) cPsi
            P.fmt_ppr_inst sgnQuery.instMVars;
          (* Print proof term. *)
          begin match sgnQuery.optName with
          | Some n ->
             fprintf std_formatter "%a@\n"
               P.fmt_ppr_inst [(n, tM)]
          | None -> ()
          end;
          fprintf std_formatter "@\n"
        end;
      (* Interactive. *)
      if !Options.askSolution && not (moreSolutions ())
      then raise Done;

      (* Stop when no. of solutions exceeds tries. *)
      if exceeds (Some !solutions) sgnQuery.tries
      then raise Done
    in

    if Bool.not (boundEq sgnQuery.tries (Some 0))
    then
      begin
        if !Options.chatter >= 1
        then P.printQuery sgnQuery;
        try
          Solver.solve sgnQuery.cD LF.Null sgnQuery.query scInit (Some 100);
          (* Check solution bounds. *)
          checkSolutions sgnQuery.expected sgnQuery.tries !solutions
        with
        | Done -> printf "Done.\n"
        | AbortQuery s -> printf "%s\n" s
        | Solver.End_Of_Search ->
           (if (boundEq (lowerBound sgnQuery.expected sgnQuery.tries) (Some !solutions))
            then
              printf "Done.\n"
            else
              begin
               printf
               "Query error: Wrong number of solutions -- \
                expected %a in %a tries, but found %d. @\n \n"
               P.fmt_ppr_bound sgnQuery.expected
               P.fmt_ppr_bound sgnQuery.tries
               !solutions
              end)
        | _ -> ()
      end
    else if !Options.chatter >= 2
    then printf "Skipping query -- bound for tries = 0. @\n"

  (* Used when the auto-invert-solve and inductive-auto-solve tactics are
     called from Harpoon *)
  (* Will return the Beluga expression found by cgSolve for
     the given mquery                                          *)
  let msolve_tactic
        (cD, cG, cIH) (mquery, tau, instMMVars) depth
        (theorem, cid, invrt, mfs)  =

    dprintf
        begin fun p ->
        p.fmt
          "[msolve_tactic] BEGIN"
        end;

    (* Transform signature into clauses. *)
    Index.robStore ();

    (* This reference will hold the return of cgSolve
       (i.e. the Beluga proof term with type tau)     *)
    let exp = ref (Comp.Impossible
                     (Location.ghost, Comp.Var
                                          (Location.ghost, 0)))
    in

    (* Remove duplicates from cIH *)
    let cIH' =
      let cIH' = CSolver.remove_mvar_subs cIH in
      let unique_cIH = CSolver.unique_IH cIH' cD in
      let v_free_cIH = CSolver.remove_IH unique_cIH in
      CSolver.cnormIHCtx' (CSolver.fix_IH_args v_free_cIH cD, LF.MShift 0)
    in

    (* Put the mmVar list in correct format. *)
    let mmVars =
      let rec clean_instMMVars mmvars =
        match mmvars with
        | (n, (l, mf)) :: xs ->
           (n, mf) :: (clean_instMMVars xs)
        | [] -> []
      in
      clean_instMMVars instMMVars
    in

    (* Replaces any instantiated mmvars/mvars with their instantiations.  *)
    (* Will fail during check otherwise...                                *)
    let remove_hd_mvars hd =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_hd_mvars]"
        end;
      match hd with
      | LF.MMVar ((mmvar, ms), s) ->
         let Some iterm = !(mmvar.LF.instantiation) in
         (match iterm with
         | LF.IHead hd -> hd
         | _ -> raise NotImplementedYet)
      | LF.MPVar ((mmvar, ms), s) ->
         let Some iterm = !(mmvar.LF.instantiation) in
         (match iterm with
         | LF.IHead hd -> hd
         | _ -> raise NotImplementedYet)
      | LF.MVar (LF.Inst mmvar, s) ->
         let Some iterm = !(mmvar.LF.instantiation) in
         (match iterm with
         | LF.IHead hd -> hd
         | _ -> raise NotImplementedYet)
      | _ -> hd

    in
    let rec remove_sub_mvars s =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_sub_mvars]"
        end;
      match s with
      | LF.Dot (LF.Head hd, s') ->
         LF.Dot (LF.Head (remove_hd_mvars hd), remove_sub_mvars s')
      | LF.Dot (LF.Obj norm, s') ->
         LF.Dot (LF.Obj (remove_norm_mvars norm), remove_sub_mvars s')
      | _ -> s

    and remove_norm_mvars norm =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_norm_mvars]"
        end;
      let remove_head_mvars hd =
        match hd with
        | LF.MMVar ((mmvar, ms), s) ->
           let Some iterm = !(mmvar.LF.instantiation) in
           iterm
        | LF.MPVar ((mmvar, ms), s) ->
           let Some iterm = !(mmvar.LF.instantiation) in
           iterm
        | LF.MVar (LF.Inst mmvar, s) ->
           let Some iterm = !(mmvar.LF.instantiation) in
           iterm
        | _ -> LF.IHead hd
      in
      match norm with
      | LF.Lam (l, n, norm') -> LF.Lam (l, n, remove_norm_mvars norm')
      | LF.Root (l, hd, spine, p) ->
         (match remove_head_mvars hd with
         | LF.IHead hd -> LF.Root (l, hd, remove_spine_mvars spine, p)
         | LF.INorm norm -> norm)
      | LF.Clo (norm', s) ->
         LF.Clo (remove_norm_mvars norm', remove_sub_mvars s)
      | _ -> raise NotImplementedYet

    and remove_spine_mvars spine =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_spine_mvars]"
        end;
      match spine with
      | LF.Nil -> spine
      | LF.App (norm, spine') ->
         LF.App (remove_norm_mvars norm, remove_spine_mvars spine')
      | LF.SClo (spine', s) ->
         LF.SClo (remove_spine_mvars spine', remove_sub_mvars s)
    in

    let rec remove_typ_mvars tA =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_typ_mvars]"
        end;
      match tA with
      | LF.Atom (l, cid, spine) ->
         LF.Atom (l, cid, (remove_spine_mvars spine))
      | LF.PiTyp ((td, d, p), tA') -> LF.PiTyp ((td, d, p), remove_typ_mvars tA')
      | LF.Sigma (_) -> tA
      | LF.TClo (tA', s) -> raise NotImplementedYet
    in

    let rec remove_dctx_mvars cpsi =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_dctx_mvars]"
        end;
      match cpsi with
      | LF.DDec (cpsi', LF.TypDecl (n, tA)) ->
         LF.DDec (remove_dctx_mvars cpsi',
                  LF.TypDecl (n, remove_typ_mvars tA))
      | LF.DDec (cpsi', td) -> LF.DDec (remove_dctx_mvars cpsi', td)
      | _ -> cpsi
    in

    let remove_clobj_mvars co =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_clobj_mvars]"
        end;
      match co with
      | LF.MObj norm -> LF.MObj (remove_norm_mvars norm)
      | LF.PObj hd -> LF.PObj (remove_hd_mvars hd)
      | LF.SObj s -> LF.SObj (remove_sub_mvars s)
    in

    let remove_mfront_mvars mf =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_mfront_mvars]"
        end;
      match mf with
      | LF.CObj cpsi -> LF.CObj (remove_dctx_mvars cpsi)
      | LF.ClObj (dctx_hat, clobj) ->
         LF.ClObj (dctx_hat, remove_clobj_mvars clobj)
      | _ -> mf
    in

    let remove_ctyp_mvars ct =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_ctyp_mvars]"
        end;
      match ct with
      | LF.ClTyp (LF.MTyp tA, dctx) ->
         LF.ClTyp (LF.MTyp  (remove_typ_mvars tA), remove_dctx_mvars dctx)
      | LF.ClTyp (LF.PTyp tA, dctx) ->
         LF.ClTyp (LF.PTyp  (remove_typ_mvars tA), remove_dctx_mvars dctx)
      | LF.ClTyp (LF.STyp (sv, cpsi), dctx) ->
         LF.ClTyp (LF.STyp (sv, remove_dctx_mvars cpsi),
                   remove_dctx_mvars dctx)
      | _ -> ct
    in

    let rec remove_msub_mvars ms =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_msub_mvars]"
        end;
      match ms with
      | LF.MDot (mf, ms') ->
         LF.MDot (remove_mfront_mvars mf, remove_msub_mvars ms')
      | _ -> ms
    in

    let rec remove_pspine_mvars pspine =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_pspine_mvars]"
        end;
      match pspine with
      | Comp.PatApp (l, pat, pspine') ->
         Comp.PatApp (l, remove_pat_mvars pat, remove_pspine_mvars pspine')
      | _ -> pspine

    and remove_pat_mvars pat =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_pat_mvars]"
        end;
      match pat with
      | Comp.PatMetaObj (l, (l', mf)) ->
         Comp.PatMetaObj (l, (l', remove_mfront_mvars mf))
      | Comp.PatConst (l, cid, pspine) ->
         Comp.PatConst (l, cid, remove_pspine_mvars pspine)
      | Comp.PatVar (_) -> pat
      | Comp.PatAnn (l, pat', tau, plicity) ->
         Comp.PatAnn (l, remove_pat_mvars pat', tau, plicity)
      | _ -> raise NotImplementedYet
    in

    let rec remove_exp_mvars e =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_exp_mvars]"
        end;
      match e with
      | Comp.Fn (l, n, e) -> Comp.Fn (l, n, remove_exp_mvars e)
      | Comp.MLam (l, n, e, p) -> Comp.MLam (l, n, remove_exp_mvars e, p)
      | Comp.Box (l, (l', mf), mt) ->
         Comp.Box (l, (l', remove_mfront_mvars mf), remove_ctyp_mvars mt)
      | Comp.Case (l, c, s, bl) ->
         Comp.Case (l, c, remove_exp_mvars s, remove_branch_mvars bl)
      | Comp.Var (_) | Comp.DataConst (_) | Comp.Const (_) -> e
      | Comp.MApp (l, s, (l', mf), mt, p) ->
         Comp.MApp (l, remove_exp_mvars s, (l', remove_mfront_mvars mf),
                    remove_ctyp_mvars mt, p)
      | Comp.Apply (l, s, e) ->
         Comp.Apply (l, remove_exp_mvars s, remove_exp_mvars e)
      | Comp.AnnBox (l, (l2, mf), mT) ->
         Comp.AnnBox (l, (l2, remove_mfront_mvars mf), remove_ctyp_mvars mT)
      | _ -> dprintf
        begin fun p ->
        p.fmt
          "[remove_exp_mvars] NOT IMPLEMENTED YET"
        end; raise NotImplementedYet

    and remove_branch_mvars bl =
      dprintf
        begin fun p ->
        p.fmt
          "[remove_branch_mvars]"
        end;
      match bl with
      | (Comp.Branch (l, cD, bc, pat, ms, e)) :: bl' ->
         (Comp.Branch (l, cD, bc, remove_pat_mvars pat,
                       remove_msub_mvars ms, remove_exp_mvars e)) :: bl'
      | [] -> bl
    in

    (* Success continuation function *)
    let scInit e =
      let e = Whnf.cnormExp(e, LF.MShift 0) in
      dprintf
        begin fun p ->
        p.fmt
          "FINAL CHECK before fix e = %a"
          (Printer.fmt_ppr_cmp_exp cD cG) e
        end;
      let e = CSolver.fix_plicities e cD in
      dprintf
        begin fun p ->
        p.fmt
          "FINAL CHECK e = %a"
          (Printer.fmt_ppr_cmp_exp cD cG) e
        end;
      try
      Check.Comp.check None cD cG mfs ~cIH:cIH' e
        (tau, (Convert.solToMSub mmVars));
      exp := (remove_exp_mvars e);
      raise Done
      with
      | Done -> raise Done
      | _ ->
         begin
           fprintf std_formatter "Proof Search failed. Term found does not type check : %a"
                 (Printer.fmt_ppr_cmp_exp cD cG) e
         end;
         raise NotImplementedYet

    in

    let (cgoal, ms) = mquery in
    dprintf (fun p ->
      p.fmt "[msolve_tactic] \
              Goal = %a \
              cD = %a \
              cG = %a \
             theorem = %a \ "
        (Printer.fmt_ppr_cmp_goal cD) (cgoal, LF.Shift 0)
        (Printer.fmt_ppr_mctx) cD
        (Printer.fmt_ppr_gctx cD) cG
        (Printer.fmt_ppr_cmp_typ cD) theorem);

    (* We only specify an index if we are doing full proof search (inductive-auto-solve), otherwise none is given *)
    let get_ind_index tau invert =
        (* Finds the index of the tagged inductive variable to split on, if any*)
      let rec ind_index tau n =
        match tau with
        | Comp.TypPiBox(_, LF.Decl(_, _, _, inductive), _)
             when Inductivity.is_inductive inductive -> Some n
        | Comp.TypPiBox(_, _, tau') -> ind_index tau' (n + 1)
        | Comp.TypInd(_) -> Some n
        | Comp.TypBox(_, _) -> None
        | Comp.TypBase(_, _, _) -> None
        | Comp.TypArr(_, tau1, tau2) ->
           let ind = ind_index tau1 n in
           match ind with
           | None -> ind_index tau2 (n + 1)
           | _ -> ind
      in
      match invert with
      | 2 -> ind_index theorem 1
      | _ -> None
    in

    (try
       CSolver.cgSolve cD cG cIH' mquery scInit (depth, get_ind_index theorem invrt, invrt) (theorem, Some cid, mfs);
       raise NotImplementedYet
    with
    | Done ->
       Index.clearIndex ();
       Some (!exp)
    | _ ->
       Index.clearIndex ();
       None)


end

(* Interface *)

let storeQuery p (tA, i) cD e t =
  Index.storeQuery (p, (tA, i), cD, e, t)

(* runLogic () = ()
   If !enabledLogic, run the logic programming engine. Otherwise
   do nothing, i.e. return unit.
*)
let runLogic () =
  if !Options.enableLogic
  then
    begin
      (* Transform signature into clauses. *)
      Index.robStore ();
      (* Optional: Print signature clauses. *)
      if !Options.chatter >= 4
      then Printer.printAllSig ();
      (* Solve! *)
      Index.iterQueries Frontend.solve;
      (* Clear the local storage.  *)
      Index.clearIndex ()
    end


let runLogicOn n (tA, i) cD e t  =
  Index.singleQuery (n, (tA, i), cD, e, t) Frontend.solve

let prepare () =
  Index.clearIndex ();
  Index.robStore ();

(*
let runLogicOn n (cD, cPsi, tA, i) e t  =
  Index.singleQuery (n, (tA, i), e, t) Frontend.solve
 *)
