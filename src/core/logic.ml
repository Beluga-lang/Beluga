open Support.Equality
(* module Logic *)
(* author:
   Costin Badescu
   Jacob Thomas Errington
   Johanna Schwartzentruber
 *)

open Support
module S = Substitution.LF
open Format
open Syntax.Int

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
    | LF.PiTyp ((tD, Plicity.Implicit), tA') ->
       typToClause' (LF.DDec (eV, tD)) cG tA' (cS, dS, dR)
    | LF.PiTyp ((LF.TypDecl (_, tA), Plicity.Explicit), tB) ->
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
    | LF.PiTyp ((tdec, Plicity.Implicit), tA') ->
       All (tdec, typToGoal tA' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (x, tA) as tdec, Plicity.Explicit), tB) ->
       Impl ((typToRes tA (cS, dS, dR), tdec), typToGoal tB (cS, dS, dR + 1))
    | LF.Atom _ ->
       Atom (Shift.shiftAtom tA (-cS, -dS, dR))

  and typToRes tM (cS, dS, dR) =
    match tM with
    | LF.PiTyp ((tD, Plicity.Implicit), tM') ->
       Exists (tD, typToRes tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (_, tA), Plicity.Explicit), tB) ->
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
       let loc = Syntax.Loc.ghost in
       let ctyp = LF.ClTyp (LF.MTyp tA, cPsi) in
       Comp.TypBox (loc, ctyp)
    | Box (cPsi, Atom tA, Some P) ->
       let loc = Syntax.Loc.ghost in
       let ctyp = LF.ClTyp (LF.PTyp tA, cPsi) in
       Comp.TypBox (loc, ctyp)

  (* Converts an atomic comp goal to a Comp.TypBase *)
  let atomicToBase atomic =
    let rec asToMs aS =
      match aS with
      | End -> Comp.MetaNil
      | Spine (aS', (mt, mf, pl)) ->
         Comp.MetaApp ((Syntax.Loc.ghost, mf), mt, asToMs aS', pl)
    in
    match atomic with
    | Atomic (cid, aS) ->
       let loc = Syntax.Loc.ghost in
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
       LF.Root (Syntax.Loc.ghost, LF.MVar (u, S.id), LF.Nil, Plicity.explicit)
    | LF.PiTyp ((LF.TypDecl (x, tA) as tD, _), tB) ->
       LF.Lam
         ( Syntax.Loc.ghost
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

  let rec mctxToMSub cD (mV, ms) fS =
    let etaExpand' cD cPsi (tA, ms) name =
      let cvar = Whnf.newMMVar (Some name) (cD, cPsi, tA) Plicity.implicit Inductivity.not_inductive in
       LF.Root (Syntax.Loc.ghost, LF.MMVar((cvar, ms), S.id), LF.Nil, Plicity.explicit)
    in
    let noLoc = Syntax.Loc.ghost in
    match mV with
    | LF.Empty -> (ms, fS)
    | LF.Dec (mV',
              LF.Decl (name, ((LF.ClTyp (LF.MTyp tA, cPsi)) as ctyp), plicity, _)) ->
       let (ms', fS') = mctxToMSub cD (mV', ms) fS in
       let tM = etaExpand' cD cPsi (tA, ms) name in
       let dctx_hat = Context.dctxToHat cPsi in
       let mfront = LF.ClObj (dctx_hat, LF.MObj tM) in
       (LF.MDot (mfront, ms'),
        (fun s ->
          fS' (Comp.MApp (noLoc, s, (noLoc, mfront), ctyp, plicity))))
    | LF.Dec (mV',
              LF.Decl (name, ((LF.ClTyp (LF.PTyp tA, cPsi)) as ctyp), plicity, _)) ->
       let (ms', fS') = mctxToMSub cD (mV', ms) fS in
       let tM = etaExpand' cD cPsi (tA, ms') name in
       let LF.Root (noLoc, hd, LF.Nil, _) = tM in
       let dctx_hat = Context.dctxToHat cPsi in
       let mfront =
         LF.ClObj (dctx_hat, LF.PObj hd) in
       (LF.MDot (mfront, ms'),
        (fun s ->
          fS' (Comp.MApp (noLoc, s, (noLoc, mfront), ctyp, plicity))))
    | LF.Dec (mV',
              LF.Decl (name, ((LF.CTyp (Some cid)) as ctyp), plicity, inductivity)) ->
       let (ms', fS') = mctxToMSub cD (mV', ms) fS in
       let dctx = Whnf.newCVar (Some name) cD (Some cid) plicity inductivity in
       let mfront = LF.CObj (LF.CtxVar dctx) in
       (* let mf = Whnf.cnormMFt mfront ms' in *)
       (LF.MDot (mfront, ms'),
        (fun s -> fS'
                    (Comp.MApp (noLoc, s, (noLoc, mfront), ctyp, plicity))))
    | _ -> raise NotImplementedYet


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
      | LF.PiTyp ((LF.TypDecl (x, tA), Plicity.Implicit), tB) when i > 0 ->
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
          let LF.Decl(x, mtyp, plicity, inductivity) = mdecl in  (* where mtyp = (LF.MTyp tA, cPsi) *)
          (* generate a meta-variable (instantiated by unification) of type (LF.MTyp tA, cPsi)
             and make sure it is an mfront *)
          let mmV = Whnf.newMMVar' (Some x) (LF.Empty, mtyp) plicity inductivity in
          let mfront = Whnf.mmVarToMFront loc mmV mtyp in
          comptypToMQuery' (tau', i - 1) (LF.MDot (mfront, ms)) ((x, (loc, mfront)) :: xs)
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
  open Store

  let types = Hashtbl.create 0          (* typConst Hashtbl.t          *)

  let compITypes = Hashtbl.create 0     (* compTypConst Hashtbl.t      *)

  let compTTypes = Hashtbl.create 0     (* comp theorem Hashtbl.t      *)

  type inst = (Name.t *  LF.normal)    (* I ::= (x, Y[s]) where Y is an MVar        *)
                                        (* where mf contains an MMVar *)
  type sgnQuery =
    { query : query                   (* Query ::= (g, s)            *)
    ; typ : LF.typ                    (* Query as LF.typ.            *)
    ; skinnyTyp : LF.typ              (* Query stripped of E-vars.   *)
    ; optName : Name.t option        (* Opt. name of proof term.    *)
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
    let { Cid.Term.Entry.typ = tA; _ } = Cid.Term.get cidTerm in
    (cidTerm, Convert.typToClause tA)

  (* Computation Theorem Constants  *)
  let compileSgnCClause cidTerm =
    let { Cid.Comp.Entry.typ = tau; _ } = Cid.Comp.get cidTerm in
    (cidTerm, Convert.comptypToCClause tau)

  (* Computation Inductive Constants *)
  let compileSgnConstClause cidCompTerm =
    let { Cid.CompConst.Entry.typ = tau; _ } = Cid.CompConst.get cidCompTerm in
    (cidCompTerm, Convert.comptypToCClause tau)


  (* termName c = Name.t
     Get the string representation of term constant c.
  *)
  let termName cidTerm =
    (Cid.Term.get cidTerm).Cid.Term.Entry.name

  let compName cidTerm =
    (Cid.Comp.get cidTerm).Cid.Comp.Entry.name

  let compConstName cidTerm =
    (Cid.CompConst.get cidTerm).Cid.CompConst.Entry.name

  (* storeTypConst c = ()
     Add a new entry in `types' for type constant c and fill the DynArray
     with the clauses corresponding to the term constants associated with c.
     The revIter function serves to preserve the order of term constants
     intrinsic to the Beluga source file, since the constructors for c are
     listed in reverse order.
  *)
  let storeTypConst (cidTyp, typEntry) =
    let typConstr = !(typEntry.Cid.Typ.Entry.constructors) in
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

  (* storeCompConst c = ()
     Add a new entry in `compTTypes' for comptype constant c and fill the
     DynArray with the clause corresponding to the comp. theorem
     associated  with c.
   *)

  let storeCompConst (cidTyp, typEntry) =
    (* TODO:: Typ or CompTyp?? *)
    let typConst = addComp cidTyp in
    addSgnClause typConst (compileSgnCClause cidTyp)


  (* storeCompTypConst c = ()
     Add a new entry in `Comptypes' for comptype constant c and fill the
     DynArray with the clauses corresponding to the comp. term constants
     associated  with c.
   *)


  let storeCompTypConst (cidCompTyp, compTypEntry) =
    let ctypConstr = !(compTypEntry.Cid.CompTyp.Entry.constructors) in
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

  (* robStore () = ()
     Store all type constants in the `types' table.
  *)
  let robStore () =
    try
      List.iter storeTypConst (Cid.Typ.current_entries ())
    with
    | _ -> ()

  (* robSecondStore () = ()
     Store all comptype theorem constants in the `compTTypes' table.
  *)
  let robSecondStore () =
    try
      List.iter storeCompConst (Cid.Comp.current_entries ())
    with
    | _ -> ()

  (* robThirdStore () = ()
     Store all  comptyp Inductive constants in the `compITypes' table.
  *)
  let robThirdStore () =
    try
      List.iter storeCompTypConst (Cid.CompTyp.current_entries ())
    with
    | _ -> ()

  (* Store all signature constants in their respective tables *)
  let robAll () =
    robStore ();
    robSecondStore ();
    robThirdStore ()


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
    robAll ();
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
  module P = Pretty.Int.DefaultPrinter
  open Index

  let fmt_ppr_dctx cD ppf cPsi =
    P.fmt_ppr_lf_dctx cD P.l0 ppf cPsi

  let fmt_ppr_gctx cD ppf cG =
    P.fmt_ppr_cmp_gctx cD P.l0 ppf cG

  let fmt_ppr_mctx ppf cD =
    P.fmt_ppr_lf_mctx P.l0 ppf cD

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

  (** Prints each comp. subgoal with a leading `<-`. *)
  let fmt_ppr_csubgoals cD ppf subgoals =
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut
         (fun ppf sg ->
           fprintf ppf "<- %a"
             (fmt_ppr_cmp_goal cD) (sg, S.id)))
         (list_of_subgoals subgoals)


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
    fprintf std_formatter "%a.@.@."
      fmt_ppr_sgn_query q

  (* Prints all LF signatures *)
  let printSignature () =
    iterAllSClauses
      (fun w ->
        fprintf std_formatter "%a@."
          fmt_ppr_sgn_clause w)

  (* Prints all the computation theorems *)
  let printCompSignature () =
    iterAllTSClauses
      (fun w ->
        fprintf std_formatter "%a@."
          fmt_ppr_sgn_cclause w)

  (* Prints all Inductive type signatures *)
  let printCompConstSignature () =
    iterAllISClauses
      (fun w ->
        fprintf std_formatter "%a@."
          fmt_ppr_sgn_compclause w)


  let printAllSig () =
    printSignature ();
    printCompSignature ();
    printCompConstSignature ()

 (* Prints the current state of proof loop
    (used for debugging) *)

  (* let printState cD cG cg ms =
    let fmt_ppr_gctx cD ppf cG =
      P.fmt_ppr_cmp_gctx cD P.l0 ppf cG
    in
    let fmt_ppr_mctx ppf cD =
      P.fmt_ppr_lf_mctx P.l0 ppf cD
    in
    fprintf std_formatter "Current State: \n
                 cD = %a \n
                 cG = %a \n
                 goal = %a \n
                 ms = %a \n"
        (fmt_ppr_mctx) cD
        (fmt_ppr_gctx cD) cG
        (fmt_ppr_cmp_goal cD) (cg, S.id)
        (Pretty.Int.DefaultPrinter.fmt_ppr_lf_msub cD Pretty.Int.DefaultPrinter.l0) ms *)

end

module Solver = struct
  module P = Printer.P
  module U = Unify.StdTrail
  module C = Convert
  module I = Index

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

  let uninstantiated hd =
      match hd with
    | LF.MMVar ((mmvar, ms'), s)
         when mmvar.LF.instantiation.contents == None ->
       true
    | LF.MVar (LF.Inst mmvar, s)
         when mmvar.LF.instantiation.contents == None ->
       true
    | LF.MPVar ((mmvar, ms'), s)
         when mmvar.LF.instantiation.contents == None ->
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

  (* Instantiate the nth position of sub s with the front ft. *)
  let rec instantiate_sub (n, s) ft curr =
    match s with
    | LF.Dot (_, s') when n == curr ->
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
  let rec gSolve dPool cD (cPsi, k) (g, s) sc =
    match g with
    | Atom tA ->
       matchAtom dPool cD (cPsi, k) (tA, s) sc

    | Impl ((r, (LF.TypDecl (x, _) as tD)), g') ->
       (* extend the dynamic pool with the new assumption and prove the conclusion *)
       let dPool' =
         DynCl (dPool, (C.resToClause (r, s), k))
       in
       gSolve dPool' cD (LF.DDec (cPsi, S.decSub tD s), k + 1) (g', S.dot1 s)
         (fun (u, tM) -> sc (u, LF.Lam (Syntax.Loc.ghost, x, tM)))

    | All (LF.TypDecl (x, _) as tD, g') ->
       (* we *don't* get an assumption from a forall; it's just a parameter.
          So we just prove the conclusion in an extended context. *)
       gSolve dPool cD (LF.DDec (cPsi, S.decSub tD s), k + 1) (g', S.dot1 s)
         (fun (u, tM) -> sc (u, LF.Lam (Syntax.Loc.ghost, x, tM)))

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
    | LF.Empty -> raise NotImplementedYet
    | LF.Dec (cD', LF.Decl (_, LF.CTyp (_), _, _)) ->
       solve_sub_delta (cD_all, cD', k+1, cPhi, dPool) (tA, s, curr_sub) (u, s_all) (goal, s_goal)
    | LF.Dec (cD', LF.Decl (_, LF.ClTyp (cltyp, cPsi), _, _)) ->
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
           instantiate_sub (curr_sub, s_all) (LF.Head(LF.MVar(LF.Offset k, LF.Shift 0))) 1

           with
           | U.Failure _ ->
                U.unifyTyp cD_all cPhi'
                  (Whnf.cnormTyp(tA, LF.MShift k), LF.Shift 0)
                  (Whnf.cnormTyp(tA', LF.MShift k), LF.Shift 0);
                U.unifyTyp cD_all cPhi (goal, s_goal) (LF.TClo(u, s_all), LF.Shift 0);
                (* Instantiate the correct sub in s_all with the front *)
           instantiate_sub (curr_sub, s_all) (LF.Head(LF.MVar(LF.Offset k, LF.Shift 0))) 1
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
         check_sub (Whnf.normSub s_all) then s_all
       else raise NotImplementedYet
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
         | U.Failure _ | NotImplementedYet -> raise NotImplementedYet)

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
         | U.Failure _ | NotImplementedYet -> raise NotImplementedYet)

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
         | U.Failure _ | NotImplementedYet -> raise NotImplementedYet)
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
         | U.Failure _ | NotImplementedYet -> raise NotImplementedYet)
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
         | U.Failure _ | NotImplementedYet -> raise NotImplementedYet)
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
         | U.Failure _ | NotImplementedYet -> raise NotImplementedYet)
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
  and matchAtom dPool cD (cPsi, k) (tA, s) sc =
    (* some shorthands for creating syntax *)
    let root x = LF.Root (Syntax.Loc.ghost, x, LF.Nil, Plicity.explicit) in
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
             try
               trail
                 begin fun () ->
                 unify cD cPsi (tA, s) (dCl.tHead, s')
                   begin fun () ->
                   solveSubGoals dPool cD (cPsi, k) (dCl.subGoals, s')
                     begin fun (u, tS) ->
                     let tM =
                       LF.Root
                         ( Syntax.Loc.ghost
                         , LF.BVar (k - k')
                         , fS (spineFromRevList tS)
                         , Plicity.explicit
                         )
                     in
                     sc (u, tM)
                     end
                   end
                 end
             with
             | U.Failure _ -> ()
           end;
         matchDProg dPool')

      | Empty ->
         matchSig (cidFromAtom tA)

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
                    else raise NotImplementedYet

                 | LF.STyp _ ->
                    (* ignore substitution variables for now *)
                    ()
                 end
             with
             | U.Failure s -> ()
           end;
           loop cD' (k + 1)
        | LF.Dec (cD', _dec) ->
           loop cD' (k + 1)
      in
      loop cD0 1

    (* matchSig c = ()
       Try all the clauses in the static signature with head matching
       type constant c.
     *)
     and matchSig cidTyp =
       I.iterSClauses (fun w -> matchSgnClause w sc) cidTyp

    (* matchSgnClause (c, sCl) sc = ()
       Try to unify the head of sCl with A[s]. If unification succeeds,
       attempt to solve the subgoals of sCl.
     *)
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
                  ( Syntax.Loc.ghost
                  , LF.Const (cidTerm)
                  , fS (spineFromRevList tS)
                  , Plicity.explicit
                  )
              in
              sc (u, tM)
              end
            end
        with
        | U.Failure _ -> ()
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
       Any effect of (sc S).
   *)
  and solveSubGoals dPool cD (cPsi, k) (cG, s) sc =
    match cG with
    | True -> sc (cPsi, [])
    | Conjunct (cG', g) ->
       gSolve dPool cD (cPsi, k) (g, s)
         (fun (u, tM) ->
           solveSubGoals dPool cD (cPsi, k) (cG', s)
             (fun (v, tS) ->  sc (v, tM :: tS))
         )

  (* solve (g, s) sc = ()
     Invariants:
       Empty |- g[s] : goal
       sc : dctx * normal -> unit

     Effects:
       Same as gSolve.
  *)
  let solve cD cPsi (g, s) sc =
    gSolve Empty cD (cPsi, Context.dctxLength cPsi) (g, s) sc

end

module CSolver = struct
  module U = Unify.StdTrail
  module C = Convert
  module I = Index

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

  let noLoc = Syntax.Loc.ghost

  exception AbortMQuery of string

  (* unify (A, s) (B, s') sc = ()
     Invariants:
       sc : unit -> unit

     Effects:
       Instatiation of MMVars in ms and ms'.
       Any effect of (sc ()).
    *)
  let unify cD sA sB sc =
    U.unifyCompTyp cD sA sB;
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

    (* Abort mquery. *)

  let abort f =
    let s =
      f str_formatter ();
      flush_str_formatter ()
    in
    raise (AbortMQuery s)

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
         when mmvar.LF.instantiation.contents == None ->
       hd
    | LF.MPVar ((mmvar, ms'), s)
         when mmvar.LF.instantiation.contents == None ->
       hd
    | LF.MVar (LF.Inst mmvar, s)
         when mmvar.LF.instantiation.contents == None ->
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

  (* Applies the msub to the comp goal. *)
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
         let mf' = Whnf.cnormMFt mf ms in
         Spine (aS'', (mt, mf', pl))
    in
    match cg with
    | Box (cPsi, Atom typ, _lfTyp) ->
       let typ' = Whnf.cnormTyp (typ, ms) in
       let cPsi' = Whnf.cnormDCtx (cPsi, ms) in
       Box (cPsi', Atom typ', _lfTyp)
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

  let rec normSubGoals (sg, ms) cD =
    match sg with
    | Proved -> sg
    | Solve (sg', cg) ->
       let cg' = normCompGoal (cg, ms) in
       Solve (normSubGoals (sg', ms) cD, cg')

  (* Applies the msub to the ihctx (excluding the mmvars and mvars) *)
  let cnormIHCtx' (ihctx, ms) =
    let cnormIHArg (a, t) =
      match a with
      | Comp.M cM ->
         Comp.M (cnormMetaObj (cM, t))
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

  let rec cnormCPool (cPool, ms) cD =
    match cPool with
    | Emp -> cPool
    | Full (cPool', ({cHead = hd; cMVars = mV; cSubGoals = sg}, _k, _s)) ->
       let cPool'' = cnormCPool (cPool', ms) cD in
       let hd' = Whnf.cnormCTyp (hd, ms) in
       let sg' = normSubGoals (sg, ms) cD in
       Full (cPool'', ({cHead = hd'; cMVars = mV; cSubGoals = sg'}, _k, _s))

   (*
  (* mctx -> ctyp_decl *)
  let least_cases cD =
    let consOfTyp cltyp =
      let typ =
        match cltyp with
        | LF.MTyp tA | LF.PTyp tA -> tA
      in
      let cid = Solver.cidFromAtom typ in
      let typEntry = Store.Cid.Typ.get cid in
      let typConstructors = !(typEntry.Store.Cid.Typ.Entry.constructors) in
      (List.length typConstructors, typConstructors)
    in
    let rec find_max cD cltyp_d k lst =
      match cD with
      | LF.Empty -> (cltyp_d, lst)
      | LF.Dec (cD', ((LF.Decl (name, LF.ClTyp (cltyp', _cPsi), _)) as cltyp_d')) ->
         let (k', lst') = consOfTyp cltyp' in
         if k' < k then
           find_max cD' cltyp_d' k' lst'
         else
           find_max cD' cltyp_d k lst
    in
    match cD with
    | LF.Empty -> raise NotImplementedYet
    | LF.Dec (cD', ((LF.Decl (name, LF.ClTyp (cltyp, _cPsi), _)) as cltyp_d)) ->
       let (k, lst) = consOfTyp cltyp in
       find_max cD' cltyp_d k lst
    *)

  (* rev_ms ms k =
       reverses ms with first sub MShift k
 *)

  let rev_ms ms k =
    let rec rev ms ms_ret =
      match ms with
      | LF.MShift k' -> ms_ret
      | LF.MDot (mf, ms') -> rev ms' (LF.MDot (mf, ms_ret))
    in
    rev ms (LF.MShift k)

  (* Generates, from cIH, a new cIH where each entry is unique. *)
  let unique_IH cIH cD =

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

  let remove_mvar_subs cIH =
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
      | LF.PiTyp ((td, dep), tA') ->
         LF.PiTyp ((td, dep), remove_typ tA)
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
      | Comp.M (loc, mf) -> Comp.M (loc, remove_mf mf)
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
           if mmvar.LF.instantiation.contents == None
           then
             normal :: (list_of_mvars_spine spine)
           else
             list_of_mvars_spine spine
        | LF.Root(_, LF.MMVar ((mmvar,_),_), spine, _) ->
           if mmvar.LF.instantiation.contents == None
           then
             normal :: (list_of_mvars_spine spine)
           else
             list_of_mvars_spine spine
        | LF.Root(_, LF.MPVar ((mmvar,_),_), spine, _) ->
           if mmvar.LF.instantiation.contents == None
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
               when mmvar.LF.mmvar_id == cid -> true
          | (LF.Root(_, LF.MPVar(((mmvar, _),_)), _, _)) :: xs
               when mmvar.LF.mmvar_id == cid -> true
          | (LF.Root(_, LF.MVar(LF.Inst mmvar,_), _, _)) :: xs
               when mmvar.LF.mmvar_id == cid -> true
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
           | LF.Root (_, ((LF.PVar (_)) as hd), _, _) ->
              (Comp.M (noLoc, LF.ClObj ((None, 0), LF.PObj hd)))
              :: (fix_args xs mvars')
           | LF.Root (_, ((LF.MPVar ((mmvar,_), _)) as hd), _, _) ->
              let dctx_hat = match mmvar.LF.typ with
                | LF.ClTyp (_, dctx) -> Context.dctxToHat dctx
                | _ -> raise NotImplementedYet
              in
              (Comp.M (noLoc, LF.ClObj (dctx_hat, LF.PObj hd)))
              :: (fix_args xs mvars')
           | LF.Root (_, LF.MMVar ((mmvar,_), _), _, _) ->
              let dctx_hat = match mmvar.LF.typ with
                | LF.ClTyp (_, dctx) -> Context.dctxToHat dctx
                | _ -> raise NotImplementedYet
              in
              (Comp.M (noLoc, LF.ClObj (dctx_hat, LF.MObj x)))
              :: (fix_args xs mvars')
           | LF.Root (_, LF.MVar (LF.Inst mmvar, _), _, _) ->
              let dctx_hat = match mmvar.LF.typ with
                | LF.ClTyp (_, dctx) -> Context.dctxToHat dctx
                | _ -> raise NotImplementedYet
              in
              (Comp.M (noLoc, LF.ClObj (dctx_hat, LF.MObj x)))
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

  let rec mSpineToPSpine mS =
    match mS with
    | Comp.MetaNil -> Comp.PatNil
    | Comp.MetaApp (mO, mT, mS', plicity) ->
       Comp.PatApp (noLoc, (Comp.PatMetaObj (noLoc, mO)), mSpineToPSpine mS')

  let rec cgSolve' (cD: LF.mctx) (cG: Comp.gctx) (cPool: cPool)
            (mq:mquery) (sc: Comp.exp -> unit) (currDepth: bound) (maxDepth: bound) (blur: blur_it) =

    (* fprintf std_formatter
          "No solution found: Maximum depth reached! -- \
          Current Depth %a , Maximum Depth allowed %a \n"
          Printer.fmt_ppr_bound currDepth
          Printer.fmt_ppr_bound maxDepth; *)
    if (checkDepth currDepth maxDepth)
    then
        abort
        begin fun ppf () ->
        fprintf std_formatter
          "No solution found: Maximum depth reached! -- \
          Current Depth %a , Maximum Depth allowed %a \n\n"
          Printer.fmt_ppr_bound currDepth
          Printer.fmt_ppr_bound maxDepth
        end
    else
    begin
      let ((cg:comp_goal), (ms:LF.msub)) = mq in
      uniform_right cD cG cPool cg ms sc currDepth maxDepth blur
    end

  (* Stable phase : cD ; cG >> . ==> e : Q


       cD ; cGamma  >> e : Q   (prove Q from the stable context cGamma and meta-context cD)


       CHOICE:

      1)   Q = Box(cPsi, A)      cD ; cG >> box(cPsihat.M) :Box(cPsi, A)

             cD ; cPsi ==>  M: A     (this is solve!)
            -----------------------------------------------------    [in Harpoon some msolve (args) ]
               cD ; cG >> box(cPsihat.M) : Box(cPsi, A)                (assumes that cG is stable)


      2) Q = Inductive(Atomic)

         matchCompAtom (Signature) (a) = computation-level clauses c (for example Ev_z) that have a (for example Even) in its cHead
         this will result in some subgoals (cgᵢ)

         for all i.   cD ; cG ===>  eᵢ :  cgᵢ   (uniform right phase)
         --------------------------------------------------------------------[in Harpoon some auto-solve]
         cD ; cG >> c e₁ ...en  : Inductive(a, meta-spine)                       (assumes that cG is stable)


      For example:

      inductive Even: [ |- nat] -> ctype =
      | Ev_z : Even [ |- z]
      | Ev_ss: Pi N:[ |- nat]. Even [ |- N] -> Even [ |- suc (suc N)]


    3) Q = Box(cPsi, A) or Inductive(a, meta-spine)  we solve it using some assumption from cG

      cG might contain  f: tau₁ -> Q  , x:tau₁   ===> Q


      focus left  (on some comp_goal cgᵢ in cG)

        cD ; cGamma > f:cgᵢ ===> e : Q
       --------------------------------- transition to focus left
       cD ; cGamma  >> e : Q




    cD ; cGamma > e e₁ : cg₂ ==>   Q     cD ; cGamma ===> e1 : cg₁
    -----------------------------------------------------------------
     cD ; cGamma > e : cg₁ -> cg₂ ==>   Q



    cD ; cGamma > e C : [C/X]cg₂ ==>   Q
    ----------------------------------------
     cD ; cGamma > e : Pi X:U. cg₂ ==>   Q


    ----------------------------------------
    cD ; cGamma  > e : Q   ====> Q
   *)

  and solveSubGoals cD cG cPool (sg, k) ms mV sc fS currDepth maxDepth =
    match sg with
    | Proved ->
       let e' = (Comp.Var (noLoc, k)) in
       let e = fS e' in
       let e = Whnf.cnormExp (e, LF.MShift 0) in
       sc e
    | Solve (sg', cg') ->
        (*printf "solve gamma SG \n";
        let cg = normCompGoal (cg', ms) in
        Printer.printState cD cG cg ms;*)
       cgSolve' cD cG cPool (cg', ms)
         (fun e ->
           solveSubGoals cD cG cPool (sg', k) ms mV
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS currDepth maxDepth)
         (succ currDepth) maxDepth No_Blur


  and solveCClauseSubGoals cD cG cPool cid sg ms mV sc fS currDepth maxDepth =
   (* fprintf std_formatter "CID = %a \n"
      Name.pp (Index.compConstName cid); *)
    match sg with
    | Proved ->
       let e' = (Comp.DataConst (noLoc, cid)) in
       let e = fS e' in
       let e = Whnf.cnormExp (e, LF.MShift 0) in
       sc e
    | Solve (sg', cg') ->
       (*printf "solve sig SG \n";
       let cg = normCompGoal (cg', ms) in
       Printer.printState cD cG cg ms;*)
       cgSolve' cD cG cPool (cg', ms)
         (fun e ->
           solveCClauseSubGoals cD cG cPool cid sg' ms mV
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS currDepth maxDepth)
             (succ currDepth) maxDepth No_Blur

  and solveTheoremSubGoals cD cG cPool cid sg ms mV sc fS currDepth maxDepth =
     (* fprintf std_formatter "CID = %a \n"
       Name.pp (Index.compName cid); *)
    match sg with
    | Proved ->
       let e' = (Comp.Const (noLoc, cid)) in
       let e = fS e' in
       let e = Whnf.cnormExp (e, LF.MShift 0) in
       sc e
    | Solve (sg', cg') ->
       (*printf "solve thm SG \n";
       let cg = normCompGoal (cg', ms) in
       Printer.printState cD cG cg ms;*)
       cgSolve' cD cG cPool (cg', ms)
         (fun e ->
           solveTheoremSubGoals cD cG cPool cid sg' ms mV
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS currDepth maxDepth)
            (succ currDepth) maxDepth No_Blur

  (* We focus on one of the computation-type theorems *)
  and focusT cD cG cPool cg ms sc currDepth maxDepth =
     (* printf "focus Theorem \n";
     Printer.printState cD cG cg ms; *)
    let matchThm (cid, sCCl) =
      if (* Check to see if the comp goal is the head of the assumption *)
         matchHead sCCl.cHead cg;
      then
        (let (ms', fS) = C.mctxToMSub cD (sCCl.cMVars, LF.MShift 0) (fun s -> s) in
         let ms'' = rev_ms ms' (Context.length (sCCl.cMVars)) in
         let tau = if isBox cg then C.boxToTypBox cg else C.atomicToBase cg in
        (try
           Solver.trail
             begin fun () ->
               unify cD (tau, ms) (sCCl.cHead, ms'')
                 (fun () ->
                  solveTheoremSubGoals cD cG cPool cid sCCl.cSubGoals ms'' sCCl.cMVars
                    sc fS currDepth maxDepth)
              end
         with
         | U.Failure _ -> ()))
      else
        ()
    in
    Index.iterAllTSClauses (fun w -> matchThm w)

  (* Focus on the clause in the static Comp signature with head matching
     type constant c. *)
  and focusS cidTyp cD cG cPool cg ms sc currDepth maxDepth =
     (* printf "focus Sig \n";
     Printer.printState cD cG cg ms; *)
    let matchSig (cidTerm, sCCl) sc =
      let (ms', fS) = C.mctxToMSub cD (sCCl.cMVars, LF.MShift 0) (fun s -> s) in
      let ms'' = rev_ms ms' (Context.length (sCCl.cMVars)) in
      let tau = C.atomicToBase cg in
      (try
         Solver.trail
           begin fun () ->
           unify cD (tau, ms) (sCCl.cHead, ms'')
               (fun () ->
                solveCClauseSubGoals cD cG cPool cidTerm sCCl.cSubGoals ms'' sCCl.cMVars
                  sc fS currDepth maxDepth)
            end
         with
         | U.Failure _ -> ())
    in
    I.iterISClauses (fun w -> matchSig w sc) cidTyp


(*      Focusing Gamma Phase:   cD ; cG  > tau ==> e: Q


      if our cPool is empty,
        we finish the loop.
      otherwise, we investigate each clause in cPool, starting
        with most recently added
        if the head of the clause we are looking at
          matches cg, we focus on that clause, and try to solve
          the subgoals (if any)
     *)

  (* We focus on one of the computation assumptions in cPool/Gamma *)
  and focusG cD cG cPool cPool_all cg ms sc currDepth maxDepth =
    (* printf "focus Gamma \n";
    Printer.printState cD cG cg ms;  *)
    match cPool with
    | Emp -> ()
    | Full (cPool', ({cHead = hd; cMVars; cSubGoals = sg}, k', Boxed)) ->
       if (* Check to see if the comp goal is the head of the assumption *)
         matchHead hd cg
       then (* If so, try to solve the subgoals *)
         let (ms', fS) = C.mctxToMSub cD (cMVars, LF.MShift 0) (fun s -> s) in
         let ms'' = rev_ms ms' (Context.length (cMVars)) in
         let tau = if isBox cg then C.boxToTypBox cg else C.atomicToBase cg in
         (* Trail to undo MVar instantiations. *)
         (try
           Solver.trail
             begin fun () ->
             unify cD (tau, ms) (hd, ms'')
               (fun () ->
               solveSubGoals cD cG cPool_all (sg, k') ms'' cMVars
                 sc fS currDepth maxDepth)
             end
         with
         | U.Failure _ -> ());
         focusG cD cG cPool' cPool_all cg ms sc currDepth maxDepth

       else (* Otherwise, try the remaining comp assumptions *)
         focusG cD cG cPool' cPool_all cg ms sc currDepth maxDepth
    | Full (cPool', cc) -> focusG cD cG cPool' cPool_all cg ms sc currDepth maxDepth

  and focus cD cG cPool cg ms sc currDepth maxDepth =
    (*printf "FOCUS \n";
    let cg' = normCompGoal (cg, ms) in
    Printer.printState cD cG cg' ms;*)
    match cg with
    | Box (cPsi, g, Some M) ->
       (* If our goal is of box type, we first try to find the
          proof term in the LF level, otherwise we focus on
          an assumption in our computation context cG          *)
       let cg' = normCompGoal (cg, ms) in
       let Box(_, g', _) = cg' in
       let Atom tA = g' in
       (* note, we take the goal's type because the main check
          is checking the meta_obj against meta_typ of the goal *)
       let cltyp = LF.MTyp tA in
       let sc' =
         (fun (cPsi', tM) ->
           let dctx_hat = Context.dctxToHat cPsi' in
           let mfront = LF.ClObj (dctx_hat, LF.MObj tM) in
           let meta_obj = (noLoc, mfront) in
           let meta_typ = LF.ClTyp (cltyp, cPsi') in
           sc (Comp.Box(noLoc, meta_obj, meta_typ)))
       in
       Solver.solve cD cPsi (g', S.id) sc';
       focusG cD cG cPool cPool cg ms sc currDepth maxDepth;
       focusT cD cG cPool cg ms sc currDepth maxDepth;
     (*  msplit cD cD cG cPool cg ms sc currDepth maxDepth; *)
    | Box (cPsi, g, Some P) ->
       let Atom tA = g in
       let cltyp = LF.PTyp tA in
       let sc' =
         (fun (cPsi', tM) ->
           let LF.Root (_, hd, _, _) = tM in
           let dctx_hat = Context.dctxToHat cPsi' in
           let mfront = LF.ClObj (dctx_hat, LF.PObj hd) in
           let meta_obj = (noLoc, mfront) in
           let meta_typ = LF.ClTyp (cltyp, cPsi') in
           sc (Comp.Box(noLoc, meta_obj, meta_typ)))
       in
       Solver.solve cD cPsi (g, S.id) sc';
       focusG cD cG cPool cPool cg ms sc currDepth maxDepth;
       focusT cD cG cPool cg ms sc currDepth maxDepth;
    | Atomic (name, spine) ->
       (* If our goal is of atomic type, we first try looking for
          a solution in the computation signature, cG, and in the
          theorems                                                *)
       focusS name cD cG cPool cg ms sc currDepth maxDepth;
       focusG cD cG cPool cPool cg ms sc currDepth maxDepth;
       focusT cD cG cPool cg ms sc currDepth maxDepth;

  and solveGblur cD cG cPool (sg, k) ms sc fS cDepth mDepth =
    match sg with
    | Proved ->
       let i = (Comp.Var (noLoc, k)) in
       let i' = fS i in
       let i'' = Whnf.cnormExp (i', LF.MShift 0) in
       sc i''
    | Solve (sg', cg') ->
       try
         focus cD cG cPool cg' ms
           (fun e -> solveGblur cD cG cPool (sg', k) ms
                     (fun i -> sc (Comp.Apply (noLoc, i, e)))
                     fS cDepth mDepth)
           (Some 0) (Some 0)
       with
       | AbortMQuery s -> printf "%s\n" s

  and blurGamma cD cG cPool cPool_all cg ms sc cDepth mDepth =
    match cPool with
    | Emp -> uniform_left cD cG cPool Emp cg ms sc cDepth mDepth No_Blur
    | Full (cPool',({cHead = hd;
                     cMVars;
                     cSubGoals = (Solve (_,_)) as sg}, k', Boxed))
         when cMVars == LF.Empty ->
       let fS = (fun s -> s) in
       let n = Name.mk_name Name.NoName in
       let name =
         let names = Context.(names_of_mctx cD @ names_of_gctx cG) in
         Name.gen_fresh_name names n
       in
       let pattern =
         match hd with
         | Comp.TypBox (_, meta_typ) ->
            Comp.PatVar (noLoc, 1)
         | Comp.TypBase (_, cid, mS) ->
            (* TODO:: Not sure if this correct... *)
            Comp.PatConst (noLoc, cid, mSpineToPSpine mS)
       in
       let cPool_all' = Full (shift_cPool cPool_all 1, ({cHead=hd;
                                           cMVars=LF.Empty;
                                           cSubGoals=Proved} , 1, Boxed)) in
       let tdecl = Comp.CTypDecl(name, hd, true) in
       let cG' = Whnf.extend_gctx cG (tdecl, LF.MShift 0) in
       (try
         solveGblur cD cG cPool_all (sg, k') ms
           (fun i -> blurGamma cD cG' cPool' cPool_all' cg ms
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
                       cDepth mDepth)
           fS (Some 0) (Some 0)
       with
       | AbortMQuery s -> printf "%s\n" s)

    | Full (cPool', ({cHead = hd; cMVars; cSubGoals = sg}, k', _)) ->
       blurGamma cD cG cPool' cPool_all cg ms sc cDepth mDepth

    (* uniform_left_ cD cG cG_ret cPool cPool_ret cg ms sc =
         (cD', cPool_ret, cG_ret, sc')
        (where the sc continuation builds skeleton term
        ex. (fn e -> let box X = x in ..... in e ))

    Pre-conditions:

       cD : meta-context
       cPool, cPool_ret : computation assumptions in clausal form
       cPool  ~~ cG
       cPool_ret ~~ cG_ret
       k = |cPool|
       cg : comp_goal
       ms : msub
       sc : exp_chk -> unit


      if cD |- cPool   (list of comp_goals is well-formed in cD)
      then
         cD' |- cPool_ret  where

      cD'       : meta-context and is an extension of cD
      cPool_ret : cPool where each entry is a clause representing
                  either an implication, a universal, or Atomic (Inductive)
      cG_ret    : stable computation-context and is a reduction of cG



      Uniform Phase on the left:   cD ; cG  ==> e : Q


        cD ; (cG @ cG_ret) |- e : Q


                cD, X:U; cG >> cG_ret => e : Q
       ------------------------------------------------ box left
        cD; cG, x:[U] >> cG_ret => let box X = x in e : Q


       tau =/= [U]   D; cG >> x:tau, cG_ret => e : Q   (x:tau, cG_ret ~~ {cHead; MV; subG}, cPool_ret)
       ------------------------------------------------------------------------------------ tau is left synchronous
                             cD; cG, x:tau >> cG_ret => e : Q


               cD ; cG_ret  >> e : Q           (prove Q from the stable context
       ----------------------------------   cG and meta-context cD)
            cD ; . >> cG_ret  => e  : Q



     cG (gctx)  ~~ cPool (clausal comp assumptions)

     *)


  and uniform_left cD cG cPool cPool_ret cg ms sc currDepth maxDepth blur =
 (*   printf "UNIFORM LEFT \n";
    let cg'= normCompGoal (cg, ms) in
    Printer.printState cD cG (cg') ms; *)
    let unbox cp =
      match cp with
        | (_cc, _k, Boxed) -> (_cc, _k, Unboxed)
    in
    match cPool with
    | Emp ->
       (match blur with
        (* We first see if any assumptions can be gained by burring *)
        | Blur ->
           blurGamma cD cG cPool_ret cPool_ret cg ms sc
             currDepth maxDepth
        | _ ->
           focus cD cG cPool_ret cg ms sc currDepth maxDepth)
    | Full (cPool', ((({cHead = Comp.TypBox(m, r); cMVars = cmv;cSubGoals = Proved }, k', Boxed)) as cP)) ->
       (* In this case, we want to "unbox" the assumption and add it to
          the cD.
          When an assumption gets unboxed, we no longer consider it in Gamma. *)
       let name = Name.mk_name (Whnf.newMTypName r) in
       let mctx_decl = LF.Decl (name, r, Plicity.explicit, Inductivity.not_inductive) in
       let cD' = Whnf.extend_mctx cD (mctx_decl, ms) in
       let cG' = Whnf.cnormGCtx (cG, LF.MShift 1) in
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
             LF.ClObj (Context.dctxToHat (Whnf.cnormDCtx (cPsi, LF.MShift 1)), LF.MObj tM)
          | LF.ClTyp (LF.PTyp _, cPsi) ->
             let hd = LF.PVar (1, S.id) in
             LF.ClObj (Context.dctxToHat (Whnf.cnormDCtx (cPsi, LF.MShift 1)), LF.PObj hd)
          | LF.CTyp _ ->
             LF.CObj (LF.CtxVar (LF.CtxOffset 1))
                                )
           )
       in
       let sc' =
         (fun e ->
           sc (Comp.Case (noLoc, Comp.PragmaNotCase, box,
                          [Comp.Branch (noLoc, LF.Empty, (cD', LF.Empty), pattern, LF.MShift 1, e)]))) in
       let ms' = Whnf.mvar_dot1 ms in
       let cPool'' = cnormCPool (cPool', LF.MShift 1) cD' in
       let cPool_ret' = prependToCPool (unbox cP) cPool_ret in
       let cPool_ret'' = cnormCPool (cPool_ret', LF.MShift 1) cD' in
       let cg' = normCompGoal (cg, (LF.MShift 1)) in
       uniform_left cD' cG' cPool'' cPool_ret'' cg' ms' sc' currDepth maxDepth blur
    | Full (cPool', x) ->
       (* Otherwise we leave the assumption in cG *)
       let cPool_ret' = prependToCPool x cPool_ret in
       uniform_left cD cG cPool' cPool_ret' cg ms sc currDepth maxDepth blur


       (* uniform_right cD cG cPool cg ms sc =
         (cD', cG', cPool', cg', sc')
        (where the sc continuation builds skeleton term
        ex. (fn e -> let box X = x in ..... in e ))

    Pre-conditions:

       cD : meta-context
       cPool : computation assumptions in clausal form
       cPool  ~~ cG
       cg : comp_goal
       ms : msub
       sc : exp_chk -> unit

      if cD ; cG |- cg   (comp_goal is well-formed in cD and cG)
      then
         cD' ; cG' |- cg'  where

      cD'       : meta-context holding meta assumption from cg
      cPool'    : cPool where each entry is a clause representing
                  a computation assumption
      cG'       : computation-context holding computation assumptions from cg
      cg'       : comp_goal is either a Box or an Atomic comp goal

       Uniform Right Phase :

       cD; cG >> .  => e : Q
       ------------------------ (where Q is either Box or Atomic (Inductive) type)
       cD; cG => e : Q


        cD; cG, x:tau  => e : cg   (cG, x:tau ~~ cPool, {cHead; MV; subG})
       ------------------------------------------------------------------ tau is left synchronous
               cD;cG => fn x -> e  : (res , tau) -> cg

         cD, X:U ; cG => e : cg
       ------------------------------------------------------
       cD ; cG  => mlam X -> e  : forall X:U. cg

       *)

     (* First we break our goal down into an atomic one *)
  and uniform_right cD cG cPool cg ms sc currDepth maxDepth blur =
    (*printf "UNIFORM RIGHT \n";
    Printer.printState cD cG cg ms;*)
    match cg with
    | Box (_) | Atomic (_) ->
       uniform_left cD cG cPool Emp cg ms sc currDepth maxDepth blur
    | Forall (tdecl, cg') ->
       (* In this case we gain an assumption in the meta-context *)
       let cD' = Whnf.extend_mctx cD (tdecl, ms) in
       let name = LF.name_of_ctyp_decl tdecl in
       let cG' = Whnf.cnormGCtx (cG, LF.MShift 1) in
       let cPool' = cnormCPool (cPool, LF.MShift 1) cD in
       let sc' =
         (fun e ->
           sc (Comp.MLam (noLoc, name, e, Plicity.explicit))) in
       uniform_right cD' cG' cPool' cg' (Whnf.mvar_dot1 ms) sc' currDepth maxDepth blur
    | Implies ((r, tdecl), cg') ->
       (* We gain an assumption for the computation context *)
       let cc = C.cResToCClause (r, ms) in
       let cPool' = Full (shift_cPool cPool 1, (cc, 1, Boxed)) in
       let cG' = Whnf.extend_gctx cG (tdecl, ms) in
       let Comp.CTypDecl (name, _, _) = tdecl in
       let sc' =
         (fun e ->
            sc (Comp.Fn (noLoc, name, e))) in
       uniform_right cD cG' cPool' cg' ms sc' currDepth maxDepth blur


  let cgSolve cD cG mq sc maxDepth =
    cgSolve' cD cG Emp mq sc None maxDepth Blur

end

module Frontend = struct
  module P = Printer
  open Index

  exception Done                        (* Solved query successfully. *)
  exception AbortQuery of string        (* Abort solving the query.   *)
  (* exception DepthReached of bound                (* Stops a query going beyond the specified depth *) *)

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
    | (None, None) -> ()
    | _ ->
       if Bool.not (boundEq (lowerBound e t) (Some s))
       then
         abort
           begin fun ppf () ->
           fprintf ppf
             "Query error: Wrong number of solutions -- \
              expected %a in %a tries, but found %d"
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
             fprintf std_formatter "%a@."
               P.fmt_ppr_inst [(n, tM)]
          | None -> ()
          end;
          fprintf std_formatter "@."
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
          Solver.solve sgnQuery.cD LF.Null sgnQuery.query scInit;
          (* Check solution bounds. *)
          checkSolutions sgnQuery.expected sgnQuery.tries !solutions
        with
        | Done -> printf "Done.\n"
        | AbortQuery s -> printf "%s\n" s
        | _ -> ()
      end
    else if !Options.chatter >= 2
    then printf "Skipping query -- bound for tries = 0.\n"

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
                     (Syntax.Loc.ghost, Comp.Var
                                          (Syntax.Loc.ghost, 0)))
    in

    (* Remove duplicates from cIH *)
    let cIH' =
      let cIH' = CSolver.remove_mvar_subs cIH in
      let unique_cIH = CSolver.unique_IH cIH' cD in
      CSolver.cnormIHCtx' (CSolver.fix_IH_args unique_cIH cD, LF.MShift 0) in

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
         let Some iterm = mmvar.LF.instantiation.contents in
         (match iterm with
         | LF.IHead hd -> hd
         | _ -> raise NotImplementedYet)
      | LF.MPVar ((mmvar, ms), s) ->
         let Some iterm = mmvar.LF.instantiation.contents in
         (match iterm with
         | LF.IHead hd -> hd
         | _ -> raise NotImplementedYet)
      | LF.MVar (LF.Inst mmvar, s) ->
         let Some iterm = mmvar.LF.instantiation.contents in
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
           let Some iterm = mmvar.LF.instantiation.contents in
           iterm
        | LF.MPVar ((mmvar, ms), s) ->
           let Some iterm = mmvar.LF.instantiation.contents in
           iterm
        | LF.MVar (LF.Inst mmvar, s) ->
           let Some iterm = mmvar.LF.instantiation.contents in
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
      | LF.PiTyp ((td, d), tA') -> LF.PiTyp ((td, d), remove_typ_mvars tA')
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
      | _ -> raise NotImplementedYet

    in

    let (cgoal, ms) = mquery in
    printf
       "[msolve_tactic] \
              Goal = %a \
              cD = %a \
              cG = %a \
             theorem = %a \ "
        (Printer.fmt_ppr_cmp_goal cD) (cgoal, LF.Shift 0)
        (Printer.fmt_ppr_mctx) cD
        (Printer.fmt_ppr_gctx cD) cG
        (Printer.fmt_ppr_cmp_typ cD) theorem
    ;
    (try
       CSolver.cgSolve cD cG mquery scInit depth;
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
      Index.robAll ();
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
  Index.robAll ();

(*
let runLogicOn n (cD, cPsi, tA, i) e t  =
  Index.singleQuery (n, (tA, i), e, t) Frontend.solve
 *)
