open Support.Equality
(* module Logic *)
(* author:
   Costin Badescu
   Jacob Thomas Errington
 *)

open Support
module S = Substitution.LF
open Format
open Syntax.Int

let (dprintf, _, _) = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

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
                             * Syncom.LF.plicity) (* For recreating type*)

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
    | LF.PiTyp ((tD, LF.Maybe), tA') ->
       typToClause' (LF.DDec (eV, tD)) cG tA' (cS, dS, dR)
    | LF.PiTyp ((LF.TypDecl (_, tA), LF.No), tB) ->
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
    | LF.PiTyp ((tdec, LF.Maybe), tA') ->
       All (tdec, typToGoal tA' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (x, tA) as tdec, LF.No), tB) ->
       Impl ((typToRes tA (cS, dS, dR), tdec), typToGoal tB (cS, dS, dR + 1))
    | LF.Atom _ ->
       Atom (Shift.shiftAtom tA (-cS, -dS, dR))

  and typToRes tM (cS, dS, dR) =
    match tM with
    | LF.PiTyp ((tD, LF.Maybe), tM') ->
       Exists (tD, typToRes tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (_, tA), LF.No), tB) ->
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
       let name = Id.mk_name Id.NoName in
       let typ_dec = Comp.CTypDecl (name, tau1 , true) in
       Implies ((cr1,typ_dec), cg2)
    | Comp.TypBase (_, comp_cid, s) ->
       Atomic (comp_cid, msToAs s)

  and comptypToCompRes tau =
    match tau with
    | Comp.TypBox (_) | Comp.TypBase(_) ->
       Base tau
    | Comp.TypArr (_,tau1,tau2) ->
       CAnd (comptypToCompGoal tau1, comptypToCompRes tau2)
    | Comp.TypPiBox (_,typ_dec, tau') ->
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
       let u = LF.Inst (Whnf.newMMVar None (cD, cPsi, LF.TClo (tA, s)) LF.Maybe) in
       LF.Root (Syntax.Loc.ghost, LF.MVar (u, S.id), LF.Nil, `explicit)
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

  let rec mctxToMSub cD (mV, ms) fS =
    let etaExpand' cD cPsi (tA, ms) name =
      let cvar = Whnf.newMMVar (Some name) (cD, cPsi, tA) LF.Maybe in
       LF.Root (Syntax.Loc.ghost, LF.MMVar((cvar, ms), S.id), LF.Nil, `explicit)
    in
    let get_plicity dep =
      match dep with
      | LF.No -> `explicit
      | LF.Maybe -> `implicit
    in
    let noLoc = Syntax.Loc.ghost in
    match mV with
    | LF.Empty -> (ms, fS)
    | LF.Dec (mV',
              LF.Decl (name, ((LF.ClTyp (LF.MTyp tA, cPsi)) as ctyp), dep)) ->
       let (ms', fS') = mctxToMSub cD (mV', ms) fS in
       let tM = etaExpand' cD cPsi (tA, ms) name in
       let dctx_hat = Context.dctxToHat cPsi in
       let plicity = get_plicity dep in
       let mfront = LF.ClObj (dctx_hat, LF.MObj tM) in
       (* let mf = Whnf.cnormMFt mfront ms' in *)
       (* let ctyp' = Whnf.cnormMTyp (ctyp, ms') in *)
       (LF.MDot (mfront, ms'),
        (fun s ->
          fS' (Comp.MApp (noLoc, s, (noLoc, mfront), ctyp, plicity))))
    | LF.Dec (mV',
              LF.Decl (name, ((LF.ClTyp (LF.PTyp tA, cPsi)) as ctyp), dep)) ->
       let (ms', fS') = mctxToMSub cD (mV', ms) fS in
       let tM = etaExpand' cD cPsi (tA, ms') name in
       let LF.Root (noLoc, hd, LF.Nil, _) = tM in
       let dctx_hat = Context.dctxToHat cPsi in
       let plicity = get_plicity dep in
       let mfront =
         LF.ClObj (dctx_hat, LF.PObj hd) in
       (* let mf = Whnf.cnormMFt mfront ms' in *)
       (LF.MDot (mfront, ms'),
        (fun s ->
          fS' (Comp.MApp (noLoc, s, (noLoc, mfront), ctyp, plicity))))
    | LF.Dec (mV',
              LF.Decl (name, ((LF.CTyp (Some cid)) as ctyp), dep)) ->
       let (ms', fS') = mctxToMSub cD (mV', ms) fS in
       let plicity = get_plicity dep in
       let dctx = Whnf.newCVar (Some name) cD (Some cid) dep in
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
      | LF.PiTyp ((LF.TypDecl (x, tA), LF.Maybe), tB) when i > 0 ->
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
  comptypToMQuery (tau,i) = comp_goal

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
          (((comptypToCompGoal tau),ms), tau, ms, xs)
      | Comp.TypBox (_loc, LF.ClTyp (LF.PTyp _tA, _cPsi)) ->
         (((comptypToCompGoal tau),ms), tau, ms, xs)
      | Comp.TypBox (loc, LF.ClTyp (LF.STyp (_svar_c, _cPhi),  _cPsi)) ->
          raise NotImplementedYet
      | Comp.TypPiBox (loc, mdecl, tau')  when i > 0 ->
          let LF.Decl(x, mtyp, dep) = mdecl in  (* where mtyp = (LF.MTyp tA, cPsi) *)
          (* generate a meta-variable (instantiated by unification) of type (LF.MTyp tA, cPsi)
             and make sure it is an mfront *)
          let mmV = Whnf.newMMVar' (Some x) (LF.Empty, mtyp) dep in
          let mfront = Whnf.mmVarToMFront loc mmV mtyp in
          comptypToMQuery' (tau', i-1) (LF.MDot (mfront, ms)) ((x, (loc, mfront)) :: xs)
      | Comp.TypPiBox (_,_, tau') when i = 0 ->
         (((comptypToCompGoal tau),ms), tau, ms, xs)
      | Comp.TypArr (loc, tau1, tau2) ->
         (((comptypToCompGoal tau),ms), tau, ms, xs)
      | Comp.TypBase (_) ->
         (((comptypToCompGoal tau),ms), tau, ms, xs)
      | _ -> raise NotImplementedYet
    in
    comptypToMQuery' (tau, i) (LF.MShift 0) []

end


module Index = struct
  open Store

  let types = Hashtbl.create 0          (* typConst Hashtbl.t          *)

  let compITypes = Hashtbl.create 0     (* compTypConst Hashtbl.t      *)

  let compTTypes = Hashtbl.create 0     (* comp theorem Hashtbl.t      *)

  type inst = (Id.name *  LF.normal)    (* I ::= (x, Y[s]) where Y is an MVar        *)
  type minst = (Id.name * LF.mfront)    (* I ::= (x, mf)   where mf is (Psihat.term) *)
                                        (* where mf contains an MMVar *)
  type sgnQuery =
    { query : query                   (* Query ::= (g, s)            *)
    ; typ : LF.typ                    (* Query as LF.typ.            *)
    ; skinnyTyp : LF.typ              (* Query stripped of E-vars.   *)
    ; optName : Id.name option        (* Opt. name of proof term.    *)
    ; cD : LF.mctx                    (* Meta context.               *)
    ; expected : bound                (* Expected no. of solutions.  *)
    ; tries : bound                   (* No. of tries to find soln.  *)
    ; instMVars : inst list           (* MVar instantiations.        *)
    }

  type sgnMQuery =
    { mquery : mquery                 (* MQuery ::= (c_g, ms)        *)
    ; skinnyCompTyp : Comp.typ        (* MQuery stripped of E-vars.  *)
    ; mexpected : bound               (* Expected no. of solutions.  *)
    ; mtries : bound                  (* No. of tries to find soln.  *)
    ; depth : bound                   (* Depth of search tree.       *)
    ; instMMVars : minst list         (* MMVar instantiations.       *)
    }


  let queries = DynArray.create ()      (* sgnQuery DynArray.t         *)
  let mqueries = DynArray.create ()     (* sgnMQuery DynArray.t        *)

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


  (* addSgnMQuery (tau', ttau, xs, e, t)  = ()
     Add a new sgnMQuery to the `mqueries' DynArray.
   *)
  let addSgnMQuery (tau', mq, xs, e, t, d) =
    DynArray.add mqueries
      { mquery = mq
      ; skinnyCompTyp = tau'
      ; mexpected = e
      ; mtries = t
      ; depth = d
      ; instMMVars = xs
      }

  (* compile _ Clause c = (c, sCl)
     Retrieve type for term constant c, clausify it, and
     return the respective clause (c, sCl).
   *)

  (* LF Constants  *)
  let compileSgnClause cidTerm =
    let termEntry = Cid.Term.get cidTerm in
    let tA = termEntry.Cid.Term.Entry.typ in
    (cidTerm, Convert.typToClause tA)

  (* Computation Theorem Constants  *)
  let compileSgnCClause cidTerm =
    let termEntry = Cid.Comp.get cidTerm in
    let tau = termEntry.Cid.Comp.Entry.typ in
    (cidTerm, Convert.comptypToCClause tau)

  (* Computation Inductive Constants *)
  let compileSgnConstClause cidCompTerm =
    let ctermEntry = Cid.CompConst.get cidCompTerm in
    let tau = ctermEntry.Cid.CompConst.Entry.typ in
    (cidCompTerm, Convert.comptypToCClause tau)


  (* termName c = Id.name
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


  (* storeMQuery ((tau, i), e, t) = ()
     Invariants:
       i = # of abstracted EVars in tau
       e = expected number of  solutions
       t = expected number of tries to find soln.
  *)
  let storeMQuery ((tau, i), e, t, d) =
    (*  TO BE IMPLEMENTED AND FINISHED *)
    let (mq, tau', ms, xs) = (Convert.comptypToMQuery (tau, i)) in
    addSgnMQuery (tau', mq, [], e, t, d)


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

  let iterMQueries f =
    DynArray.iter (fun q -> f q) mqueries
  (* clearIndex () = ()
     Empty the local storage.
  *)
  let clearIndex () =
    DynArray.clear queries;
    DynArray.clear mqueries;
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

 (* let fmt_ppr_gctx cD ppf cG =
    P.fmt_ppr_cmp_gctx cD P.l0 ppf cG

  let fmt_ppr_mctx ppf cD =
    P.fmt_ppr_lf_mctx P.l0 ppf cD     *)

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
         Id.print x
    | LF.TypDecl (x, tA) ->
       fprintf ppf "%a : %a"
         Id.print x
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


  let fmt_ppr_cmp_exp_chk cD cG ppf eChk =
    P.fmt_ppr_cmp_exp_chk cD cG P.l0 ppf eChk


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
      Id.print (termName cidTerm)
      (fmt_ppr_typ LF.Empty sCl.eVars) (sCl.tHead, S.id)
      (fmt_ppr_subgoals LF.Empty sCl.eVars) (sCl.subGoals, S.id)

  (** Prints a Computation Type clause *)
  let fmt_ppr_sgn_cclause ppf (cidTerm, sCCl) =
    fprintf ppf "@[<v 2>@[%a@] : @[%a@]@,%a@]"
      Id.print (compName cidTerm)
      (fmt_ppr_cmp_typ sCCl.cMVars) (sCCl.cHead)
      (fmt_ppr_csubgoals sCCl.cMVars) (sCCl.cSubGoals)

   (** Prints clausal form of a Computation Constant *)
  let fmt_ppr_sgn_compclause ppf (cidTerm, sCCl) =
    fprintf ppf "@[<v 2>@[%a@] : @[%a@]@,%a@]"
      Id.print (compConstName cidTerm)
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

  let fmt_ppr_sgn_mquery ppf mq =
      fprintf ppf "--mquery %a %a %a %a"
        fmt_ppr_bound mq.mexpected
        fmt_ppr_bound mq.mtries
        fmt_ppr_bound mq.depth
        (fmt_ppr_cmp_typ LF.Empty) mq.skinnyCompTyp

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
                Id.print x
                (fmt_ppr_normal LF.Empty LF.Null) (tA, S.id)))
         xs

  let printQuery q =
    fprintf std_formatter "%a.@.@."
      fmt_ppr_sgn_query q

  let printMQuery mq =
    fprintf std_formatter "%a.@.@."
      fmt_ppr_sgn_mquery mq

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
(*
   let printState cD cG cg ms =
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
        (fmt_ppr_cmp_goal cD) (cg,S.id)
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

  (* eqHead A dCl = bool
     Compare the cid_typ's of A and the head of dCl.
  *)
  let eqHead tA dCl =
    match (tA, dCl.tHead) with
    | (LF.Atom (_, i, _), LF.Atom (_, j, _)) -> Id.cid_equals i j
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
    let root x = LF.Root (Syntax.Loc.ghost, x, LF.Nil, `explicit) in
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
                         , `explicit
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
     and matchDelta (cD' : LF.mctx) =
      let rec loop cD' k =
        match cD' with
        | LF.Empty -> matchDProg dPool
        | LF.Dec (cD', LF.Decl (_, LF.ClTyp (cltyp, psi), _)) ->
           begin
             let psi' = Whnf.cnormDCtx (psi, LF.MShift k) in
             let cltyp' = Whnf.cnormClTyp (cltyp, LF.MShift k) in
             try
               trail
                 begin fun () ->
                 U.unifyDCtx cD psi' cPsi;
                 (* We look to see whether we're dealing with a sigma type.
                    In this case, we must consider the projections of the sigma.
                    If it isn't a sigma then we can just try to unify the types.
                  *)
                 match cltyp' with
                 | LF.PTyp (LF.Sigma typs) ->
                    matchSigma (pvar k) cD psi' typs
                      (fun k' ->
                        (* recall: k is the index of the variable in the _context_ *)
                        (* k' is the index of the projection into the _sigma_ *)
                        sc (psi', root (proj (pvar k) k'))
                      )

                 | LF.PTyp typ' ->
                    (* I don't think this case ever happens; I'm pretty
                     * sure that whenever we have a PTyp, its type is a
                     * Sigma, so we can probably remove this case or assert
                     * that it's impossible.
                     * -jake
                     *)

                    U.unifyTyp cD psi' (typ', LF.Shift 0) (tA, s);

                    (* We need to create the syntax to refer to this _pattern_ variable *)
                    sc (psi', root (pvar k))

                 | LF.MTyp typ' ->
                    U.unifyTyp cD psi' (typ', LF.Shift 0) (tA, s);
                    dprintf
                      begin fun p ->
                      p.fmt "[logic] [matchDelta] found solution: variable %d" k
                      end;

                    (* We need to create the syntax to refer to this _meta_ variable *)
                    sc (psi', root (mvar k))

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
      loop cD' 1

    (* matchSig c = ()
       Try all the clauses in the static signature with head matching
       type constant c.
     *)
     and matchSig cidTyp =
       I.iterSClauses (fun w -> matchSgnClause w sc) cidTyp

    (* matchSgnClause (c, sCl) sc = ()
       Try to unify the LF type of sCl with A[s]. If unification succeeds,
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
                  , `explicit
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
  type cPool =                             (* cP ::=                    *)
    | Emp                                  (*   | Emp                   *)
    | Full of
        (cPool * (cclause * int * status)) (*   | Full (cP', (cc, k,s)) *)
                                           (*      where k denotes the
                                                   postion of the
                                                   correspoding type
                                                   declaration in cG   *)

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
       Id.cid_equals (Solver.cidFromAtom tA) (Solver.cidFromAtom tA')
    | (Comp.TypBox (_, LF.ClTyp (LF.PTyp tA, cPsi))),
       Box (cPsi', Atom tA', Some P) ->
       Id.cid_equals (Solver.cidFromAtom tA) (Solver.cidFromAtom tA')
    | (Comp.TypBase (_, cid, _meta_spine), Atomic (cid', _atomic_spine)) ->
       Id.cid_equals cid cid'
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
      | Spine (aS', (mt, mf,pl)) ->
         let aS'' = normAtomicSpine ms aS' in
         let mf' = Whnf.cnormMFt mf ms in
         Spine (aS'', (mt, mf',pl))
    in
    match cg with
    | Box (cPsi, Atom typ, _lfTyp) ->
       let typ' = Whnf.cnormTyp (typ,ms) in
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

  let rec normSubGoals ms sg cD =
    match sg with
    | Proved -> sg
    | Solve (sg', cg) ->
       let cg' = normCompGoal (cg, ms) in
       Solve (normSubGoals ms sg' cD, cg')

  let rec cnormCPool (cPool, ms) cD =
    match cPool with
    | Emp -> cPool
    | Full (cPool', ({cHead = hd; cMVars = mV; cSubGoals = sg}, _k, _s)) ->
       let cPool'' = cnormCPool (cPool', ms) cD in
       let hd' = Whnf.cnormCTyp (hd, ms) in
       let sg' = normSubGoals ms sg cD in
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
      | LF.Dec (cD', ((LF.Decl (name, LF.ClTyp (cltyp', _cPsi), _dep)) as cltyp_d')) ->
         let (k', lst') = consOfTyp cltyp' in
         if k' < k then
           find_max cD' cltyp_d' k' lst'
         else
           find_max cD' cltyp_d k lst
    in
    match cD with
    | LF.Empty -> raise NotImplementedYet
    | LF.Dec (cD', ((LF.Decl (name, LF.ClTyp (cltyp, _cPsi), _dep)) as cltyp_d)) ->
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
    
    
  let rec cgSolve' (cD: LF.mctx) (cG: Comp.gctx) (cPool: cPool)
            (mq:mquery) (sc: Comp.exp_chk -> unit) (currDepth: bound) (maxDepth: bound) =

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
      uniform_right cD cG cPool cg ms sc currDepth maxDepth
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


    3) Q = Box(cPsi,A) or Inductive(a, meta-spine)  we solve it using some assumption from cG

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
       let e = Whnf.cnormExp' (e,ms) in
       sc e
    | Solve (sg', cg') ->
       (* printf "solve gamma SG \n"; *)
       let cg' = normCompGoal (cg', ms) in
       (* Printer.printState cD cG cg' ms; *)
       cgSolve' cD cG cPool (cg', ms)
         (fun e ->
           solveSubGoals cD cG cPool (sg', k) ms mV
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS currDepth maxDepth)
         (succ currDepth) maxDepth


  and solveCClauseSubGoals cD cG cPool cid sg ms mV sc fS currDepth maxDepth =
   (* fprintf std_formatter "CID = %a \n"
      Id.print (Index.compConstName cid); *)
    match sg with
    | Proved ->
       let e' = (Comp.DataConst (noLoc, cid)) in
       let e = fS e' in
       let e = Whnf.cnormExp' (e,ms) in
       sc e
    | Solve (sg', cg') ->
       (* printf "solve sig SG \n"; *)
      let cg' = normCompGoal (cg', ms) in
      (* let ms = Whnf.cnormMSub ms in *)
       (*Printer.printState cD cG (cg') ms;*)
       cgSolve' cD cG cPool (cg', ms)
         (fun e ->
           solveCClauseSubGoals cD cG cPool cid sg' ms mV
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS currDepth maxDepth)
             (succ currDepth) maxDepth

  and solveTheoremSubGoals cD cG cPool cid sg ms mV sc fS currDepth maxDepth =
     (* fprintf std_formatter "CID = %a \n"
       Id.print (Index.compName cid); *)
    match sg with
    | Proved ->
       let e' = (Comp.Const (noLoc, cid)) in
       let e = fS e' in
       let e = Whnf.cnormExp' (e,ms) in
       sc e
    | Solve (sg', cg') ->
       let cg'= normCompGoal (cg',ms) in
      (* Printer.printState cD cG cg' ms; *)
       cgSolve' cD cG cPool (cg', ms)
         (fun e ->
           solveTheoremSubGoals cD cG cPool cid sg' ms mV
             (fun e' -> sc (Comp.Apply (noLoc, e', e))) fS currDepth maxDepth)
            (succ currDepth) maxDepth

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
      (*  printf "focus Thm NEW MS \n";
         Printer.printState cD cG cg ms';
         let ms''' = Whnf.cnormMSub ms' in
         printf "focus Thm normedd MS \n";
         Printer.printState cD cG cg ms'''; *)
         let tau = if isBox cg then C.boxToTypBox cg else C.atomicToBase cg in
        (try
           Solver.trail
             begin fun () ->
               unify cD (tau, ms) (sCCl.cHead, ms'')
                 (fun () ->
                  solveTheoremSubGoals cD cG cPool cid sCCl.cSubGoals ms'' sCCl.cMVars
                    (fun e' -> sc (Comp.Syn (noLoc, e'))) fS currDepth maxDepth)
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
      let ms'' = rev_ms ms' (Context.length ((sCCl.cMVars))) in
      (* printf "focus Sig NEW MS \n";
      Printer.printState cD cG cg ms'; *)
      let tau = C.atomicToBase cg in
      (* printf "focus Sig match with assump head: \n";
      Printer.fmt_ppr_cmp_typ cD std_formatter sCCl.cHead; *)
      (try
         Solver.trail
           begin fun () ->
           unify cD (tau, ms) (sCCl.cHead, ms'')
               (fun () ->
                solveCClauseSubGoals cD cG cPool cidTerm sCCl.cSubGoals ms'' sCCl.cMVars
                  (fun e' -> sc (Comp.Syn (noLoc, e'))) fS currDepth maxDepth)
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
                 (fun e' -> sc  (Comp.Syn (noLoc, e'))) fS currDepth maxDepth)
             end
         with
         | U.Failure _ -> ());
         focusG cD cG cPool' cPool_all cg ms sc currDepth maxDepth

       else (* Otherwise, try the remaining comp assumptions *)
         focusG cD cG cPool' cPool_all cg ms sc currDepth maxDepth
    | Full (cPool', cc) -> focusG cD cG cPool' cPool_all cg ms sc currDepth maxDepth

      (*
  (* creates the set-up to build the branch corresponding to the current
     constructor/case.  *)
  and solveBranch cD cG cPool cg (name, con) con_list b_list ms sc currD maxD =
 (*   let termEntry = Store.Cid.Term.get con in
    let tA = termEntry.Store.Cid.Term.Entry.typ in *)
    let hd = LF.Const con in
    let norm = LF.Root (noLoc, hd, LF.Nil, `explicit) in
    let pattern = Comp.PatMetaObj (noLoc,(noLoc,
                    LF.ClObj ((None, 0),
                      LF.MObj (norm)))) in
    let makeBranch =
      (fun e -> Comp.Branch
                  (noLoc, LF.Empty, (cD, cG), pattern, LF.MShift 0, e))
    in
    cgSolve' cD cG cPool (cg, ms)
      (fun e -> solveCases cD cG cPool cg (name, con_list) ms sc ((makeBranch e)::b_list) currD maxD) currD maxD


  and instMV cg n cD cG cPool =
    (cD, LF.MShift 0, cG, cPool, cg)

  (* solve the top case of the split;
     when done, tests the returned branch list  *)
  and solveCases cD cG cPool cg (name, constructors) ms sc b_list currD maxD =
    match constructors with
    | [] -> sc b_list
    | con :: con_list ->
      (* let termEntry = Store.Cid.Term.get con in
       let tA = termEntry.Store.Cid.Term.Entry.typ in *)
       let hd = LF.Const con in
       let norm = LF.Root (noLoc, hd, LF.Nil, `explicit) in
       let (cD', ms', cG', cPool', cg') = instMV cg norm cD cG cPool in
       solveBranch cD' cG' cPool' cg' (name, con) con_list b_list ms' sc currD maxD

  (* finds the mvar with the least constructors and "splits" on it;
     tries to solve with that split.
     if fails, splits on next smallest, ect.  *)
  and msplit mvars cD cG cPool cg ms sc currD maxD =
    match mvars with
    | LF.Empty -> ();
    | LF.Dec (mvars', _mv) ->
       try
         (let (ctyp_d, constructors) = least_cases mvars in
          let LF.Decl (name, ctyp, dep) = ctyp_d in
          let LF.ClTyp (cltyp, cPsi) = ctyp in
          let hd = LF.FVar name in
          let norm = LF.Root (noLoc, hd, LF.Nil, `explicit) in
          let mf = LF.ClObj (Context.dctxToHat cPsi, LF.MObj norm) in
          let mo = (noLoc, mf) in
          let var = Comp.AnnBox (mo, ctyp) in
          let sc' =
            (fun e ->
              sc (Comp.Case (noLoc, Comp.PragmaCase, var, e)))
          in
          solveCases cD cG cPool cg (name, constructors) ms sc' [] currD maxD)
       with
       | Failure _ ->
          msplit mvars' cD cG cPool cg ms sc currD maxD

          *)

  and focus cD cG cPool cg ms sc currDepth maxDepth =
   (*  printf "FOCUS \n";
    (* let ms = Whnf.cnormMSub ms in
    let cg = normCompGoal (cg, ms) in *)
    Printer.printState cD cG cg ms; *)
    match cg with
    | Box (cPsi, g, Some M) ->
       (* If our goal is of box type, we first try to find the
          proof term in the LF level, otherwise we focus on
          an assumption in our computation context cG          *)
       let cg' = normCompGoal (cg, ms) in
       let Box(_,g',_) = cg' in
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
           let LF.Root (_,hd,_,_) = tM in
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


  and uniform_left cD cG cPool cPool_ret cg ms sc currDepth maxDepth =
 (*   printf "UNIFORM LEFT \n";
    let cg'= normCompGoal (cg, ms) in
    Printer.printState cD cG (cg') ms; *)
    let unbox cp =
      match cp with
        | (_cc, _k, Boxed) -> (_cc, _k, Unboxed)
    in
    match cPool with
    | Emp ->
       focus cD cG cPool_ret cg ms sc currDepth maxDepth
    | Full (cPool', ((({cHead = Comp.TypBox(m,r); cMVars = cmv;cSubGoals = Proved }, k', Boxed)) as cP)) ->
       (* In this case, we want to "unbox" the assumption and add it to
          the cD.
          When an assumption gets unboxed, we no longer consider it in Gamma. *)
       let name = Id.mk_name (Whnf.newMTypName r) in
       let mctx_decl = LF.Decl (name, r, LF.No) in
       let cD' = Whnf.extend_mctx cD (mctx_decl, ms) in
       let cG' = Whnf.cnormGCtx (cG, LF.MShift 1) in
       let box = Comp.Var (noLoc, k') in
       let pattern =
         Comp.PatMetaObj (noLoc,(noLoc,
          match r with
          | LF.ClTyp (LF.MTyp _, cPsi) ->
             let tM =
               LF.Root
                 (noLoc
                 ,LF.MVar (LF.Offset 1, S.id)
                 , LF.Nil
                 , `explicit
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
                          [Comp.Branch (noLoc, LF.Empty, (cD', LF.Empty), pattern, LF.MShift 1,e)]))) in
       let ms' = Whnf.mvar_dot1 ms in
       let cPool'' = cnormCPool (cPool', LF.MShift 1) cD' in
       let cPool_ret' = prependToCPool (unbox cP) cPool_ret in
       let cPool_ret'' = cnormCPool (cPool_ret', LF.MShift 1) cD' in
       let cg' = normCompGoal (cg, (LF.MShift 1)) in
       uniform_left cD' cG' cPool'' cPool_ret'' cg' ms' sc' currDepth maxDepth
    | Full (cPool', x) ->
       (* Otherwise we leave the assumption in cG *)
       let cPool_ret' = prependToCPool x cPool_ret in
       uniform_left cD cG cPool' cPool_ret' cg ms sc currDepth maxDepth


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
  and uniform_right cD cG cPool cg ms sc currDepth maxDepth =
    (* printf "UNIFORM RIGHT \n";
    Printer.printState cD cG cg ms;*)
    match cg with
    | Box (_) | Atomic (_) ->
       uniform_left cD cG cPool Emp cg ms sc currDepth maxDepth
    | Forall (tdecl, cg') ->
       (* In this case we gain an assumption in the meta-context *)
       let cD' = Whnf.extend_mctx cD (tdecl, ms) in
       let name = LF.name_of_ctyp_decl tdecl in
       let cG' = Whnf.cnormGCtx (cG, LF.MShift 1) in
       let cPool' = cnormCPool (cPool, LF.MShift 1) cD in
       let sc' =
         (fun e ->
           sc (Comp.MLam (noLoc, name, e, `explicit))) in
       uniform_right cD' cG' cPool' cg' (Whnf.mvar_dot1 ms) sc' currDepth maxDepth
    | Implies ((r, tdecl), cg') ->
       (* We gain an assumption for the computation context *)
       let cc = C.cResToCClause (r, ms) in
       let cPool' = Full (shift_cPool cPool 1, (cc, 1, Boxed)) in
       let cG' = Whnf.extend_gctx cG (tdecl, ms) in
       let Comp.CTypDecl (name, _, _) = tdecl in
       let sc' =
         (fun e ->
            sc (Comp.Fn (noLoc, name, e))) in
       uniform_right cD cG' cPool' cg' ms sc' currDepth maxDepth


  let cgSolve cD cG mq sc maxDepth =
    cgSolve' cD cG Emp mq sc None maxDepth

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
       if not (boundEq (lowerBound e t) (Some s))
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

    if not (boundEq sgnQuery.tries (Some 0))
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

  (*
     msolve (sgnMQ: {mquery        : mquery;
                     skinnyCompTyp : Comp.typ;
                     mexpected     : bound;
                     mtries        : bound
                     depth         : bound
                     instMMVars    : minst list})=


  *)

  let msolve sgnMQuery =

    (* Retrieve the total_dec list of the signature *)
    let total_dec = [] in
  (*  getTDecs () in *)

    let solutions = ref 0 in
      (* Type checking function. *)
    let check cD cG (e : Comp.exp_chk) ms =
      Check.Comp.check None cD cG total_dec e (sgnMQuery.skinnyCompTyp, ms)
    in

    (* Success continuation function *)
    let scInit e =
      incr solutions;
      (*
      fprintf std_formatter "\n FINAL check e = \n %a \n"
        (P.fmt_ppr_cmp_exp_chk LF.Empty LF.Empty) e;  *)
        (* Rebuild the substitution and type check the proof term. *)
      if !Options.checkProofs
      then
        check LF.Empty LF.Empty e (Convert.solToMSub sgnMQuery.instMMVars);

      if !Options.chatter >= 3
      then
        begin
          fprintf std_formatter  "@[<v>---------- Solution %d ----------\n %a@,@,@]"
            (*              "@[<hov 2>@[%a@] |-@ @[%a@]@]" *)
            (!solutions)
            (P.fmt_ppr_cmp_exp_chk LF.Empty LF.Empty) e
        end;

      (* Stop when no. of solutions exceeds tries. *)
      if exceeds (Some !solutions) sgnMQuery.mtries
      then raise Done;

      (* Temporary: Exiting as soon as we receive as many solutions as required *)
      if exceeds (Some !solutions) sgnMQuery.mexpected
      then raise Done;
    in
    if not (boundEq sgnMQuery.mtries (Some 0))
    then
      begin
         if !Options.chatter >= 1
           then P.printMQuery sgnMQuery;
         try
             CSolver.cgSolve LF.Empty LF.Empty sgnMQuery.mquery scInit sgnMQuery.depth;
             (* Check solution bounds. *)
             checkSolutions sgnMQuery.mexpected sgnMQuery.mtries !solutions
           with
           | Done -> printf "Done.\n"
           | AbortQuery s -> printf "%s\n" s
           (* | DepthReached d -> printf "Query complete -- depth = %a was reached\n" P.fmt_ppr_bound d *)
           | _ -> ()
       end
     else if !Options.chatter >= 2
     then printf "Skipping query -- bound for tries = 0.\n";


end

(* Interface *)

let storeQuery p (tA, i) cD e t =
  Index.storeQuery (p, (tA, i), cD, e, t)

let storeMQuery  (tau, i) e t d =
  Index.storeMQuery ((tau, i), e, t, d)


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
      Index.iterMQueries Frontend.msolve;
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
