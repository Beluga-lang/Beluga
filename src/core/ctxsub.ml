(**

   @author Brigitte Pientka
*)

(* Context substitution  *)

open Context
open Syntax.Int.LF
open Store.Cid

module P = Pretty.Int.DefaultPrinter

let rec subToString = function
  | Shift n -> "Shift(NoCtxShift, " ^ string_of_int n ^ ")"
  | SVar _ -> "SVar(_,_)"
  | FSVar _ -> "FSVar(_,_)"
  | Dot(front, s) -> "Dot(" ^ frontToString front ^ ", " ^ subToString s ^ ")"

and frontToString = function
  | Head h -> "Head _"
  | Obj tM -> "Obj _"
  | Undef -> "Undef"

module Comp = Syntax.Int.Comp

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [12])


let ctxShift cPsi = EmptySub (* match cPsi with *)
  (* | Null              -> Shift (NoCtxShift , 0 ) *)
  (* | CtxVar psi        -> Shift (CtxShift psi, 0) *)
  (* | DDec   (cPsi, _x) -> *)
  (*     let Shift(cshift, n) = ctxShift cPsi in *)
  (*       Shift (cshift, n+1) *)

(* ctxToSub_mclosed cD psi cPsi = (cD', s)

   if x1:A1, ... xn:An = cPsi  and
       . ; cD |- cPsi dctx


      cD, cD_ext ; psi  |-  s : cPsi
   then

   s.t. cD, cD_ext; psi |- u1[id]/x1 ... un[id]/xn : cPsi
    and where cD_ext = u1:A1[psi], ... un:An[psi]

if  ctxToSub_mclosed  cD psi cPsi = (cD',s) then
   cD' ; psi |- s : cPsi

*)
let ctxToSub_mclosed cD psi cPsi =
  let rec toSub cPsi =  match cPsi with
    | Null ->
      (* Substitution.LF.id  --changed 2010-07-26*)
      (cD, ctxShift psi, 0)

    | DDec (cPsi', TypDecl (_, (Atom _  as tA))) ->
        Debug.indent 2;
      let (cD', s, k) = toSub cPsi' in  (* cD' ; psi |- s : cPsi' *)
        Debug.outdent 2;
        dprint (fun () -> "s = " ^ subToString s);
        (* For the moment, assume tA atomic. *)

      let u     = Root(Syntax.Loc.ghost, MVar(Offset 1,  Substitution.LF.id), Nil) in

        (* cD' ; psi |- s : cPsi' *)
        (* cD' ; psi |- u[id] : [s]tA *)

      let tA'   = TClo(tA, s) in
      (* cD', u: _   ; psi |- s : cPsi', x:tA *)
      let s' = Whnf.cnormSub (s, MShift 1) in
      let result = Dot(Obj u, s') in

      let u_name = Id.mk_name (Id.MVarName (Typ.gen_mvar_name tA')) in
        (* dprint (fun () -> "[ctxToSub_mclosed] result = " ^ subToString result); *)
        (Dec (cD', Decl(u_name , MTyp (tA', Whnf.cnormDCtx (psi, MShift k), Maybe))), result, k+1)
  in
    toSub cPsi





(* ctxToSub' cD cPhi cPsi = s

   if x1:A1, ... xn:An = cPsi
      . ; . |- cPsi dctx
      cD    |- cPhi dctx

   then D = u1:A1[cD ; cPhi], ... un:An[cD ; cPhi]

   s.t. D; cPhi |- u1[m_id ; id]/x1 ... un[m_id]/xn : cPsi

   and  cD ; cPhi |- s : cPsi

*)
let rec ctxToSub' cD cPhi cPsi = match cPsi with
  | Null ->
      (* Substitution.LF.id  --changed 2010-07-26*)
      ctxShift cPhi

  | DDec (cPsi', TypDecl (n, tA)) ->
      Debug.indent 2;
      let s = ((ctxToSub' cD cPhi cPsi') : sub) in
      (* cD ; cPhi |- s : cPsi' *)
         Debug.outdent 2;
      dprint (fun () -> "s = " ^ subToString s);
        (* For the moment, assume tA atomic. *)
        (* lower tA? *)
        (* A = A_1 -> ... -> A_n -> P

           create cPhi = A_1, ..., A_n
           \x_1. ... \x_n. u[id]
           u::P[cPhi]

           already done in reconstruct.ml
           let (_, d) = dctxToHat cPsi in
           let tN     = etaExpandMV Null (tA, s) (Shift d) in
           in elSpineIW
        *)
      (* let (_, phat') = dctxToHat cPsi' in*)
      (* let u     = Whnf.etaExpandMV Null (tA, s) (Shift (NoCtxShift, phat')) in *)
      (* let u     = Whnf.etaExpandMV Null (tA, s) LF.id in *)
        (* let u = Whnf.newMVar (Null ,  TClo(tA, s)) in *)
(* following 3 lines removed, 2010-07-26
      let composition = Substitution.LF.comp s (ctxShift cPhi) in
      dprint (fun () -> "composition = " ^ subToString composition);
      let u     = Whnf.etaExpandMMV None cD cPhi (tA, composition) Substitution.LF.id in
*)
      let u     = Whnf.etaExpandMMV Syntax.Loc.ghost cD cPhi (tA, s) n Substitution.LF.id in
      let front = (Obj ((* Root(MVar(u, S.LF.id), Nil) *) u) : front) in
      (* cD ; cPhi |- s : cPsi' *)
      (* cD ; cPhi |- u[id] : [s]tA *)
      (* cD ; cPhi |- Dot(s, Obj u) : cPsi', x:tA *)
      (* let shifted = Substitution.LF.comp s Substitution.LF.shift in*)
      (* dprint (fun () -> "shifted = " ^ subToString shifted);*)
      let result = Dot(front, s) in
      dprint (fun () -> "result = " ^ subToString result);
        result




(* TODO: Clean this up more *)
let declToCVar (n, ctypn) = match ctypn with
  | MTyp (tA, cPsi, dep) ->
      let u     = Whnf.newMVar (Some n) (cPsi, tA) dep in
      let phat  = Context.dctxToHat cPsi in
      MObj (phat, Root (Syntax.Loc.ghost, MVar (u, Substitution.LF.id), Nil))
  | PTyp (tA, cPsi, dep) ->
    	let p    = Whnf.newPVar (Some n) (cPsi, tA) dep in
    	let phat = dctxToHat cPsi in
    	PObj (phat, PVar (p, Substitution.LF.id))
  | STyp (cPhi, cPsi, dep) ->
      let u     = Whnf.newSVar (Some n) (cPsi, cPhi) dep (* I guess these swap? *) in
  	  let phat  = Context.dctxToHat cPsi in
      SObj (phat, SVar (u, 0, Substitution.LF.id))
  | CTyp (sW, _) ->
        let cvar = Whnf.newCVar (Some n) sW in
	CObj (CtxVar cvar)

let rec mctxToMSub cD = match cD with
  | Empty -> Whnf.m_id
  | Dec (cD', Decl(n, ctyp)) ->
      let t     = mctxToMSub cD' in
      let ctypn = Whnf.cnormMTyp (ctyp, t) in
      MDot (declToCVar (n, ctypn) , t)

let mdeclToMMVar cD0 n mtyp = match mtyp with
  | MTyp (tA, cPsi, dep) ->
    let u     = Whnf.newMMVar (Some n) (cD0, cPsi, tA) dep in
    let phat  = Context.dctxToHat cPsi in
    MObj (phat, Root (Syntax.Loc.ghost, MMVar (u, (Whnf.m_id, Substitution.LF.id)), Nil))
  | STyp (cPhi, cPsi, dep) ->
    let u     = Whnf.newMSVar (Some n) (cD0, cPsi, cPhi) dep in
    let phat  = Context.dctxToHat cPsi in
    SObj (phat, MSVar (u, 0, (Whnf.m_id, Substitution.LF.id)))
  | PTyp (tA, cPsi, dep) ->
    let p    = Whnf.newPVar (Some n) (cPsi, tA) dep in
    let phat = dctxToHat cPsi in
    PObj (phat, PVar (p, Substitution.LF.id))
  | CTyp (sW, _) ->
    let cvar = Whnf.newCVar (Some n) sW in
    CObj (CtxVar cvar)

let rec mctxToMMSub cD0 cD = match cD with
  | Empty -> MShift (Context.length cD0)
  | Dec (cD', Decl(n, mtyp)) ->
      let t     = mctxToMMSub cD0 cD' in
      let mtyp' = Whnf.cnormMTyp (mtyp,t) in
      MDot (mdeclToMMVar cD0 n mtyp' , t)


(* The following functions are from an attempt to improve printing of meta-variables;
   the idea was to check if the result of applying a substitution produced an "equivalent"
   context, and if so, to use the original names.  -jd 2010-07 *)
(* let rec isomorphic cD1 cD2 = match (cD1, cD2) with
  | (Empty, Empty) -> true
  | (Empty, _) -> false
  | (_, Empty) -> false
  | (Dec(cD1', dec1),  Dec(cD2', dec2)) ->
       isomorphic cD1' cD2' && isomorphic_ctyp_decl dec1 dec2

and isomorphic_ctyp_decl dec1 dec2 = match (dec1, dec2) with
  | (MDecl(_, tA1, dctx1, _),  MDecl(_, tA2, dctx2, _)) -> isomorphic_typ tA1 tA2 && isomorphic_dctx dctx1 dctx2              
  | (PDecl(_, tA1, dctx1, _),  PDecl(_, tA2, dctx2, _)) -> isomorphic_typ tA1 tA2 && isomorphic_dctx dctx1 dctx2
  | (SDecl(_, dctx1A, dctx1B, _),  SDecl(_, dctx2A, dctx2B, _)) -> isomorphic_dctx dctx1A dctx2A && isomorphic_dctx dctx2A dctx2B
  | (CDecl _, CDecl _) -> false  (* unsupported *)
  | (MDeclOpt _, MDeclOpt _) -> true
  | (PDeclOpt _, PDeclOpt _) -> true
  | (CDeclOpt _, CDeclOpt _) -> false  (* unsupported *)
  | (_, _) -> false

and isomorphic_dctx dctx1 dctx2 = (dctx1 = dctx2) (* match (dctx1, dctx2) with *)

and isomorphic_typ tA1 tA2 = (tA1 = tA2)
;; (* ocaml is unhappy without the ;; *)
*)
