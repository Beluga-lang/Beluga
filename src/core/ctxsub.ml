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
  | FSVar (i, (n, _)) -> "FSVar(" ^ n.Id.string_of_name ^ ", " ^ string_of_int i ^ ")"
  | Dot(front, s) -> "Dot(" ^ frontToString front ^ ", " ^ subToString s ^ ")"
  | MSVar _ -> "MSVar_"
  | EmptySub -> "EmptySub"
  | Undefs -> "Undefs"
  
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
        (Dec (cD', Decl(u_name , ClTyp (MTyp tA', Whnf.cnormDCtx (psi, MShift k)), Maybe)), result, k+1)
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



let mdeclToMMVar cD0 n mtyp = match mtyp with
  | ClTyp (MTyp tA, cPsi) ->
    let u     = Whnf.newMMVar (Some n) (cD0, cPsi, tA)  in
    let phat  = Context.dctxToHat cPsi in
    ClObj (phat, MObj (Root (Syntax.Loc.ghost, MMVar (u, (Whnf.m_id, Substitution.LF.id)), Nil)))
  | ClTyp (STyp cPhi, cPsi) ->
    let u     = Whnf.newMSVar (Some n) (cD0, cPsi, cPhi)  in
    let phat  = Context.dctxToHat cPsi in
    ClObj (phat, SObj (MSVar (0, (u, (Whnf.m_id, Substitution.LF.id)))))
  | ClTyp (PTyp tA, cPsi) ->
    let p    = Whnf.newMPVar (Some n) (cD0, cPsi, tA)  in
    let phat = dctxToHat cPsi in
    ClObj (phat, PObj (MPVar (p, (Whnf.m_id, Substitution.LF.id))))
  | CTyp sW ->
    let cvar = Whnf.newCVar (Some n) cD0 sW in
    CObj (CtxVar cvar)

let rec mctxToMMSub cD0 cD = match cD with
  | Empty -> MShift (Context.length cD0)
  | Dec (cD', Decl(n, mtyp, _)) ->
      let t     = mctxToMMSub cD0 cD' in
      let mtyp' = Whnf.cnormMTyp (mtyp,t) in
      MDot (mdeclToMMVar cD0 n mtyp' , t)

let mctxToMSub cD = mctxToMMSub Empty cD
;; (* ocaml is unhappy without the ;; *)
