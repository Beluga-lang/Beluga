(**

   @author Brigitte Pientka
*)

(* Context substitution  *)

open Context
open Syntax.Int.LF
open Store.Cid

module Loc = Syntax.Loc

let (dprintf, dprint, _) = Debug.makeFunctions' (Debug.toFlags [12])
open Debug.Fmt

(* module P = Pretty.Int.DefaultPrinter *)

let rec subToString =
  function
  | Shift n -> "Shift(NoCtxShift, " ^ string_of_int n ^ ")"
  | SVar _ -> "SVar(_,_)"
  | FSVar (i, (n, _)) -> "FSVar(" ^ Id.string_of_name n ^ ", " ^ string_of_int i ^ ")"
  | Dot (front, s) -> "Dot(" ^ frontToString front ^ ", " ^ subToString s ^ ")"
  | MSVar _ -> "MSVar_"
  | EmptySub -> "EmptySub"
  | Undefs -> "Undefs"

and frontToString =
  function
  | Head _ -> "Head _"
  | Obj _ -> "Obj _"
  | Undef -> "Undef"

(* module Comp = Syntax.Int.Comp *)

let ctxShift cPsi = EmptySub (* match cPsi with *)
  (* | Null -> Shift (NoCtxShift, 0) *)
  (* | CtxVar psi -> Shift (CtxShift psi, 0) *)
  (* | DDec (cPsi, _x) -> *)
  (*     let Shift (cshift, n) = ctxShift cPsi in *)
  (*       Shift (cshift, n+1) *)

(* ctxToSub_mclosed cD psi cPsi = (cD', s)

   if x1:A1, ... xn:An = cPsi
   and cD |- cPsi dctx


      cD, cD_ext ; psi  |-  s : cPsi
   then

   s.t. cD, cD_ext; psi |- u1[id]/x1 ... un[id]/xn : cPsi
        and where cD_ext = u1:A1[psi], ... un:An[psi]

   if  ctxToSub_mclosed  cD psi cPsi = (cD',s) then
   cD' ; psi |- s : cPsi

   Concretely, this will extend the input cD with one MVar for each
   entry in cPsi and construct a substitution s that sends the context
   cPsi to the context consisting of just a context variable psi.
*)
let rec ctxToSub_mclosed cD psi =
  function
  | Null ->
     (* Substitution.LF.id  --changed 2010-07-26*)
     (cD, ctxShift psi, 0)

  | DDec (cPsi', TypDecl (_, (Atom _ as tA))) ->
     let (cD', s, k) = ctxToSub_mclosed cD psi cPsi' in (* cD' ; psi |- s : cPsi' *)
     dprint (fun () -> "s = " ^ subToString s);

     let u =
       Root
         ( Loc.ghost
         , MVar (Offset 1, Substitution.LF.id)
         , Nil
         , `explicit
         )
     in

     (* cD' ; psi |- s : cPsi' *)
     (* cD' ; psi |- u[id] : [s]tA *)

     let tA' = TClo (tA, s) in
     (* cD', u: _   ; psi |- s : cPsi', x:tA *)
     let s' = Whnf.cnormSub (s, MShift 1) in
     let result = Dot (Obj u, s') in

     let u_name = Id.mk_name (Id.MVarName (Typ.gen_mvar_name tA')) in
     (* dprint (fun () -> "[ctxToSub_mclosed] result = " ^ subToString result); *)
     ( Dec
         ( cD'
         , Decl
             ( u_name
             , ClTyp (MTyp tA', Whnf.cnormDCtx (CtxVar psi, MShift k))
             , Maybe
             )
         )
     , result
     , k + 1
     )

  | DDec (_, TypDecl _) ->
     (* For the moment, assume tA atomic. *)
     Error.not_implemented' "[ctxToSub_mclosed] non-atomic cPsi entry not supported"

(* ctxToSub' cD cPhi cPsi = s

   if x1:A1, ... xn:An = cPsi
      . ; . |- cPsi dctx
      cD    |- cPhi dctx

   then D = u1:A1[cD ; cPhi], ... un:An[cD ; cPhi]

   s.t. D; cPhi |- u1[m_id ; id]/x1 ... un[m_id]/xn : cPsi

   and  cD ; cPhi |- s : cPsi

*)
let rec ctxToSub' cD cPhi =
  function
  | Null ->
     (* Substitution.LF.id  --changed 2010-07-26*)
     ctxShift cPhi

  | DDec (cPsi', TypDecl (n, tA)) ->
     dprintf (fun p -> p.fmt "  @[<v>");
     let s = (ctxToSub' cD cPhi cPsi' : sub) in
     (* cD ; cPhi |- s : cPsi' *)
     dprintf (fun p -> p.fmt "@]");
     dprint (fun () -> "s = " ^ subToString s);
     (* For the moment, assume tA atomic. *)
     (* lower tA? *)
     (* A = A_1 -> ... -> A_n -> P

           create cPhi = A_1, ..., A_n
           \x_1. ... \x_n. u[id]
           u::P[cPhi]

           already done in reconstruct.ml
           let (_, d) = dctxToHat cPsi in
           let tN = etaExpandMV Null (tA, s) (Shift d) in
           in elSpineIW
      *)
     (* let (_, phat') = dctxToHat cPsi' in*)
     (* let u = Whnf.etaExpandMV Null (tA, s) (Shift (NoCtxShift, phat')) in *)
     (* let u = Whnf.etaExpandMV Null (tA, s) LF.id in *)
     (* let u = Whnf.newMVar (Null, TClo (tA, s)) in *)
     (* following 3 lines removed, 2010-07-26
      let composition = Substitution.LF.comp s (ctxShift cPhi) in
      dprint (fun () -> "composition = " ^ subToString composition);
      let u = Whnf.etaExpandMMV None cD cPhi (tA, composition) Substitution.LF.id in
*)
     let u = Whnf.etaExpandMMV Syntax.Loc.ghost cD cPhi (tA, s) n Substitution.LF.id Maybe in
     let front = (Obj ((* Root (MVar (u, S.LF.id), Nil) *) u) : front) in
     (* cD ; cPhi |- s : cPsi' *)
     (* cD ; cPhi |- u[id] : [s]tA *)
     (* cD ; cPhi |- Dot(s, Obj u) : cPsi', x:tA *)
     (* let shifted = Substitution.LF.comp s Substitution.LF.shift in*)
     (* dprint (fun () -> "shifted = " ^ subToString shifted);*)
     let result = Dot (front, s) in
     dprint (fun () -> "result = " ^ subToString result);
     result



let mdeclToMMVar cD0 n mtyp dep =
  match mtyp with
  | ClTyp (MTyp tA, cPsi) ->
     let u = Whnf.newMMVar (Some n) (cD0, cPsi, tA) dep in
     let phat = Context.dctxToHat cPsi in
     let tR =
       Root
         ( Loc.ghost
         , MMVar ((u, Whnf.m_id), Substitution.LF.id)
         , Nil
         , `explicit
         )
     in
     ClObj (phat, MObj tR)

  | ClTyp (STyp (cl, cPhi), cPsi) ->
     let u = Whnf.newMSVar (Some n) (cD0, cl, cPsi, cPhi) dep in
     let phat = Context.dctxToHat cPsi in
     ClObj (phat, SObj (MSVar (0, ((u, Whnf.m_id), Substitution.LF.id))))

  | ClTyp (PTyp tA, cPsi) ->
     let p = Whnf.newMPVar (Some n) (cD0, cPsi, tA) dep in
     let phat = dctxToHat cPsi in
     ClObj (phat, PObj (MPVar ((p, Whnf.m_id), Substitution.LF.id)))

  | CTyp sW ->
     let cvar = Whnf.newCVar (Some n) cD0 sW dep in
     CObj (CtxVar cvar)

let rec mctxToMMSub cD0 =
  function
  | Empty -> MShift (Context.length cD0)
  | Dec (cD', Decl (n, mtyp, dep)) ->
     let t = mctxToMMSub cD0 cD' in
     let mtyp' = Whnf.cnormMTyp (mtyp,t) in
     MDot (mdeclToMMVar cD0 n mtyp' dep, t)

let mctxToMSub cD = mctxToMMSub Empty cD

(** Drops `n` rightmost entries from an msub. *)
let rec drop n =
  function
  | t when n <= 0 -> t
  | MDot (_, t') -> drop (n - 1) t'

(** Counts the entries in an msub. *)
let rec length =
  function
  | MShift _ -> 0
  | MDot (_, t') -> 1 + length t'
