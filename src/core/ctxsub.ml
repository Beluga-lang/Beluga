(**

   @author Brigitte Pientka
*)

(* Context substitution  *)
open Support

open Context
open Beluga_syntax
open Synint.LF

let (dprintf, _, _) = Debug.makeFunctions' (Debug.toFlags [12])
open Debug.Fmt

(* module P = Prettyint.DefaultPrinter *)

let rec pp_sub ppf =
  function
  | Shift n -> Format.fprintf ppf "Shift(NoCtxShift, %d)" n
  | SVar _ -> Format.pp_print_string ppf "SVar(_,_)"
  | FSVar (i, (n, _)) -> Format.fprintf ppf "FSVar(%a, %d)" Name.pp n i
  | Dot (front, s) -> Format.fprintf ppf "Dot(%a, %a)" pp_front front pp_sub s
  | MSVar _ -> Format.pp_print_string ppf "MSVar_"
  | EmptySub -> Format.pp_print_string ppf "EmptySub"
  | Undefs -> Format.pp_print_string ppf "Undefs"

and pp_front ppf =
  function
  | Head _ -> Format.pp_print_string ppf "Head _"
  | Obj _ -> Format.pp_print_string ppf "Obj _"
  | Undef -> Format.pp_print_string ppf "Undef"

(* module Comp = Synint.Comp *)

let ctxShift cPsi = EmptySub (* match cPsi with *)
  (* | Null -> Shift (NoCtxShift, 0) *)
  (* | CtxVar psi -> Shift (CtxShift psi, 0) *)
  (* | DDec (cPsi, _x) -> *)
  (*     let Shift (cshift, n) = ctxShift cPsi in *)
(*       Shift (cshift, n + 1) *)



let rec lowerMVar cPsi sA' =
  match sA' with
  | (PiTyp ((decl, _, _), tA'), s') ->
     let (tM , sAmv) =
       lowerMVar
         (DDec (cPsi, Substitution.LF.decSub decl s'))
         (tA', Substitution.LF.dot1 s')
     in
       (Lam (Location.ghost, Name.mk_name Name.NoName, tM) , sAmv)

  | (TClo (tA, s), s') ->
     lowerMVar cPsi (tA, Substitution.LF.comp s s')

  | (Atom (loc, a, tS), s') ->
     (Root
         ( Location.ghost
         , MVar (Offset 1, Substitution.LF.id)
         , Nil
         , Plicity.explicit
         ) ,
      ClTyp(MTyp (TClo sA') , cPsi))


(* ctxToSub_mclosed cD psi cPsi = (cD', s)

   if x1:A1, ... xn:An = cPsi
   and cD |- cPsi dctx


      cD, cD_ext ; psi  |-  s : cPsi
   then

   s.t. cD, cD_ext; psi |- u1[id]/x1 ... un[id]/xn : cPsi
        and where cD_ext = u1:A1[psi], ... un:An[psi]

   if  ctxToSub_mclosed  cD psi cPsi = (cD', s) then
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
     dprintf (fun p -> p.fmt "s = %a@\n" pp_sub s);

     let u =
       Root
         ( Location.ghost
         , MVar (Offset 1, Substitution.LF.id)
         , Nil
         , Plicity.explicit
         )
     in

     (* cD' ; psi |- s : cPsi' *)
     (* cD' ; psi |- u[id] : [s]tA *)

     let tA' = TClo (tA, s) in
     (* cD', u: _   ; psi |- s : cPsi', x:tA *)
     let s' = Whnf.cnormSub (s, MShift 1) in
     let result = Dot (Obj u, s') in

     let u_name = Name.mk_name (Name.MVarName (Store.Cid.Typ.gen_mvar_name tA')) in
     (* dprint (fun () -> "[ctxToSub_mclosed] result = " ^ subToString result); *)
     ( Dec
         ( cD'
         , Decl
             { name = u_name
             ; typ = ClTyp (MTyp tA', Whnf.cnormDCtx (CtxVar psi, MShift k))
             ; plicity = Plicity.implicit
             ; inductivity = Inductivity.not_inductive
             }
         )
     , result
     , k + 1
     )

  | DDec (cPsi', TypDecl (_, (PiTyp _ as tA))) ->
     let (cD', s, k) = ctxToSub_mclosed cD psi cPsi' in (* cD' ; psi |- s : cPsi' *)
     dprintf (fun p -> p.fmt "s = %a@\n" pp_sub s);

     (* cD' ; psi |- s : cPsi' *)
     (* cD' ; psi |- u[id] : [s]tA *)

     let tA' = TClo (tA, s) in
     (* cD', u: _   ; psi |- s : cPsi', x:tA *)
     let s' = Whnf.cnormSub (s, MShift 1) in
     let tM , clT = lowerMVar (Whnf.cnormDCtx (CtxVar psi, MShift k)) (tA, s) in   (* where clT is the type of the mvar in M *)
     let u_name = Name.mk_name (Name.MVarName (Store.Cid.Typ.gen_mvar_name tA')) in
     let result = Dot (Obj tM, s') in
     (* dprint (fun () -> "[ctxToSub_mclosed] result = " ^ subToString result); *)
     ( Dec
         ( cD'
         , Decl
             { name = u_name
             ; typ = clT
             ; plicity = Plicity.implicit
             ; inductivity = Inductivity.not_inductive
             }
         )
     , result
     , k + 1
     )

  | DDec (_, TypDecl _) ->
     (* For the moment, assume tA atomic. *)
     Error.raise_not_implemented "[ctxToSub_mclosed] non-atomic cPsi entry not supported"

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
     dprintf (fun p -> p.fmt "s = %a@\n" pp_sub s);
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
     let u = Whnf.etaExpandMMV Location.ghost cD cPhi (tA, s) n Substitution.LF.id Plicity.implicit Inductivity.not_inductive in
     let front = (Obj ((* Root (MVar (u, S.LF.id), Nil) *) u) : front) in
     (* cD ; cPhi |- s : cPsi' *)
     (* cD ; cPhi |- u[id] : [s]tA *)
     (* cD ; cPhi |- Dot(s, Obj u) : cPsi', x:tA *)
     (* let shifted = Substitution.LF.comp s Substitution.LF.shift in*)
     (* dprint (fun () -> "shifted = " ^ subToString shifted);*)
     let result = Dot (front, s) in
     dprintf (fun p -> p.fmt "result = %a@\n" pp_sub result);
     result



let mdeclToMMVar cD0 n mtyp plicity inductivity =
  match mtyp with
  | ClTyp (MTyp tA, cPsi) ->
     let u = Whnf.newMMVar (Some n) (cD0, cPsi, tA) plicity inductivity in
     let phat = Context.dctxToHat cPsi in
     let tR =
       Root
         ( Location.ghost
         , MMVar ((u, Whnf.m_id), Substitution.LF.id)
         , Nil
         , Plicity.explicit
         )
     in
     ClObj (phat, MObj tR)

  | ClTyp (STyp (cl, cPhi), cPsi) ->
     let u = Whnf.newMSVar (Some n) (cD0, cl, cPsi, cPhi) plicity inductivity in
     let phat = Context.dctxToHat cPsi in
     ClObj (phat, SObj (MSVar (0, ((u, Whnf.m_id), Substitution.LF.id))))

  | ClTyp (PTyp tA, cPsi) ->
     let p = Whnf.newMPVar (Some n) (cD0, cPsi, tA) plicity inductivity in
     let phat = dctxToHat cPsi in
     ClObj (phat, PObj (MPVar ((p, Whnf.m_id), Substitution.LF.id)))

  | CTyp sW ->
     let cvar = Whnf.newCVar (Some n) cD0 sW plicity inductivity in
     CObj (CtxVar cvar)

let rec mctxToMMSub cD0 =
  function
  | Empty -> MShift (Context.length cD0)
  | Dec (cD', Decl { name = n; typ = mtyp; plicity; inductivity }) ->
     let t = mctxToMMSub cD0 cD' in
     let mtyp' = Whnf.cnormMTyp (mtyp, t) in
     MDot (mdeclToMMVar cD0 n mtyp' plicity inductivity, t)

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
