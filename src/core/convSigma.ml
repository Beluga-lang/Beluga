(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

open Support.Equality

open Syntax
open Int
module S = Substitution

module P = Pretty.Int.DefaultPrinter

let fmt_ppr_conv_list =
  Format.(pp_print_list ~pp_sep: Support.Fmt.comma pp_print_int)

(* blockdeclInDctx is unused as of commit c899234fe2caf15a42699db013ce9070de54c9c8 -osavary *)
let rec _blockdeclInDctx cPsi = match cPsi with
  | LF.Null -> false
  | LF.CtxVar psi -> false
  | LF.DDec (cPsi',LF.TypDecl(x, tA)) ->
     begin match Whnf.whnfTyp (tA, S.LF.id) with
       | (LF.Sigma _ , _ ) -> true
       | _  ->    _blockdeclInDctx cPsi'
     end
  | _ -> false

type error =
  | BlockInDctx of LF.mctx * LF.head * LF.typ * LF.dctx

type t = Id.offset list

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | BlockInDctx (cD, h, tA, cPsi) ->
            Format.fprintf ppf
              "Encountered contextual object [%a.%a] of type [%a.%a].@.\
               Unification cannot prune it because its context contains blocks.@."
            (P.fmt_ppr_lf_dctx cD P.l0) cPsi
            (P.fmt_ppr_lf_head cD cPsi P.l0) h
            (P.fmt_ppr_lf_dctx cD P.l0) cPsi
            (P.fmt_ppr_lf_typ cD cPsi P.l0) tA)
  )
(* ************************************************************************ *)
let rec map conv_list k = match (conv_list, k) with
    | (d::conv_list', 1 ) -> d
    | (d::conv_list', _ ) -> d + map conv_list' (k-1)

let rec strans_norm cD cPsi sM conv_list = strans_normW cD cPsi (Whnf.whnf sM) conv_list
and strans_normW cD cPsi (tM, s) conv_list = match tM with
  | LF.Lam(loc,x, tN) ->
     let tN' = strans_norm cD cPsi (tN, S.LF.dot1 s) (1::conv_list) in
     LF.Lam(loc, x, tN')
  | LF.Root(loc, h, tS, plicity) ->
     let h' = strans_head loc cD cPsi h conv_list in
     let tS' = strans_spine cD cPsi (tS, s) conv_list in
     LF.Root(loc, h', tS', plicity)
  | LF.LFHole _ as n -> n

and strans_head loc cD cPsi h conv_list = match h with
  | LF.BVar x ->  LF.BVar (map conv_list x)

  | LF.MVar (LF.Offset u, sigma) ->
     LF.MVar(LF.Offset u, strans_sub cD cPsi sigma conv_list)

  | LF.MVar (u, sigma) ->
     LF.MVar(u, strans_sub cD cPsi sigma conv_list)

  | LF.PVar (p, sigma) -> LF.PVar(p, strans_sub cD cPsi sigma conv_list)

  | LF.Const c -> LF.Const c
  | LF.FVar x -> LF.FVar x
  | LF.FMVar (u,s) -> LF.FMVar (u, strans_sub cD cPsi s conv_list)
  | LF.FPVar (u,s) -> LF.FPVar (u, strans_sub cD cPsi s conv_list)
  | LF.MMVar  ((u, ms), s) ->
      let ms' = strans_msub cD cPsi ms conv_list in
      let s'  = strans_sub cD cPsi s conv_list in
        LF.MMVar ((u, ms'), s')

  | LF.MPVar  ((u, ms), s) ->
      let ms' = strans_msub cD cPsi ms conv_list in
      let s'  = strans_sub cD cPsi s conv_list in
        LF.MPVar ((u, ms'), s')

  | LF.Proj (LF.PVar (p, sigma), j) ->
      LF.Proj (LF.PVar (p, strans_sub cD cPsi sigma conv_list), j)

  | LF.Proj (LF.FPVar (p, sigma), j) ->
      LF.Proj (LF.FPVar (p, strans_sub cD cPsi sigma conv_list), j)

  | LF.Proj (LF.MPVar ((p, ms), sigma), j) ->
      let ms' = strans_msub cD cPsi ms conv_list in
      let sigma' = strans_sub cD cPsi sigma conv_list in
        LF.Proj (LF.MPVar ((p, ms'), sigma'), j)

  | LF.Proj (LF.BVar x, j) ->
     try
       let _ = Context.ctxDec cPsi x in
	     (* check that there exists a typ declaration for x
	        – if there is none, then it is mapped to itself. *)
       let x' = (map conv_list x) - j + 1  in
	     LF.BVar x'
     with
     | _ -> LF.Proj (LF.BVar x, j)

and strans_msub cD cPsi  ms conv_list = match ms with
  | LF.MShift k -> LF.MShift k
  | LF.MDot (mf , ms) ->
      let mf' = strans_mfront cD cPsi mf conv_list in
      let ms' = strans_msub cD cPsi ms conv_list in
        LF.MDot (mf',ms')

and strans_mfront cD cPsi mf conv_list = match mf with
  | LF.ClObj (phat, LF.MObj tM) ->
      LF.ClObj (phat, LF.MObj (strans_norm cD cPsi (tM, S.LF.id) conv_list ))
  | LF.ClObj (phat, LF.PObj h) ->
      LF.ClObj (phat, LF.PObj (strans_head Syntax.Loc.ghost cD cPsi h conv_list))
  | LF.MV u -> LF.MV u
  | LF.MUndef -> LF.MUndef

and shift_conv_list n = function
  | (0, xs) -> n
  | (k, x::xs) -> shift_conv_list (n+x) (k-1, xs)

and strans_sub cD cPsi s conv_list = match s with
(*  | LF.Shift (LF.NoCtxShift, 0) ->s *)
  | LF.EmptySub -> LF.EmptySub
  | LF.Undefs -> LF.Undefs
  | LF.Shift offset -> LF.Shift (shift_conv_list 0 (offset, conv_list))
  | LF.Dot (ft, s) ->
      LF.Dot (strans_front cD cPsi ft conv_list, strans_sub cD cPsi s conv_list)
  | LF.SVar (s, offset, sigma) ->
      let sigma' = strans_sub cD cPsi sigma conv_list in
        LF.SVar (s, offset, sigma')
  | LF.FSVar (n, (s, sigma)) ->
      let sigma' = strans_sub cD cPsi sigma conv_list in
        LF.FSVar (n, (s, sigma'))
  | LF.MSVar (offset, ((rho, mt), sigma)) ->
      let sigma' = strans_sub cD cPsi sigma conv_list in
        LF.MSVar (offset, ((rho, mt), sigma'))

and strans_front cD cPsi ft  conv_list = match ft with
  | LF.Head h -> LF.Head (strans_head Syntax.Loc.ghost cD cPsi h conv_list)
  | LF.Obj tM -> LF.Obj (strans_norm cD cPsi (tM, S.LF.id) conv_list)
  | LF.Undef -> LF.Undef


and strans_spine cD cPsi (tS,s) conv_list = match tS with
  | LF.Nil -> LF.Nil
  | LF.SClo (tS',s') -> strans_spine cD cPsi (tS', S.LF.comp s' s) conv_list
  | LF.App (tM, tS) ->
    let tM' = strans_norm cD cPsi (tM, s) conv_list in
    let tS' = strans_spine cD cPsi (tS, s) conv_list in
      LF.App (tM', tS')


let rec strans_typ cD cPsi sA conv_list = strans_typW cD cPsi (Whnf.whnfTyp sA) conv_list
and strans_typW cD cPsi (tA,s) conv_list = match tA with
  | LF.Atom (loc, a, tS ) ->
     LF.Atom (loc, a, strans_spine cD cPsi (tS, s) conv_list )

  | LF.PiTyp ((LF.TypDecl(x, tA), dep), tB) ->
    let tA' = strans_typ cD cPsi (tA, s) conv_list in
    let tB' = strans_typ cD cPsi (tB, S.LF.dot1 s) (1::conv_list) in
      LF.PiTyp ((LF.TypDecl(x,tA'), dep), tB')

  (* no sigma types allowed *)


let rec flattenSigmaTyp cD cPsi strec conv_list = match strec with
  | (LF.SigmaLast(n, tA), s) ->
      let tA' = strans_typ cD cPsi (tA,s) conv_list in
     (LF.DDec (cPsi, LF.TypDecl (Id.mk_name Id.NoName, tA')), 1)

  | (LF.SigmaElem (x, tA, trec), s) ->
      let tA' = strans_typ cD cPsi (tA,s) conv_list in
      let (cPhi, k) =
        flattenSigmaTyp cD (LF.DDec (cPsi, LF.TypDecl (x, tA'))) (trec, S.LF.dot1 s)  (1::conv_list)
      in
      (cPhi, k+1)


(* flattenDCtx cPsi = (cPsi'  ,  L )

   if   O ; D |- cPsi
        and cPsi contains Sigma-types

   then
        O ; D |- cPsi'  where all Sigma-types in cPsi have been flattened.
        L is a vector i.e. pos(i,L) = n  where n denotes the length of the type tA
        for element i


   Example:  cPsi  =  .,  Sigma x:A.B,  y:A,  Sigma w1:A  w2:A. A
       then flattenDCtx cPsi = (cPsi', L)
       where  cPsi' = ., x:A, x':B, y:A, w1:A, w2:A, w3:A
                L   =    [3,1,2]    (note reverse order since contexts are built in reverse order)
*)

let rec flattenDCtx cD cPsi = flattenDCtx' cD (Whnf.cnormDCtx (cPsi, Whnf.m_id))
and flattenDCtx' cD cPsi = match cPsi with
  | LF.Null -> (LF.Null , [])
  | LF.CtxVar psi -> (LF.CtxVar psi , [] )
  | LF.DDec (cPsi', LF.TypDecl (x, tA)) ->
      let (cPhi, conv_list) = flattenDCtx' cD cPsi' in
        begin
          match Whnf.whnfTyp (tA, S.LF.id) with
            | (LF.Sigma trec, s) -> let (cPhi', k) = flattenSigmaTyp cD cPhi (trec,s) conv_list in (cPhi', k::conv_list)
            | _          -> (LF.DDec(cPhi, LF.TypDecl(x, strans_typ cD cPsi (tA, S.LF.id) conv_list)), 1::conv_list)
        end

  | LF.DDec (cPsi', LF.TypDeclOpt x) ->
      let (cPhi, conv_list) = flattenDCtx' cD cPsi' in
        (LF.DDec(cPhi, LF.TypDeclOpt x), 1::conv_list)




(* genConvSub conv_list = s

   If cO ; cD |- cPsi   and    cO ; cD |- cPhi
      where conv_list relates cPsi to cPhi

   then

      cO ; cD ; cPsi |- s : cPhi


   Example:
            cPsi:        g, b:block x:exp. nat
            cPhi:        g, x:exp, y:nat
            conv_list    [2]

   genConvSub generates:

            cPsi |- s   :        ^1, b.1 , b.2  : cPhi

   AND

   genConvSub' generates :
         cPhi |-   s'  : ^2, <x,y>  : cPsi

*)
let gen_proj_sub conv_list  =
  let l  = List.length conv_list in                         (* length of cPsi *)
  let rec gen_sub conv_list pos = match conv_list with
    | [] -> LF.Shift l
    | 1::clist ->
        let s = gen_sub clist (pos + 1) in
          LF.Dot (LF.Head (LF.BVar pos), s)

    | k::clist ->
        let s = gen_sub clist (pos + 1) in
          gen_projs s pos (k, 1)

  and gen_projs s pos (k, index) =
    if k = index then
       LF.Dot (LF.Head (LF.Proj (LF.BVar pos, index)), s)
    else
      gen_projs (LF.Dot (LF.Head (LF.Proj (LF.BVar pos, index)), s))
        pos (k, index+1)
  in
    gen_sub conv_list 1

let gen_tup_sub conv_list  =
  let l' = List.fold_left (fun r x -> r + x) 0 conv_list in (* length of cPhi *)
  let rec gen_sub' conv_list pos = match conv_list with
    | [] -> LF.Shift l'
    | 1::clist ->
        let s = gen_sub' clist (pos + 1) in
          LF.Dot (LF.Head (LF.BVar pos), s)
    | k::clist ->
        let s = gen_sub' clist (pos + 1) in
        (* let tM = gen_tup  pos (k, 1) in *)
	let tM = gen_tup  (pos + k - 1) (k, 1) in
	  LF.Dot(LF.Obj(LF.Tuple (Syntax.Loc.ghost, tM)), s)

  and gen_tup pos (k,index) =
    if k = index then
      (* only correct if pos stands for a variable of atomic type *)
      LF.Last (LF.Root (Syntax.Loc.ghost, LF.BVar pos, LF.Nil, `explicit))
    else
      let tM = LF.Root (Syntax.Loc.ghost, LF.BVar pos, LF.Nil, `explicit) in
      let tTup = gen_tup (pos-1) (k, index+1) in
	LF.Cons (tM, tTup)
  in
    gen_sub' conv_list 1



  (*
(** Builds a tuple consisting of all valid projections for the given
    head. *)
let rec etaExpandTuple tRec h k =
  let open LF in
  let tM = Root (Loc.ghost, Proj (h, k), Nil, `explicit) in
  match tRec with
  | SigmaLast (_, _) -> Last tM
  | LF.SigmaElem (_, _, tRec) ->
     LF.Cons (tM, etaExpandTuple tRec h (k+1))
   *)

let rec etaExpandStrGeneric new_mxvar mk_head loc cD cPsi sA dep n =
  match Whnf.whnfTyp sA with
  | LF.Sigma tRec as tA, s ->
     (* XXX this doesn't do any strengthening !! -je *)
     let tH =
       mk_head ( (new_mxvar n (cD, cPsi, LF.tclo tA s) dep, Whnf.m_id), s )
     in
     (*
     let tTup =
       etaExpandTuple tRec tH 1
     in
     LF.Tuple (Loc.ghost, tTup)
      *)
     LF.Root (Loc.ghost, tH, LF.Nil, `explicit)

  | (LF.Atom (_, a, _tS) as tP, s) ->
      let (cPhi, conv_list) = flattenDCtx cD cPsi in
      let s_proj = gen_proj_sub conv_list in
      let s_tup  = gen_tup_sub conv_list in
      let tQ = Whnf.normTyp (tP, Substitution.LF.comp s s_tup) in
	    (*  cPsi |- s_proj : cPhi
          cPhi |- s_tup : cPsi
          cPhi |- tQ   where  cPsi |- tP  !! tQ = [s_tup]tP !!
       *)

      let (ss', cPhi') = Subord.thin' cD a cPhi in
      (* cPhi |- ss' : cPhi' *)
      let ssi' = S.LF.invert ss' in
      (* cPhi' |- ssi : cPhi *)
      (* cPhi' |- [ssi]tQ    *)
      let u = new_mxvar n (cD, cPhi', LF.TClo(tQ,ssi')) dep in
      (* cPhi |- ss'    : cPhi'
         cPsi |- s_proj : cPhi
         cPsi |- comp  ss' s_proj   : cPhi' *)
      let ss_proj = S.LF.comp ss' s_proj in
      LF.Root
        ( loc
        , mk_head ((u, Whnf.m_id), ss_proj)
        , LF.Nil
        , `explicit
        )

  | (LF.PiTyp ((LF.TypDecl (x, _tA) as decl, _ ), tB), s) ->
     let cPsi' = (LF.DDec (cPsi, S.LF.decSub decl s)) in
     LF.Lam
       ( loc
       , x
       , etaExpandStrGeneric new_mxvar mk_head loc cD cPsi' (tB, S.LF.dot1 s) dep n
       )

(* etaExpandMMVstr loc cD cPsi sA  = tN
 *
 *  cD ; cPsi   |- [s]A <= typ
 *
 *  cD ; cPsi   |- tN   <= [s]A
 *)
let etaExpandMMVstr =
  etaExpandStrGeneric Whnf.newMMVar LF.mmvar

let etaExpandMPVstr =
  etaExpandStrGeneric Whnf.newMPVar LF.mpvar

let gen_flattening cD cPsi =
  let (cPhi, conv_list) = flattenDCtx cD cPsi in
  let s_proj = lazy (gen_proj_sub conv_list) in
  let s_tup = lazy (gen_tup_sub conv_list) in
  (cPhi, s_proj, s_tup)
