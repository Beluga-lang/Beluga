(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

open Syntax
open Substitution

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
module RR = Store.Cid.NamedRenderer


let (dprint, _) = Debug.makeFunctions (Debug.toFlags [7])

let rec conv_listToString clist = match clist with
  | [] -> " "
  | x::xs -> string_of_int x ^ ", " ^ conv_listToString xs

(* blockdeclInDctx is unused as of commit c899234fe2caf15a42699db013ce9070de54c9c8 -osavary *)
let rec _blockdeclInDctx cPsi = match cPsi with
  | Int.LF.Null -> false
  | Int.LF.CtxVar psi -> false
  |Int.LF.DDec (cPsi',Int.LF.TypDecl(x, tA)) ->
     begin match Whnf.whnfTyp (tA, LF.id) with
       | (Int.LF.Sigma _ , _ ) -> true
       | _  ->    _blockdeclInDctx cPsi'
     end

type error =
  | BlockInDctx of Int.LF.mctx * Int.LF.head * Int.LF.typ * Int.LF.dctx

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | BlockInDctx (cD, h, tA, cPsi) ->
            Format.fprintf ppf
              "Encountered contextual object [%a.%a] of type [%a.%a].@.\
               Unification cannot prune it because its context contains blocks.@."
            (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPsi
            (P.fmt_ppr_lf_head cD cPsi Pretty.std_lvl) h
            (P.fmt_ppr_lf_dctx cD Pretty.std_lvl) cPsi
            (P.fmt_ppr_lf_typ cD cPsi Pretty.std_lvl) tA)
  )
(* ************************************************************************ *)
let rec new_index k conv_list = match (conv_list, k) with
    | (d::conv_list', 1 ) -> d
    | (d::conv_list', _ ) -> d + new_index (k-1) conv_list'

let rec strans_norm cD sM conv_list = strans_normW cD (Whnf.whnf sM) conv_list
and strans_normW cD (tM, s) conv_list = match tM with
  | Int.LF.Lam(loc,x, tN) -> let tN' = strans_norm cD (tN, LF.dot1 s) (1::conv_list) in
      Int.LF.Lam(loc, x, tN')
  | Int.LF.Root(loc, h, tS) ->
      let h' = strans_head loc cD h conv_list in
      let tS' = strans_spine cD (tS, s) conv_list in
        Int.LF.Root(loc, h', tS')

and strans_head loc cD h conv_list = match h with
  | Int.LF.BVar x -> Int.LF.BVar (new_index x conv_list)
  | Int.LF.MVar (Int.LF.Offset u, sigma) ->
(*      let (_, tA, cPsi') =  Whnf.mctxMDec cD u in
        if blockdeclInDctx cPsi' then
          raise (Error (loc, BlockInDctx (cD, h, tA, cPsi')))
        else *)
          Int.LF.MVar(Int.LF.Offset u, strans_sub cD sigma conv_list)
  | Int.LF.MVar (u, sigma) ->
          Int.LF.MVar(u, strans_sub cD sigma conv_list)
  | Int.LF.PVar (p, sigma) -> Int.LF.PVar(p, strans_sub cD sigma conv_list)
  | Int.LF.Proj (Int.LF.BVar x, j) ->
    let x' = (new_index x conv_list) - j + 1  in
      Int.LF.BVar x'

  | Int.LF.Proj (Int.LF.PVar (p, sigma), j) ->
      Int.LF.Proj (Int.LF.PVar (p, strans_sub cD sigma conv_list), j)

  | Int.LF.Proj (Int.LF.FPVar (p, sigma), j) ->
      Int.LF.Proj (Int.LF.FPVar (p, strans_sub cD sigma conv_list), j)

  | Int.LF.Proj (Int.LF.MPVar (p, (ms, sigma)), j) ->
      let ms' = strans_msub cD ms conv_list in
      let sigma' = strans_sub cD sigma conv_list in
        Int.LF.Proj (Int.LF.MPVar (p, (ms', sigma')), j)

  | Int.LF.Const c -> Int.LF.Const c
  | Int.LF.FVar x -> Int.LF.FVar x
  | Int.LF.FMVar (u,s) -> Int.LF.FMVar (u, strans_sub cD s conv_list)
  | Int.LF.FPVar (u,s) -> Int.LF.FPVar (u, strans_sub cD s conv_list)
  | Int.LF.MMVar  (u, (ms, s)) ->
      let ms' = strans_msub cD ms conv_list in
      let s'  = strans_sub cD s conv_list in
        Int.LF.MMVar (u, (ms', s'))
  | Int.LF.MPVar  (u, (ms, s)) ->
      let ms' = strans_msub cD ms conv_list in
      let s'  = strans_sub cD s conv_list in
        Int.LF.MPVar (u, (ms', s'))

and strans_msub cD ms conv_list = match ms with
  | Int.LF.MShift k -> Int.LF.MShift k
  | Int.LF.MDot (mf , ms) ->
      let mf' = strans_mfront cD mf conv_list in
      let ms' = strans_msub cD ms conv_list in
        Int.LF.MDot (mf',ms')

and strans_mfront cD mf conv_list = match mf with
  | Int.LF.MObj (phat, tM) ->
      Int.LF.MObj (phat, strans_norm cD (tM, LF.id) conv_list )
  | Int.LF.PObj (phat, h) ->
      Int.LF.PObj (phat, strans_head Syntax.Loc.ghost cD h conv_list)
  | Int.LF.MV u -> Int.LF.MV u
  | Int.LF.MUndef -> Int.LF.MUndef


and strans_sub cD s conv_list = match s with
(*  | Int.LF.Shift (Int.LF.NoCtxShift, 0) ->s *)
  | Int.LF.Shift (ctx_offset, offset) ->
      let offset' = List.fold_left (fun x -> fun y -> x + y) 0 conv_list in
      let _ = dprint (fun () -> "conv_list = " ^ conv_listToString conv_list ) in
      let _ = dprint (fun () -> "Old offset " ^ string_of_int offset ) in
      let _ = dprint (fun () -> "New offset " ^ string_of_int offset') in
        Int.LF.Shift (ctx_offset, offset')
  | Int.LF.Dot (ft, s) ->
      Int.LF.Dot (strans_front cD ft conv_list, strans_sub cD s conv_list)
  | Int.LF.SVar _ -> s
  | Int.LF.FSVar _ -> s
  | Int.LF.MSVar _ -> s

and strans_front cD ft  conv_list = match ft with
  | Int.LF.Head h -> Int.LF.Head (strans_head Syntax.Loc.ghost cD h conv_list)
  | Int.LF.Obj tM -> Int.LF.Obj (strans_norm cD (tM, LF.id) conv_list)
  | Int.LF.Undef -> Int.LF.Undef


and strans_spine cD (tS,s) conv_list = match tS with
  | Int.LF.Nil -> Int.LF.Nil
  | Int.LF.SClo (tS',s') -> strans_spine cD (tS', LF.comp s' s) conv_list
  | Int.LF.App (tM, tS) ->
    let tM' = strans_norm cD (tM, s) conv_list in
    let tS' = strans_spine cD (tS, s) conv_list in
      Int.LF.App (tM', tS')


let rec strans_typ cD sA conv_list = strans_typW cD (Whnf.whnfTyp sA) conv_list
and strans_typW cD (tA,s) conv_list = match tA with
  | Int.LF.Atom (loc, a, tS ) ->
     Int.LF.Atom (loc, a, strans_spine cD (tS, s) conv_list )

  | Int.LF.PiTyp ((Int.LF.TypDecl(x, tA), dep), tB) ->
    let tA' = strans_typ cD (tA, s) conv_list in
    let tB' = strans_typ cD (tB, LF.dot1 s) (1::conv_list) in
      Int.LF.PiTyp ((Int.LF.TypDecl(x,tA'), dep), tB')

  (* no sigma types allowed *)


let rec flattenSigmaTyp cD cPsi strec conv_list = match strec with
  | (Int.LF.SigmaLast tA, s) ->
      let tA' = strans_typ cD (tA,s) conv_list in
     (Int.LF.DDec (cPsi, Int.LF.TypDecl (Id.mk_name Id.NoName, tA')), 1)

  | (Int.LF.SigmaElem (x, tA, trec), s) ->
      let tA' = strans_typ cD (tA,s) conv_list in
      let (cPhi, k) = flattenSigmaTyp cD (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA'))) (trec, LF.dot1 s)  (1::conv_list) in
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
  | Int.LF.Null -> (Int.LF.Null , [])
  | Int.LF.CtxVar psi -> (Int.LF.CtxVar psi , [] )
  | Int.LF.DDec (cPsi', Int.LF.TypDecl (x, tA)) ->
      let (cPhi, conv_list) = flattenDCtx' cD cPsi' in
        begin
          match Whnf.whnfTyp (tA, LF.id) with
            | (Int.LF.Sigma trec, s) -> let (cPhi', k) = flattenSigmaTyp cD cPhi (trec,s) conv_list in (cPhi', k::conv_list)
            | _          -> (Int.LF.DDec(cPhi, Int.LF.TypDecl(x, strans_typ cD (tA, LF.id) conv_list)), 1::conv_list)
        end

  | Int.LF.DDec (cPsi', Int.LF.TypDeclOpt x) ->
      let (cPhi, conv_list) = flattenDCtx' cD cPsi' in
        (Int.LF.DDec(cPhi, Int.LF.TypDeclOpt x), 1::conv_list)




(* genConvSub conv_list = s

   If cO ; cD |- cPsi   and    cO ; cD |- cPhi
      where conv_list relates cPsi to cPhi

   then

      cO ; cD ; cPsi |- s : cPhi


   Example: cPsi:        g, b:block x:exp. nat
            cPhi:        g, x:exp, y:nat
            conv_list    [2]
            s   :        ^1, b.1 , b.2

*)
let gen_conv_sub conv_list  =
  let l = List.length conv_list in
  let rec gen_sub conv_list pos = match conv_list with
    | [] -> Int.LF.Shift (Int.LF.NoCtxShift, l)
    | 1::clist ->
        let s = gen_sub clist (pos + 1) in
          Int.LF.Dot (Int.LF.Head (Int.LF.BVar pos), s)

    | k::clist ->
        let s = gen_sub clist (pos + 1) in
          gen_projs s pos (k, 1)

  and gen_projs s pos (k, index) =
    if k = index then
       Int.LF.Dot (Int.LF.Head (Int.LF.Proj (Int.LF.BVar pos, index)), s)
    else
      gen_projs (Int.LF.Dot (Int.LF.Head (Int.LF.Proj (Int.LF.BVar pos, index)), s))
        pos (k, index+1)

  in
    gen_sub conv_list 1
