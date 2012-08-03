(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

open Syntax
open Substitution

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
module RR = Store.Cid.NamedRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [7])

let rec conv_listToString clist = match clist with
  | [] -> " "
  | x::xs -> string_of_int x ^ ", " ^ conv_listToString xs

(* ************************************************************************ *)
let rec new_index k conv_list = match (conv_list, k) with
    | (d::conv_list', 1 ) -> d
    | (d::conv_list', _ ) -> d + new_index (k-1) conv_list'

let rec strans_norm sM conv_list = strans_normW (Whnf.whnf sM) conv_list
and strans_normW (tM, s) conv_list = match tM with
  | Int.LF.Lam(loc,x, tN) -> let tN' = strans_norm (tN, LF.dot1 s) (1::conv_list) in
      Int.LF.Lam(loc, x, tN')
  | Int.LF.Root(loc, h, tS) ->
      let h' = strans_head h conv_list in
      let tS' = strans_spine (tS, s) conv_list in
        Int.LF.Root(loc, h', tS')

and strans_head h conv_list = match h with
  | Int.LF.BVar x -> Int.LF.BVar (new_index x conv_list)
  | Int.LF.MVar (u, sigma) -> Int.LF.MVar(u, strans_sub sigma conv_list)
  | Int.LF.PVar (p, sigma) -> Int.LF.PVar(p, strans_sub sigma conv_list)
  | Int.LF.Proj (Int.LF.BVar x, j) ->
    let x' = (new_index x conv_list) - j + 1  in
      Int.LF.BVar x'

  | Int.LF.Proj (Int.LF.PVar (p, sigma), j) ->
      Int.LF.Proj (Int.LF.PVar (p, strans_sub sigma conv_list), j)

  | Int.LF.Proj (Int.LF.FPVar (p, sigma), j) ->
      Int.LF.Proj (Int.LF.FPVar (p, strans_sub sigma conv_list), j)

  | Int.LF.Const c -> Int.LF.Const c
  | Int.LF.FVar x -> Int.LF.FVar x
  | Int.LF.FMVar (u,s) -> Int.LF.FMVar (u, strans_sub s conv_list)
  | Int.LF.FPVar (u,s) -> Int.LF.FPVar (u, strans_sub s conv_list)
  | Int.LF.MMVar  (u, (ms, s)) ->
      let ms' = strans_msub ms conv_list in
      let s'  = strans_sub s conv_list in
        Int.LF.MMVar (u, (ms', s'))

and strans_msub ms conv_list = match ms with
  | Int.LF.MShift k -> Int.LF.MShift k
  | Int.LF.MDot (mf , ms) ->
      let mf' = strans_mfront mf conv_list in
      let ms' = strans_msub ms conv_list in
        Int.LF.MDot (mf',ms')

and strans_mfront mf conv_list = match mf with
  | Int.LF.MObj (phat, tM) ->
      Int.LF.MObj (phat, strans_norm (tM, LF.id) conv_list )
  | Int.LF.PObj (phat, h) ->
      Int.LF.PObj (phat, strans_head h conv_list)
  | Int.LF.MV u -> Int.LF.MV u
  | Int.LF.MUndef -> Int.LF.MUndef


and strans_sub s conv_list = match s with
  | Int.LF.Shift (ctx_offset, offset) ->
      let offset' = List.fold_left (fun x -> fun y -> x + y) 0 conv_list in
      let _ = dprint (fun () -> "conv_list = " ^ conv_listToString conv_list ) in
      let _ = dprint (fun () -> "Old offset " ^ string_of_int offset ) in
      let _ = dprint (fun () -> "New offset " ^ string_of_int offset') in
        Int.LF.Shift (ctx_offset, offset')
  | Int.LF.Dot (ft, s) ->
      Int.LF.Dot (strans_front ft conv_list, strans_sub s conv_list)

and strans_front ft  conv_list = match ft with
  | Int.LF.Head h -> Int.LF.Head (strans_head h conv_list)
  | Int.LF.Obj tM -> Int.LF.Obj (strans_norm (tM, LF.id) conv_list)
  | Int.LF.Undef -> Int.LF.Undef


and strans_spine (tS,s) conv_list = match tS with
  | Int.LF.Nil -> Int.LF.Nil
  | Int.LF.SClo (tS',s') -> strans_spine (tS', LF.comp s' s) conv_list
  | Int.LF.App (tM, tS) ->
    let tM' = strans_norm (tM, s) conv_list in
    let tS' = strans_spine (tS, s) conv_list in
      Int.LF.App (tM', tS')


let rec strans_typ sA conv_list = strans_typW (Whnf.whnfTyp sA) conv_list
and strans_typW (tA,s) conv_list = match tA with
  | Int.LF.Atom (loc, a, tS ) ->
     Int.LF.Atom (loc, a, strans_spine (tS, s) conv_list )

  | Int.LF.PiTyp ((Int.LF.TypDecl(x, tA), dep), tB) ->
    let tA' = strans_typ (tA, s) conv_list in
    let tB' = strans_typ (tB, LF.dot1 s) (1::conv_list) in
      Int.LF.PiTyp ((Int.LF.TypDecl(x,tA'), dep), tB')

  (* no sigma types allowed *)


let rec flattenSigmaTyp cPsi strec conv_list = match strec with
  | (Int.LF.SigmaLast tA, s) ->
      let tA' = strans_typ (tA,s) conv_list in
     (Int.LF.DDec (cPsi, Int.LF.TypDecl (Id.mk_name Id.NoName, tA')), 1)

  | (Int.LF.SigmaElem (x, tA, trec), s) ->
      let tA' = strans_typ (tA,s) conv_list in
      let (cPhi, k) = flattenSigmaTyp (Int.LF.DDec (cPsi, Int.LF.TypDecl (x, tA'))) (trec, LF.dot1 s)  (1::conv_list) in
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

let rec flattenDCtx cPsi = flattenDCtx' (Whnf.cnormDCtx (cPsi, Whnf.m_id))
and flattenDCtx' cPsi = match cPsi with 
  | Int.LF.Null -> (Int.LF.Null , [])
  | Int.LF.CtxVar psi -> (Int.LF.CtxVar psi , [] )
  | Int.LF.DDec (cPsi', Int.LF.TypDecl (x, tA)) -> 
      let (cPhi, conv_list) = flattenDCtx' cPsi' in 
        begin
          match Whnf.whnfTyp (tA, LF.id) with
            | (Int.LF.Sigma trec, s) -> let (cPhi', k) = flattenSigmaTyp cPhi (trec,s) conv_list in (cPhi', k::conv_list)
            | _          -> (Int.LF.DDec(cPhi, Int.LF.TypDecl(x, strans_typ (tA, LF.id) conv_list)), 1::conv_list)
        end

  | Int.LF.DDec (cPsi', Int.LF.TypDeclOpt x) -> 
      let (cPhi, conv_list) = flattenDCtx' cPsi' in
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
let rec gen_conv_sub conv_list  =
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


