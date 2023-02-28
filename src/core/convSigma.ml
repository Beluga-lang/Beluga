(**
   @author Renaud Germain
   @author Brigitte Pientka
*)

open Support.Equality
open Support

open Beluga_syntax
open Syntax
open Int
module S = Substitution

module P = Pretty.Int.DefaultPrinter

let fmt_ppr_conv_list =
  Format.(pp_print_list ~pp_sep: Support.Format.comma pp_print_int)

(* blockdeclInDctx is unused as of commit c899234fe2caf15a42699db013ce9070de54c9c8 -osavary *)
let rec _blockdeclInDctx =
  function
  | LF.Null -> false
  | LF.CtxVar psi -> false
  | LF.DDec (cPsi', LF.TypDecl (x, tA)) ->
     begin match Whnf.whnfTyp (tA, S.LF.id) with
     | (LF.Sigma _, _) -> true
     | _ -> _blockdeclInDctx cPsi'
     end
  | _ -> false

type error =
  | BlockInDctx of LF.mctx * LF.head * LF.typ * LF.dctx

type t = Id.offset list

exception Error of Location.t * error

let () =
  Error.register_exception_printer (function
      | Error (location, BlockInDctx (cD, h, tA, cPsi)) ->
      Error.located_exception_printer
        (Format.dprintf
           "Encountered contextual object [%a.%a] of type [%a.%a].@ \
            Unification cannot prune it because its context contains \
            blocks."
           (P.fmt_ppr_lf_dctx cD P.l0) cPsi
           (P.fmt_ppr_lf_head cD cPsi P.l0) h
           (P.fmt_ppr_lf_dctx cD P.l0) cPsi
           (P.fmt_ppr_lf_typ cD cPsi P.l0) tA)
        (List1.singleton location)
      | exn -> Error.raise_unsupported_exception_printing exn)

(* ************************************************************************ *)
let rec map conv_list k =
  match (conv_list, k) with
  | (d :: conv_list', 1) -> d
  | (d :: conv_list', _) -> d + map conv_list' (k - 1)


(*
  strans_norm cD cPsi sM conv_list = tM'

   If   cD |- cPsi   and cD ; cPsi |- sM
   and  cD |- flat_cPsi
        where conv_list relates cPsi to flat_cPsi, i.e. | conv_list | = |cPsi|
       s.t. if cPsi = xn:tBn, .... x1:tB1   and conv_list(i) = |tBi|
      (for example: cPsi = x2: block (y22:tA22, y21:tA21), x1:block (y13:tA13, y12:tA12, y11:tA11)
                    then conv_list = [2 ; 3]
   then
      cD ; flat_cPsi |- tM'

  NOTE: in principle the same thing should be achieved by simply [s_tup]sM where
     cD;  flat_cPsi |- s_tup : cPsi   and   cD ; cPsi |- sM

 *)
let rec strans_norm cD cPsi sM conv_list =
  strans_normW cD cPsi (Whnf.whnf sM) conv_list
and strans_normW cD cPsi (tM, s) conv_list =
  match tM with
  | LF.Lam (loc, x, tN) ->
     let tN' = strans_norm cD (LF.DDec (cPsi, LF.TypDeclOpt x)) (tN, S.LF.dot1 s) (1 :: conv_list) in
     LF.Lam (loc, x, tN')
  | LF.Root (loc, h, tS, plicity) ->
     let h' = strans_head loc cD cPsi h conv_list in
     let tS' = strans_spine cD cPsi (tS, s) conv_list in
     LF.Root (loc, h', tS', plicity)
  | LF.LFHole _ -> tM

and strans_head loc cD cPsi h conv_list =
  match h with
  | LF.BVar x -> LF.BVar (map conv_list x)

  | LF.MVar (LF.Offset u, sigma) ->
     LF.MVar (LF.Offset u, strans_sub cD cPsi sigma conv_list)

  | LF.MVar (u, sigma) ->
     LF.MVar (u, strans_sub cD cPsi sigma conv_list)

  | LF.PVar (p, sigma) -> LF.PVar (p, strans_sub cD cPsi sigma conv_list)

  | LF.Const c -> LF.Const c
  | LF.FVar x -> LF.FVar x
  | LF.FMVar (u, s) -> LF.FMVar (u, strans_sub cD cPsi s conv_list)
  | LF.FPVar (u, s) -> LF.FPVar (u, strans_sub cD cPsi s conv_list)
  | LF.MMVar ((u, ms), s) ->
     let ms' = strans_msub cD cPsi ms conv_list in
     let s' = strans_sub cD cPsi s conv_list in
     LF.MMVar ((u, ms'), s')

  | LF.MPVar ((u, ms), s) ->
     let ms' = strans_msub cD cPsi ms conv_list in
     let s' = strans_sub cD cPsi s conv_list in
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
     begin
       try
         ignore (Context.ctxDec cPsi x);
         (* check that there exists a typ declaration for x
            – if there is none, then it is mapped to itself. *)
         let x' = (map conv_list x) - j + 1 in
         LF.BVar x'
       with
       | _ -> LF.Proj (LF.BVar x, j)
     end

and strans_msub cD cPsi ms conv_list =
  match ms with
  | LF.MShift k -> LF.MShift k
  | LF.MDot (mf, ms) ->
     let mf' = strans_mfront cD cPsi mf conv_list in
     let ms' = strans_msub cD cPsi ms conv_list in
     LF.MDot (mf', ms')

and strans_mfront cD cPsi mf conv_list =
  match mf with
  | LF.ClObj (phat, LF.MObj tM) ->
     LF.ClObj (phat, LF.MObj (strans_norm cD cPsi (tM, S.LF.id) conv_list ))
  | LF.ClObj (phat, LF.PObj h) ->
     LF.ClObj (phat, LF.PObj (strans_head Location.ghost cD cPsi h conv_list))
  | LF.MV u -> LF.MV u
  | LF.MUndef -> LF.MUndef

and shift_conv_list n =
  function
  | (0, xs) -> n
  | (k, x :: xs) -> shift_conv_list (n + x) (k - 1, xs)

and strans_sub cD cPsi s conv_list =
  match s with
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

and strans_front cD cPsi ft conv_list =
  match ft with
  | LF.Head h -> LF.Head (strans_head Location.ghost cD cPsi h conv_list)
  | LF.Obj tM -> LF.Obj (strans_norm cD cPsi (tM, S.LF.id) conv_list)
  | LF.Undef -> LF.Undef


and strans_spine cD cPsi (tS, s) conv_list =
  match tS with
  | LF.Nil -> LF.Nil
  | LF.SClo (tS', s') -> strans_spine cD cPsi (tS', S.LF.comp s' s) conv_list
  | LF.App (tM, tS) ->
     let tM' = strans_norm cD cPsi (tM, s) conv_list in
     let tS' = strans_spine cD cPsi (tS, s) conv_list in
     LF.App (tM', tS')


let rec strans_typ cD cPsi sA conv_list =
  strans_typW cD cPsi (Whnf.whnfTyp sA) conv_list
and strans_typW cD cPsi (tA, s) conv_list =
  match tA with
  | LF.Atom (loc, a, tS ) ->
     LF.Atom (loc, a, strans_spine cD cPsi (tS, s) conv_list )

  | LF.PiTyp ((LF.TypDecl (x, tA), plicity), tB) ->
     let tA' = strans_typ cD cPsi (tA, s) conv_list in
     let tB' = strans_typ cD cPsi (tB, S.LF.dot1 s) (1 :: conv_list) in
     LF.PiTyp ((LF.TypDecl (x, tA'), plicity), tB')

  (* no sigma types allowed *)


let rec flattenSigmaTyp cD cPsi strec conv_list =
  match strec with
  | (LF.SigmaLast (n, tA), s) ->
     (* bp: this could be replaced by generating a substitution s_tup / s_proj and then
        applying this substitution to tA – this would remove calls to strans entirely *)
     let tA' = strans_typ cD cPsi (tA, s) conv_list in
     (LF.DDec (cPsi, LF.TypDecl (Name.mk_name Name.NoName, tA')), 1)

  | (LF.SigmaElem (x, tA, trec), s) ->
     let tA' = strans_typ cD cPsi (tA, s) conv_list in
     let (cPhi, k) =
       flattenSigmaTyp cD (LF.DDec (cPsi, LF.TypDecl (x, tA'))) (trec, S.LF.dot1 s) (1 :: conv_list)
     in
     (cPhi, k + 1)


let rec flattenDCtx' cD =
  function
  | LF.Null -> (LF.Null, [])
  | LF.CtxVar psi -> (LF.CtxVar psi, [])
  | LF.DDec (cPsi', LF.TypDecl (x, tA)) as cPsi ->
     let (cPhi, conv_list) = flattenDCtx' cD cPsi' in
     begin match Whnf.whnfTyp (tA, S.LF.id) with
     | (LF.Sigma trec, s) ->
        let (cPhi', k) = flattenSigmaTyp cD cPhi (trec, s) conv_list in
        ( cPhi'
        , k :: conv_list
        )
     | _ ->
        ( LF.DDec (cPhi, LF.TypDecl (x, strans_typ cD cPsi (tA, S.LF.id) conv_list))
        , 1 :: conv_list
        )
     end
  | LF.DDec (cPsi', LF.TypDeclOpt x) ->
     let (cPhi, conv_list) = flattenDCtx' cD cPsi' in
     ( LF.DDec (cPhi, LF.TypDeclOpt x)
     , 1 :: conv_list
     )


(* flattenDCtx cD cPsi = (cPsi', L)

   if    cD |- cPsi and cPsi contains possibly Sigma-types
         cPsi = ., bn:tBn, ... b0:tB0  and tBi = Sigma yik:Aik(i)...yi0:Ai0 or simply tBi = Ai0
         and k(i) is the #elements in tBi.
   then
         cD |- cPsi'  where all Sigma-types in cPsi have been flattened, i.e.

         cD |- . , ynk:Ank(n) .... yn0:An0, .... y0k:A0k(0), ... y00:A00


         and L is a vector [k(0) ; .... ; k(n)]


   Example:  cPsi  =  .,  bx:Sigma x:A.B,  y:A,  bw: Sigma w1:A  w2:A. A
       then flattenDCtx cPsi = (cPsi', L)
       where  cPsi' = ., x:A, x':B, y:A, w1:A, w2:A, w3:A
                L   =    [3,1,2]    (note reverse order since contexts are built in reverse order)
       and #elements (bx) = 2 ,#elements (y) = 1, #elements (bw) = 3
*)
let flattenDCtx cD cPsi =
  flattenDCtx' cD (Whnf.cnormDCtx (cPsi, Whnf.m_id))




(* gen_proj_sub conv_list =  s
   gen_tup_sub convlist = ss

   If cD |- cPsi   and    cD |- flat_cPsi
      where conv_list relates cPsi to flat_cPsi, i.e. | conv_list | = |cPsi|

   the
      cD ; cPsi      |- s : flat_cPsi
      cD ; flat_cPsi |- ss : cPsi
            and s is a projection substitution

   Example:
            cPsi:        g, b:block x:exp. nat
            flat_cPsi         g, x:exp, y:nat
            conv_list    [2]

   genConvSub generates:

            cPsi |- s   :        ^1, b.1 , b.2  : cPhi

   AND

         cPhi |-   s'  : ^2, <x,y>  : cPsi

 *)
(* NEW VERSIONS *)
let gen_proj_sub' conv_list =
  let rec gen_projs s k index =
    if k = index
    then LF.Dot (LF.Head (LF.Proj (LF.BVar 1, index)), s)
    else
      gen_projs
        (LF.Dot (LF.Head (LF.Proj (LF.BVar 1, index)), s))
        k (index + 1)
  in
  let rec gen_sub conv_list  =
    match conv_list with
    | [] -> LF.Shift 0  (* . |- . : .  and flat_cPsi = . = cPsi *)
    | 1 :: clist ->
       let s = gen_sub clist in  (* cPsi |- s : flat_cPsi *)
       Substitution.LF.dot1 s
       (* cPsi, x:tA |- s¹, x : flat_cPsi, x:tA *)
    | k :: clist ->
       let s = gen_sub clist in  (* cPsi |- s : flat_cPsi *)
       (* cPsi, b: tB |- s¹ : flat_cPsi *)
       gen_projs (Substitution.LF.comp s Substitution.LF.shift) k 1
  in
  gen_sub conv_list

let gen_tup_sub' conv_list =
  let rec gen_tup k  =
    if k = 1
    then
      (* only correct if pos stands for a variable of atomic type *)
      LF.Last (LF.Root (Location.ghost, LF.BVar k, LF.Nil, Plicity.explicit))
    else
      begin
        let tM = LF.Root (Location.ghost, LF.BVar k, LF.Nil, Plicity.explicit) in
        let tTup = gen_tup (k - 1) in
        LF.Cons (tM, tTup)
      end
  in
  let rec shift s n = if n = 0 then s else
                    shift (Substitution.LF.comp s Substitution.LF.shift) (n-1) in
  let rec gen_sub' conv_list  =
    match conv_list with
    | [] -> LF.Shift 0  (* . |- . : .  and flat_cPsi = . = cPsi *)
    | 1 :: clist ->
       let s = gen_sub' clist in  (* flat_cPsi |- s : cPsi *)
       Substitution.LF.dot1 s
    | k :: clist ->
       let s = gen_sub' clist in (* flat_cPsi |- s : cPsi *)
       let tM = gen_tup k  in  (* flat_cPsi, xk:Ak, ... x0:A0 |- <xn, ..., x0>  *)
       LF.Dot (LF.Obj (LF.Tuple (Location.ghost, tM)), shift s k)
  in
  gen_sub' conv_list


let gen_proj_sub conv_list =
  let l = List.length conv_list in (* length of cPsi *)
  let rec gen_projs s pos (k, index) =
    if k = index
    then LF.Dot (LF.Head (LF.Proj (LF.BVar pos, index)), s)
    else
      gen_projs
        (LF.Dot (LF.Head (LF.Proj (LF.BVar pos, index)), s))
        pos
        (k, index + 1)
  in
  let rec gen_sub conv_list pos =
    match conv_list with
    | [] -> LF.Shift l
    | 1 :: clist ->
       let s = gen_sub clist (pos + 1) in
       LF.Dot (LF.Head (LF.BVar pos), s)
    | k :: clist ->
       let s = gen_sub clist (pos + 1) in
       gen_projs s pos (k, 1)
  in
  gen_sub conv_list 1

let gen_tup_sub conv_list =
  let l' = List.fold_left (fun r x -> r + x) 0 conv_list in (* length of cPhi *)
  let rec gen_tup pos (k, index) =
    if k = index
    then
      (* only correct if pos stands for a variable of atomic type *)
      LF.Last (LF.Root (Location.ghost, LF.BVar pos, LF.Nil, Plicity.explicit))
    else
      begin
        let tM = LF.Root (Location.ghost, LF.BVar pos, LF.Nil, Plicity.explicit) in
        let tTup = gen_tup (pos - 1) (k, index + 1) in
        LF.Cons (tM, tTup)
      end
  in
  let rec gen_sub' conv_list pos =
    match conv_list with
    | [] -> LF.Shift l'
    | 1 :: clist ->
       let s = gen_sub' clist (pos + 1) in
       LF.Dot (LF.Head (LF.BVar pos), s)
    | k :: clist ->
       let s = gen_sub' clist (pos + k) in
       (* let tM = gen_tup pos (k, 1) in *)
       let tM = gen_tup (pos + k - 1) (k, 1) in
       LF.Dot (LF.Obj (LF.Tuple (Location.ghost, tM)), s)
  in
  gen_sub' conv_list 1


  (*
(** Builds a tuple consisting of all valid projections for the given
    head. *)
let rec etaExpandTuple tRec h k =
  let open LF in
  let tM = Root (Location.ghost, Proj (h, k), Nil, Plicity.explicit) in
  match tRec with
  | SigmaLast (_, _) -> Last tM
  | LF.SigmaElem (_, _, tRec) ->
     LF.Cons (tM, etaExpandTuple tRec h (k + 1))
   *)

let rec etaExpandStrGeneric new_mxvar mk_head loc cD cPsi sA plicity n names =
  match Whnf.whnfTyp sA with
  | LF.Sigma tRec as tA, s ->
     (* XXX this doesn't do any strengthening !! -je *)
     let tH =
       mk_head ((new_mxvar n (cD, cPsi, LF.tclo tA s) plicity Inductivity.not_inductive, Whnf.m_id), s)
     in
     (*
     let tTup =
       etaExpandTuple tRec tH 1
     in
     LF.Tuple (Location.ghost, tTup)
      *)
     LF.Root (Location.ghost, tH, LF.Nil, Plicity.explicit)

  | (LF.Atom (_, a, _tS) as tP, s) ->
      let (cPhi, conv_list) = flattenDCtx cD cPsi in
      let s_proj = gen_proj_sub conv_list in
      let s_tup = gen_tup_sub conv_list in
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
      let u = new_mxvar n (cD, cPhi', LF.TClo (tQ, ssi')) plicity Inductivity.not_inductive in
      (* cPhi |- ss'    : cPhi'
         cPsi |- s_proj : cPhi
         cPsi |- comp  ss' s_proj   : cPhi' *)
      let ss_proj = S.LF.comp ss' s_proj in
      LF.Root
        ( loc
        , mk_head ((u, Whnf.m_id), ss_proj)
        , LF.Nil
        , Plicity.explicit
        )

  | (LF.PiTyp ((LF.TypDecl (x, tA), _), tB), s) ->
     let x = NameGen.renumber names x in
     let decl = LF.TypDecl (x, tA) in
     let cPsi' = LF.DDec (cPsi, S.LF.decSub decl s) in
     let tN =
       etaExpandStrGeneric new_mxvar mk_head loc cD cPsi' (tB, S.LF.dot1 s) plicity n (x :: names)
     in
     LF.Lam (loc, x, tN)

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
