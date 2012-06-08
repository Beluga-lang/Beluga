(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   code walk with Joshua Dunfield, Dec 3 2008
*)


(* The functor itself is called Make (hence Unify.Make to other modules);
   the instantiations EmptyTrail and StdTrail (hence Unify.EmptyTrail and Unify.StdTrail
   to other modules) are declared at the end of this file.
*)

open Syntax.Int.LF
open Syntax.Int
open Trail

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [15])

let numPruneSub = ref 0

(* let print_trail () = 
   Printf.printf "\nPruneSub failed because notInvertible : %d times.\n" !numPruneSub *)
  
    
module type UNIFY = sig
  
  type unifTrail

  exception Error of string
  
(*  val disallowUndefineds : (unit -> 'a) -> 'a *)
  
  (* trailing of variable instantiation *)

  val reset  : unit -> unit
  val mark   : unit -> unit
  val unwind : unit -> unit

  val instantiateMVar : normal option ref * normal * cnstr list -> unit
  val instantiatePVar : head   option ref * head   * cnstr list -> unit
  val instantiateCtxVar : dctx option ref * dctx -> unit

  val resetDelayedCnstrs : unit -> unit
  val resetGlobalCnstrs : unit -> unit
  val globalCnstrs : cnstr list ref
  val unresolvedGlobalCnstrs : unit -> bool

  val nextCnstr         : unit -> cnstr option
  val addConstraint     : cnstr list ref * cnstr -> unit
  val forceGlobalCnstr : cnstr list -> unit
  val solveConstraint   : cnstr -> unit

  val isPatSub          : sub  -> bool

  (* unification *)

  val intersection : psi_hat -> sub -> sub -> dctx -> (sub * dctx)

  exception Unify of string
  exception NotInvertible
  
  (* All unify* functions return () on success and raise Unify on failure *)
  val unify        : mctx -> dctx  -> nclo  -> nclo -> unit
  val unifyTyp     : mctx -> dctx  -> tclo  -> tclo -> unit
  val unifyTypRec  : mctx -> dctx  -> (typ_rec * sub) -> (typ_rec * sub) -> unit
  val unifyDCtx    : mctx -> dctx -> dctx -> unit
  val unify_phat   : psi_hat -> psi_hat -> unit
  
  val unifyCompTyp : mctx -> (Comp.typ * LF.msub) -> (Comp.typ * msub) -> unit
  val unifyMSub    : msub  -> msub -> unit
  val unifyCSub    : csub  -> csub -> unit
  
  val matchTerm    : mctx -> dctx -> nclo -> nclo -> unit 
  val matchTyp     : mctx -> dctx -> tclo -> tclo -> unit 
  val matchTypRec  : mctx -> dctx -> (typ_rec * sub) -> (typ_rec * sub) -> unit 


  type cvarRef =
    | MMVarRef of normal option ref
    | MVarRef of normal option ref
    | PVarRef of head option ref

  val pruneTyp : mctx -> dctx -> psi_hat -> tclo  -> (msub * sub)  -> cvarRef -> typ

end

(* Unification *)
(* Author: Brigitte Pientka *)
(* Trailing is taken from Twelf 1.5 *)

module Make (T : TRAIL) : UNIFY = struct

  open Substitution.LF
  module P = Pretty.Int.DefaultPrinter

  exception Unify of string

  exception NotInvertible
  
  exception Error of string

  type matchFlag = Matching | Unification

  (* Matching not fully implemented yet -bp *)

  let rec phatToDCtx phat = match phat with 
    | (None,      0) -> Null
    | (Some psi , 0) -> CtxVar psi
    | (ctx_v    , k) -> 
        DDec (phatToDCtx (ctx_v, k-1), TypDeclOpt (Id.mk_name Id.NoName)) 


  type cvarRef =
    | MMVarRef of normal option ref
    | MVarRef of normal option ref
    | PVarRef of head option ref


  let eq_cvarRef cv cv' = match (cv, cv') with
    | (MVarRef r, MVarRef r') -> r == r'
    | (PVarRef r, PVarRef r') -> r == r'
    | (_, _)                  -> false

  let rec raiseType cPsi tA = match cPsi with
    | Null -> tA
    | DDec (cPsi', decl) ->
        raiseType cPsi' (PiTyp ((decl, Maybe), tA))

  let rec emptySpine tS = match tS with
    | Nil -> true
    | SClo(tS, _s) -> emptySpine tS

  (* isPatSub s = B

     Invariant:

     If    Psi |- s : Psi' 
     and   s = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
     and  ni <= k or ni = _ for all 1 <= i <= m
  *)
  let rec isPatSub s = 
    (* let s = (Whnf.normSub s) in  *)
    begin match s with
    | Shift (_,_k)              -> true
    | Dot (Head(BVar n), s) ->
        let rec checkBVar s' = match s' with
          | Shift (_ , k)           -> n <= k
          | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
          | Dot (Head (Proj(BVar n', _)), s) -> n <> n' && checkBVar s 
          | Dot (Undef, s)          -> checkBVar s
          | _                       -> false
        in
          checkBVar s && isPatSub s

    | Dot (Undef, s)        -> isPatSub s

    | _                     -> false
    end 

  (* isProjPatSub s = B

     Invariant:

     If    Psi |- s : Psi' 
     and   s = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
     and  ni <= k or ni = _ for all 1 <= i <= m

     *** includes possibly projections ***
  *)
  let rec isProjPatSub s = 
    (* let s = (Whnf.normSub s) in  *)
    begin match s with
    | Shift (_,_k)              -> true
    | Dot (Head(BVar n), s) ->
        let rec checkBVar s' = match s' with
          | Shift (_ , k)           -> n <= k
          | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
          | Dot (Head (Proj(BVar n', _)), s) -> n <> n' && checkBVar s 
          | Dot (Undef, s)          -> checkBVar s
          | _                       -> false
        in
          checkBVar s && isProjPatSub s

    | Dot (Head(Proj(BVar n, index)), s) ->
        let rec checkBVar s' = match s' with
          | Shift (_ , k)           -> n <= k
          | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
          | Dot (Head (Proj(BVar n', index')), s) -> (n <> n' || index' <> index) && checkBVar s 
          | Dot (Undef, s)          -> checkBVar s
          | _                       -> false
        in
          checkBVar s && isProjPatSub s

    | Dot (Undef, s)        -> isProjPatSub s
    | _                     -> false
    end 


  (* isPatMSub t = B

     Invariant:

     If    cD |- t : cD' 
     and   t = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
     and  ni <= k or ni = _ for all 1 <= i <= m
  *)
  let rec isPatMSub t = 
    let t = (Whnf.cnormMSub t) in 
    begin match t with
    | MShift _k             -> true
    | MDot (MV n, t) ->
        let rec checkMVar s' = match s' with
          | MShift  k               -> n <= k
          | MDot (MV n', s)         -> n <> n' && checkMVar s
          | _                       -> false
        in
          checkMVar t && isPatMSub t
(*    | Dot (Obj tM , s)      -> 
        begin match tM with
          | Root(BVar n, tS) -> 
              let rec checkBVar s' = match s' with
                | Shift k                 -> n <= k
                | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
                | Dot (Undef, s)          -> checkBVar s
                | _                       -> false
              in
                emptySpine tS && checkBVar s && isPatSub s
          | _ -> false
        end 
*)    
    | MDot (MUndef, s)       -> isPatMSub s
    | _                     -> false
    end 

  (*-------------------------------------------------------------------------- *)
  (* Trailing and Backtracking infrastructure *)

  type action =
    | InstNormal of normal option ref
    | InstHead   of head   option ref
    | InstCtx    of dctx   option ref
    | Add        of cnstr list ref
    | Solve      of cnstr * constrnt   (* FIXME: names *)

  type unifTrail = action T.t

  let globalTrail : action T.t = T.trail()

  let rec undo action = (dprint (fun () -> "Call to UNDO\n") ; match action with
    | InstNormal refM         -> refM   := None
    | InstHead   refH         -> refH   := None
    | Add cnstrs              -> cnstrs := List.tl !cnstrs
    | Solve (cnstr, constrnt) -> cnstr  := constrnt)

  let rec reset  () = T.reset globalTrail

  let rec mark   () = T.mark globalTrail

  let rec unwind () = T.unwind globalTrail undo


  let rec solveConstraint ({contents=constrnt} as cnstr) =
    cnstr := Queued;
    T.log globalTrail (Solve (cnstr, constrnt))

  (* trail a function;
     if the function raises an exception,
       backtrack and propagate the exception  *)
  let rec trail f =
    let _ = mark  () in
      try f () with e -> (unwind (); raise e)
        
  (* ---------------------------------------------------------------------- *)

  let delayedCnstrs : cnstr list ref = ref []
  let globalCnstrs : cnstr list ref = ref []

  let resetDelayedCnstrs () = delayedCnstrs := []
  let resetGlobalCnstrs () = globalCnstrs := []

  let rec addConstraint (cnstrs, cnstr) = 
  (begin match cnstr with
    | {contents= (Eqn (cD0, cPsi, tM, tN))} -> 
        dprint (fun () -> "Add constraint: " ^ P.normalToString cD0 cPsi (tM, id)  ^ 
                   " = " ^ P.normalToString cD0 cPsi (tN, id))
    | _ -> () end ; 
   cnstrs := cnstr :: !cnstrs;
   T.log globalTrail (Add cnstrs))


  let rec nextCnstr () = match !delayedCnstrs with
    | []              -> None
    | cnstr :: cnstrL ->        
        delayedCnstrs := cnstrL;
        Some cnstr


  let rec instantiateCtxVar (ctx_ref, cPsi) =
    ctx_ref := Some cPsi;
    T.log globalTrail (InstCtx ctx_ref)


  let rec instantiatePVar (q, head, cnstrL) =
    q := Some head;
    (* screen screenUndefsHead head; *)
    T.log globalTrail (InstHead q);
    delayedCnstrs := cnstrL @ !delayedCnstrs;
    globalCnstrs := cnstrL @ !globalCnstrs


  let rec instantiateMVar (u, tM, cnstrL) =
     u := Some (Whnf.norm (tM, id)); 
(*    screen screenUndefs tM;
    u := Some tM; *)
    T.log globalTrail (InstNormal u);
    delayedCnstrs := cnstrL @ !delayedCnstrs;
    globalCnstrs := cnstrL @ !globalCnstrs



  let rec instantiateMMVar (u, tM, cnstrL) =
    u := Some tM;
    T.log globalTrail (InstNormal u);
    delayedCnstrs := cnstrL @ !delayedCnstrs;
    globalCnstrs := cnstrL @ !globalCnstrs


  (* ---------------------------------------------------------------------- *)
  (* Higher-order unification *)

  (* Preliminaries:

     cD: a context of contextual variables; this is modelled
         implicitly since contextual variables are implemented as
         references.  cD thus describes the current status of
         memory cells for contextual variables.


     phat: a context of LF bound variables, without their typing
          annotations. While technically cPsi (or hat (cPsi) = phat) does
          not play a role in the unification algorithm itself, it allows
          us to print normal terms and their types if they do not unify.

     tM: normal term that only contains MVar (MInst _, t) and
          PVar (PInst _, t), that is, all meta-variables and parameter
          variables are subject to instantiation. There are no bound
          contextual variables present, i.e. MVar (Offset _, t),
          PVar (Offset _, t).

          Normal terms are in weak head normal form; the following is
          guaranteed by whnf:

     - all meta-variables are of atomic type, i.e.

       H = (MVar (MInst (r, cPsi, tP, _), t)) where tP = Atom _

     - Since meta-variables are of atomic type, their spine will
       always be Nil, i.e.

        Root (MVar (MInst (r, cPsi, tP, _), t), Nil).

     - Weak head normal forms are either
         (Lam (x, tM), s)   or   (Root (H, tS), id).
     *)

  (* pruneMCtx cD (mt, cD1) ms = (mt', cD2)

     Invariant:

     If cD  |- mt <= cD1  and
        cD' |- ms <= cD   and (ms')^-1 = ms
     then
        cD1 |- mt' <= cD2
        where every declaration x:A[Psi] in cD2 is also in cD1
        and mt' is a weakened identity substitution.

        moreover:
        [mt]mt' = t'  s.t. cD  |- t'  <= cD2 ,
        and [ms']^-1 (t') = t'' exists
        and cD' |- t'' <= cD2
  *)

  let rec pruneMCtx' cD (t, cD1) ms = match (t, cD1) with
    | (MShift _k, Empty) ->
        (Whnf.m_id, Empty)

   | (MShift k, Dec (_, CDecl (_x, _w, _dep))) ->
       pruneMCtx' cD (MDot (MV (k + 1), MShift (k + 1)), cD1) ms

   | (MShift k, Dec (_, MDecl (_x, _tA, _cPsi))) ->
       pruneMCtx' cD (MDot (MV (k + 1), MShift (k + 1)), cD1) ms

   | (MShift k, Dec (_, PDecl (_x, _tA, _cPsi))) ->
       pruneMCtx' cD (MDot (MV (k + 1), MShift (k + 1)), cD1) ms


   | (MDot (MV k, mt), Dec (cD1, CDecl (g, w, dep))) ->
       let (mt', cD2) = pruneMCtx' cD (mt, cD1) ms in
         (* cD1 |- mt' <= cD2 *)
         begin match applyMSub k ms with
           | MUndef          ->
               (* Psi1, x:tA |- s' <= Psi2 *)
               (Whnf.mcomp mt' (MShift 1), cD2)

           | MV _n ->
               (* cD1, u:A[Psi] |- mt' <= cD2, u:([mt']^-1 (A[cPsi])) since
                  A = [mt']([mt']^-1 A)  and cPsi = [mt']([mt']^-1 cPsi *)
               (Whnf.mvar_dot1 mt',  Dec(cD2, CDecl(g, w, dep)))
         end



   | (MDot (MV k, mt), Dec (cD1, MDecl (u, tA, cPsi))) ->
       let (mt', cD2) = pruneMCtx' cD (mt, cD1) ms in
         (* cD1 |- mt' <= cD2 *)
         begin match applyMSub k ms with
           | MUndef          ->
               (* Psi1, x:tA |- s' <= Psi2 *)
               (Whnf.mcomp mt' (MShift 1), cD2)

           | MV _n ->
               (* cD1, u:A[Psi] |- mt' <= cD2, u:([mt']^-1 (A[cPsi])) since
                  A = [mt']([mt']^-1 A)  and cPsi = [mt']([mt']^-1 cPsi *)
               let mtt'  = Whnf.m_invert (Whnf.cnormMSub mt') in 
               let cPsi' = Whnf.cnormDCtx (cPsi, mtt') in 
               let tA'   = Whnf.cnormTyp  (tA , mtt') in 
               (Whnf.mvar_dot1 mt',  Dec(cD2, MDecl(u, tA', cPsi')))
         end


   | (MDot (MV k, mt), Dec (cD1, PDecl (u, tA, cPsi))) ->
       let (mt', cD2) = pruneMCtx' cD (mt, cD1) ms in
         (* cD1 |- mt' <= cD2 *)
         begin match applyMSub k ms with
           | MUndef          ->
               (* Psi1, x:tA |- s' <= Psi2 *)
               (Whnf.mcomp mt' (MShift 1), cD2)

           | MV _n ->
               (* cD1, u:A[Psi] |- mt' <= cD2, u:([mt']^-1 (A[cPsi])) since
                  A = [mt']([mt']^-1 A)  and cPsi = [mt']([mt']^-1 cPsi *)
               let mtt'  = Whnf.m_invert (Whnf.cnormMSub mt') in 
               let cPsi' = Whnf.cnormDCtx (cPsi, mtt') in 
               let tA'   = Whnf.cnormTyp  (tA , mtt') in 
               (Whnf.pvar_dot1 mt',  Dec(cD2, PDecl(u, tA', cPsi')))
         end
   | (MDot (MUndef, mt), Dec (cD1, _)) ->
       let (mt', cD2) = pruneMCtx' cD (mt, cD1) ms in
         (* cD1 |- mt' <= cD2 *)
         (Whnf.mcomp mt' (MShift 1), cD2)

  let pruneMCtx cD (t, cD1) ms = 
      pruneMCtx' cD (Whnf.cnormMSub t, cD1) ms


  (* intersection (phat, (s1, s2), cPsi') = (s', cPsi'')
     s' = s1 /\ s2 (see JICSLP'96 and Pientka's thesis)

     Invariant:
     If   D ; Psi  |- s1 : Psi'    s1 patsub
     and  D ; Psi  |- s2 : Psi'    s2 patsub
     then D ; Psi' |- s' : Psi'' for some Psi'' which is a subset of Psi'
     and  s' patsub   s.t.  [s1]s'  = [s2]s' 
  *)
  let rec intersection phat subst1 subst2 cPsi' = begin match (subst1, subst2, cPsi') with
    | (Dot (Head (BVar k1), s1), Dot (Head (BVar k2), s2), DDec (cPsi', TypDecl (x, tA)))  ->
        let (s', cPsi'') = intersection phat s1 s2 cPsi' in
          (* D ; Psi' |- s' : Psi'' where Psi'' =< Psi' *)
          if k1 = k2 then
            let ss' = invert (Whnf.normSub s') in
              (* cD ; cPsi'' |- ss' <= cPsi' *)
              (* by assumption:
                 cD ; cPsi' |- tA <= type *)
              (* tA'' = [(s')^-1]tA   and cPsi'' |- tA'' <= type *)

            (* let tA'' = TClo (tA, ss') in *)
            let tA'' = TClo (tA, ss') in

              (dot1 s', DDec (cPsi'', TypDecl(x, tA''))) 
              
          else  (* k1 =/= k2 *)
            (comp s' shift, cPsi'') 

    | (Dot (Head (Proj (BVar k1, index1)), s1), Dot (Head (Proj (BVar k2, index2)), s2), DDec (cPsi', TypDecl (x, tA)))  ->
        let (s', cPsi'') = intersection phat s1 s2 cPsi' in
          (* D ; Psi' |- s' : Psi'' where Psi'' =< Psi' *)
          if k1 = k2 && index1 = index2 then
            let ss' = invert (Whnf.normSub s') in
              (* cD ; cPsi'' |- ss' <= cPsi' *)
              (* by assumption:
                 cD ; cPsi' |- tA <= type *)
              (* tA'' = [(s')^-1]tA   and cPsi'' |- tA'' <= type *)

            (* let tA'' = TClo (tA, ss') in *)
            let tA'' = TClo (tA, ss') in

              (dot1 s', DDec (cPsi'', TypDecl(x, tA''))) 
              
          else  (* k1 =/= k2 or index1 =/= index2 *)
            (comp s' shift, cPsi'') 


    | (Dot (Undef, s1), Dot (Head (BVar _k2), s2), DDec (cPsi', TypDecl _)) ->
        let (s', cPsi'') = intersection phat s1 s2 cPsi' in
            (comp s' shift, cPsi'')

    | (Dot (Undef, s1), Dot (Head (Proj(BVar _k2, _)), s2), DDec (cPsi', TypDecl _)) ->
        let (s', cPsi'') = intersection phat s1 s2 cPsi' in
            (comp s' shift, cPsi'')


    | (Dot (Head (BVar _k), s1), Dot (Undef, s2), DDec (cPsi', TypDecl _ )) ->
        let (s', cPsi'') = intersection phat s1 s2 cPsi' in
            (comp s' shift, cPsi'')

    | (Dot (Head (Proj(BVar _k, _)), s1), Dot (Undef, s2), DDec (cPsi', TypDecl _ )) ->
        let (s', cPsi'') = intersection phat s1 s2 cPsi' in
            (comp s' shift, cPsi'')

    | (Dot (Undef, s1), Dot (Undef, s2), DDec (cPsi', TypDecl _)) ->
        let (s', cPsi'') = intersection phat s1 s2 cPsi' in
            (comp s' shift, cPsi'')

    | ((Dot _ as s1), Shift (psi, n2), cPsi) ->
        intersection phat s1 (Dot (Head (BVar (n2 + 1)), Shift (psi, n2 + 1))) cPsi

    | (Shift (psi, n1), (Dot _ as s2), cPsi) ->
        intersection phat (Dot (Head (BVar (n1 + 1)), Shift (psi, n1 + 1))) s2 cPsi

    | (Shift (NoCtxShift, _k), Shift (NoCtxShift, _k'), cPsi) -> (id, cPsi) 
        (* both substitutions are the same number of shifts by invariant *)

    | (Shift (CtxShift _psi, _k), Shift (CtxShift _psi', _k'), cPsi) -> (id, cPsi)
        (* psi = psi' and k = k' by invariant *)

    | (Shift (NegCtxShift _psi, _k), Shift (NegCtxShift _psi', _k'), cPsi) -> (id, cPsi)
        (* psi = psi' and k = k' by invariant *)

    (* all other cases impossible for pattern substitutions *)

    | (_s1, _s2, _cPsi )  -> 
           raise (Error "Intersection not defined")
  end 

  (* m_intersection (mt1, mt2) cD' = (mt', cD'')
     (adapted from intersection code above)

     Invariant:
     If   D    |- mt1 : cD'    mt1 patsub
     and  D    |- mt2 : cD'    mt2 patsub
     then  cD' |- mt' : cD'' for some cD'' which is a subset of cD'
     and  mt' patsub   s.t.  [mt1]mt'  = [mt2]mt' 
  *)
  let rec m_intersection  subst1 subst2 cD' = begin match (subst1, subst2, cD') with
    | (MDot (MV k1, mt1), MDot (MV k2, mt2), Dec (cD', MDecl (x, tA, cPsi))) ->
        let (mt', cD'') = m_intersection  mt1 mt2 cD' in
          (* cD' |- mt' : cD'' where cD'' =< cD' *)
          if k1 = k2 then
            let mtt' = Whnf.m_invert (Whnf.cnormMSub mt') in
              (* cD'' |- mtt' <= cD' *)
              (* by assumption:
                 cD' ; cPsi |- tA <= type *)
              (* tA'' = [(mt')^-1]tA   and cPsi'' = [(mt')^-1]cPsi 
                 cD'' ; cPsi'' |- tA'' <= type  *)
              (* NOTE: Can't create m-closures CtxMClo(cPsi, mtt') and TMClo(tA'', mtt') *)
            let cPsi''  = Whnf.cnormDCtx (cPsi, mtt') in 
            let tA''    = Whnf.cnormTyp (tA, mtt') in 
              (Whnf.mvar_dot1 mt', Dec (cD'', MDecl(x, tA'', cPsi''))) 
              
          else  (* k1 =/= k2 *)
            (Whnf.mcomp mt' (MShift 1), cD'') 

    | (MDot (MUndef, mt1), MDot (MV _k2, mt2), Dec (cD', MDecl _)) ->
        let (mt', cD'') = m_intersection  mt1 mt2 cD' in
            (Whnf.mcomp mt' (MShift 1), cD'')

    | (MDot (MUndef, mt1), MDot (MV _k2, mt2), Dec (cD', PDecl _)) ->
        let (mt', cD'') = m_intersection  mt1 mt2 cD' in
            (Whnf.mcomp mt' (MShift 1), cD'')

    | (MDot (MV _k, mt1), MDot (MUndef, mt2), Dec (cD', _ )) ->
        let (mt', cD'') = m_intersection mt1 mt2 cD' in
            (Whnf.mcomp mt' (MShift 1), cD'')


    | (MDot (MUndef, mt1), MDot (MUndef, mt2), Dec (cD', _)) ->
        let (mt', cD'') = m_intersection mt1 mt2 cD' in
            (Whnf.mcomp mt' (MShift 1), cD'')

    | (MDot _ as mt1, MShift  n2, cD) ->
        m_intersection  mt1 (MDot (MV (n2 + 1), MShift  (n2 + 1))) cD

    | (MShift n1, (MDot _ as mt2), cD) ->
        m_intersection (MDot (MV (n1+1), MShift (n1 + 1))) mt2 cD

    | (MShift _k, MShift _k', cD) -> (MShift 0, cD)
      (* both substitutions are the same number of shifts by invariant *)

    (* all other cases impossible for pattern substitutions *)

    | (_mt1, _mt2, _cC )  -> 
           raise (Error "m-intersection not defined")
  end 


  (* invNorm cD0 (cPsi, (tM, s), ss, rOccur) = [ss](tM[s])

     Invariant:

    if D ; Psi  |- s <= Psi'
       D ; Psi' |- tM <= tA  (D ; Psi |- tM[s] <= tA[s])

       D ; Psi'' |- ss  <= Psi  and ss = (ss')^-1
       D ; Psi   |- ss' <= Psi''

     Effect:

     Raises NotInvertible if [ss](tM[s]) does not exist
     or rOccurs occurs in tM[s].

     Does NOT prune MVars or PVars in tM[s] according to ss;
     fails  instead.
  *)
  let rec invNorm cD0 (phat, sM, ss, rOccur) =
    let _ : (msub * sub) = ss in 
    invNorm' cD0 (phat, Whnf.whnf sM, ss, rOccur)

  and invNorm' cD0 ((cvar, offset) as phat, sM, ((ms, ssubst) as ss), rOccur) = match sM with
    | (Lam (loc, x, tM), s) ->
        Lam (loc, x, invNorm cD0 ((cvar, offset + 1), (tM, dot1 s), (ms, dot1 ssubst), rOccur))

    | (Root (loc, MVar (Inst (_n, r, cPsi1, _tP, _cnstrs) as u, t), _tS (* Nil *)), s) -> 
        (* by invariant tM is in whnf and meta-variables are lowered;
           hence tS = Nil and s = id *)
        let ( _ , ssubst) = ss in 
        if eq_cvarRef (MVarRef r) rOccur then
          raise NotInvertible
        else
          let t' = Monitor.timer ("Normalisation", fun () -> Whnf.normSub (comp t s) (* t' = t, since s = Id *)) in
            (* D ; Psi |- s <= Psi'   D ; Psi' |- t <= Psi1
               t' =  t o s     and    D ; Psi  |-  t' <= Psi1 *)
            if isPatSub t' then
              let (s', _cPsi2) = pruneCtx phat (t', cPsi1) ss in
                (* D ; Psi  |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then
                  Root(loc, MVar(u, comp t' ssubst), Nil)
                else
                  raise NotInvertible
            else (* t' not patsub *)
              Root(loc, MVar(u, invSub cD0 phat (t', cPsi1) ss rOccur), Nil)

   | (Root (loc, MMVar (MInst (_n, r, cD, cPsi1, _tP, _cnstrs) as u, (mt,s')), _tS (* Nil *)), s) -> 
        (* by invariant tM is in whnf and meta-variables are lowered;
           hence tS = Nil and s = id *) 
        if eq_cvarRef (MVarRef r) rOccur then 
          raise NotInvertible 
        else 
          let s0 = Monitor.timer ("Normalisation", fun () -> Whnf.normSub (comp s' s) (* s0 = s', since s = Id *)) in  
            (* D ; Psi |- s <= Psi'   D ; Psi' |- t <= Psi1
               s0 =  s' o s     and    D ; Psi  |-  s0 <= Psi1 *)
            if isPatSub s0 && isPatMSub mt then  
              let (s0', _cPsi2) = pruneCtx phat (s0, cPsi1) ss in  
              let (mt0, _cD2)   = pruneMCtx cD0 (mt, cD) ms in  
                (* cD ; cPsi  |- s0  <= cPsi1 and
                 * cD ; cPsi1 |- s0' <= cPsi2 and
                 * cD ; cPsi  |- [s0]s0' <= cPsi2 
                 *
                 * cD  |- mt  <= cD1  and
                 * cD1 |- mt0 <= cD2  and
                 * cD  |- [mt]mt0 <= cD2
                 *)

                if isId s0' && isMId mt0 then 
                  Root(loc, MMVar(u, (Whnf.mcomp mt ms, comp s0 ssubst)), Nil) 
                else
                  raise NotInvertible
            else (* s0 not patsub *)
              Root(loc, MMVar(u, (invMSub cD0 (mt, cD) ms rOccur ,  
                                  invSub cD0 phat (s0, cPsi1) ss rOccur)), Nil)

    | (Root (loc, MVar (Offset u, t), _tS (* Nil *)), s (* id *)) ->
        let t' = comp t s (* t' = t, since s = Id *) in
        let (_, _tA, cPsi1) = Whnf.mctxMDec cD0 u in 
          begin match applyMSub u ms with 
            | MV v -> 
                Root(loc, MVar(Offset v, invSub cD0 phat (t', cPsi1) ss rOccur), Nil)
            | MUndef -> raise NotInvertible
          end 

    | (Root (loc, FMVar (u, t), _tS (* Nil *)), s (* id *)) ->
        let (cD_d, MDecl(_, _tA, cPsi1)) = Store.FCVar.get u in 
	let d = Context.length cD0 - Context.length cD_d in 
	let cPsi1 = if d = 0 then cPsi1 else 
	   Whnf.cnormDCtx (cPsi1, MShift d) in 
        let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
          Root (loc, FMVar (u, s'), Nil)

    | (Root (loc, FPVar (p, t), _tS (* Nil *)), s (* id *)) ->
        let (cD_d, PDecl (_, _tA, cPsi1)) = Store.FCVar.get p in 
	let d = Context.length cD0 - Context.length cD_d in 
	let cPsi1 = if d = 0 then cPsi1 else 
	  Whnf.cnormDCtx (cPsi1, MShift d) in 
        let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
          Root (loc, FPVar (p, s'), Nil)

    | (Root (loc, PVar (Offset p, t), _tS (* Nil *)), s (* id *)) ->
        let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
        let t' = comp t s (* t' = t, since s = Id *) in
          begin match applyMSub p ms with
            | MV q -> 
                Root(loc, PVar(Offset q, invSub cD0 phat (t', cPsi1) ss rOccur), Nil)
            | MUndef -> raise NotInvertible
          end 

    | (Root (loc, PVar (PInst (_n, r, cPsi1, _tA, _cnstrs) as q, t), tS), s) ->
        (* by invariant tM is in whnf and meta-variables are lowered and s = id *)
        let ( _ , ssubst) = ss in 
        if eq_cvarRef (PVarRef r) rOccur then
          raise NotInvertible
        else
          let t' = Monitor.timer ("Normalisation", fun () -> Whnf.normSub(comp t s) (* t' = t, since s = Id *)) in
            (* D ; Psi |- s <= Psi'   D ; Psi' |- t <= Psi1
               t' =  t o s
               D ; Psi |-  t' <= Psi1 *)
            if isPatSub t' then
              let (s', _cPsi2) = pruneCtx phat (t', cPsi1) ss in
                (* D ; Psi' |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then (* cPsi1 = cPsi2 *)
                  Root (loc, PVar (q, comp t' ssubst), 
                        invSpine cD0 (phat, (tS, s), ss, rOccur))
                else
                  raise NotInvertible
            else (* t' not patsub *)
              Root (loc, PVar (q, invSub cD0 phat (t', cPsi1) ss rOccur),
                    invSpine cD0 (phat, (tS,s), ss, rOccur))

    | (Root (loc, Proj (PVar (PInst (_n, r, cPsi1, _tA, _cnstrs) as q, t), i), tS), s) ->
        let ( _ , ssubst) = ss in 
        if eq_cvarRef (PVarRef r) rOccur then
          raise NotInvertible
        else
          let t' = Monitor.timer ("Normalisation", fun () -> Whnf.normSub (comp t s)   (* t' = t, since s = Id *)) in
            if isPatSub t' then
              let (s', _cPsi2) = pruneCtx phat (t', cPsi1) ss in
                (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                   t' =  t o s r
                   cD ; cPsi |-  t' <= cPsi1 and
                   cD ; cPsi1 |- s' <= cPsi2 and
                   cD ; cPsi  |- [t']s' <= cPsi2  *)
                if isId s' then (* cPsi1 = cPsi2 *)
                  Root (loc, Proj (PVar(q, comp t' ssubst), i),
                        invSpine cD0 (phat, (tS,s), ss, rOccur))
                else
                  raise NotInvertible
            else (* t' not patsub *)
              Root (loc, Proj (PVar (q, invSub cD0 phat (t', cPsi1) ss rOccur), i),
                    invSpine cD0 (phat, (tS,s), ss, rOccur))

    | (Root (loc, head, tS), s (* = id *)) ->
        Root (loc, invHead  cD0 (phat, head , ss, rOccur),
              invSpine cD0 (phat, (tS, s), ss, rOccur))

    | (Tuple(loc, trec), s) -> 
         Tuple(loc, invTuple cD0 (phat, (trec,s), ss, rOccur))

  and invTuple cD0 (phat, trec, ss, rOccur) = match trec with
    | (Last tM,s)  -> Last (invNorm cD0 (phat, (tM,s), ss, rOccur)) 
    | (Cons (tM, trec'), s) -> 
        let tN = invNorm cD0 (phat, (tM,s), ss, rOccur) in 
        let trec'' = invTuple cD0 (phat, (trec',s), ss, rOccur) in 
          Cons (tN, trec'')

  and invSpine cD0 (phat, spine, ss, rOccur) = match spine with
    | (Nil          , _s) -> Nil
    | (App (tM, tS) ,  s) ->
        App (invNorm  cD0 (phat, (tM, s), ss, rOccur),
             invSpine cD0 (phat, (tS, s), ss, rOccur))
    | (SClo (tS, s'),  s) ->
        invSpine cD0 (phat, (tS, comp s' s), ss, rOccur)


  (* invHead(phat, head, ss, rOccur) = h'
     cases for parameter variable and meta-variables taken
     care in invNorm' *)
  and invHead cD0 (phat, head, ((ms, ssubst) as ss), rOccur) = match head with
    | BVar k            ->
        begin match bvarSub k ssubst with
          | Undef          -> raise NotInvertible
          | Head (BVar k') -> BVar k'
        end

    | Const _           ->
        head

    | Proj (BVar k, _i) ->
        let (_ , ssubst) = ss in 
        begin match bvarSub k ssubst with
          | Head (BVar _k' as head) -> head
          | Undef                   -> raise NotInvertible
        end

    | FVar _x           -> head
      (* For any free variable x:tA, we have  . |- tA <= type ;
         Occurs check is necessary on tA Dec 15 2008 -bp  :(
       *)

    | MVar (Inst (_n, r, cPsi1, _tP, _cnstrs) as u, t) -> 
        if eq_cvarRef (MVarRef r) rOccur then
          raise NotInvertible
        else
          let t = Monitor.timer ("Normalisation", fun () -> Whnf.normSub t) in 
          if isPatSub t then
            let (_ , ssubst) = ss in 
            let (s', _cPsi2) = pruneCtx phat (t, cPsi1) ss in
                (* D ; Psi  |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then
                  MVar(u, comp t ssubst)
                else
                  raise NotInvertible
            else (* t' not patsub *)
              MVar(u, invSub cD0 phat (t, cPsi1) ss rOccur)

    | MVar (Offset u, t) -> 
        let (_, _tA, cPsi1) = Whnf.mctxMDec cD0 u in 
          begin match applyMSub u ms with 
            | MV v -> 
                MVar(Offset v, invSub cD0 phat (t, cPsi1) ss rOccur)
            | MUndef -> raise NotInvertible
          end 


    | PVar (Offset p, t) -> 
        let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
          begin match applyMSub p ms with 
            | MV q -> 
                PVar(Offset q, invSub cD0 phat (t, cPsi1) ss rOccur)
            | MUndef -> raise NotInvertible
          end 


    | PVar (Inst (_n, r, cPsi1, _tP, _cnstrs) as u, t) -> 
        let t = Monitor.timer ("Normalisation", fun () -> Whnf.normSub t) in 
        if eq_cvarRef (MVarRef r) rOccur then
          raise NotInvertible
        else
          if isPatSub t then
            let (_ , ssubst) = ss in 
              let (s', _cPsi2) = pruneCtx phat (t, cPsi1) ss in
                (* D ; Psi  |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then
                  PVar(u, comp t ssubst)
                else
                  raise NotInvertible
            else (* t' not patsub *)
              PVar(u, invSub cD0 phat (t, cPsi1) ss rOccur)

    | Proj(PVar (Offset p, t), i) -> 
        let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
          begin match applyMSub p ms with 
            | MV q -> 
                Proj(PVar(Offset q, invSub cD0 phat (t, cPsi1) ss rOccur), i)
            | MUndef -> raise NotInvertible
          end 


    | Proj(PVar (Inst (_n, r, cPsi1, _tP, _cnstrs) as u, t), i) -> 
        let t = Monitor.timer ("Normalisation", fun () -> Whnf.normSub t) in 
        if eq_cvarRef (MVarRef r) rOccur then
          raise NotInvertible
        else
          if isPatSub t then
            let (_ , ssubst) = ss in 
              let (s', _cPsi2) = pruneCtx phat (t, cPsi1) ss in
                (* D ; Psi  |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then
                  Proj(PVar(u, comp t ssubst), i)
                else
                  raise NotInvertible
            else (* t' not patsub *)
              PVar(u, invSub cD0 phat (t, cPsi1) ss rOccur)





  (* invSub cD0 (phat, s, ss, rOccur) = s'

     if phat = hat(Psi)  and
        D ; Psi  |- s <= Psi'
        D ; Psi''|- ss <= Psi
     then s' = [ss]s   if it exists, and
        D ; cPsi'' |- [ss]s <= cPsi'
   *)
  and invSub cD0 phat (s, cPsi1) ((_ms , ssubst) as ss) rOccur = match (s, cPsi1) with
    | (Shift (psi, n), DDec(_cPsi', _dec)) ->
        invSub cD0 phat (Dot (Head (BVar (n + 1)), Shift (psi, n + 1)), cPsi1) ss rOccur

    | (Shift (psi, n), Null) -> 
        let r = comp (Shift (psi, n)) ssubst  in 
          r
      (* Sat Dec 27 15:45:18 2008 -bp DOUBLE CHECK *)
      (* must be defined -- n = offset
       * otherwise it is undefined 
       *)

    | (Shift (psi, n), CtxVar _psi) -> comp (Shift (psi, n)) ssubst
        (* Sat Dec 27 15:45:18 2008 -bp DOUBLE CHECK *)
        (* must be defined -- n = offset
         * otherwise it is undefined 
         *)

    | (Dot (Head (BVar n), s'), DDec(cPsi', _dec)) ->
        begin match bvarSub n ssubst with
          | Undef -> 
              (* let si = invSub cD0 phat (s', cPsi') ss rOccur in *)
                (* Dot(Undef, si)  *)
                raise NotInvertible
                  (* Mon Feb  9 14:37:27 2009 -bp : previously raise NotInvertible) *)
          | ft   -> Dot (ft , invSub cD0 phat (s', cPsi') ss rOccur)
        end

    | (Dot (Head (Proj (BVar n, k)), s'), DDec(cPsi', _dec)) ->
        begin match bvarSub n ssubst with
          | Undef -> 
              let si = invSub cD0 phat (s', cPsi') ss rOccur in 
                Dot(Undef, si) 
                  (* Mon Feb  9 14:37:27 2009 -bp : previously raise NotInvertible) *)
          | Head(BVar m)  -> 
              Dot (Head (Proj (BVar m, k)) , invSub cD0 phat (s', cPsi') ss rOccur)
          | _ -> raise NotInvertible
        end


    | (Dot (Obj tM, s'), DDec(cPsi', _dec))        ->
        (* below may raise NotInvertible *)
        let tM' = invNorm cD0 (phat, (tM, id), ss, rOccur) in 
          Dot (Obj tM', invSub cD0 phat (s', cPsi') ss rOccur)

    | _ -> (dprint (fun () -> "invSub -- undefined") ; raise (Error "invSub -- undefined"))



  (* invMSub cD0 (mt, cD') ms rOccur = mt'

     if cD  |- mt <= cD'
        cD''|- ms <= cD
     then mt' = [ms]mt   if it exists, and
        D'' |- [ms]mt <= cD'
   *)
  and invMSub cD0 (mt, cD1) ms  rOccur = match (mt, cD1) with
    | (MShift n, Dec(_cD', _dec)) ->
        invMSub cD0 (MDot (MV (n + 1), MShift (n + 1)), cD1) ms rOccur

    | (MShift  n, Empty) -> Whnf.mcomp (MShift  n) ms  

    | (MDot (MV n, mt'), Dec(cD', _dec)) ->
        begin match applyMSub n ms with
          | MUndef -> 
              let msi = invMSub cD0 (mt', cD') ms rOccur in 
                MDot(MUndef, msi) 
                (* Mon Feb  9 14:37:27 2009 -bp : previously raise NotInvertible) *)
          | ft    -> MDot (ft, invMSub cD0 (mt', cD') ms rOccur)
        end

    | (MDot (MObj (phat, tM), mt'), Dec(cD', MDecl _))        ->
        (* below may raise NotInvertible *)
        let tM' = invNorm cD0 (phat, (tM, id), (ms, id), rOccur) in 
          MDot (MObj (phat, tM'), invMSub cD0 (mt', cD') ms rOccur)


    | (MDot (PObj (phat, h), mt'), Dec(cD', PDecl _))        ->
        (* below may raise NotInvertible *)
        let h' = invHead cD0 (phat, h, (ms, id), rOccur) in 
          MDot (PObj (phat, h'), invMSub cD0 (mt', cD') ms rOccur)





  (* prune cD0 cPsi'' (phat, (tM, s), ss, rOccur) = tM'

     Given: cD ; cPsi  |- s <= cPsi'  and
            cD ; cPsi' |- tM <= tA    and phat = hat(cPsi)
            ss = (ss')^-1 is a pattern substitution where

     cD ; cPsi   |- ss' <= cPsi''
     cD ; cPsi'' |- ss  <= cPsi    where  ss = (ss')^-1

     succeeds, returning (tM', sc')
          if
            - rOccur does not occur in tM
            - there exists a pruning substitution rho s.t.
              cD' |- rho <= cD   and [ss]([|rho|]([s]tM)) = tM' exists.

          where cD' ; [|rho|]cPsi'' |- tM' <= tA'
            and tA' = [ss]([|rho|]([s]tA)) will exist

         effect
         - MVars and PVars in tM are pruned;

     can fail:

       - raises Unify if rOccur occurs in tM (occurs check)
         or [ss]([|rho|][s]tM) does not exist,

       - raises NotInvertible if there exist meta-variables u[t] where t is not a
         pattern substitution and [ss](t) does not exist
  *)

  and prune  cD0 cPsi' phat sM ss rOccur =
    let _qq : (msub * sub) = ss in 
      prune' cD0 cPsi' phat (Whnf.whnf sM) ss rOccur

  and prune' cD0 cPsi' ((cvar, offset) as phat) sM ss rOccur = match sM with
    | (Lam (loc, x, tM),   s) ->
        let (ms, ssubst) = ss in 
        let tM' = prune cD0 (DDec(cPsi', TypDeclOpt (Id.mk_name Id.NoName))) 
                        (cvar, offset + 1) (tM, dot1 s) (ms, dot1 ssubst) rOccur in
          Lam (loc, x, tM')

    | (Tuple (loc, tuple),   s) ->
        let tuple' = pruneTuple cD0 cPsi' phat (tuple, s) ss rOccur in
          Tuple (loc, tuple')

    | (Root (loc, head, tS),   s) ->
        let (ms , ssubst) = ss in 
        let returnNeutral newHead =
          let tS' = pruneSpine cD0 cPsi' phat (tS, s) ss rOccur in 
            Root (loc, newHead, tS')
        in
          match head with
            | MMVar (MInst (_n, r, cD1, cPsi1, tP, cnstrs) as _u, (mt, t)) ->  (* s = id *)
              (* cD |- t <= cD1
                 cD ; cPsi |- t <= [|mt|]Psi1    
                 cD ; cPsi |- [t]([|mt|]tP) 
              *)
                let tM = Root(loc, head, tS) in
                let t  = Whnf.normSub t in 
                  (* by invariant: MVars are lowered since tM is in whnf *)
                  if eq_cvarRef (MMVarRef r) rOccur then
                    raise (Unify "Variable occurrence")
                  else
                    if isPatSub t && isPatMSub mt then
                      let (id_sub, cPsi2) = pruneCtx phat (comp t s, cPsi1) ss in
                        (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= [|mt|]cPsi1
                           cD ; cPsi |-  t o s <= [|mt|]cPsi1 and
                           cD ; [|mt|]cPsi1 |- id_sub <= cPsi2 and
                           cD ; cPsi |- t o s o idsub <= cPsi2 *)
                      let (id_msub, cD2) = pruneMCtx cD0 (mt, cD1) ms in
                        (* cD  |- mt <= cD1  
                         * cD1 |- id_msub <=  cD2
                         * cD  |- [|mt|]id_msub <= cD2
                         * 
                         * Note: cD |- cPsi2 ctx  and cD1 ; cPsi1 |- tP <= type
                         *       cD ; [|mt|]cPsi1 |- [|mt|]tP <= type
                         *)
                      let i_id_sub  = invert id_sub in 
                      let i_msub = Whnf.m_invert (Whnf.mcomp id_msub mt) in 
                        (* cD2 |- i_msub <= cD 
                         * cD ; cPsi2 |- i_id_sub <= cPsi1
                         * cD2 ; [|i_msub|]cPsi2 |- [|i_msub|]i_id_sub <= [|i_msub|]cPsi1
                         * 
                         * and more importantly: cD2 |- [|i_msub|]cPsi2 ctx
                         *)
                      let i_id_msub = Whnf.m_invert id_msub in 
                        (* cD2 |- i_id_msub <= cD1 
                         * cD2 ; [|i_id_msub|]cPsi1 |- [|i_id_msub|]tP <= type
                         * cD2 ; [|i_msub|]cPsi2 |- [i_sub][|i_id_msub|]tP <= type
                        *)
                      let cPsi2' = Whnf.cnormDCtx (cPsi2, i_msub) in 
                      let i_sub  = Whnf.cnormSub (i_id_sub, i_msub) in 
                      let tP'    = Whnf.cnormTyp (tP, i_id_msub) in 

                      let v = Whnf.newMMVar(cD2, cPsi2', TClo(tP', i_sub)) in
                        (instantiateMMVar (r, Root (loc, MMVar (v, (id_msub, id_sub)), Nil), !cnstrs);
                         Clo(tM, comp s ssubst))                        
                        
                         (* [|v[id_msub, id_sub] / u|] *)
                    else (* mt is not patsub but t is not *)
                      if isPatMSub mt then
                      (* cD ; cPsi' |- u[mt;t] <= [|mt|][t]tP, and u::tP[cD1 ; cPsi1]  and 
                         cD  |- mt <= cD1
                         cD ; cPsi'  |- t <= [|mt|]cPsi1
                      *)
                      let (id_msub, cD2) = pruneMCtx cD0 (mt, cD1) ms in
                        (* cD  |- mt <= cD1  
                         * cD1 |- id_msub <=  cD2
                         * cD  |- [|mt|]id_msub <= cD2
                         * cD1 |- cPsi1 ctx
                         *)
                      let i_msub = Whnf.m_invert (Whnf.mcomp id_msub mt) in 
                        (* cD2 |- i_msub <= cD               *)
                      let id_msub_i = Whnf.m_invert id_msub in 
                        (* cD2 |= id_msub_i <= cD1 *)
                      let cPsi1' = Whnf.cnormDCtx (cPsi1, id_msub_i) in 
                      (* cD2 |- cPsi1' ctx *)
                      (* cD ; cPsi'  |- t <= [|mt|]cPsi1 
                         cD2 |- i_msub <= cD
                         cD2 ; [|i_msub|]Psi' |- [|i_msub|]t <= [|i_msub|]([|mt|]cPsi1)

                         note: [|i_msub|]([|mt|]cPsi1) = [|([|mt|]id_msub) ^ 1|] [|mt|] cPsi1

                         where cD  |- mt <= cD1
                               cD2 |- [|mt|](id_msub) ^ 1 <= cD
                       *)

                      let t'  = Whnf.cnormSub (Whnf.normSub (comp t s), i_msub) in 
                      let cPsi'' = Whnf.cnormDCtx (cPsi', i_msub) in 
                      (* ss = (ms, ssubst)   cD ; cPsi0 |- ss cPsi' *)
                      (* let (idsub, cPsi2) = pruneSub  cD0 cPsi' phat (t', cPsi1') ss rOccur in *)
                      let (idsub, cPsi2) = pruneSub  cD2 cPsi'' phat (t', cPsi1') ss rOccur in 
                      (* cD2 ; [|mt|]Psi1 |- idsub   : Psi2 
                         cD2 ; Psi2 |- idsub_i : [|mt|]Psi1
                       *)
                      let idsub_i = invert idsub in 

                      let cPsi2' = Whnf.cnormDCtx (cPsi2, i_msub) in 
                      (* cD  ; cPsi   |- [t]([|mt|]tP) 
                         cD1 ; cPsi1  |- tP 
                         cD2 ; [|id_msub^-1|]cPsi1   |-    [|id_msub^-1|] tP  <= type
                         cD2 ; cPsi2' |-  [id_sub_i]  [|id_msub^-1|] tP 
                      *)
                      let tP' = Whnf.cnormTyp (tP, id_msub_i) in 
                      let v = Whnf.newMMVar(cD2, cPsi2', TClo(tP', invert idsub_i)) in                       
                        (instantiateMMVar (r, Root (loc, MMVar (v, (id_msub, idsub)), Nil), !cnstrs) ;
                         Clo(tM, comp s ssubst) )
                      else 
                        raise NotInvertible
                          (* may raise NotInvertible *)
                          


            | MVar (Inst (_n, r, cPsi1, tP, cnstrs) (*as u*), t) ->  (* s = id *)
                let tM = Root(loc, head, tS) in
                let t  = Whnf.normSub (comp t s) in 
                  (* by invariant: MVars are lowered since tM is in whnf *)
                  if eq_cvarRef (MVarRef r) rOccur then
                    raise (Unify "Variable occurrence")
                  else
                    if isPatSub t then
                      let _ = dprint (fun () -> "[prune] MVar " ^
                                        P.normalToString cD0 cPsi' sM) in 

                      let (idsub, cPsi2) = pruneCtx phat (t, cPsi1) ss in                        
                      let _ = dprint (fun () -> "[prune] cPsi1 = " ^
                                        P.dctxToString cD0 cPsi1) in 
                      let _ = dprint (fun () -> "[prune] t = " ^ 
                                        P.subToString cD0 cPsi' t) in 
                      let _ = dprint (fun () -> "[prune] cPsi2 = " ^
                                        P.dctxToString cD0 cPsi2) in 
                        (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                           cD ; cPsi |-  t o s <= cPsi1 and
                           cD ; cPsi1 |- idsub <= cPsi2 and
                           cD ; cPsi |- t o s o idsub <= cPsi2 *)
                      let idsub_i = invert idsub in
                      let v = Whnf.newMVar(cPsi2, TClo(tP, idsub_i)) in

                      let _  = instantiateMVar (r, Root (loc, MVar (v, idsub), Nil), !cnstrs) in 
                         Clo(tM, comp s ssubst)   
                          (* [|v[idsub] / u|] *)
                    else (* s not patsub *) 
                      (* cD ; cPsi' |- u[t] <= [t]tP, and u::tP[cPsi1]  and  
                         cD ; cPsi' |- t <= cPsi1
                         cD ; cPsi  |- s <= cPsi'
                         CD ; cPsi  |- comp t s <= cPsi1  and cD ; cPsi''|- ssubst <= cPsi
                         s' = [ssubst]([s]t) and  cD ; cPsi'' |- s' <= cPsi1  *)
                      (* Mon Feb  9 14:38:08 2009 -bp : instead of simply computing the inverted
                         substitution, we now actually prune the substitution *)
                      (*
                        let s' = invSub cD0 phat (comp t s, cPsi1)  ss rOccur in
                          Root (loc, MVar (u, s'), Nil) 
                      *)
                       let (idsub, cPsi2) = pruneSub  cD0 cPsi' phat (t, cPsi1) ss rOccur in
                      (* Psi1 |- idsub   : Psi2 
                         Psi2 |- idsub_i : Psi1
                       *)
                        (* could maybe just prune tP and cPsi1 ? 
                           29 Jan, 2011  -bp  *)
                      let idsub_i = invert idsub in 
                      let v = Whnf.newMVar(cPsi2, TClo(tP, idsub_i)) in 
                      (* let _ = print_string ("prune non-pattern sub s  where u[s] \n") in *)
                      let _ = instantiateMVar (r, Root (loc, MVar (v, idsub), Nil), !cnstrs) in 
                        Clo(tM, comp s ssubst)
                          (* may raise NotInvertible *)
                          

            | MVar (Offset u, t)   (* tS = Nil,   s = id *) ->
                ((* dprint (fun () -> "Pruning bound meta-variable...") ; *)
                begin match applyMSub u ms with 
                  | MV v -> 
                      begin try 
                        let (_, _tA, cPsi1) = Whnf.mctxMDec cD0 u in 
                        let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
(*                        let (_, ssSubst) = ss in
                          dprint (fun () -> "##       s  = " ^ P.subToString cD0 cPsi' s);
                          dprint (fun () -> "##       t  = " ^ P.subToString cD0 cPsi' t);
                          dprint (fun () -> "##       ss = " ^ P.subToString cD0 cPsi' ssSubst);
                          dprint (fun () -> "##       s' = " ^ P.subToString cD0 cPsi' s'); 
                          dprint (fun () -> "## comp t s = " ^ P.subToString cD0 cPsi' (comp t s));
*)
                          returnNeutral (MVar (Offset v, s'))
                      with 
                        | Error.Violation msg -> 
                            raise (Unify ("ERROR: prune: " ^ msg ^ 
                                          "\n Looking for " ^ R.render_cvar cD0 u ^ 
                                          "\n in context " ^ P.mctxToString cD0))
                        | Error msg -> raise (Unify ("ERROR: prune (2) " ^ msg ^ "\n Looking for " ^ 
                                              R.render_cvar cD0 u ^ "\n in context " ^ 
                                              P.mctxToString cD0))
                      end
                  | MUndef -> raise (Unify "[Prune] Bound MVar dependency")
                  | _      -> raise (Unify "[Prune] MObj / PObj dependency")
                end 
                )
            | FMVar (u, t)   (* tS = Nil,   s = id *) ->
                let (cD_d, MDecl (_, _tA, cPsi1)) = Store.FCVar.get u in 
                let d = Context.length cD0 - Context.length cD_d in 
	        let cPsi1 = if d = 0 then cPsi1 else 
	          Whnf.cnormDCtx (cPsi1, MShift d) in 
                let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
                  returnNeutral (FMVar (u, s'))
                    
            | FPVar (p, t)   (* tS = Nil,   s = id *) ->
                let (cD_d, PDecl (_, _tA, cPsi1)) = Store.FCVar.get p in 
                let d = Context.length cD0 - Context.length cD_d in 
	        let cPsi1 = if d = 0 then cPsi1 else 
	          Whnf.cnormDCtx (cPsi1, MShift d) in 
                let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
                  returnNeutral (FPVar (p, s'))
                    
            | PVar (Offset p, t)   (* tS = Nil,   s = id *) ->
                begin match applyMSub p ms with 
                  | MV q -> 
                      let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
                      let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
                        returnNeutral (PVar (Offset q, s'))
                  | MUndef -> raise (Unify "[Prune] Bound PVar dependency")
                end

            | Proj (PVar (Offset p, t), i)   (* tS = Nil,   s = id *) ->
                begin match applyMSub p ms with 
                  | MV q ->                       
                      let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
                      let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
                        returnNeutral (Proj (PVar (Offset q, s'), i))
                  | MUndef -> raise (Unify "[Prune] Bound PVar dependency in projection")
                end 

            | PVar (PInst (_n, r, cPsi1, tA, cnstrs) as q, t) (* tS *)   (* s = id *) ->
                let t = Whnf.normSub t in 
                  if eq_cvarRef (PVarRef r) rOccur then
                    raise (Unify "[Prune] Parameter variable occurrence")
                  else
                    if isPatSub t then
                      let (idsub, cPsi2) = pruneCtx phat (comp t s, cPsi1) ss in
                        (* cD ; cPsi1 |- idsub <= cPsi2 *)
                      let p = Whnf.newPVar (cPsi2, TClo(tA, invert idsub)) (* p::([(idsub)^-1]tA)[cPsi2] *) in
                      let _ = instantiatePVar (r, PVar (p, idsub), !cnstrs) in
                        (* [|p[idsub] / q|] *)
                        (* h = p[[ssubst] ([t] idsub)] *)
                        returnNeutral (PVar(p, comp (comp t idsub) ssubst))
                    else (* s not patsub *)
                      let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
                        returnNeutral (PVar (q, s'))
                        
            | Proj (PVar (PInst (_n, r, cPsi1, tA, cnstrs) as q, t), i)  (* s = id *) ->
                let t = Whnf.normSub t in 
                if eq_cvarRef (PVarRef r) rOccur then
                  raise (Unify "[Prune] Parameter variable occurrence")
                else
                  if isPatSub t then
                    let (idsub, cPsi2) = pruneCtx phat (comp t s, cPsi1) ss in
                      (* cD ; cPsi1 |- idsub <= cPsi2 *)
                    let p = Whnf.newPVar(cPsi2, TClo(tA, invert idsub)) (* p::([(idsub)^-1] tA)[cPsi2] *) in
                    let _ = instantiatePVar (r, PVar (p, idsub), !cnstrs) (* [|p[idsub] / q|] *) in
                    let s_comp = comp (comp t idsub) ssubst in  
                      returnNeutral (Proj (PVar(p, s_comp), i))  

                  else (* s not patsub *)
                    let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
                      returnNeutral (Proj (PVar (q, s'), i))
                        
            | Proj (FPVar(p,t), i)   (* tS = Nil,   s = id *) ->
                begin try
                  let (cD_d, PDecl (_, _tA, cPsi1)) = Store.FCVar.get p in 
                  let d = Context.length cD0 - Context.length cD_d in 
	          let cPsi1 = if d = 0 then cPsi1 else 
	                        Whnf.cnormDCtx (cPsi1, MShift d) in 
                  let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
                    returnNeutral (Proj (FPVar(p,s'), i))
                with
                  | Not_found -> 
                      if isId ssubst && isMId ms  then returnNeutral head 
                      else raise (Unify ("[Prune] Free parameter variable to be pruned with non-identity substitution"))
                end
                    
            | BVar k  (* s = id *) ->
                begin match bvarSub k ssubst with
                  | Undef                -> raise (Unify ("[Prune] Bound variable dependency : " ^ 
                                                      "head = " ^ P.headToString cD0 cPsi' head))
                  | Head (BVar _k as h') ->
                      returnNeutral h'
                end
                  
            | Const _ as h  (* s = id *)  ->  returnNeutral h
                  
            | FVar _ as h  (* s = id *)  ->  returnNeutral h
                  
            | Proj (BVar k, i)  (* s = id *) ->
                begin match bvarSub k ssubst with
                  | Head (BVar _k' as h') -> returnNeutral (Proj (h', i))
                  | _                     -> raise (Unify "[Prune] Bound variable dependency (Proj) ")
                end

  and pruneTuple cD0 cPsi phat sTuple ss rOccur = match sTuple with
    | (Last tM, s) ->
        let tM' = prune cD0 cPsi phat (tM, s) ss rOccur in
          Last tM'

    | (Cons (tM, rest), s) ->
        let tM' = prune cD0 cPsi phat (tM, s) ss rOccur in
        let rest' = pruneTuple cD0 cPsi phat (rest, s) ss rOccur in
          Cons (tM', rest')

  
  and pruneSpine cD0 cPsi1 phat spine ss rOccur = match spine with
    | (Nil, _s)           -> Nil

    | (App (tM, tS), s)   ->
        let tM' = prune cD0 cPsi1 phat (tM, s) ss rOccur in
        let tS' = pruneSpine cD0 cPsi1 phat (tS, s) ss rOccur in
          App (tM', tS')

    | (SClo (tS, s'), s) ->
        pruneSpine cD0 cPsi1 phat (tS, comp s' s) ss rOccur

  (* pruneSub cD0 cPsi phat (s, cPsi1) ss rOccur = (s', cPsi1')

     if phat = hat(Psi)  and
        D ; Psi  |- s <= Psi1
        D ; Psi''|- ss <= Psi
     then  cPsi1 |- s' <= Psi1'
           ss' = [ss][s](s')   if it exists, and
        D ; cPsi'' |- [ss][s]s' <= cPsi1'
   *)

  and pruneSub cD0 cPsi phat (s, cPsi1) ss rOccur = 
    begin try 
        pruneSub' cD0 cPsi phat (s, cPsi1) ss rOccur
    with NotInvertible -> 
      (numPruneSub := !numPruneSub + 1  ; 
       raise NotInvertible)
    end

  and pruneSub' cD0 cPsi phat (s, cPsi1) ss rOccur =
    match (s, cPsi1) with
    | (Shift (psi, n), DDec(_cPsi', _dec)) ->       
        pruneSub' cD0 cPsi phat (Dot (Head (BVar (n + 1)), Shift (psi, n + 1)), cPsi1) ss rOccur 

    | (Shift (_psi, _n), Null) -> (id, Null)

    | (Shift (_psi', _n), CtxVar psi) -> (id, CtxVar psi)

    | (Dot (Head (BVar n), s'), DDec(cPsi', TypDecl(x, tA))) ->
        let (_, ssubst) = ss in 
        begin match bvarSub n ssubst with
          | Undef -> 
              let (s1', cPsi1') = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur  in 
                (comp s1' shift, cPsi1')

           | Head (BVar _n) ->
              let (s1', cPsi1') = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur in
              (* prune tA with respect to s1_i since we have constraints and we cannot guarantee 
                 in the presence of constraints that [s1_i]A really exists *)
              let s1_i = invert (Monitor.timer ("Normalisation", fun () -> Whnf.normSub s1')) in      (* cPsi1' |- s1_i <= cPsi' *)
               (dot1 s1' ,  DDec(cPsi1', TypDecl(x, TClo (tA, s1_i))))
        end


    | (Dot (Head (Proj (BVar n, _projIndex)), s'), DDec(cPsi', TypDecl(x, tA))) ->
      (* copied immediately preceding case for Head (BVar _)...is this right?  -jd *)
      let (_ , ssubst) = ss in 
        begin match bvarSub n ssubst with
          | Undef -> 
              let (s1', cPsi1') = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur  in 
                (comp s1' shift, cPsi1')

           | Head (BVar _n) ->
              let (s1', cPsi1') = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur in
              let s1_i = invert (Monitor.timer ("Normalisation", fun () -> Whnf.normSub s1')) in      (* cPsi1' |- s1_i <= cPsi' *)
               (dot1 s1' ,  DDec(cPsi1', TypDecl(x, TClo (tA, s1_i))))
        end

    | (Dot (Obj tM, s'), DDec(cPsi', TypDecl(x, tA)))        ->
        (* below may raise NotInvertible *)
        (* let _tM' = invNorm cD0 (phat, (tM, id), ss, rOccur) in    *)
        let _tM' = prune cD0 cPsi1 phat (tM, id) ss rOccur in     

        let (s1', cPsi1')  = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur in 
        let s1_i = invert (Monitor.timer ("Normalisation", fun () -> Whnf.normSub s1')) in      (* cPsi1' |- s1_i <= cPsi' *)
        (* We need to prune the type here as well;  Feb  9  2009 -bp *)
        let tA' = pruneTyp cD0 cPsi1' phat (tA, id) (MShift 0, s1_i) rOccur in  
          (dot1 s1'  , DDec(cPsi1', TypDecl(x, tA'))) 

   | (Dot (Undef, t), DDec (cPsi1, _)) ->
       let (s1', cPsi1') = pruneSub' cD0 cPsi phat (t, cPsi1) ss rOccur in
         (comp s1' shift, cPsi1')


  (* pruneMSub cD0 (t, cD1) mtt rOccur = (t', cD')

     if cD0   |- t   <= cD1
        cD''  |- mtt <= cD0
     then cD1 |- t' <= cD1'
          t' = [mtt]t   if it exists, and
         cD'' |- [mtt]t <= cD1'
   *)

  and pruneMSub cD0 (t, cD1) mtt rOccur = match (t, cD1) with
    | (MShift n, Dec(_cD', _dec)) ->       
        pruneMSub cD0 (MDot (MV (n + 1), MShift (n + 1)), cD1) mtt rOccur

    | (MShift _n, Empty) -> (Whnf.m_id, Empty)

    | (MDot (MV n, t'), Dec(cD', MDecl(x, tA, cPsi))) ->
        begin match applyMSub n mtt with
          | MUndef -> 
              let (t1', cD1') = pruneMSub cD0 (t', cD') mtt rOccur  in 
                (Whnf.mcomp t1' (MShift 1), cD1')

           | MV _n ->
              let (t1', cD1') = pruneMSub cD0 (t', cD') mtt rOccur in
              let t1_i = Whnf.m_invert (Whnf.cnormMSub t1') in      (* cD1' |- t1_i <= cD' *)
              (* cD' |- cPsi ctx  and cD' ; cPsi |- tA     *)
              let cPsi' = Whnf.cnormDCtx (cPsi, t1_i) in 
              let tA'   = Whnf.cnormTyp (tA, t1_i) in                 
               (Whnf.mvar_dot1 t1' ,  Dec(cD1', MDecl(x, tA', cPsi')))
        end

    | (MDot (MV n, t'), Dec(cD', PDecl(x, tA, cPsi))) ->
        begin match applyMSub n mtt with
          | MUndef -> 
              let (t1', cD1') = pruneMSub cD0 (t', cD') mtt rOccur  in 
                (Whnf.mcomp t1' (MShift 1), cD1')

           | MV _n ->
              let (t1', cD1') = pruneMSub cD0 (t', cD') mtt rOccur in
              let t1_i = Whnf.m_invert (Whnf.cnormMSub t1') in      (* cD1' |- t1_i <= cD' *)
              let cPsi' = Whnf.cnormDCtx (cPsi, t1_i) in 
              let tA'   = Whnf.cnormTyp (tA, t1_i) in                 
               (Whnf.mvar_dot1 t1' ,  Dec(cD1', PDecl(x, tA', cPsi')))
        end

    | (MDot (MObj (phat, tM), t'), Dec(cD', MDecl(x, tA, cPsi)))        ->
        (* below may raise NotInvertible *)
        (* let _tM' = invNorm cD0 (phat, (tM, id), ss, rOccur) in    *)
        let _tM' = prune cD0 cPsi phat (tM, id) (mtt, id) rOccur in     

        let (t1', cD1')  = pruneMSub cD0 (t', cD') mtt rOccur in 
        let t1_i = Whnf.m_invert (Whnf.cnormMSub t1') in      (* cD1' |- t1_i <= cD' *)
        (* We need to prune the type here as well;  -bp *)
        let tA' = pruneTyp cD0 cPsi phat (tA, id) (t1_i, id) rOccur in  
        let cPsi' = pruneDCtx cD0 cPsi  t1_i rOccur in  
          (Whnf.mvar_dot1 t1'  , Dec(cD1', MDecl(x, tA', cPsi'))) 

   | (MDot (MUndef, t), Dec (cD1, _)) ->
       let (t1', cD1') = pruneMSub cD0 (t, cD1) mtt rOccur in
         (Whnf.mcomp t1' (MShift 1), cD1')

  and pruneTypW cD0 cPsi phat sA (mss, ss) rOccur = match sA with
    | (Atom(loc, a, tS) , s) -> Atom(loc, a, pruneSpine cD0  cPsi phat (tS, s) (mss, ss) rOccur) 
    | (PiTyp((TypDecl(x, tA), dep), tB), s) -> 
        let tA' = pruneTyp cD0 cPsi phat (tA, s) (mss, ss) rOccur in 
        let tB' = pruneTyp cD0 cPsi phat (tB, dot1 s) (mss, dot1 ss) rOccur in 
          PiTyp((TypDecl(x, tA'), dep), tB')

    | (PiTyp ((TypDeclOpt x, dep), tB), s) -> 
        let tB' = pruneTyp cD0 cPsi phat (tB, dot1 s) (mss, dot1 ss) rOccur in 
          PiTyp ((TypDeclOpt x, dep), tB')

    | (Sigma typ_rec, s) -> 
        let typ_rec' = pruneTypRec  cD0 cPsi phat (typ_rec, s) (mss, ss) rOccur in 
          Sigma typ_rec'

  and pruneTyp cD0 cPsi1 phat sA ss rOccur = 
    let _ : (msub * sub) = ss in 
      pruneTypW cD0 cPsi1 phat (Whnf.whnfTyp sA) ss rOccur

  and pruneTypRec cD0 cPsi phat (typ_rec, s) (mss, ss) rOccur = match (typ_rec, s) with
    | (SigmaLast tA, s) -> SigmaLast (pruneTyp cD0 cPsi phat (tA, s) (mss, ss) rOccur)
    | (SigmaElem (x, tA, typ_rec'), s) -> 
      let tA' = pruneTyp cD0 cPsi phat (tA, s) (mss, ss) rOccur in 
      let typ_rec'' = pruneTypRec cD0 cPsi phat (typ_rec', dot1 s) (mss, dot1 ss) rOccur in 
        SigmaElem (x, tA', typ_rec'')



  and pruneDCtx cD0 cPsi mtt rOccur = match cPsi with
    | Null -> Null
    | DDec (cPsi', TypDecl(x, tA)) -> 
        let cPsi'' = pruneDCtx cD0 cPsi mtt rOccur in 
        let phat   = Context.dctxToHat cPsi' in 
        let tA''   = pruneTyp cD0 cPsi phat (tA, id) (mtt, id) rOccur in 
          DDec (cPsi'', TypDecl (x, tA''))
    

  (* pruneCtx cD (phat, (t, Psi1), ss) = (s', cPsi2)

     Invariant:

     If phat = hat (Psi)  and
        cD ; Psi |- t  <= Psi1  and
        cD ; Psi'|- ss <= Psi   and (ss')^-1 = ss
     then
        cD ; Psi1 |- s' <= Psi2
        where every declaration x:A in Psi2 is also in Psi1
        and s' is a weakened identity substitution.

        moreover:
        [t]s' = t'  s.t. D ; Psi  |- t'  <= Psi2 ,
        and [ss']^-1 (t') = t'' exists
        and D ; Psi' |- t'' <= Psi2
  *)

  and pruneCtx' phat (t, cPsi1) ss = match (t, cPsi1) with
    | (Shift (_psi ,_k), Null) ->
        (id, Null)

    | (Shift (NoCtxShift, 0), CtxVar psi) -> 
        let ( _ , ssubst) = ss in 
          begin match ssubst with 
            | Shift (NegCtxShift phi, 0) -> 
                if psi = phi then 
                  (Shift (CtxShift phi,0), Null)
                else (raise NotInvertible)
            | _ -> (id, CtxVar psi)
          end 


    | (Shift (_, _k), CtxVar psi) ->
        (id, CtxVar psi)

   | (Shift (psi, k), DDec (_, TypDecl (_x, _tA))) ->
       pruneCtx' phat (Dot (Head (BVar (k + 1)), Shift (psi, k + 1)), cPsi1) ss


   | (Dot (Head (BVar k), s), DDec (cPsi1, TypDecl (x, tA))) ->
       let (s', cPsi2) = pruneCtx' phat (s, cPsi1) ss in
         (* Ps1 |- s' <= Psi2 *)
       let ( _ , ssubst) = ss in 
         begin match bvarSub k ssubst with
           | Undef          ->
               (* Psi1, x:tA |- s' <= Psi2 *)
               (comp s' shift, cPsi2)

           | Head (BVar _n) ->
               (* Psi1, x:A |- s' <= Psi2, x:([s']^-1 A) since
                  A = [s']([s']^-1 A) *)
               (dot1 s',  DDec(cPsi2, TypDecl(x, TClo(tA, invert (Whnf.normSub s')))))
         end
              

   | (Dot (Head (Proj(BVar k, index)), s), DDec (cPsi1, TypDecl (x, tA))) ->
       let (s', cPsi2) = pruneCtx' phat (s, cPsi1) ss in
         (* Ps1 |- s' <= Psi2 *)
       let ( _ , ssubst) = ss in 
         begin match bvarSub k ssubst with
           | Undef          ->
               (* Psi1, x:tA |- s' <= Psi2 *)
               (comp s' shift, cPsi2)

           | Head (BVar _n) ->
               (* Psi1, x:A |- s' <= Psi2, x:([s']^-1 A) since
                  A = [s']([s']^-1 A) *)
               (dot1 s',  DDec(cPsi2, TypDecl(x, TClo(tA, invert (Whnf.normSub s')))))
         end

   | (Dot (Undef, t), DDec (cPsi1, _)) ->
       let (s', cPsi2) = pruneCtx' phat (t, cPsi1) ss in
         (* sP1 |- s' <= cPsi2 *)
         (comp s' shift, cPsi2)


  and pruneCtx phat (t, cPsi1) ss = pruneCtx' phat (Whnf.normSub t, cPsi1) ss



  (* Unification:

       Precondition: D describes the current contextual variables

       Given cD ; cPsi1 |- tN <= tA1    and cD ; cPsi |- s1 <= cPsi1
             cD ; cPsi2 |- tM <= tA2    and cD ; cPsi |- s2 <= cPsi2
             cD ; cPsi  |- [s1]tA1 = [s2]tA2 <= type

             hat(cPsi) = phat

        unify phat (tN,s) (tM,s') succeeds if there exists a
        contextual substitution theta such that

        [|theta|]([s1]tN) = [|theta|]([s2]tM) where cD' |- theta <= cD.

       Also, applies instantiation theta as an effect, and returns ().
       Otherwise, raises exception Unify.

       Postcondition: cD' includes new and possibly updated contextual variables;

       Other effects: MVars in cD' may have been lowered and pruned;
                      Constraints may be added for non-patterns.
  *)

  let rec unifyTerm  mflag cD0 cPsi sN sM = unifyTerm'  mflag cD0 cPsi (Whnf.whnf sN) (Whnf.whnf sM)

  and unifyTerm'  mflag cD0 cPsi sN sM = match (sN, sM) with
    | ((Lam (_, _, tN), s1), (Lam (_ , x, tM), s2)) ->
        unifyTerm  mflag cD0 (DDec(cPsi, TypDeclOpt x)) (tN, dot1 s1) (tM, dot1 s2)

    (* MVar-MVar case *)
    | (((Root (_, MVar (Inst (_n1, r1,  cPsi1,  tP1, cnstrs1), t1), _tS1) as _tM1), s1) as sM1,
       (((Root (_, MVar (Inst (_n2, r2, cPsi2,  tP2, cnstrs2), t2), _tS2) as _tM2), s2) as sM2)) ->
         dprnt "(000) MVar-MVar"; 
        (* by invariant of whnf:
           meta-variables are lowered during whnf, s1 = s2 = id or co-id
           r1 and r2 are uninstantiated  (None)
        *)
        let t1' = Whnf.normSub (comp t1 s1)    (* cD ; cPsi |- t1' <= cPsi1 *) in
        let t2' = Whnf.normSub (comp t2 s2) in (* cD ; cPsi |- t2' <= cPsi2 *)
        let _ = dprint (fun () ->  "\n[Unify] MVar-MVar:"  ) in
        let _ = dprint (fun () -> "                "^ P.normalToString cD0 cPsi  sM1 ) in 
        let _ = dprint (fun () ->  "with type: "  ) in 
        let _ = dprint (fun () ->  P.dctxToString cD0 cPsi1 ) in 
        let _ = dprint (fun () -> " |- " ^
                          P.typToString cD0 cPsi1 (tP1 , id)) in
        let _ = dprint (fun () -> "\n and "
                                 ^ P.normalToString cD0 cPsi sM2 ^  "\n with type: "
                                 ^ P.dctxToString cD0 cPsi2 ^ " |- " ^ P.typToString cD0 cPsi2 (tP2 , id)) in

          if r1 == r2 then (* by invariant:  cPsi1 = cPsi2, tP1 = tP2, cnstr1 = cnstr2 *)
            match (isProjPatSub t1' , isProjPatSub t2') with                 
(*            match (isPatSub t1' , isPatSub t2') with                 *)
              | (true, true) ->                 
                  if Whnf.convSub t1' t2' then  
                    () 
                  else 
                    let phat = Context.dctxToHat cPsi in 
                    let (s', cPsi') = intersection phat t1' t2' cPsi1 in
                      (* if cD ; cPsi |- t1' <= cPsi1 and cD ; cPsi |- t2' <= cPsi1
                         then cD ; cPsi1 |- s' <= cPsi' *)                  

                    let ss' = invert (Monitor.timer ("Normalisation", fun () -> Whnf.normSub s')) in
                      (* cD ; cPsi' |- [s']^-1(tP1) <= type *)
                      
                    let w = Whnf.newMVar (cPsi', TClo(tP1, ss')) in
                      (* w::[s'^-1](tP1)[cPsi'] in cD'            *)
                      (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tP1)
                         [|w[s']/u|](u[t1]) = [t1](w[s'])
                         [|w[s']/u|](u[t2]) = [t2](w[s'])
                      *)
                      instantiateMVar (r1, Root(Syntax.Loc.ghost, MVar(w, s'),Nil), !cnstrs1)
                        
              | (true, false) ->
                    addConstraint (cnstrs2, ref (Eqn (cD0, cPsi, Clo sM, Clo sN))) (* XXX double-check *)
              | (false, true) ->
                  addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, Clo sM, Clo sN))) (* XXX double-check *)
              | (false, false) ->
                  if Whnf.convSub t1' t2' then
                    ()
                  else 
                    (dprint (fun () ->  "\nAttempt to unify :"  
                            ^ P.normalToString cD0 cPsi sM1 ^ "\n with type: " ^ 
                              P.dctxToString cD0 cPsi1 ^ " |- " ^ P.typToString cD0 cPsi1 (tP1 , id)
                             ^ "\n and " ^ 
                              P.normalToString cD0 cPsi sM2 ^  "\n with type: " ^ 
                              P.dctxToString cD0 cPsi2 ^ " |- " ^ P.typToString cD0 cPsi2 (tP2 , id) ^ "\n Generate constraint\n"
                          );
                   addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, Clo sN, Clo sM)))  (* XXX double-check *))
          else
            begin match (isPatSub t1' , isPatSub t2') with
              | (true, _) ->
                  (* cD ; cPsi' |- t1 <= cPsi1 and cD ; cPsi |- t1 o s1 <= cPsi1 *)
                  begin try
                    let _ = dprint (fun () -> "MVar - MVar (different ) ... inverting substitution " ) in 
                    let ss1  = invert (Monitor.timer ("Normalisation", fun () -> Whnf.normSub t1')) (* cD ; cPsi1 |- ss1 <= cPsi *) in 
                    let phat = Context.dctxToHat cPsi in 
                    let _ = dprint (fun () -> "MVar-MVar : inverted ss1 : " ^
                                      P.subToString cD0 cPsi1 ss1) in 
                    let _ = dprint (fun () -> "MVar-MVar case initiate pruning " ) in 
                    let tM2' = trail (fun () -> prune cD0 cPsi1 phat sM2 (MShift 0, ss1) (MVarRef r1)) in 
                    (* let _ = dprint (fun () -> 
                                      "UNIFY: MVar =/= MVAR: Result of pruning : " ^ 
                                        "\n cPsi1  = " ^ P.dctxToString cD0 cPsi1 ^ "\n tMs' = " ^ 
                                      P.normalToString cD0 cPsi1 (tM2', id) ^ "\n") in *)

                    (* sM2 = [ss1][s2]tM2 *) 
                    instantiateMVar (r1, tM2', !cnstrs1)  
                      
                  with
                    | NotInvertible ->
                        ((* Printf.printf "Added constraints: NotInvertible: \n "; *)
                         addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))))
                  end
              | (false, true) ->
                  begin try
                    let ss2 = invert (Monitor.timer ("Normalisation", fun () -> Whnf.normSub t2'))(* cD ; cPsi2 |- ss2 <= cPsi *) in
                    (* let _ = dprint (fun () -> 
                                      "UNIFY(2): \n cPsi = " ^ 
                                        P.dctxToString cD0 cPsi ^ "\n" ^ 
                                        P.mctxToString cD0 ^ "\n" ^
                                        P.normalToString cD0 cPsi sM1  
                                          ^ " : " ^ P.typToString cD0 cPsi (tP1, t1') ^ 
                                        "\n    " ^
                                              P.normalToString cD0 cPsi sM2  
                                          ^ " : " ^ P.typToString cD0 cPsi (tP2, t2') ^ 
                                        "\n")
                    in 
                  let _ = dprint (fun () -> 
                                        "t2' = " ^   
                                        P.subToString cD0 cPsi t2' ^
                                        "prune  " ^ P.normalToString cD0 cPsi sM1 ^ 
                                        " with respect to \n ssubst = " ^  
                                        P.subToString cD0 cPsi1 ss2 ^ "\n") in *)


                    let phat = Context.dctxToHat cPsi in 
                    let tM1' = trail (fun () -> prune cD0 cPsi2 phat sM1 (MShift 0, ss2) (MVarRef r2)) in
                      instantiateMVar (r2, tM1', !cnstrs2)                       
                  with
                    | NotInvertible ->
                        ((* Printf.printf "Added constraints: NotInvertible: \n" ; *)
                            addConstraint (cnstrs2, ref (Eqn (cD0, cPsi, Clo sM2, Clo sM1))))
                  end
              | (false , false) ->
                  (* Check if t1' or t2' are proj-patt sub *)
                  begin match  (isProjPatSub t1' , isProjPatSub t2') with
                    | ( _ , true ) -> 
                        begin try 
                          let _ = dprint (fun () -> "about to call flattenDCtx from unify.ml projpatsub case; cPsi = " ^ P.dctxToString cD0 cPsi) in
                          let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in 
                          let phat = Context.dctxToHat flat_cPsi in 
                          let t_flat = ConvSigma.strans_sub t2' conv_list in 
                          let tM1'   = ConvSigma.strans_norm sM1 conv_list in 
                          let ss = invert t_flat in
                          let sM1' = trail (fun () -> prune cD0 cPsi2 phat (tM1', id) (MShift 0, ss) (MVarRef r2)) in
                            instantiateMVar (r2, sM1', !cnstrs2) 
                        with
                          | NotInvertible ->
                              ((* Printf.printf "Added constraints: NotInvertible: \n" ;*)
                               addConstraint (cnstrs2, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))))
                        end


                    | ( true , _ ) -> 
                        begin try
                          let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in 
                          let phat = Context.dctxToHat flat_cPsi in 
                          let t_flat = ConvSigma.strans_sub t1' conv_list in 
                          let tM2'   = ConvSigma.strans_norm sM2 conv_list in 
                          let ss = invert t_flat in
                          let sM2' = trail (fun () -> prune cD0 cPsi1 phat (tM2', id) (MShift 0, ss) (MVarRef r1)) in
                            instantiateMVar (r1, sM2', !cnstrs1) 
                        with
                          | NotInvertible ->
                              ((* Printf.printf "Added constraints: NotInvertible: \n" ;*)
                               addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))))
                        end


                    | ( false , false ) -> 
                        (* neither t1' nor t2' are pattern substitutions *)
                        let cnstr = ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)) in                    
                          addConstraint (cnstrs1, cnstr)
                  end 
            end

    (* MVar-normal case *)
    | ((Root (_, MVar (Inst (_n, r, cPsi1, _tP, cnstrs), t), _tS), s1) as sM1, ((_tM2, _s2) as sM2)) ->
        dprnt "(001) MVar-_";
        let t' = Monitor.timer ("Normalisation", fun () -> Whnf.normSub (comp t s1)) in
          if isPatSub t' then
            try
              let ss = invert t' in
              let _ = dprint (fun () -> 
                                          "UNIFY(2): " ^
                                            P.mctxToString cD0 ^ "\n    " ^
                                            P.normalToString cD0 cPsi sM1 ^ "\n    " ^
                                            P.normalToString cD0 cPsi sM2) in              
              let phat = Context.dctxToHat cPsi in 
              let _ = dprint (fun () -> "Pruning substitution: " ^ P.dctxToString cD0 cPsi1 ^ " |- " ^ P.subToString cD0 cPsi1 ss ^ " <= " ^ P.dctxToString cD0 cPsi) in 
              let tM2' = trail (fun () -> prune cD0 cPsi1 phat sM2 (MShift 0, ss) (MVarRef r)) in
              let _ = dprint (fun () -> 
                                          "UNIFY(2) -- AFTER PRUNING: " ^
                                            P.mctxToString cD0 ^ "\n    " ^
                                            P.normalToString cD0 cPsi1 (tM2', id)) in              
              let _ = instantiateMVar (r, tM2', !cnstrs) in 
              let _ = dprint (fun () -> 
                                          "UNIFY(2) [RESULT]: " ^
                                            P.mctxToString cD0 ^ "\n    "  ^
                                            P.normalToString cD0 cPsi sM1  ^ " ==   " ^
                                            P.normalToString cD0 cPsi sM2) in              
                ()
            with
              | NotInvertible ->
                  (* Printf.printf "Added constraints: NotInvertible: \n";*)
                  addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)))
            else
              if isProjPatSub t' then 
                begin try 
                  let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in 
                  let phat = Context.dctxToHat flat_cPsi in 
                  let t_flat = ConvSigma.strans_sub t' conv_list in 
                  let tM2'   = ConvSigma.strans_norm sM2 conv_list in 
                  let ss = invert t_flat in
                  let sM2' = trail (fun () -> prune cD0 cPsi1 phat (tM2', id) (MShift 0, ss) (MVarRef r)) in
                    instantiateMVar (r, sM2', !cnstrs) 
                with
                  | NotInvertible ->
                      ((* Printf.printf "Added constraints: NotInvertible: \n" ;*)
                       addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))))
              end
            else
             (dprint (fun () -> "Add constraint: MVAR-Normal case"
                              ^ P.normalToString cD0 cPsi sM1
                              ^ " = " ^ P.normalToString cD0 cPsi sM2);
             addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))))
    
    (* normal-MVar case *)
    | ((_tM1, _s1) as sM1, ((Root (_, MVar (Inst (_n, r, cPsi1, tP1, cnstrs), t), _tS), s2) as sM2)) ->
(*        dprnt "(002) _-MVar"; *)
        let t' = Monitor.timer ("Normalisation" , fun () -> Whnf.normSub (comp t s2)) in

          if isPatSub t' then
            try
(*              dprnt "isPatSub";
              let _ = dprint (fun () -> 
                                "UNIFY (3): " ^
                                  P.mctxToString cD0 ^ "\n        " ^
                                  P.normalToString cD0 cPsi sM1 ^ "\n        " ^
                                  P.normalToString cD0 cPsi sM2 ^
                                  " : " ^ P.typToString cD0 cPsi (tP1, t')) in 
*)
              let ss = Monitor.timer ("Normalisation", fun () -> invert (Whnf.normSub t')) in
              let phat = Context.dctxToHat cPsi in 
              let tM1' = trail (fun () -> prune cD0 cPsi1 phat sM1 (MShift 0, ss) (MVarRef r)) in
(*              let _ = dprint (fun () -> "UNIFY (3) : INSTANTIATE! \n" ^
                                P.normalToString cD0 cPsi sM2 ^ "\n with " ^ 
                                P.normalToString cD0 cPsi1 (tM1', id) ^ "\n in context cPsi1 = " ^ 
                                P.dctxToString cD0 cPsi1
                             ) in
*)

                instantiateMVar (r, tM1', !cnstrs)  
            with
              | NotComposable _ -> raise (Unify "NotComposable")
              | NotInvertible ->
                  ((* Printf.printf "Pruning failed -- NotInvertible\n" ; *)
                   (* Printf.printf "Added constraints: NotInvertible: \n" ;*)
                     addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)))
                   (* raise (Unify "NotInvertible") *)
                  )
          else            
            if isProjPatSub t' then 
              begin try 
                dprnt "isProjPatSub";
                let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in 
                let phat = Context.dctxToHat flat_cPsi in 
                let t_flat = ConvSigma.strans_sub t' conv_list in 
                let tM1'   = ConvSigma.strans_norm sM1 conv_list in
                let ss = invert t_flat in
                dprint (fun () -> "! t'     = " ^ P.subToString cD0 cPsi t');
                dprint (fun () -> "! t_flat = " ^ P.subToString cD0 flat_cPsi t_flat);
                dprint (fun () -> "! tM1' = " ^ P.normalToString cD0 flat_cPsi (tM1', id));
                dprint (fun () -> "! ss = " ^ P.subToString cD0 flat_cPsi ss);
                dprnt "isProjPatSub - 5";
                let sM1' = trail (fun () -> prune cD0 cPsi1 phat (tM1', id) (MShift 0, ss) (MVarRef r)) in
                dprnt "isProjPatSub - 6";
                  instantiateMVar (r, sM1', !cnstrs) 
              with
              | NotInvertible ->
                  ( Printf.printf "Added constraints: NotInvertible: \n" ;
                    addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))) 
                    (* Printf.printf "Pruning failed -- NotInvertible\n" ; *)
                    (* raise (Unify "NotInvertible") *)
                  )
              end
            else 
            (dprint (fun () -> "Add constraint: Normal-MVar case");
             addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))))



    (* MMVar-MMVar case *)
    | (((Root (_, MMVar (MInst (_n1, r1,  cD1, cPsi1,  tP1, cnstrs1), (mt1, t1)), _tS1) as _tM1), s1) as sM1,
       (((Root (_, MMVar (MInst (_n2, r2, _cD2, cPsi2, tP2, cnstrs2), (mt2, t2)), _tS2) as _tM2), s2) as sM2)) ->
        dprnt "(010) MMVar-MMVar";
        (* by invariant of whnf:
           meta^2-variables are lowered during whnf, s1 = s2 = id
           r1 and r2 are uninstantiated  (None)
        *)
        let t1' = Whnf.normSub (comp t1 s1)    (* cD ; cPsi |- t1' <= cPsi1 *)
        and t2' = Whnf.normSub (comp t2 s2)    (* cD ; cPsi |- t2' <= cPsi2 *)
        in
          if r1 == r2 then (* by invariant:  cD1 = cD2, cPsi1 = cPsi2, tP1 = tP2, cnstr1 = cnstr2 *)
            match (isPatMSub mt1, isProjPatSub t1' , isPatMSub mt2, isProjPatSub t2') with                
              | (true, true, true, true) -> 
                  if Whnf.convSub t1' t2' && Whnf.convMSub mt1 mt2 then 
                    ()
                  else 
                    let phat = Context.dctxToHat cPsi in 
                    let (s', cPsi') = intersection phat (Whnf.normSub t1') (Whnf.normSub t2') cPsi1 in
                      (* if cD ; cPsi |- t1' <= cPsi1 and cD ; cPsi |- t2' <= cPsi1
                         then cD ; cPsi1 |- s' <= cPsi' *)
                    let (mt', cD') = m_intersection (Whnf.cnormMSub mt1) (Whnf.cnormMSub mt2) cD1 in              
                      (* if cD |- mt1 <= cD1 and cD |- mt2 <= cD1 
                         then cD1 |- mt' <= cD' *)
                    let ss'  = invert (Whnf.normSub s') in
                      (* if cD ; cPsi1 |- s' <= cPsi' 
                         then cD ; cPsi' |- ss' <= cPsi1 *)
                    let mtt' = Whnf.m_invert (Whnf.cnormMSub mt') in
                    (* if cD1 |- mt' <= cD' 
                       then cD' |- mtt' <= cD1 *)
                    (* by assumption: cD1 ; cPsi1 |- tP1 <= type 
                     * by assumption: cD' |- mtt' <= cD1           
                     *                cD' ; [mtt']cPsi1 |- [mtt']tP1 <= type
                     * 
                     *                cD ; cPsi' |- ss' <= cPsi1

                     * We want         cD' ; [mtt']cPsi' |- [mss'][mtt']tP1 <= type
                     * 
                     * Since we can't create m-closures, we need to normalize here.
                     *)

                    let cPsi_n = Whnf.cnormDCtx (cPsi', mtt') in 
                    let tP1_n  = Whnf.cnormTyp (TClo(tP1,ss'), mtt') in 
                      
                      
                    let w = Whnf.newMMVar (cD', cPsi_n, tP1_n) in
                      (* w::[s'^-1](tP1)[cPsi'] in cD'            *)
                      (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tP1)
                         [|w[s']/u|](u[t1]) = [t1](w[s'])
                         [|w[s']/u|](u[t2]) = [t2](w[s'])
                      *)
                    let _ = instantiateMMVar (r1, Root(Syntax.Loc.ghost, MMVar(w, (mt', s')), Nil), !cnstrs1) in 

                     dprint (fun () -> "Instantiated with new meta^2-variable " ^ 
                                        P.normalToString cD0 cPsi sM1)
                      

              | (true, true, _, false) ->
                  (* t2' is not a pattern substitution *)
                  addConstraint (cnstrs2, ref (Eqn (cD0, cPsi, Clo sM, Clo sN))) (* XXX double-check *) 

              | (true, true, false, _ ) ->
                  addConstraint (cnstrs2, ref (Eqn (cD0, cPsi, Clo sM, Clo sN))) (* XXX double-check *)

              | (false, _, _, _) ->
                  addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, Clo sN, Clo sM)))  (* XXX double-check *)

              | (_, false, _, _) ->
                  (* t1' is not a pattern substitution *)

                  addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, Clo sN, Clo sM)))  (* XXX double-check *) 

          else
            begin match (isPatMSub mt1, isPatSub t1' , isPatMSub mt2, isPatSub t2') with
              | (true, true, _, _) ->
                  (* since   cD ; cPsi' |- t1 <= cPsi1 and cD ; cPsi |- t1 o s1 <= cPsi1,
                   * we have cD ; cPsi |- t1' <= cPsi1 and cD  |- mt1 <= cD1
                   *)
                  
                  begin try
                    let ss1  = invert t1' in
                      (* cD ; cPsi1 |- ss1 <= cPsi *)
                    let mtt1 = Whnf.m_invert (Whnf.cnormMSub mt1) in 
                      (* cD1 |- mtt1 <= cD *)
                     let _ = dprint (fun () -> 
                                      "UNIFY(1 a): " ^ 
                                              P.mctxToString cD0 ^ "\n" ^
                                              P.normalToString cD0 cPsi sM1  
                                      ^ " : " ^ P.typToString cD0 cPsi (tP1, t1') ^ 
                                        "\n    " ^
                                              P.normalToString cD0 cPsi sM2 
                                      ^ " : " ^ P.typToString cD0 cPsi (tP2, t2')  
                                      ^ "\n") in 
                    let phat = Context.dctxToHat cPsi in 
                    let tM2' = trail (fun () -> prune cD0 cPsi1 phat sM2 (mtt1, ss1) (MVarRef r1)) in 
                    (* sM2 = [ss1][s2]tM2 *) 

                    (instantiateMMVar (r1, tM2', !cnstrs1)  ; 
                    dprint (fun () -> "Instantiated with sM1 with pruned tM2' " ^ 
                                        P.normalToString cD0 cPsi sM1) )

                  with
                    | NotInvertible ->
                        ((* Printf.printf "Added constraints: NotInvertible: \n ";*)
                          addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))) 
                    (* Printf.printf "Pruning failed -  NotInvertible: \n" ; *)
                    (* raise (Unify "NotInvertible") *)
                        )
                  end
              | (_ , _, true, true) ->
                  begin try
                    let ss2 = invert t2'(* cD ; cPsi2 |- ss2 <= cPsi *) in
                    let mtt2 = Whnf.m_invert (Whnf.cnormMSub mt2) in 
                      (* cD1 |- mtt1 <= cD *)
                    let phat = Context.dctxToHat cPsi in 

                     let _ = dprint (fun () -> 
                                      "UNIFY(1 b): " ^ 
                                              P.mctxToString cD0 ^ "\n" ^
                                              P.normalToString cD0 cPsi sM1  
                                      ^ " : " ^ P.typToString cD0 cPsi (tP1, t1') ^ 
                                        "\n    " ^
                                              P.normalToString cD0 cPsi sM2 
                                      ^ " : " ^ P.typToString cD0 cPsi (tP2, t2')  
                                      ^ "\n") in 


                    let tM1' = trail (fun () -> prune cD0 cPsi2 phat sM1 (mtt2, ss2) (MVarRef r2)) in
                      (instantiateMMVar (r2, tM1', !cnstrs2) ;                    
                       dprint (fun () -> "Instantiated with new meta^2-variable " ^ 
                                        P.normalToString cD0 cPsi sM2) )
                  with
                    | NotInvertible ->
                        (  (* Printf.printf "Added constraints: NotInvertible: \n" ; *)
                          addConstraint (cnstrs2, ref (Eqn (cD0, cPsi, Clo sM2, Clo sM1)))
                    (* Printf.printf "Pruning failed -- NotInvertible:\n" ;*)
                    (* raise (Unify "NotInvertible") *)
                             )
                  end
(*              | ( _ , false , _ , _ ) -> 
                  (* neither t1' is not pattern substitutions -- add projPat case *)
                  let cnstr = ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)) in                    
                   addConstraint (cnstrs1, cnstr)

              | ( _ , _ , _ , false ) -> 
                  (* neither t2' is not pattern substitutions -- add projPat case *)
                  let cnstr = ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)) in                    
                   addConstraint (cnstrs1, cnstr)
*)
              | (_ , _ , _ , _) ->
                  begin match  (isProjPatSub t1' , isProjPatSub t2') with
                    | ( _ , true ) -> 
                        begin try 
                          let mtt2 = Whnf.m_invert (Whnf.cnormMSub mt2) in 
                          let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in 
                          let phat = Context.dctxToHat flat_cPsi in 
                          let t_flat = ConvSigma.strans_sub t2' conv_list in 
                          let tM1'   = ConvSigma.strans_norm sM1 conv_list in 
                          let ss = invert t_flat in

                     let _ = dprint (fun () -> 
                                      "UNIFY(1 c (proj-sub)): " ^ 
                                              P.mctxToString cD0 ^ "\n" ^
                                              P.normalToString cD0 cPsi sM1  
                                      ^ " : " ^ P.typToString cD0 cPsi (tP1, t1') ^ 
                                        "\n    " ^
                                              P.normalToString cD0 cPsi sM2 
                                      ^ " : " ^ P.typToString cD0 cPsi (tP2, t2')  
                                      ^ "\n") in 

                          let sM1' = trail (fun () -> prune cD0 cPsi2 phat (tM1', id) (mtt2, ss) (MVarRef r2)) in
                            instantiateMMVar (r2, sM1', !cnstrs2) 
                        with
                          | NotInvertible ->
                              ( (* Printf.printf "Added constraints: NotInvertible: \n" ; *)
                               addConstraint (cnstrs2, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)))
                                (* Printf.printf "Pruning failed -  NotInvertible: \n" ; *)
                                (* raise (Unify "NotInvertible") *)
                              ) 
                        end


                    | ( true, _ ) -> 
                        begin try 
                          let mtt1 = Whnf.m_invert (Whnf.cnormMSub mt1) in 
                          let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in 
                          let phat = Context.dctxToHat flat_cPsi in 
                          let t_flat = ConvSigma.strans_sub t1' conv_list in 
                          let tM2'   = ConvSigma.strans_norm sM2 conv_list in 
                          let ss = invert t_flat in
                          let sM2' = trail (fun () -> prune cD0 cPsi1 phat (tM2', id) (mtt1, ss) (MVarRef r1)) in
                            instantiateMMVar (r1, sM2', !cnstrs1) 
                        with
                          | NotInvertible ->
                              ( (* Printf.printf "Added constraints: NotInvertible: \n" ; *)
                                 addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)))
                                (* Printf.printf "Pruning failed -  NotInvertible: \n" ;*)
                                (* raise (Unify "NotInvertible")*)
                              )
                        end



                    | ( _ , _ ) -> 
                        (* neither t1' nor t2' are pattern substitutions *)
                        let cnstr = ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)) in                    
                          addConstraint (cnstrs1, cnstr)
                  end
            end


    (* MMVar-normal case *)
    | ((Root (_, MMVar (MInst (_n, r, _cD,  cPsi1, _tP, cnstrs), (mt, t)), _tS), s1) as sM1, ((_tM2, _s2) as sM2)) ->
        dprnt "(011) MMVar-_";
        let t' = Whnf.normSub (comp t s1) in
          if isPatSub t' && isPatMSub mt then
            begin try
              let ss  = invert t' in
              let mtt = Whnf.m_invert (Whnf.cnormMSub mt) in 
              let _ = dprint (fun () -> 
                                "UNIFY(2): MMVar-Normal\n" ^ 
                                  P.mctxToString cD0 ^ "\n" ^ 
                                  P.normalToString cD0 cPsi sM1 ^ "\n    " ^
                                  P.normalToString cD0 cPsi sM2 ^ "\n") in  
              let phat = Context.dctxToHat cPsi in 
              let sM2' = trail (fun () -> prune cD0 cPsi1 phat sM2 (mtt, ss) (MMVarRef r)) in
                (instantiateMMVar (r, sM2', !cnstrs) ;
                 dprint (fun () -> "Instantiated with new meta^2-variable " ^ 
                                        P.normalToString cD0 cPsi sM1))
            with
              | NotInvertible ->
                  ( (* Printf.printf "Added constraints: NotInvertible: \n" ; *)
                        addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))))
                    (*(* Printf.printf "Pruning failed -- NotInvertible:\n" ;*)
                    raise (Unify "NotInvertible")) *)
            end 
          else 
            (* If we have Sigma types in the context cPsi and we have proj-pat-substitutions *)           
            if isProjPatSub t' && isPatMSub mt then
              begin try
                let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in 
                let phat = Context.dctxToHat flat_cPsi in 
                let t_flat = ConvSigma.strans_sub t' conv_list in 
                let tM2'   = ConvSigma.strans_norm sM2 conv_list in 
                let ss = invert t_flat in
                let mtt = Whnf.m_invert (Whnf.cnormMSub mt) in                   
                let sM2' = trail (fun () -> prune cD0 cPsi1 phat (tM2', id) (mtt, ss) (MMVarRef r)) in
                  instantiateMMVar (r, sM2', !cnstrs)                          
              with | NotInvertible -> 
                ( (* Printf.printf "Added constraints: NotInvertible: \n" ; *)
                    addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))))
                  (* Printf.printf "Pruning failed -- NotInvertible:\n" ; *)
                  (* raise (Unify "NotInvertible")) *)
              end
          else            
             addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)))


    (* normal-MMVar case *)
    | ((_tM1, _s1) as sM1, ((Root (_, MMVar (MInst (_n, r, _cD, cPsi2, _tP, cnstrs), (mt, t)), _tS), s2) as sM2)) ->
        dprnt "(012) _-MMVar"; 
        let t' = Whnf.normSub (comp t s2) in
          if isPatSub t' && isPatMSub mt then
            try
               let _ = dprint (fun () -> 
                                "UNIFY(3): normal-MMVar" ^ 
                                  P.mctxToString cD0 ^ "\n" ^
                                  P.normalToString cD0 cPsi sM1 ^ "\n    " ^
                                  P.normalToString cD0 cPsi sM2 ^ "\n") in 
              
              let ss = invert t' in
              let mtt = Whnf.m_invert (Whnf.cnormMSub mt) in 
              let phat = Context.dctxToHat cPsi in 
              let sM1' = trail (fun () -> prune cD0 cPsi2 phat sM1 (mtt, ss) (MMVarRef r)) in
                instantiateMMVar (r, sM1', !cnstrs)               
            with
              | NotInvertible ->
                  ( Printf.printf "Added constraints: NotInvertible: \n" ; 
                      addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))))
                    (* Printf.printf "Pruning failed -  NotInvertible: \n" ;*)
                    (* raise (Unify "NotInvertible")*)
          else 
            (* If we have Sigma types in the context cPsi and we have proj-pat-substitutions *)           
            if isProjPatSub t' && isPatMSub mt then
            try
              let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in 
              let phat = Context.dctxToHat flat_cPsi in 
              let t_flat = ConvSigma.strans_sub t' conv_list in 
              let tM1'   = ConvSigma.strans_norm sM1 conv_list in 
              let ss = invert t_flat in
              let mtt = Whnf.m_invert (Whnf.cnormMSub mt) in 
              let sM1' = trail (fun () -> prune cD0 cPsi2 phat (tM1', id) (mtt, ss) (MMVarRef r)) in
                instantiateMMVar (r, sM1', !cnstrs)                          
            with | NotInvertible -> 
              ( (* Printf.printf "Added constraints: NotInvertible: \n" ; *)
               addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)))
                (* Printf.printf "Pruning failed -  NotInvertible: \n" ;*)
                (* raise (Unify "NotInvertible") *)
              )
            else        
              addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2)))


    | (((Root(_, h1,tS1), s1) as _sM1), ((Root(_, h2, tS2), s2) as _sM2)) ->
(*        dprnt "(020) Root-Root"; *)
(*        let _ = dprint (fun () -> 
                          "UNIFY: normal - normal (non MVar cases) " ^ 
                            P.mctxToString cD0 ^ "      |-    " ^
                            P.normalToString cD0 cPsi sM1 ^ "           ==       " ^
                            P.normalToString cD0 cPsi sM2 ^ "\n") in 
*)
        (* s1 = s2 = id by whnf *)
        unifyHead  mflag cD0 cPsi h1 h2;
        unifySpine mflag cD0 cPsi (tS1, s1) (tS2, s2)

    | (_sM1, _sM2) ->
        raise (Unify "Expression clash")

  and unifyHead mflag cD0 cPsi head1 head2 = 
    match (head1, head2) with
    | (BVar k1, BVar k2) ->
        if k1 = k2 then
          ()
        else
          raise (Unify "Bound variable clash")

    | (Const c1, Const c2) ->
        if c1 = c2 then
          ()
        else
          raise (Unify "Constant clash")

    | (FVar x1, FVar x2) ->
        if x1 = x2 then
          ()
        else
          raise (Unify "Free Variable clash")

    | (MVar (Offset k, s) , MVar(Offset k', s')) -> 
        if k = k' then unifySub mflag cD0 cPsi s s' 
        else raise (Unify "Bound MVar clash")

    | (FMVar (u, s) , FMVar(u', s')) ->         
        if u = u' then unifySub mflag cD0 cPsi s s' 
        else raise (Unify "Bound MVar clash")

    | (FPVar (q, s), FPVar (p, s'))
        ->   (if p = q then 
                unifySub mflag cD0 cPsi s s' 
              else raise (Error "Front FPVar mismatch"))

    | (PVar (Offset k, s) , PVar(Offset k', s')) -> 
        if k = k' then 
           unifySub mflag cD0 cPsi s s' 
        else raise (Unify "Parameter variable clash")

    | (PVar (PInst (_n, q, _cPsi1, tA1, cnstr), s1) as h1, BVar k2) ->
        let s1' = Whnf.normSub s1 in 
          if isPatSub s1' then
           (begin try             
               let TypDecl(_ , tA2) = Context.ctxDec cPsi k2 in 
                 unifyTyp mflag cD0 cPsi (tA1, s1') (tA2, id)
            with Context.NoTypAvailable -> ()
            end;
            dprint (fun () -> "\n unifyHead bvar - pvar \n") ;
            begin match bvarSub k2 (invert s1') with
                  | Head (BVar k2') -> instantiatePVar (q, BVar k2', !cnstr)
                  | _               -> raise (Unify "Parameter violation")
            end)
          else
            (* example: q[q[x,y],y] = x  should succeed
                        q[q[x,y],y] = y  should fail
               This will be dealt with when solving constraints.
            *)
            addConstraint (cnstr, ref (Eqh (cD0, cPsi, h1, BVar k2)))

    | (BVar k1, (PVar (PInst (_n, q, _cPsi2, tA2, cnstr), s2) as h1)) ->
        let s2' = Whnf.normSub s2 in 
          if isPatSub s2' then
            begin
              begin try
                let _ = dprint (fun () -> "\n unifyHead bvar -pvar \n") in
                let TypDecl(_ , tA1) = Context.ctxDec cPsi k1 in 
                  unifyTyp mflag cD0 cPsi (tA1, id) (tA2, s2') 
              with Context.NoTypAvailable -> () end;
              dprint (fun () -> "unifyHead bvar -pvar ");
              match bvarSub k1 (invert s2') with
                | Head (BVar k1') -> 
                    instantiatePVar (q, BVar k1', !cnstr)
                | _ -> raise (Unify "Parameter violation")
             end
          else
            addConstraint (cnstr, ref (Eqh (cD0, cPsi, BVar k1, h1)))

    | (PVar (PInst (_n1, q1, cPsi1, tA1, cnstr1) as q1', s1'),
       PVar (PInst (_n2, q2, cPsi2, tA2, cnstr2) as q2', s2')) ->
        (* check s1' and s2' are pattern substitutions; possibly generate constraints;
           check intersection (s1', s2'); possibly prune;
           check q1 = q2 *)        
        let s1' = Whnf.normSub s1' in 
        let s2' = Whnf.normSub s2' in 
        let _ = dprint (fun () -> "[unifyHead] PVar (PInst) = PVar(PInst) " ) in
        if q1 == q2 then (* cPsi1 = _cPsi2 *)
          (let _ = dprint (fun () -> "[unifyHead] PVar (PInst) q1 = q2 " ) in
          match (isPatSub s1' ,  isPatSub s2') with
            | (true, true) ->
                let phat = Context.dctxToHat cPsi in 
                let _ = dprint (fun () -> "[unifyHead] " ^ P.headToString cD0 cPsi head1 ^ 
                                  " === " ^ P.headToString cD0 cPsi head2 ) in
                let _ = dprint (fun () -> "compute intersection of") in 
                let _ = dprint (fun () -> "s1'" ^ P.subToString cD0 cPsi s1') in 
                let _ = dprint (fun () -> "s2'" ^ P.subToString cD0 cPsi s2') in
                let _ = dprint (fun () -> "domain cPsi1: " ^ P.dctxToString cD0 cPsi1) in
                let _ = dprint (fun () -> "domain cPsi1: " ^ P.dctxToString cD0 cPsi2) in
                let _ = dprint (fun () -> "target cPsi: " ^ P.dctxToString cD0 cPsi) in
                let (s', cPsi') = intersection phat s1' s2' cPsi1 in
                  (* if cD ; cPsi |- s1' <= cPsi1 and cD ; cPsi |- s2' <= cPsi1
                     then cD ; cPsi1 |- s' <= cPsi' *)
                  (* cPsi' =/= Null ! otherwise no instantiation for
                     parameter variables exists *)
                let ss' = invert (Whnf.normSub s') in
                  (* cD ; cPsi' |- [s']^-1(tA1) <= type *)
                let w = Whnf.newPVar (cPsi', TClo(tA1, ss')) in
                  (* w::[s'^-1](tA1)[cPsi'] in cD'            *)
                  (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tA1)
                     [|w[s']/u|](u[t]) = [t](w[s'])
                  *)
                  instantiatePVar (q2, PVar(w, s'), !cnstr2)
            | (true, false) ->
                addConstraint (cnstr2, ref (Eqh (cD0, cPsi, head1, head2))) (*XXX double-check *)
            | (false, _) ->
                addConstraint (cnstr1, ref (Eqh (cD0, cPsi, head2, head1)))  (*XXX double-check *))
        else
          (let _ = dprint (fun () -> "[unifyHead] PVar (PInst) q1 =/= q2 " ) in
            match (isPatSub s1' , isPatSub s2') with
             | (true, true) ->
                let _ = dprint (fun () -> "[unifyHead] " ^ P.headToString cD0 cPsi head1 ^ 
                                  " === " ^ P.headToString cD0 cPsi head2 ) in
                let _ = dprint (fun () -> "q1 .  cPsi1: " ^ P.dctxToString cD0 cPsi1) in
                let _ = dprint (fun () -> "q2 .  cPsi2: " ^ P.dctxToString cD0 cPsi2) in
                let _ = dprint (fun () -> "q1 .  tA1  : " ^ P.typToString cD0 cPsi1 (tA1, id)) in 
                let _ = dprint (fun () -> "q2 .  tA2  : " ^ P.typToString cD0 cPsi2 (tA2, id)) in 

                 (* no occurs check necessary, because s1' and s2' are pattern subs. *)
                 let _ = (unifyDCtx1 mflag cD0  (Whnf.normDCtx cPsi1) (Whnf.normDCtx cPsi2) ;  (* check that cnstr1 = cnstr2 *)
                          unifyTyp mflag cD0 cPsi1 (tA1, id) (tA2, id)) in 
                 let _ = dprint (fun () -> "Unification of the types and contexts done ... \n") in 
                 (* at this point: s1' = s2'    ! *)
                 let ss = invert s1' in
                  let _ = dprint (fun () -> "Inverted s1' " ^ P.subToString cD0 cPsi ss ) in 
                 let phat = Context.dctxToHat cPsi in  
                 let (s', cPsi') = pruneCtx phat (s2', cPsi2) (MShift 0, ss) in
                   (*
                   (* if   cPsi  |- s2' <= cPsi2  and cPsi1 |- ss <= cPsi
                      then cPsi2 |- s' <= cPsi' and [ss](s2' (s')) exists *)
                   (* cPsi' =/= Null ! otherwise no instantiation for
                      parameter variables exists *)
                 *)
                 let p = Whnf.newPVar (cPsi', TClo(tA2, invert (Whnf.normSub s'))) in
                   (* p::([s'^-1]tA2)[cPsi'] and
                      [|cPsi2.p[s'] / q2 |](q2[s2']) = p[[s2'] s']

                      and   cPsi |- [s2'] s' : cPsi'
                      and   cPsi |- p[[s2'] s'] : [s2'][s'][s'^-1] tA2
                      and [s2'][s'][s'^-1] tA2  = [s2']tA2 *)
                   (instantiatePVar (q2, PVar(p, s'), !cnstr2);
                    instantiatePVar (q1, PVar(p, s'), !cnstr1);
                    (* instantiatePVar (q1, PVar(p, comp ss (comp s2' s')), !cnstr1)*))

             | (true, false) ->
                 let _ = (unifyDCtx1 mflag cD0 (Whnf.normDCtx cPsi1)
                                               (Whnf.normDCtx cPsi2) ;  (* check that cnstr1 = cnstr2 *)
                          unifyTyp mflag cD0 cPsi1 (tA1, id) (tA2, id)) in 

                  (* only s1' is a pattern sub
                     [(s1)^-1](q2[s2']) = q2[(s1)^-1 s2']
                  *)
                 let ss1 = invert s1' in 
                 let phat = Context.dctxToHat cPsi in 
                 let s' = invSub cD0 phat (s2', cPsi2) (MShift 0 , ss1)  (PVarRef q1) in
                   instantiatePVar (q1, PVar(q2',s'), !cnstr1)

             | (false, true) ->
                 let _ = (unifyDCtx1 mflag cD0 (Whnf.normDCtx cPsi1)
                                               (Whnf.normDCtx cPsi2) ;  (* check that cnstr1 = cnstr2 *)
                          unifyTyp mflag cD0 cPsi1 (tA1, id) (tA2, id)) in 

                 (* only s2' is a pattern sub *)
                 let ss2 = invert s2' in 
                 let phat = Context.dctxToHat cPsi in 
                 let s' = invSub cD0 phat (s1', cPsi1) (MShift 0, ss2) (PVarRef q2) in
                   instantiatePVar (q2, PVar(q1', s'), !cnstr2)

             | (false, false) ->
                 (* neither s1' nor s2' are patsub *)
                 addConstraint (cnstr1, ref (Eqh (cD0, cPsi, head1, head2))))

    | (Proj(BVar k, i) , PVar (PInst (_n1, q1, _cPsi1, _tA1, cnstr1), s1)) ->
        let s1' = Whnf.normSub s1 in 
         if isPatSub s1' then
           let ss' = invert (Whnf.normSub s1') in
             begin match bvarSub k ss' with
               | Head (BVar k') ->
                   instantiatePVar (q1, Proj(BVar k', i), !cnstr1)
               | _ -> raise (Unify "parameter variable =/= projection of bound variable ")
             end 
         else 
           addConstraint (cnstr1, ref (Eqh (cD0, cPsi, head1, head2))) 

    | (PVar (PInst (_n1, q1, _cPsi1, _tA1, cnstr1), s1), Proj(BVar k, i)) ->
        let s1' = Whnf.normSub s1 in 
         if isPatSub s1' then
           let ss' = invert (Whnf.normSub s1') in
             begin match bvarSub k ss' with
               | Head (BVar k') ->
                   instantiatePVar (q1, Proj(BVar k', i), !cnstr1)
               | _ -> raise (Unify "parameter variable =/= projection of bound variable ")
             end
         else 
           addConstraint (cnstr1, ref (Eqh (cD0, cPsi, head1, head2))) 
             

    | (Proj (h1, i1),  Proj (h2, i2)) ->
        let _ = dprint (fun () -> "[unifyHead] Proj - Proj ") in 
        if i1 = i2 then
          (dprint (fun () -> "[unifyHead] " ^ P.headToString cD0 cPsi h1 ^ " === " ^ P.headToString cD0 cPsi h2 ) ;
          unifyHead mflag cD0 cPsi h1 h2 )
        else
          raise (Unify ("(Proj) Index clash: " ^ string_of_int i1 ^ " /= " ^ string_of_int i2))

    | (Proj (PVar (PInst (_n, q, _, _, cnstr), s1), projIndex) as h1, BVar k2) ->
        let _ = (q, cnstr, s1, projIndex, h1, k2) in
          (print_string "Unifying projection of parameter with bound variable currently disallowed\n";
           raise (Unify "Projection of parameter variable =/= bound variable"))

    | (BVar k2, Proj (PVar (PInst (_n, q, cPsi2, tA2, cnstr), s1), projIndex) as h1) ->
        let _ = (q, cnstr, s1, projIndex, h1, k2) in
           (print_string "Unifying projection of parameter with bound variable currently disallowed\n";
            raise (Unify "Projection of parameter variable =/= bound variable"))

    | (FVar _, Proj (PVar _, _)) ->
        (print_string "[UnifyHead] Unify free variable with projection of parameter variable\n";
         raise (Unify "Projection of parameter variable =/= free variable"))

    | (PVar _ , Proj (PVar _, _)) ->
        (print_string "[UnifyHead] Projection of a parameter variable\n";
         raise (Unify "PVar =/= Proj PVar"))

    | ((PVar (Offset k, s1)) as _sM1,   ((PVar (PInst (_n, r, cPsi1, tP1, cnstrs), t')) as _sM2)) ->
(*
    | ((_tM1, _s1) as s1,      ((Root (_, MVar (Inst (_n, r, cPsi1, tP1, cnstrs), t), _tS), s2) as sM2)) ->
*)
          if isPatSub t' then
            try
(*              let _ = dprint (fun () -> 
                                "UNIFYHEAD(3): " ^
                                  P.mctxToString cD0 ^ "\n        " ^
                                  P.headToString cD0 cPsi sM1 ^ "\n        " ^
                                  P.headToString cD0 cPsi sM2 ^
                                  " : " ^ P.typToString cD0 cPsi (tP1,   t')) in                 
*)
              let ss = invert (Whnf.normSub t') in 
              let sM1' = PVar (Offset k, comp s1 ss) in  

              let _phat = Context.dctxToHat cPsi in 
                instantiatePVar (r, sM1', !cnstrs)
            with
              | NotInvertible ->
                  ( (* Printf.printf "Pruning failed -- NotInvertible\n" ; *)
                    (* Printf.printf "Added constraints: NotInvertible:\n" ;
                     addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))) *)
                    raise (Unify "PVar - BVar dependency") 
                  )
          else            
            if isProjPatSub t' then 
              begin try 
                let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in 
                let _phat = Context.dctxToHat flat_cPsi in 
                let t_flat = ConvSigma.strans_sub t' conv_list in 
(*                let _tM1'   = ConvSigma.strans_head sM1 conv_list in  *)
                let ss = invert t_flat in
(*                let sM1' = trail (fun () -> prune cD0 cPsi1 phat (tM1', id) (MShift 0, ss) (MVarRef r)) in*)
                let sM1' = PVar (Offset k, comp s1 ss) in
                  instantiatePVar (r, sM1', !cnstrs) 
              with
              | NotInvertible ->
                  ((* Printf.printf "Added constraints: NotInvertible: \n" ;
                       addConstraint (cnstrs, ref (Eqn (cD0, cPsi, Clo sM1, Clo sM2))) *)
                    (* Printf.printf "Pruning failed -- NotInvertible\n";*)
                     raise (Unify "PVar - BVar dependency") 
                  )
              end
            else 
             raise (Unify "PVar - Nonpattern substitution")
(*        (print_string "[UnifyHead] PVar(Offset,_) - PVar (PInst,_)\n";
         raise (Unify "PVar Offset - PVar PInst"))
*)

    | (PVar (PInst _, _s1),  PVar (Offset k, _s2)) ->
        (print_string "[UnifyHead] PVar(PInst,_) - PVar (Offset,_)\n";
         raise (Unify "PVar Inst - PVar Offset"))


    | (_h1 , _h2 ) ->
        raise (Unify "Head clash")


    (* unifySpine mflag cD0 (cPsi, (tS1, s1), (tS2, s2)) = ()

       Invariant:
       If   hat(cPsi) = phat
       and  cPsi |- s1 : cPsi1   cPsi1 |- tS1 : tA1 > tP1
       and  cPsi |- s2 : cPsi2   cPsi2 |- tS2 : tA2 > tP2
       and  cPsi |- tA1 [s1] = tA2 [s2]  <= type
       and  cPsi |- tP1 [s1] = tP2 [s2]
       then if there is an instantiation t :
                 s.t. cPsi |- [|theta|] (tS1 [s1]) == [|theta|](tS2 [s2])
            then instantiation is applied as effect, () returned
            else exception Unify is raised

       Other effects: MVars may be lowered during whnf,
                      constraints may be added for non-patterns
    *)
    and unifySpine mflag cD0 cPsi spine1 spine2 = match (spine1, spine2) with
      | ((Nil, _), (Nil, _)) ->
          ()

      | ((SClo (tS1, s1'), s1), sS) ->
          unifySpine mflag cD0 cPsi (tS1, comp s1' s1) sS

      | (sS, (SClo (tS2, s2'), s2)) ->
          unifySpine mflag cD0 cPsi sS (tS2, comp s2' s2)

      | ((App (tM1, tS1), s1), (App (tM2, tS2), s2)) ->
          dprint (fun () -> "[unifySpine] " ^ P.normalToString cD0 cPsi (tM1,s1) ^ 
                    " == " ^ P.normalToString cD0 cPsi (tM2, s2));
          unifyTerm mflag cD0 cPsi (tM1, s1) (tM2, s2);
          unifySpine mflag cD0 cPsi (tS1, s1) (tS2, s2)
      (* Nil/App or App/Nil cannot occur by typing invariants *)


    and unifySub mflag cD0 cPsi s1 s2 = match (s1, s2) with 

      | (Shift (psi, n), Shift (phi, k)) ->
          let rec compatible_cv = function
            | (CtxName n1,  CtxName n2) -> n1 = n2
            | (CtxOffset off1,  CtxOffset off2) -> off1 = off2
            | (CInst (_, {contents=None}, _, _, _),  _) -> true
            | (_,  CInst (_, {contents=None}, _, _, _)) -> true
            | (CInst (_, {contents=Some (CtxVar ctx_var1)}, _, _, _),  ctx_var2) -> compatible_cv (ctx_var1, ctx_var2)
            | (ctx_var1,  CInst (_, {contents=Some (CtxVar ctx_var2)}, _, _, _)) -> compatible_cv (ctx_var1, ctx_var2)
            | (_, _) -> false
          and compatible = function
            | (NoCtxShift, NoCtxShift) -> true
            | (CtxShift ctx_var1, CtxShift ctx_var2) -> compatible_cv (ctx_var1, ctx_var2)
            | (NegCtxShift ctx_var1, NegCtxShift ctx_var2) -> compatible_cv (ctx_var1, ctx_var2)
            | (_, _) -> false
          in
            if n = k && compatible (psi, phi) then
              () 
            else
              raise (Error "Substitutions not well-typed")

      | (SVar(Offset s1, sigma1), SVar(Offset s2, sigma2)) 
        -> if s1 = s2 then 
          unifySub mflag cD0 cPsi sigma1 sigma2
        else raise (Error "SVar mismatch")

      | (Dot (f, s), Dot (f', s'))
        -> (unifyFront mflag cD0 cPsi f f' ;
            unifySub mflag cD0 cPsi s s')
      
      | (Shift (psi, n), Dot(Head BVar _k, _s')) 
          -> 
           unifySub mflag cD0 cPsi (Dot (Head (BVar (n+1)), Shift (psi, n+1))) s2

      | (Dot(Head BVar _k, _s'), Shift (psi, n)) 
          ->  
            unifySub mflag cD0 cPsi s1 (Dot (Head (BVar (n+1)), Shift (psi, n+1)))

      |  _
        -> raise (Unify (
                            "Substitution mismatch :\n " ^ P.dctxToString cD0 cPsi 
                         ^ "|-" ^ P.subToString cD0 cPsi s1 ^ " =/= " ^ P.subToString cD0 cPsi s2 ^ "\n"))


    and unifyFront mflag cD0 cPsi front1 front2 = match (front1, front2) with
      | (Head (BVar i), Head (BVar k))
        -> if i = k then () else 
              raise (Error "Front BVar mismatch")

      | (Head (Const i), Head (Const k))
        -> if i = k then () else raise (Error "Front Constant mismatch")

      | (Head (PVar (q, s)), Head (PVar (p, s')))
        -> (if p = q then
            unifySub mflag cD0 cPsi s s'
            else raise (Error "Front PVar mismatch"))


      | (Head (FPVar (q, s)), Head (FPVar (p, s')))
        ->   (if p = q then 
                unifySub mflag cD0 cPsi s s' 
              else raise (Error "Front FPVar mismatch"))

      | (Head (MVar (u, s)), Head (MVar (v, s')))
        ->  (if u = v then
               unifySub mflag cD0 cPsi s s'
             else raise (Error "Front MVar mismatch"))

      | (Head (FMVar (u, s)), Head (FMVar (v, s')))
        ->    (if u = v then
                 unifySub mflag cD0 cPsi s s'
               else raise (Error "Front FMVar mismatch"))

      | (Head (Proj (head, k)), Head (Proj (head', k')))
        ->    (if k = k' then
                 unifyFront mflag cD0 cPsi (Head head) (Head head')
               else raise (Error "Front Proj mismatch"))

      | (Head (FVar x), Head (FVar y)) 
        -> if x = y then () else raise (Error "Front FVar mismatch")

      | (Obj tM, Obj tN)
        -> unifyTerm mflag cD0 cPsi (tM, id) (tN, id)

      | (Head head, Obj tN)
        -> unifyTerm mflag cD0 cPsi (Root (Syntax.Loc.ghost, head, Nil), id) (tN, id)

      | (Obj tN, Head head)
        -> unifyTerm mflag cD0 cPsi (tN, id) (Root (Syntax.Loc.ghost, head, Nil), id)

      | (Undef, Undef)
        -> ()

      | (_, _)
        -> raise (Error "Front mismatch")


   and unifyTyp mflag cD0 cPsi sA sB = unifyTypW mflag cD0 cPsi (Whnf.whnfTyp sA) (Whnf.whnfTyp sB)

    and unifyTypW mflag cD0 cPsi sA sB = match (sA, sB) with
      | ((Atom (_, a, tS1), s1),   (Atom (_, b, tS2), s2))  ->
          if a = b then
            (dprint (fun () -> "Unify Atomic types " ^ P.typToString cD0 cPsi sA
                       ^ " == " ^ P.typToString cD0 cPsi sB);
            unifySpine mflag cD0 cPsi (tS1, s1) (tS2, s2))
          else
            (dprint (fun () -> "UnifyTyp " ^ P.typToString cD0 cPsi sA ^ " ==== " ^ P.typToString cD0 cPsi sB);
            raise (Unify "Type constant clash"))

      | ((PiTyp ((TypDecl(x, tA1), dep), tA2), s1), (PiTyp ((TypDecl(_x, tB1), _dep), tB2), s2)) -> 
          unifyTyp mflag cD0 cPsi (tA1, s1) (tB1, s2) ;
          unifyTyp mflag cD0 (DDec(cPsi, TypDecl(x, tA1))) (tA2, dot1 s1) (tB2, dot1 s2)

      | ((Sigma typ_rec1, s1), (Sigma typ_rec2, s2)) -> 
          unifyTypRecW mflag cD0 cPsi (typ_rec1, s1) (typ_rec2, s2)

      | _ ->  raise (Unify "Type mismatch")


    and unifyTypRecW mflag cD0 cPsi srec1 srec2 = match (srec1, srec2) with
      | ((SigmaLast tA1, s1) ,   (SigmaLast tA2, s2)) ->
          dprint (fun () -> "[unifyTypRecW] Last "
                          ^ P.typToString cD0 cPsi (tA1, s1)  ^ " == "
                          ^ P.typToString cD0 cPsi (tA2, s2) ^ "\n");
          unifyTyp mflag cD0 cPsi (tA1,s1) (tA2,s2)
        ; dprint (fun () ->  "succeeded   ["
                          ^ P.typRecToString cD0 cPsi srec1
                          ^ "]  ["
                          ^ P.typRecToString cD0 cPsi srec2 ^ "]");
      
      | ((SigmaElem (x1, tA1, trec1),  s1) ,   (SigmaElem (_x2, tA2, trec2), s2))  ->
          (dprint (fun () -> "[unifyTypRecW] Elements " ^ 
                     P.typToString cD0 cPsi (tA1, s1) ^ " == " 
                     ^ P.typToString cD0 cPsi (tA2, s2));
          unifyTyp mflag cD0 cPsi (tA1,s1) (tA2,s2)
         ; 
          let s1' = dot1 s1 in 
          let s2' = dot1 s2 in
             unifyTypRecW mflag cD0 (DDec(cPsi, TypDecl(x1, TClo(tA1,s1)))) (trec1,s1') (trec2,s2')
          )
      
      | ((_, _s1) ,   (_, _s2)) ->
          raise (Unify "TypRec length clash")
   

   (* Unify pattern fragment, and force constraints after pattern unification
   succeeded *)
    (* Pre-condition: cPsi1, cPsi2 are in normal form *)
 and unifyDCtx1 mflag cD0 cPsi1 cPsi2 = match (cPsi1 , cPsi2) with
      | (Null , Null) -> ()

      | (CtxVar (CInst (_n1, ({contents = None} as cvar_ref1), _schema1, _cO1, _cD1)) , 
         CtxVar (CInst (_n2, ({contents = None} as cvar_ref2), _schema2, _cO2, _cD2))) -> 
          if cvar_ref1 == cvar_ref2 then ()  
          else 
           instantiateCtxVar (cvar_ref1, cPsi2)

      | (CtxVar (CInst (_n, ({contents = None} as cvar_ref), s_cid, _cO, _cD)) , cPsi) -> 
           instantiateCtxVar (cvar_ref, cPsi);
           begin match Context.ctxVar cPsi with 
             | None -> ()
             | Some (CtxName psi) -> 
               Store.FCVar.add psi (cD0, CDecl (psi, s_cid, No))                   
             | _ -> ()
           end

      | (cPsi , CtxVar (CInst (_n, ({contents = None} as cvar_ref), s_cid, _cO, _cD) )) -> 
           instantiateCtxVar (cvar_ref, cPsi);
           begin match Context.ctxVar cPsi with 
             | None -> ()
             | Some (CtxName psi) -> 
               Store.FCVar.add psi (cD0, CDecl (psi, s_cid, No))                   
             | _ -> ()
           end

      | (CtxVar cvar, CtxVar cvar') -> 
          if cvar = cvar' then () 
          else 
             raise (Unify "Bound (named) context variable clash")

      | (DDec (cPsi1, TypDecl(_ , tA1)) , DDec (cPsi2, TypDecl(_ , tA2))) -> 
            (unifyDCtx1 mflag cD0 cPsi1 cPsi2 ; 
            unifyTyp mflag cD0 cPsi1 (tA1, id)   (tA2, id))

      | (DDec (cPsi1, _) , DDec (cPsi2, _ )) -> 
            unifyDCtx1 mflag cD0 cPsi1 cPsi2  
      | _ -> 
          (dprint (fun () -> "Unify Context clash: cPsi1 = " ^ 
                     P.dctxToString cD0 cPsi1 
                     ^ " cPsi2 = " ^ P.dctxToString cD0 cPsi2 ) ; 
           raise (Unify "Context clash"))

   (* **************************************************************** *)

  let rec unifyMetaObj cD (mO, t) (mO', t') = match ((mO, t) , (mO', t')) with
    | (Comp.MetaCtx (_, cPsi), t) , (Comp.MetaCtx (_, cPsi'), t') -> 
        unifyDCtx1 Unification cD (Whnf.cnormDCtx (cPsi, t)) (Whnf.cnormDCtx (cPsi', t'))
        
    | (Comp.MetaObj (_, phat, tR) , t) , (Comp.MetaObj (_, phat', tR') , t') -> 
        let cPsi  = Context.hatToDCtx phat in 
        let cPsi' = Context.hatToDCtx phat' in 
          unifyDCtx1 Unification cD (Whnf.cnormDCtx (cPsi, t)) (Whnf.cnormDCtx (cPsi', t'));
          unifyTerm Unification cD cPsi
            (Whnf.cnorm (tR , t), id) (Whnf.cnorm (tR', t'), id)


    | (Comp.MetaObjAnn (_, cPsi, tR) , t) , (Comp.MetaObjAnn (_, cPsi', tR') ,
      t') -> 
        let cPsi1 = Whnf.cnormDCtx (cPsi, t) in 
        let cPsi2 = Whnf.cnormDCtx (cPsi', t') in 
          unifyDCtx1 Unification cD  cPsi1 cPsi2 ;
          unifyTerm Unification cD cPsi1 
            (Whnf.cnorm (tR, t), id) (Whnf.cnorm (tR', t'), id)
    | _ -> raise (Unify "MetaObj mismatch")

  let rec unifyMetaSpine cD (mS, t) (mS', t') = match ((mS, t) , (mS', t')) with
    | (Comp.MetaNil, _ ) , (Comp.MetaNil, _ ) -> ()
    | (Comp.MetaApp (mO, mS), t) , (Comp.MetaApp (mO', mS'), t') -> 
        let mOt = Whnf.cnormMetaObj (mO, t) in 
        let mOt' = Whnf.cnormMetaObj (mO', t') in 
          (dprint (fun () -> "[unifyMetaObj] BEFORE " ^ P.metaObjToString cD mOt' ^ " == " ^ 
                    P.metaObjToString cD mOt);
          unifyMetaObj cD (mO, t) (mO', t');
          dprint (fun () -> "[unifyMetaObj] AFTER " ^ P.metaObjToString cD mOt ^ " == " ^ 
                    P.metaObjToString cD mO');
          unifyMetaSpine cD (mS, t) (mS', t');
          dprint (fun () -> "[unifyMetaObj] AFTER UNIFYING SPINES" ^ P.metaObjToString cD mOt ^ " == " ^ 
                    P.metaObjToString cD mO'))

    | _ -> raise (Unify "Meta-Spine mismatch")

    let rec unifyCompTyp cD tau_t tau_t' = 
      unifyCompTypW cD (Whnf.cwhnfCTyp tau_t) (Whnf.cwhnfCTyp tau_t')

    and unifyCompTypW cD tau_t tau_t' = match (tau_t,  tau_t') with
      | ((Comp.TypBase (_, c, mS), t), (Comp.TypBase (_, c', mS'), t')) -> 
          if c = c' then 
            (unifyMetaSpine cD (mS, t) (mS', t'); 
             dprint (fun () -> "[unifyCompTyp] " ^ 
                       P.compTypToString cD (Whnf.cnormCTyp tau_t) ^ " == "  ^
                       P.compTypToString cD (Whnf.cnormCTyp tau_t') ))
                       
          else 
            raise (Unify "Type Constant Clash")
      | ((Comp.TypBox (_, tA, cPsi), t) , (Comp.TypBox (_, tA', cPsi'), t')) -> 
          let cPsi1 = Whnf.cnormDCtx (cPsi, t) in 
          (unifyDCtx1 Unification cD cPsi1 (Whnf.cnormDCtx (cPsi', t'));
           dprint (fun () -> "Unifying contexts done");
           unifyTyp Unification cD cPsi1 (Whnf.cnormTyp (tA, t), id)  (Whnf.cnormTyp (tA', t'), id)
          )

      | ((Comp.TypArr (tau1, tau2), t), (Comp.TypArr (tau1', tau2'), t')) -> 
          (unifyCompTyp cD (tau1, t) (tau1', t') ; 
           unifyCompTyp cD (tau2, t) (tau2', t')
          )


      | ((Comp.TypCross (tau1, tau2), t), (Comp.TypCross (tau1', tau2'), t')) -> 
          (unifyCompTyp cD (tau1, t) (tau1', t') ; 
           unifyCompTyp cD (tau2, t) (tau2', t')
          )

      | ((Comp.TypCtxPi ( (psi, schema, dep), tau), t) , 
         (Comp.TypCtxPi ( (_, schema', dep'), tau'), t')) -> 
          if schema = schema' && dep = dep' then
            let cdep = (match dep with Comp.Implicit -> Maybe |  Comp.Explicit -> No) in 
            unifyCompTyp 
              (Dec(cD, CDecl (psi, schema, cdep))) 
              (tau, Whnf.mvar_dot1 t) (tau', Whnf.mvar_dot1 t')
          else
            raise (Unify "CtxPi schema clash")
                 
      | ((Comp.TypPiBox ((MDecl(u, tA, cPsi), _ ), tau), t),  
         (Comp.TypPiBox ((MDecl(_, tA', cPsi'), _ ), tau'), t')) -> 
          let tAn    = Whnf.cnormTyp (tA, t) in
          let tAn'   = Whnf.cnormTyp (tA', t') in
          let cPsin  = Whnf.cnormDCtx (cPsi, t) in
          let cPsin' = Whnf.cnormDCtx (cPsi', t') in
            (unifyDCtx1 Unification cD cPsin cPsin';
             unifyTyp Unification cD cPsin (tAn, id)  (tAn', id);
             unifyCompTyp (Dec(cD, MDecl(u, tAn, cPsin))) 
               (tau, Whnf.mvar_dot1 t) (tau', Whnf.mvar_dot1 t')
            )

      | ((Comp.TypBool, _ ), (Comp.TypBool, _ )) -> ()
      | _ -> raise (Unify "Computation-level Type Clash")


   (* **************************************************************** *)
    let rec unify1 mflag cD0 cPsi sM1 sM2 = 
      unifyTerm mflag cD0 cPsi sM1 sM2;
(*      dprint (fun () -> "Forcing constraint...") ;  *)
      forceCnstr mflag (nextCnstr ())

    (* NOTE: We sometimes flip the position when we generate constraints;
       if matching requires that the first argument is fixed then this may
       become problematic if we are outside the pattern fragment -bp *)
    and forceCnstr mflag constrnt = match constrnt with
      | None       -> () (* dprint (fun () -> "All constraints forced.") *)  (* all constraints are forced *) 
      | Some cnstr ->
          (dprint (fun () -> "Found constraint ...\n"); 
          begin match !cnstr with
            | Queued (* in process elsewhere *) ->  
                (dprint (fun () -> "Constrait is queued\n") ; 
                forceCnstr mflag (nextCnstr ()))
            | Eqn (cD, cPsi, tM1, tM2) ->
                let _ = solveConstraint cnstr in 
(*                let tM1' = Whnf.norm (tM1, id) in 
                let tM2' = Whnf.norm (tM2, id) in  *)
                  (dprint (fun () ->  "Solve constraint: " ^ P.normalToString cD cPsi (tM1, id)  ^  
                        " = " ^ P.normalToString cD cPsi (tM2, id) ^ "\n");
                   if Whnf.conv (tM1, id) (tM2, id) then dprint (fun () ->  "Constraints are trivial...")
                   else 
                     (dprint (fun () ->  "Use unification on them...");
                      unify1 mflag cD cPsi (tM2, id) (tM1, id);
                      dprint (fun () ->  "Solved constraint (DONE): " ^ 
                                P.normalToString cD cPsi (tM1, id)  ^ 
                                " = " ^ P.normalToString cD cPsi (tM2, id) ^ "\n"))
                  )
            | Eqh (cD, cPsi, h1, h2)   ->
                let _ = solveConstraint cnstr in 
                  (dprint (fun () -> "Solve constraint (H): " ^ P.headToString cD cPsi h1  ^ 
                        " = " ^ P.headToString cD cPsi h2 ^ "\n");
                  unifyHead mflag cD cPsi h1 h2 ;
                  dprint (fun () -> "Solved constraint (H): " ^ P.headToString cD cPsi h1  ^ 
                        " = " ^ P.headToString cD cPsi h2 ^ "\n"))
          end )
                  
    and forceGlobalCnstr c_list = match c_list with
      | [ ] -> ()
      | c::cnstrs -> 
          match !c with
            | Queued (* in process elsewhere *) -> forceGlobalCnstr cnstrs 
            |  Eqn (cD, cPsi, tM1, tM2) ->
                 let _ = solveConstraint c in 
                   (dprint (fun () ->  "Solve global constraint:\n") ; 
                    dprint (fun () ->  P.normalToString cD cPsi (tM1, id)  ^  
                        " = " ^ P.normalToString cD cPsi (tM2, id) ^ "\n");
                   unify1 Unification cD cPsi (tM2, id) (tM1, id);
                   dprint (fun () ->  "Solved global constraint (DONE): " ^ P.normalToString cD cPsi (tM1, id)  ^ 
                        " = " ^ P.normalToString cD cPsi (tM2, id) ^ "\n"))
            | Eqh (cD, cPsi, h1, h2)   ->
                let _ = solveConstraint c in 
                  (dprint (fun () -> "Solve global constraint (H): " ^ P.headToString cD cPsi h1  ^ 
                        " = " ^ P.headToString cD cPsi h2 ^ "\n");
                  unifyHead Unification cD cPsi h1 h2 ;
                  dprint (fun () -> "Solved global constraint (H): " ^ P.headToString cD cPsi h1  ^ 
                        " = " ^ P.headToString cD cPsi h2 ^ "\n"))


    let rec unresolvedGlobalCnstrs () = 
      begin try
        forceGlobalCnstr (!globalCnstrs); 
        resetGlobalCnstrs () ;
        false
      with Unify _ -> resetGlobalCnstrs () ; true
      end

    let unify' mflag cD0 cPsi sM1 sM2 =
      resetDelayedCnstrs ();
      unify1 mflag cD0 cPsi sM1 sM2

    let unifyTyp1 mflag cD0 cPsi sA sB = 
      unifyTyp mflag cD0 cPsi sA sB;
      forceCnstr mflag (nextCnstr ())
(*      dprint (fun () -> "Forcing Cnstr DONE") *)
         

    let unifyTyp' mflag cD0 cPsi sA sB =
       (dprint (fun () -> "\nUnifyTyp' " ^
                         P.typToString cD0 cPsi sA ^ "\n          " ^
                         P.typToString cD0 cPsi sB); 
       resetDelayedCnstrs (); 
       unifyTyp1 mflag cD0 cPsi sA sB) 
(*       dprint (fun () -> "After unifyTyp'");
       dprint (fun () -> "sA = " ^ P.typToString cD0 cPsi sA ^ "\n     ");
       dprint (fun () -> P.typToString cD0 cPsi sB) *)

    let unifyTypRec1 mflag cD0 cPsi sArec sBrec =  
      unifyTypRecW mflag cD0 cPsi sArec sBrec;
      forceCnstr mflag (nextCnstr ())

    let unifyTypRec' mflag cD0 cPsi sArec sBrec =
      resetDelayedCnstrs ();
      unifyTypRec1 mflag cD0 cPsi sArec sBrec


    let unify cD0 cPsi sM sN = 
      dprint (fun () -> "Unify " ^ P.normalToString cD0 cPsi sM
                      ^ "\n with \n" ^ P.normalToString Empty cPsi sN);
      unify' Unification cD0 cPsi sM sN;
      dprint (fun () -> "Unify DONE: " ^ P.normalToString cD0 cPsi sM ^ "\n ==  \n" ^ P.normalToString Empty cPsi sN)


   (* **************************************************************** *)

    let rec unifyMSub' ms mt = match (ms, mt) with
      (* the next three cases are questionable;
         they are needed to allow for weakening, i.e. using a function
         that makes sense in a stronger environment *)
      | (MShift k, MShift k') ->  () (* if k = k' then () 
        else raise (Unify "Contextual substitutions not of the same length")   *)
      | (MDot ( _ , ms), MShift k) -> 
          unifyMSub' ms (MShift (k-1))
      | (MShift k, MDot ( _ , ms)) -> 
          unifyMSub' ms (MShift (k-1))
      | (MDot (MObj (phat, tM), ms'), MDot (MObj(_phat', tM'), mt')) -> 
          (unify Empty (Context.hatToDCtx phat) (tM, id) (tM', id) ; 
           unifyMSub' ms' mt')
      | (MDot (PObj (phat, h), ms'), MDot (PObj(_phat', h'), mt')) -> 
          (dprint (fun () -> "[unifyMSub] PObj "); 
          (unifyHead Unification Empty (Context.hatToDCtx phat) h h'; 
           unifyMSub' ms' mt'))
      | (MDot (CObj (cPsi), ms), MDot (CObj(cPhi), mt)) -> 
          (dprint (fun () -> "[unifyMSub] CObj "); 
           unifyDCtx1 Unification Empty  cPsi cPhi;
           dprint (fun () -> "[unifyMSub] cPsi = " ^ P.dctxToString Empty cPsi);
           dprint (fun () -> "[unifyMSub] cPhi = " ^ P.dctxToString Empty cPhi);
           unifyMSub' ms mt)

    let rec unifyMSub ms mt = unifyMSub' (Whnf.cnormMSub ms) (Whnf.cnormMSub mt)



    let rec unifyCSub cs ct = match (cs, ct) with
      | (CShift _k, CShift _k') -> ()
      | (CDot ( _ , cs), CShift k) -> 
          unifyCSub cs (CShift (k-1))
      | (CShift k, CDot ( _ , cs)) -> 
          unifyCSub cs (CShift (k-1))

      | (CDot (cPsi, cs), CDot (cPhi, ct)) -> 
          (unifyDCtx1 Unification Empty (Whnf.cnormDCtx (cPsi, Whnf.m_id)) 
                                        (Whnf.cnormDCtx (cPhi, Whnf.m_id)) ; 
           unifyCSub cs ct )
 



let rec unify_phat psihat phihat = 
  match phihat with
    | (Some (CInst (_, ({contents = None} as cref), _, _, _ )), d) -> 
        begin match psihat with 
          | (Some (CInst (_, ({contents = None} as cref'), _, _, _) as c_var) , d') -> 
	      if cref == cref' then 
		(if d = d' then () else raise (Unify "Hat context mismatch - 1"))  
	      else 
		cref := Some (CtxVar (c_var))
          | ((Some (c_var)) , d') -> 
              if d = d' then 
                cref := Some (CtxVar (c_var)) 
              else                 
                (* (Some (cref), d) == (Some cpsi, d')   d' = d0+d  *)
                (if d'< d then raise (Unify "Hat Context's do not unify")
                 else 
                   let cPsi = Context.hatToDCtx (Some (c_var), d'-d) in 
                     cref := Some (cPsi))

          | (None , d') -> 
              if d = d' then 
                cref := Some (Null)
              else 
                (* (Some (cref), d) == (None, d')   d' = d0+d  *)
                (if d'< d then raise (Unify "Hat Context's do not unify")
                 else 
                   let cPsi = Context.hatToDCtx (None, d'-d) in 
                     cref := Some (cPsi))
                
        end 

    | _ ->  (if psihat = phihat then () else raise (Unify "Hat context mismatch - 2"))

   (* **************************************************************** *)

    let unifyTypRec cD0 cPsi sArec sBrec =
        unifyTypRec' Unification cD0 cPsi sArec sBrec 

    let unifyTyp cD0 cPsi sA sB = 
      unifyTyp' Unification cD0 cPsi sA sB


    let unifyDCtx cD0 cPsi1 cPsi2 =
      unifyDCtx1 Unification cD0 (Whnf.cnormDCtx (cPsi1, Whnf.m_id)) 
                                 (Whnf.cnormDCtx (cPsi2, Whnf.m_id))

    let matchTerm cD0 cPsi sM sN = 
      unify' Matching cD0 cPsi sM sN

    let matchTypRec cD0 cPsi sArec sBrec =
        unifyTypRec' Matching cD0 cPsi sArec sBrec 

    let matchTyp cD0 cPsi sA sB = 
      unifyTyp' Matching cD0 cPsi sA sB
      
end


module EmptyTrail = Make (EmptyTrail)
module StdTrail   = Make (StdTrail)
