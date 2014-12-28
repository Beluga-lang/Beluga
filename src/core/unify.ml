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
module Loc = Camlp4.PreCast.Loc

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

  val instantiateMVar : iterm option ref * normal * cnstr list -> unit
  val instantiateCtxVar : iterm option ref * dctx -> unit

  val resetDelayedCnstrs : unit -> unit
  val resetGlobalCnstrs : unit -> unit
  val globalCnstrs : cnstr list ref
  val unresolvedGlobalCnstrs : unit -> bool

  val nextCnstr         : unit -> cnstr option
  val addConstraint     : cnstr list ref * cnstr -> unit
  val forceGlobalCnstr  : cnstr list -> unit
  val solveConstraint   : cnstr -> unit

  val isVar             : head -> bool
  val isPatSub          : sub  -> bool
  val isProjPatSub          : sub  -> bool
  val isPatMSub         : msub  -> bool

  (* unification *)

  val intersection : psi_hat -> sub -> sub -> dctx -> (sub * dctx)

  exception Failure of string
  exception GlobalCnstrFailure of Loc.t * string
  exception NotInvertible

  (* All unify* functions return () on success and raise Failure on failure *)
  val unify        : mctx -> dctx  -> nclo  -> nclo -> unit
  val unifyH       : mctx -> psi_hat -> head -> head -> unit
  val unifyTyp     : mctx -> dctx  -> tclo  -> tclo -> unit
  val unifyTypRec  : mctx -> dctx  -> (typ_rec * sub) -> (typ_rec * sub) -> unit
  val unifyDCtx    : mctx -> dctx -> dctx -> unit
  val unify_phat   : psi_hat -> psi_hat -> unit

  val unifyCompTyp : mctx -> (Comp.typ * LF.msub) -> (Comp.typ * msub) -> unit
  val unifyMSub    : msub  -> msub -> unit
  val unifyMetaTyp : mctx -> (Comp.meta_typ * msub) -> (Comp.meta_typ * msub) -> unit
  val unifyMetaObj : mctx -> (Comp.meta_obj * msub) -> (Comp.meta_obj * msub) ->
                    (Comp.meta_typ * msub) -> unit

  val matchTerm    : mctx -> dctx -> nclo -> nclo -> unit
  val matchTyp     : mctx -> dctx -> tclo -> tclo -> unit
  val matchTypRec  : mctx -> dctx -> (typ_rec * sub) -> (typ_rec * sub) -> unit


  type cvarRef =
    | MMVarRef of iterm option ref


  val pruneTyp : mctx -> dctx -> psi_hat -> tclo  -> (msub * sub)  -> cvarRef -> typ

end

(* Unification *)
(* Author: Brigitte Pientka *)
(* Trailing is taken from Twelf 1.5 *)

module Make (T : TRAIL) : UNIFY = struct

  open Substitution.LF
  module P = Pretty.Int.DefaultPrinter

  exception Failure of string
  exception GlobalCnstrFailure of Loc.t * string
  exception NotInvertible

  exception Error of string

  type matchFlag = Matching | Unification

  (* Matching not fully implemented yet -bp *)

  type cvarRef =
    | MMVarRef of iterm option ref


  let eq_cvarRef cv cv' = match (cv, cv') with
    | (MMVarRef r, MMVarRef r') -> r == r'




let rec blockdeclInDctx cPsi = match cPsi with
  | Null -> false
  | CtxVar psi -> false
  | DDec (cPsi',TypDecl(x, tA)) ->
     begin match Whnf.whnfTyp (tA, id) with
       | (Sigma _ , _ ) -> true
       | _  ->    blockdeclInDctx cPsi'
     end

(* expandPatSub is unused as of commit c899234fe2caf15a42699db013ce9070de54c9c8 -osavary*)
  let rec _expandPatSub t cPsi = match (t, cPsi) with
    | Shift ( k) , Null -> t
    | Shift ( k) , CtxVar _ -> t
    | Shift ( k) , DDec (cPsi,TypDecl(x, tA)) ->
      Dot(Head (BVar (k+1)), _expandPatSub (Shift ( k+1)) cPsi)
    | Dot (h, s) , DDec (cPsi, tdec) ->
      Dot (h, _expandPatSub s cPsi)

  (* genMMVarstr cD cPsi (tP, s) = Y[ss_proj]

     if  cD ; cPsi |- [s]tP    and  let X be a mmvar of this type
     then Y[ss_proj] is a new mmvar of type
          cD ; cPhi' |- tQ'  where

          cPsi  |- ss_proj : cPhi'
  *)
  let genMMVarstr loc cD cPsi (Atom (_, a, _tS) as tP, s) =
    let (cPhi, conv_list) = ConvSigma.flattenDCtx cD cPsi in
    let s_proj = ConvSigma.gen_conv_sub conv_list in
    let tQ    = ConvSigma.strans_typ cD (tP, s) conv_list in
      (*  cPsi |- s_proj : cPhi
          cPhi |- tQ   where  cPsi |- tP   and [s_proj]^-1([s]tP) = tQ  *)

    let (ss', cPhi') = Subord.thin' cD a cPhi in
      (* cPhi |- ss' : cPhi' *)
    let ssi' = Substitution.LF.invert ss' in
      (* cPhi' |- ssi : cPhi *)
      (* cPhi' |- [ssi]tQ    *)
    let u = Whnf.newMMVar None (cD, cPhi', TClo(tQ,ssi'))  in
      (* cPhi |- ss'    : cPhi'
         cPsi |- s_proj : cPhi
         cPsi |- comp  ss' s_proj   : cPhi' *)
    let ss_proj = Substitution.LF.comp ss' s_proj in
      Root (loc, MMVar ((u, Whnf.m_id), ss_proj), Nil)



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
      | EmptySub -> true
      | Undefs -> true
    | Shift (_k)              -> true
    | Dot (Head(BVar n), s) ->
        let rec checkBVar s' = match s' with
          | Shift ( k)           -> n <= k
          | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
          | Dot (Head (Proj(BVar n', _)), s) -> n <> n' && checkBVar s
          | Dot (Undef, s)          -> checkBVar s
	  | EmptySub -> true
	  | Undefs -> true
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
    | EmptySub -> true
    | Undefs -> true 
    | Shift (_k)              -> true
    | Dot (Head(BVar n), s) ->
        let rec checkBVar s' = match s' with
          | Shift ( k)           -> n <= k
          | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
          | Dot (Head (Proj(BVar n', _)), s) -> n <> n' && checkBVar s
          | Dot (Undef, s)          -> checkBVar s
	  | EmptySub -> true
	  | Undefs -> true
          | _                       -> false
        in
          checkBVar s && isProjPatSub s

    | Dot (Head(Proj(BVar n, index)), s) ->
        let rec checkBVar s' = match s' with
          | Shift ( k)           -> n <= k
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



let isVar h = match h with
  | BVar _ -> true
  | Proj (BVar _ , _ ) -> true
  | PVar ( _ , sigma) -> isProjPatSub sigma
  | FPVar ( _ , sigma) -> isProjPatSub sigma
  | MPVar ((_ , theta), sigma) ->
    isProjPatSub sigma && isPatMSub theta
  | Proj(PVar ( _ , sigma), _ ) -> isProjPatSub sigma
  | Proj(FPVar ( _ , sigma), _ ) -> isProjPatSub sigma
  | Proj(MPVar ((_ , theta), sigma), _ ) ->
    isProjPatSub sigma && isPatMSub theta
  | _ -> false


  (*-------------------------------------------------------------------------- *)
  (* Trailing and Backtracking infrastructure *)

  type action =
    | InstI      of iterm option ref
    | Add        of cnstr list ref
    | Solve      of cnstr * constrnt   (* FIXME: names *)

  type unifTrail = action T.t

  let globalTrail : action T.t = T.trail()

  let undo action = (dprint (fun () -> "Call to UNDO\n") ; match action with
    | InstI   refH            -> refH   := None
    | Add cnstrs              -> cnstrs := List.tl !cnstrs
    | Solve (cnstr, constrnt) -> cnstr  := constrnt)

  let reset  () = T.reset globalTrail

  let mark   () = T.mark globalTrail

  let unwind () = T.unwind globalTrail undo


  let solveConstraint ({contents=constrnt} as cnstr) =
    cnstr := Queued;
    T.log globalTrail (Solve (cnstr, constrnt))

  (* trail a function;
     if the function raises an exception,
       backtrack and propagate the exception  *)
  let trail f =
    let _ = mark  () in
      try f () with
        | NotInvertible ->
            (dprint (fun () -> "Unwind trail - exception     notInvertible") ;
             unwind (); raise NotInvertible)
        | Failure msg -> (dprint (fun () -> "Unwind trail - exception Failure " ^
     msg);unwind (); raise (Failure msg))
        | Error msg -> (dprint (fun () -> "Unwind trail - exception Error " ^
     msg);unwind (); raise (Error msg))
        | GlobalCnstrFailure (loc , msg) -> (dprint (fun () -> "Unwind trail - exception GlobalCnstrFailure " ^
     msg);unwind (); raise (GlobalCnstrFailure (loc, msg)))
        | e -> (dprint (fun () -> "?? " ) ; unwind (); raise e)

  (* ---------------------------------------------------------------------- *)

  let delayedCnstrs : cnstr list ref = ref []
  let globalCnstrs : cnstr list ref = ref []

  let resetDelayedCnstrs () = delayedCnstrs := []
  let resetGlobalCnstrs () = globalCnstrs := []

  let addConstraint (cnstrs, cnstr) =
  (begin match cnstr with
    | {contents= (Eqn (cD0, cPsi, INorm tM, INorm tN))} ->
        dprint (fun () -> "Add constraint: " ^ P.normalToString cD0 cPsi (tM, id)  ^
                   " = " ^ P.normalToString cD0 cPsi (tN, id))
    | _ -> () end ;
   cnstrs := cnstr :: !cnstrs;
   globalCnstrs := cnstr :: !globalCnstrs;
   T.log globalTrail (Add cnstrs))


  let nextCnstr () = match !delayedCnstrs with
    | []              -> None
    | cnstr :: cnstrL ->
        delayedCnstrs := cnstrL;
        Some cnstr

  let instantiateMMVar' (u, t, cnstrL) =
    u := Some t;
    T.log globalTrail (InstI u);
    delayedCnstrs := cnstrL @ !delayedCnstrs;
    globalCnstrs := cnstrL @ !globalCnstrs

  let instantiateCtxVar (ctx_ref, cPsi) =
    ctx_ref := Some (ICtx cPsi);
    T.log globalTrail (InstI ctx_ref)

  let instantiateMVar (u, tM, cnstrL) =
    instantiateMMVar' (u, INorm (Whnf.norm (tM, id)), cnstrL)

  let instantiateMMVar (u, tM, cnstrL) =
    instantiateMMVar' (u, INorm tM, cnstrL)

  let instantiateMSVar (s, sigma, cnstrL) =
    instantiateMMVar' (s, ISub sigma, cnstrL)

  let instantiateMPVar (p, head, cnstrL) =
    instantiateMMVar' (p, IHead head, cnstrL)

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

  (* should perform a kind of eta expansion on the domain of a substitution.
     This implementation is totally buggy and wrong, but works for the test cases so far... *)
  let simplifySub cD0 cPsi sigma =
    let _ = dprint (fun () -> "\n[simplifySub] cPsi = " ^ P.dctxToString cD0 cPsi )  in
    let _ = dprint (fun () -> "\n[simplifySub] sigma = " ^ P.subToString cD0 cPsi sigma)  in
match sigma with
    | SVar (s , ( _ ), _s2 ) ->
      let (_, cPsi1, cPhi) = Whnf.mctxSDec cD0 s in
      begin match cPsi1 with
        | Null -> EmptySub
        | _     -> sigma
      end
    | MSVar (_, (((_,  r , _, ClTyp (STyp Null, cPhi), cnstrs, _ ) , _), _)) ->
      instantiateMSVar (r, EmptySub, !cnstrs);
      EmptySub      
    | FSVar (_, (s_name , _s2) ) ->
      let (_, Decl (_, ClTyp (STyp cPsi1,  _cPhi), _)) = Store.FCVar.get s_name in
      begin match cPsi1  with
        | Null -> EmptySub
        | _     -> sigma
      end
    | _ -> sigma

  let rec pruneMCtx' cD (t, cD1) ms = match (t, cD1) with
    | (MShift _k, Empty) -> (Whnf.m_id, Empty)

   | (MShift k, Dec (_, _)) ->
       pruneMCtx' cD (MDot (MV (k + 1), MShift (k + 1)), cD1) ms

   | (MDot (MV k, mt), Dec (cD1, Decl (n, ctyp,dep))) ->
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
               (Whnf.mvar_dot1 mt', Dec(cD2, (Decl (n, Whnf.cnormMTyp (ctyp, mtt'), dep))))
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

    | ((Dot _ as s1), Shift ( n2), cPsi) ->
        intersection phat s1 (Dot (Head (BVar (n2 + 1)), Shift (n2 + 1))) cPsi

    | (Shift (n1), (Dot _ as s2), cPsi) ->
        intersection phat (Dot (Head (BVar (n1 + 1)), Shift ( n1 + 1))) s2 cPsi

    | (Shift ( _k), Shift ( _k'), cPsi) -> (id, cPsi)
        (* both substitutions are the same number of shifts by invariant *)

    | (EmptySub, EmptySub , cPsi) -> (id , cPsi)
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
    | (MDot (MV k1, mt1), MDot (MV k2, mt2), Dec (cD', Decl (x, ctyp,dep))) ->
        let (mt', cD'') = m_intersection  mt1 mt2 cD' in
          (* cD' |- mt' : cD'' where cD'' =< cD' *)
          if k1 = k2 then
            let mtt' = Whnf.m_invert (Whnf.cnormMSub mt') in
              (* cD'' |- mtt' <= cD' *)
              (* NOTE: Can't create m-closures CtxMClo(cPsi, mtt') and TMClo(tA'', mtt') *)
              (Whnf.mvar_dot1 mt', Dec (cD'', Decl(x, Whnf.cnormMTyp (ctyp, mtt'), dep)))

          else  (* k1 =/= k2 *)
            (Whnf.mcomp mt' (MShift 1), cD'')

    | (MDot (MUndef, mt1), MDot (MV _k2, mt2), Dec (cD', _)) ->
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
    let _u : (msub * sub) = ss in
    invNorm' cD0 (phat, Whnf.whnf sM, ss, rOccur)

  and invNorm' cD0 ((cvar, offset) as phat, sM, ((ms, ssubst) as ss), rOccur) = match sM with
    | (Lam (loc, x, tM), s) ->
        Lam (loc, x, invNorm cD0 ((cvar, offset + 1), (tM, dot1 s), (ms, dot1 ssubst), rOccur))

    | (Root (loc, MVar (Inst u, t), tS), s) ->
      invNorm' cD0 (phat, (Root(loc, MMVar((u, MShift 0), t), tS), s), ss, rOccur)

   | (Root (loc, MMVar (((_n, r, cD, ClTyp (_,cPsi1), _cnstrs, _) as u, mt),s'), _tS (* Nil *)), s) ->
        (* by invariant tM is in whnf and meta-variables are lowered;
           hence tS = Nil and s = id *)
        if eq_cvarRef (MMVarRef r) rOccur then
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
                  Root(loc, MMVar((u, Whnf.mcomp mt ms), comp s0 ssubst), Nil)
                else
                  raise NotInvertible
            else (* s0 not patsub *)
              Root(loc, MMVar((u, invMSub cD0 (mt, cD) ms rOccur),
                                  invSub cD0 phat (s0, cPsi1) ss rOccur), Nil)

    | (Root (loc, MVar (Offset u, t), _tS (* Nil *)), s (* id *)) ->
        let t' = comp t s (* t' = t, since s = Id *) in
        let (_, _tA, cPsi1) = Whnf.mctxMDec cD0 u in
          begin match applyMSub u ms with
            | MV v ->
                Root(loc, MVar(Offset v, invSub cD0 phat (t', cPsi1) ss rOccur), Nil)
            | MUndef -> raise NotInvertible
          end

    | (Root (loc, FMVar (u, t), _tS (* Nil *)), s (* id *)) ->
        let (cD_d, Decl(_, ClTyp (_, cPsi1), _)) = Store.FCVar.get u in
	let d = Context.length cD0 - Context.length cD_d in
	let cPsi1 = if d = 0 then cPsi1 else
	   Whnf.cnormDCtx (cPsi1, MShift d) in
        let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
          Root (loc, FMVar (u, s'), Nil)

    | (Root (loc, FPVar (p, t), _tS (* Nil *)), s (* id *)) ->
        let (cD_d, Decl (_, ClTyp (_, cPsi1), _)) = Store.FCVar.get p in
	let d = Context.length cD0 - Context.length cD_d in
	let cPsi1 = if d = 0 then cPsi1 else
	  Whnf.cnormDCtx (cPsi1, MShift d) in
        let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
          Root (loc, FPVar (p, s'), Nil)

    | (Root (loc, PVar (p, t), _tS (* Nil *)), s (* id *)) ->
        let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in
        let t' = comp t s (* t' = t, since s = Id *) in
          begin match applyMSub p ms with
            | MV q ->
                Root(loc, PVar(q, invSub cD0 phat (t', cPsi1) ss rOccur), Nil)
            | MUndef -> raise NotInvertible
          end


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

    | MVar (Inst (_n, r, _cD, ClTyp (_,cPsi1), _cnstrs, _) as u, t) ->
        if eq_cvarRef (MMVarRef r) rOccur then
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


    | PVar (p, t) ->
        let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in
          begin match applyMSub p ms with
            | MV q ->
                PVar(q, invSub cD0 phat (t, cPsi1) ss rOccur)
            | MUndef -> raise NotInvertible
          end

    | Proj(PVar (p, t), i) ->
        let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in
          begin match applyMSub p ms with
            | MV q ->
                Proj(PVar(q, invSub cD0 phat (t, cPsi1) ss rOccur), i)
            | MUndef -> raise NotInvertible
          end

  (* invSub cD0 (phat, s, ss, rOccur) = s'

     if phat = hat(Psi)  and
        D ; Psi  |- s <= Psi'
        D ; Psi''|- ss <= Psi
     then s' = [ss]s   if it exists, and
        D ; cPsi'' |- [ss]s <= cPsi'
   *)
  and invSub cD0 phat (s, cPsi1) ((ms , ssubst) as ss) rOccur = match (s, cPsi1) with
    | (EmptySub, Null) -> EmptySub
    | (Undefs, Null) -> EmptySub
    | (Shift n, DDec(_cPsi', _dec)) ->
        invSub cD0 phat (Dot (Head (BVar (n + 1)), Shift (n + 1)), cPsi1) ss rOccur

    | (Shift n, Null) -> EmptySub

    | (Shift n, CtxVar _psi) ->
      (* can we pull this function out into something more generally useful?
	 it finds the context variable part of a (inverse) substitution *)
      let rec shiftInvSub n ss = match ss with
	| Undefs -> raise NotInvertible
	| Shift k -> Shift (n+k)
        | Dot (ft, ss') -> shiftInvSub (n-1) ss'
      in 
      shiftInvSub n ssubst

    | (SVar (s, 0, sigma), CtxVar psi) ->
        (* other cases ? -bp *)
        let (s,cPhi, cPsi') = (match applyMSub s ms with
                                           | MV v -> let (_, cPhi, cPsi') =
                                               Whnf.mctxSDec cD0  v in (v, cPhi, cPsi')
                                           | MUndef -> raise NotInvertible
                                        ) in

        let _ = dprint (fun () -> "[invSub]" ^ P.dctxToString cD0 (Context.hatToDCtx phat) ^ " |- "
        ^ P.subToString cD0 (Context.hatToDCtx phat) sigma ^ " : " ^
        P.dctxToString cD0 cPsi') in

        SVar(s, 0, invSub cD0 phat (sigma, cPsi') ss rOccur)
    | (MSVar (0, (((_,{contents=None},cD, ClTyp (STyp cPsi',cPhi), _, _) as s0, mt),sigma)), CtxVar psi) ->
      MSVar(0, ((s0, invMSub cD0 (mt, cD) ms rOccur), invSub cD0 phat (sigma, cPsi') ss rOccur))

    | (Dot (Head (BVar n), s'), DDec(cPsi', _dec)) ->
        begin match bvarSub n ssubst with
          | Undef -> raise NotInvertible
          | ft   -> Dot (ft , invSub cD0 phat (s', cPsi') ss rOccur)
        end

    | (Dot (Head (Proj (BVar n, k)), s'), DDec(cPsi', _dec)) ->
        begin match bvarSub n ssubst with
          | Undef -> raise NotInvertible
          | Head(BVar m)  ->
              Dot (Head (Proj (BVar m, k)) , invSub cD0 phat (s', cPsi') ss rOccur)
          | _ -> raise NotInvertible
        end


    | (Dot (Obj tM, s'), DDec(cPsi', _dec))        ->
        (* below may raise NotInvertible *)
        let tM' = invNorm cD0 (phat, (tM, id), ss, rOccur) in
          Dot (Obj tM', invSub cD0 phat (s', cPsi') ss rOccur)

    | (SVar (s, (n), t), cPsi1) -> (* This is probably
      buggy. Need to deal with the n *)
          begin match applyMSub s ms with
            | MV v ->
                let (_, cPhi, cPsi1) = Whnf.mctxSDec cD0  v  in
                  (* applyMSub to ctx_offset ? *)
                SVar(v, ( n), invSub cD0 phat (t, cPsi1) ss rOccur)
            | MUndef -> raise NotInvertible
          end
    | (FSVar (n, (s_name, t)), cPsi1) ->
        (dprint (fun () -> "invSub FSVar");
        let (_, Decl (_, ClTyp (STyp _cPhi,  cPsi'), _)) = Store.FCVar.get s_name in
        FSVar (n , (s_name, invSub cD0 phat (t, cPsi') ss rOccur)))
(*        if ssubst = id then s else
        (dprint (fun () -> "invSub FSVar -- undefined") ; raise (Error "invSub for
        free substitution variables -- not defined"))*)

    | (s, _ ) -> (dprint (fun () -> "invSub -- undefined: s = " ^
                      P.subToString cD0 (Context.hatToDCtx phat) s) ;
                  dprint (fun () -> "domain cPsi1 = " ^ P.dctxToString cD0 cPsi1);
                  raise (Error "invSub --   undefined"))




  (* invMSub cD0 (mt, cD') ms rOccur = mt'

     if cD  |- mt <= cD'
        cD''|- ms <= cD
     then mt' = [ms]mt   if it exists, and
        D'' |- [ms]mt <= cD'
   *)
  and invMSub cD0 (mt, cD1) ms  rOccur = match (mt, cD1) with
    | (MShift  n, _) -> checkDefined (Whnf.mcomp (MShift  n) ms)
    | (MDot (ClObj (phat, SObj sigma), mt'), Dec(cD', Decl (_ , ClTyp (STyp cPhi, _cPsi), _)))   ->
      let sigma' = invSub cD0 phat (sigma, cPhi) (ms, id) rOccur in
      MDot (ClObj (phat, SObj sigma'), invMSub cD0 (mt', cD') ms rOccur)
    | (MDot (mobj, mt'), Dec(cD',_)) ->
      MDot(invMObj cD0 mobj ms rOccur, invMSub cD0 (mt', cD') ms rOccur)

  and invMObj cD0 mobj ms rOccur = match mobj with
    | MV n ->
      begin match applyMSub n ms with
	| MUndef -> raise NotInvertible
	| ft -> ft
      end 
    | ClObj (phat, MObj tM) -> ClObj (phat, MObj (invNorm cD0 (phat, (tM, id), (ms, id), rOccur)))
    | CObj cPsi -> raise (Error.Violation "Not implemented")
    | ClObj (phat, PObj h) -> ClObj (phat, PObj (invHead cD0 (phat, h, (ms, id), rOccur)))
   (* | SObj (phat, sigma) -> SObj (phat, invSub cD0 phat (sigma, *)

  and checkDefined = function
    | MShift n -> MShift n
    | MDot (MUndef, _) -> raise NotInvertible
    | MDot (m,mt) -> MDot(m,checkDefined mt)

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

       - raises Failure if rOccur occurs in tM (occurs check)
         or [ss]([|rho|][s]tM) does not exist,

       - raises NotInvertible if there exist meta-variables u[t] where t is not a
         pattern substitution and [ss](t) does not exist
  *)

  and prune  cD0 cPsi' phat sM ss rOccur =
    let _qq : (msub * sub) = ss in
      prune' cD0 cPsi' phat (Whnf.whnf sM) ss rOccur

  and prune' cD0 cPsi' ((cvar, offset) as phat) sM ss rOccur = match sM with
    | (LFHole _ as n, s)-> n
    | (Lam (loc, x, tM),   s) ->
        let _ = dprint (fun () -> "[prune] Lam " ) in
        let _ = dprint (fun () -> "[prune[ sM = " ^
                          P.normalToString cD0  (Context.hatToDCtx phat) sM) in
        let _ = dprint (fun () -> "[prune[ sM' = " ^
                          P.normalToString cD0
                          (Context.hatToDCtx (cvar,offset+1)) (tM, dot1 s)) in
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
	let do_head = function
            | MMVar (((_n, r, cD1, ClTyp (MTyp tP,cPsi1), cnstrs, mdep) as _u, mt), t) ->  (* s = id *)
              (* cD |- t <= cD1
                 cD ; cPsi |- t <= [|mt|]Psi1
                 cD ; cPsi |- [t]([|mt|]tP)
              *)
                let tM = Root(loc, head, tS) in
                let (_ms, sigma) = ss in
                let _ = dprint (fun () -> "[prune] MMVar " ^ P.normalToString cD0 (Context.hatToDCtx phat) sM ) in
                let _ = dprint (fun () -> "[prune] with respect to ss = " ^ P.subToString cD0 cPsi' sigma) in
                let t  = Whnf.normSub t in
                  (* by invariant: MVars are lowered since tM is in whnf *)
                  if eq_cvarRef (MMVarRef r) rOccur then
                    raise (Failure "Variable occurrence")
                  else
                    if isId ssubst && isMId ms  then returnNeutral head
                    else
                      if isPatSub t && isPatMSub mt then
                        let _ = dprint (fun () -> "[prune] MMVar "
                                          ^ P.normalToString cD0 (Context.hatToDCtx phat) sM
                                          ^ "\n  with respect to ssubst = " ^ P.subToString cD0 cPsi' ssubst) in

                      let (id_sub, cPsi2) = pruneCtx phat (comp t s, cPsi1) ss in
                        let _ = dprint (fun () -> "[prune] pruneCtx done - MMVar case ") in
                        let _ = dprint (fun () -> "cPsi1 = " ^ P.dctxToString cD1 cPsi1) in
                        let _ = dprint (fun () -> "cPsi2 = " ^ P.dctxToString cD1 cPsi2) in
                        (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= [|mt|]cPsi1
                           cD ; cPsi |-  t o s <= [|mt|]cPsi1 and
                           cD ; [|mt|]cPsi1 |- id_sub <= cPsi2 and
                           cD ; cPsi |- t o s o idsub <= cPsi2 *)
                      let (id_msub, cD2) = pruneMCtx cD0 (mt, cD1) ms in
                        let _ = dprint (fun () -> "[prune] pruneMCtx done - MMVar case ") in
                        let _ = dprint (fun () -> P.mctxToString cD1 ^ " |- id_msub : " ^ P.mctxToString cD2) in
                        let _ = dprint (fun () -> "id_msub " ^ P.msubToString  cD1 id_msub) in
                        (* cD  |- mt <= cD1
                         * cD1 |- id_msub <=  cD2
                         * cD  |- [|mt|]id_msub <= cD2
                         *
                         * Note: cD |- cPsi2 ctx  and cD1 ; cPsi1 |- tP <= type
                         *       cD ; [|mt|]cPsi1 |- [|mt|]tP <= type
                         *)
                      let i_id_sub  = invert id_sub in
                      let _ = dprint (fun () -> "[prune] inverting id_sub done " ) in
                      let i_msub = Whnf.m_invert (Whnf.mcomp id_msub mt) in
                        let _ = dprint (fun () -> "i_msub " ^ P.msubToString  cD2 i_msub) in
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
                        let _ = dprint (fun () -> "[prune] invert stuff done -MMVar case ") in
                       (* let cPsi2' = Whnf.cnormDCtx (cPsi2, i_msub) in *)
                        let cPsi2' = Whnf.cnormDCtx (cPsi2, i_id_msub) in
                        let _ = dprint (fun () -> "[prune] cD2 = " ^ P.mctxToString cD2) in
                        let _ = dprint (fun () -> "[prune] cnormDCtx cPsi2' =  "
                                          ^ P.dctxToString cD2 cPsi2') in
                        let i_sub  = Whnf.cnormSub (i_id_sub, i_msub) in
                        let _ = dprint (fun () -> "[prune] cnormSub i_id_sub - MMVar case ") in
                        let tP'    = Whnf.cnormTyp (tP, i_id_msub) in
                        let _ = dprint (fun () -> "[prune] cnormTyp tP - MMVar case ") in

                      let v = Whnf.newMMVar None (cD2, cPsi2', TClo(tP', i_sub))  in
                      let tN = Root (loc, MMVar ((v, id_msub), id_sub), Nil) in
                      let _ = dprint (fun () -> "[prune] new mmvar created : " ^ P.normalToString cD1 cPsi1 (tN, Substitution.LF.id)) in
                      let _ = dprint (fun () -> "[prune] new mmvar has type : "
                                        ^ " [ " ^ P.dctxToString cD2 cPsi2' ^ " . "
                                        ^ P.typToString cD2 cPsi2' (tP', i_sub)) in
                      let _ = dprint (fun () -> "[prune] tM (before instantiation) = " ^
                                        P.normalToString cD0 cPsi' sM) in
                      let _ = instantiateMMVar (r, Root (loc, MMVar ((v, id_msub), id_sub), Nil), !cnstrs) in
                      let _ = dprint (fun () -> "[prune] tM (after instantiation) = " ^
                                        P.normalToString cD0 cPsi' sM) in
                      let s' = comp s ssubst in
		      let _ = dprint (fun () -> "composition done") in
		      let tM' = Whnf.norm (tM, s') in
		      let _ = dprint (fun () -> "norm done") in
                      let tM'= Whnf.cnorm (tM', ms) in
                                 (* Clo(tM, comp s ssubst) *)
                      let _ = dprint (fun () -> "[prune] tM' = " ^
                                        P.normalToString cD0 cPsi' (tM', Substitution.LF.id)) in
                        tM'
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
                      let _ = dprint (fun () -> "[prune] MMVar t' = " ^
                                        P.subToString cD2 cPsi' t') in
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
                      let v = Whnf.newMMVar None (cD2, cPsi2', TClo(tP', invert idsub_i))  in
                      let _  = instantiateMMVar (r, Root (loc, MMVar ((v, id_msub), idsub), Nil), !cnstrs) in
                      let tM'= Whnf.cnorm (Whnf.norm (tM, comp s ssubst), ms) in
                        tM'
                      else
                        raise NotInvertible
                          (* may raise NotInvertible *)



            | MVar (Inst (_n, r, _cD, ClTyp (MTyp tP,cPsi1), cnstrs, mdep) (*as u*), t) ->  (* s = id *)
                let tM = Root(loc, head, tS) in
                let t  = simplifySub cD0 cPsi' (Whnf.normSub (comp t s)) in
                  (* by invariant: MVars are lowered since tM is in whnf *)
                  if eq_cvarRef (MMVarRef r) rOccur then
                    raise (Failure "Variable occurrence")
                  else
                    if isPatSub t then
                      let (idsub, cPsi2) = pruneCtx phat (t, cPsi1) ss in
(*                      let (_ , ssubst) = ss in
                      let _ = dprint (fun () -> "[prune] ss = " ^
                                        P.subToString cD0 cPsi' ssubst) in
                      let _ = dprint (fun () -> "[prune] cPsi1 = " ^
                                        P.dctxToString cD0 cPsi1) in
                      let _ = dprint (fun () -> "[prune] idsub = " ^
                                        P.subToString cD0 cPsi1 idsub) in
                      let _ = dprint (fun () -> "[prune] cPsi2 = " ^
                                        P.dctxToString cD0 cPsi2) in
                      let _ = dprint (fun () -> "[prune] t = " ^
                                        P.subToString cD0 cPsi' t) in *)
                        (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                           cD ; cPsi |-  t o s <= cPsi1 and
                           cD ; cPsi1 |- idsub <= cPsi2 and
                           cD ; cPsi |- t o s o idsub <= cPsi2 *)
                      let idsub_i = invert idsub in
                      let v = Whnf.newMVar None (cPsi2, TClo(tP, idsub_i))  in

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
                      let (_ , ssubst) = ss in
                      let _ = dprint (fun () -> "[prune] MVar - calling pruneSub ") in
                      let _ = dprint (fun () -> "[prune] t = " ^
                                        P.subToString cD0 (Context.hatToDCtx phat) t) in

                      let _ = dprint (fun () -> "[prune] ss = " ^
                                        P.subToString cD0 cPsi' ssubst) in
                       let (idsub, cPsi2) = pruneSub  cD0 cPsi' phat (t, cPsi1) ss rOccur in
		       let _ = dprint (fun () -> "[prune] idsub = " ^ P.subToString cD0 cPsi1 idsub) in
                      (* Psi1 |- idsub   : Psi2
                         Psi2 |- idsub_i : Psi1
                       *)
                        (* could maybe just prune tP and cPsi1 ?
                           29 Jan, 2011  -bp  *)
                         (* *)
                      let idsub_i = invert idsub in
                      let v = Whnf.newMVar None (cPsi2, TClo(tP, idsub_i))  in
                      (* let _ = print_string ("prune non-pattern sub s  where u[s] \n") in *)
                      let _ = dprint (fun () -> "[prune] BEFORE Inst. r = " ^
                                     P.normalToString cD0 (Context.hatToDCtx phat) (tM,s) ) in
                      let _ = instantiateMVar (r, Root (loc, MVar (v, idsub),
                                        Nil), !cnstrs) in
                      let _ = dprint (fun () -> "[prune] cPsi2 = " ^
                                        P.dctxToString cD0 cPsi2) in
                      let _ = dprint (fun () -> "[prune] cPsi1 = " ^
                                        P.dctxToString cD0 cPsi1) in
                      let _ = dprint (fun () -> "[prune] cPsi = " ^
                                        P.dctxToString cD0 (Context.hatToDCtx phat)) in
                      let _ = dprint (fun () -> "[prune] Inst. r = " ^
                                     P.normalToString cD0 (Context.hatToDCtx phat) (tM,s) ) in
                      let _ = dprint (fun () -> "[prune] ssubst = " ^
                                        P.subToString cD0 cPsi' ssubst)
                      in
                      let _ = dprint (fun () -> "[prune] pruned tM = " ^
                                     P.normalToString cD0 cPsi' (tM,comp s ssubst) ) in
                        Clo(tM, comp s ssubst)
                          (* may raise NotInvertible *)


            | MVar (Offset u, t)   (* tS = Nil,   s = id *) ->
                ( dprint (fun () -> "Pruning bound meta-variable " ^             (R.render_cvar cD0 u)) ;
                begin match applyMSub u ms with
                  | MV v ->
                      begin try
                        let (_, _tA, cPsi1) = Whnf.mctxMDec cD0 v in
                        let _ = dprint (fun () -> "   cPsi1 (context of mvar)  " ^             (R.render_cvar cD0 v)
                                          ^ " ) = " ^ P.dctxToString cD0 cPsi1) in
                        let _ = dprint (fun () -> "   cPsi' " ^ P.dctxToString cD0 cPsi') in

                        let t' = simplifySub cD0 (Context.hatToDCtx phat) (comp t s) in
(*                         let s0 = invSub cD0 phat (comp t s, cPsi1) ss rOccur
                           in
                        let s' = simplifySub  cD0 cPsi' s0 in *)
                        let s' = invSub cD0 phat (t' , cPsi1) ss rOccur in
                        let (_, ssSubst) = ss in
                          dprint (fun () -> "##       s  = " ^ P.subToString cD0 cPsi' s);
                          dprint (fun () -> "##       t  = " ^ P.subToString cD0 cPsi' t);
                          dprint (fun () -> "##       ss = " ^ P.subToString cD0 cPsi' ssSubst);
(*                          dprint (fun () -> "##       s0' = " ^ P.subToString cD0 cPsi' s0);*)
                          dprint (fun () -> "##       s' = " ^ P.subToString   cD0 cPsi' s');
                          dprint (fun () -> "## comp t s = " ^ P.subToString cD0 cPsi' (comp t s));
                          returnNeutral (MVar (Offset v, s'))
                      with
                        | Error.Violation msg ->
                            (dprint (fun () -> "Pruning bound meta-variable FAILS; " ^ msg ^
                              "\n Looking for " ^ R.render_cvar cD0 u ^
                              "\n in context " ^ P.mctxToString cD0);
                            raise (Failure ("Pruning")))
                        | Error msg ->
                          (dprint (fun () -> "Pruning bound meta-variable FAILS; " ^ msg ^
                                          "\n Looking for " ^ R.render_cvar cD0 u ^
                                          "\n in context " ^ P.mctxToString cD0) ;
                           raise (Failure ("Pruning")))
                      end
                  | MUndef -> (dprint (fun () -> "pruning bound metavariable - MUndef failure ");
                               raise (Failure "[Prune] Bound MVar dependency"))
                  | _      -> (dprint (fun () -> "pruning bound meta-variable - FAIL");
                               raise (Failure "[Prune] MObj / PObj dependency"))
                end
                )
            | FMVar (u, t)   (* tS = Nil,   s = id *) ->
                let (cD_d, Decl (_, ClTyp (_, cPsi1), _)) = Store.FCVar.get u in
                let d = Context.length cD0 - Context.length cD_d in
	        let cPsi1 = if d = 0 then cPsi1 else
	          Whnf.cnormDCtx (cPsi1, MShift d) in
                let t' = simplifySub cD0 (Context.hatToDCtx phat) (comp t s) in
(*                let t' = comp t s in *)
                let s' = invSub cD0 phat (t', cPsi1) ss rOccur in
                  returnNeutral (FMVar (u, s'))

            | FPVar (p, t)   (* tS = Nil,   s = id *) ->
                let (cD_d, Decl (_, ClTyp (_, cPsi1),_)) = Store.FCVar.get p in
                let d = Context.length cD0 - Context.length cD_d in
	        let cPsi1 = if d = 0 then cPsi1 else
	          Whnf.cnormDCtx (cPsi1, MShift d) in
                let t' = simplifySub cD0 (Context.hatToDCtx phat) (comp t s) in
                let s' = invSub cD0 phat (t', cPsi1) ss rOccur in
                  returnNeutral (FPVar (p, s'))

            | PVar (p, t)   (* tS = Nil,   s = id *) ->
                begin match applyMSub p ms with
                  | MV q ->
                      let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in
                      let t' = simplifySub cD0 (Context.hatToDCtx phat) (comp t s) in
                      let s' = invSub cD0 phat (t', cPsi1) ss rOccur in
                        returnNeutral (PVar (q, s'))
                  | MUndef -> raise (Failure "[Prune] Bound PVar dependency")
                end

            | Proj (PVar (p, t), i)   (* tS = Nil,   s = id *) ->
                begin match applyMSub p ms with
                  | MV q ->
                      let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in
                      let t' = simplifySub cD0 (Context.hatToDCtx phat) (comp t s) in
                      let s' = invSub cD0 phat (t', cPsi1) ss rOccur in
                        returnNeutral (Proj (PVar (q, s'), i))
                  | MUndef -> raise (Failure "[Prune] Bound PVar dependency in projection")
                end

            | MPVar (((_n, r, cD1, ClTyp (PTyp tA,cPsi1), cnstrs, mDep) as q, mt), t) (* tS *)   (* s = id *) ->
                let t = Whnf.normSub t in
                let t = simplifySub cD0 (Context.hatToDCtx phat) t in
                  if eq_cvarRef (MMVarRef r) rOccur then
                    raise (Failure "[Prune] Parameter variable occurrence")
                  else
                    if isPatSub t && isPatMSub mt then
                      let (id_sub, cPsi2) = pruneCtx phat (comp t s, cPsi1) ss in
                        (* cD ; cPsi1 |- idsub <= cPsi2 *)
                      let (id_msub, cD2) = pruneMCtx cD0 (mt, cD1) ms in
                        (* cD  |- mt <= cD1
                         * cD1 |- id_msub <=  cD2
                         * cD  |- [|mt|]id_msub <= cD2
                         *
                         * Note: cD |- cPsi2 ctx  and cD1 ; cPsi1 |- tP <= type
                         *       cD ; [|mt|]cPsi1 |- [|mt|]tP <= type
                         *)

                      let i_id_sub  = invert id_sub in
                        (* cD; cPsi2 |- i_id_sub : cPsi1 *)
                      let i_msub = Whnf.m_invert (Whnf.mcomp id_msub mt) in
                        (* cD2 |- i_msub <= cD
                         * cD ; cPsi2 |- i_id_sub <= cPsi1
                         * cD2 ; [|i_msub|]cPsi2 |- [|i_msub|]i_id_sub <= [|i_msub|]cPsi1
                         *
                         * and more importantly: cD2 |- [|i_msub|]cPsi2 ctx
                         *)
                      let i_id_msub = Whnf.m_invert id_msub in
                        (* cD2 |- i_id_msub <= cD1
                         * cD2 ; [|i_id_msub|]cPsi1 |- [|i_id_msub|]tA <= type
                         * cD2 ; [|i_msub|]cPsi2 |- [i_sub][|i_id_msub|]tA <= type
                        *)
                      let cPsi2' = Whnf.cnormDCtx (cPsi2, i_msub) in
                      let i_sub  = Whnf.cnormSub (i_id_sub, i_msub) in
                      let tA'    = Whnf.cnormTyp (tA, i_id_msub) in

                      let v = Whnf.newMPVar None (cD2, cPsi2', TClo(tA', i_sub))  in

                      let _ = instantiateMPVar (r, MPVar ((v, id_msub), id_sub), !cnstrs) in
                        (* [|p[id_msub, id_sub] / q|] *)
                        (* h = p[[ssubst] ([t] idsub)] *)
                        returnNeutral (MPVar((v, Whnf.mcomp (Whnf.mcomp mt id_msub) ms), comp (comp t id_sub) ssubst))
                    else (* t and mt not patsub *)
                      let (ms, ssubst) = ss in
                      let _ = dprint (fun () -> "[prune] MPVar - compute invSub") in
                      let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
                      let _ = dprint (fun () -> "[prune] MPVar - compute invMSub") in
                      let _ = dprint (fun () -> "[prune] mt = " ^ P.msubToString cD0 mt) in
                      let _ = dprint (fun () -> "[prune] cD1 = " ^ P.mctxToString cD1) in
                      let mt' = invMSub cD0 (mt, cD1) ms rOccur in
                      let _ = dprint (fun () -> "[prune] MPVar - computing invMSub done") in
                        returnNeutral (MPVar ((q, mt'), s'))


            | Proj(MPVar (((_n, r, cD1, ClTyp (PTyp tA,cPsi1), cnstrs, mDep) as q, mt), t), index) (* tS *)   (* s = id *) ->
                let t = Whnf.normSub t in
                let t = simplifySub cD0 (Context.hatToDCtx phat) t in
                  if eq_cvarRef (MMVarRef r) rOccur then
                    raise (Failure "[Prune] Parameter variable occurrence")
                  else
                    if isPatSub t && isPatMSub mt then
                      let (id_sub, cPsi2) = pruneCtx phat (comp t s, cPsi1) ss in
                        (* cD ; cPsi1 |- idsub <= cPsi2 *)
                      let (id_msub, cD2) = pruneMCtx cD0 (mt, cD1) ms in
                        (* cD  |- mt <= cD1
                         * cD1 |- id_msub <=  cD2
                         * cD  |- [|mt|]id_msub <= cD2
                         *
                         * Note: cD |- cPsi2 ctx  and cD1 ; cPsi1 |- tP <= type
                         *       cD ; [|mt|]cPsi1 |- [|mt|]tP <= type
                         *)

                      let i_id_sub  = invert id_sub in
                        (* cD; cPsi2 |- i_id_sub : cPsi1 *)
                      let i_msub = Whnf.m_invert (Whnf.mcomp id_msub mt) in
                        (* cD2 |- i_msub <= cD
                         * cD ; cPsi2 |- i_id_sub <= cPsi1
                         * cD2 ; [|i_msub|]cPsi2 |- [|i_msub|]i_id_sub <= [|i_msub|]cPsi1
                         *
                         * and more importantly: cD2 |- [|i_msub|]cPsi2 ctx
                         *)
                      let i_id_msub = Whnf.m_invert id_msub in
                        (* cD2 |- i_id_msub <= cD1
                         * cD2 ; [|i_id_msub|]cPsi1 |- [|i_id_msub|]tA <= type
                         * cD2 ; [|i_msub|]cPsi2 |- [i_sub][|i_id_msub|]tA <= type
                        *)
                      let cPsi2' = Whnf.cnormDCtx (cPsi2, i_msub) in
                      let i_sub  = Whnf.cnormSub (i_id_sub, i_msub) in
                      let tA'    = Whnf.cnormTyp (tA, i_id_msub) in

                      let v = Whnf.newMPVar None (cD2, cPsi2', TClo(tA', i_sub))  in

                      let _ = instantiateMPVar (r, MPVar ((v, id_msub), id_sub), !cnstrs) in
                        (* [|p[id_msub, id_sub] / q|] *)
                        (* h = p[[ssubst] ([t] idsub)] *)
                        returnNeutral (Proj(MPVar((v, Whnf.mcomp (Whnf.mcomp mt id_msub) ms), comp (comp t id_sub) ssubst), index))
                    else (* t and mt not patsub *)
                      let (ms, ssubst) = ss in
                      let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
                      let mt' = invMSub cD0 (mt, cD1) ms rOccur in
                        returnNeutral (Proj(MPVar ((q, mt'), s'), index))

            | Proj (FPVar(p,t), i)   (* tS = Nil,   s = id *) ->
                begin try
                  let (cD_d, Decl (_, ClTyp (_, cPsi1),_)) = Store.FCVar.get p in
                  let d = Context.length cD0 - Context.length cD_d in
	          let cPsi1 = if d = 0 then cPsi1 else
	                        Whnf.cnormDCtx (cPsi1, MShift d) in
                  let t = simplifySub cD0 (Context.hatToDCtx phat) (comp t s) in
                  let s' = invSub cD0 phat (t, cPsi1) ss rOccur in
                    returnNeutral (Proj (FPVar(p,s'), i))
                with
                  | Not_found ->
                      if isId ssubst && isMId ms  then returnNeutral head
                      else raise (Failure ("[Prune] Free parameter variable to be pruned with non-identity substitution"))
                end

            | BVar k  (* s = id *) ->
                begin match bvarSub k ssubst with
                  | Undef                -> raise (Failure ("[Prune] Bound variable dependency : " ^
                                                      "head = " ^ P.headToString cD0 cPsi' head))
                  | Head (BVar _k as h') ->
                      returnNeutral h'
                end

            | Const _ as h  (* s = id *)  ->  returnNeutral h

            | FVar _ as h  (* s = id *)  ->  returnNeutral h

            | Proj (BVar k, i)  (* s = id *) ->
                begin match bvarSub k ssubst with
                  | Head (BVar _k' as h') -> returnNeutral (Proj (h', i))
                  | _                     -> raise (Failure "[Prune] Bound variable dependency (Proj) ")
                end
	in do_head head

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

  (* pruneSubst cD cPsi (s, cPsi1) ss rOccur = r
     if  ss = (mt, s')
         D'         |- mt : D
         D' ; cPsi' |- s' : cPsi
         D  ; cPsi  |- s : cPsi1
     then
         D ; cPsi' |- r : [mt]cPsi1  where
         r is the pruned version of s, i.e. every element
         in s has been pruned with respect to ss s.t.
          [s']([mt]s) = r
  *)
  and pruneSubst cD cPsi (s, cPsi1) ss rOccur = match (s, cPsi1) with
    | (EmptySub, Null) -> EmptySub
    | (Shift (n), DDec(_cPsi', _dec)) ->
        pruneSubst cD cPsi (Dot (Head (BVar (n + 1)), Shift ( n + 1)), cPsi1) ss rOccur
    | (Shift (_n), Null) ->
      let (mt, s') = ss in  (* **    cD' |- mt : cD
                                     cD' ; cPsi' |- s' : [mt]Psi
                                     cD  ; Psi   |- s  : .
                                    ————————————————————————————–
                                     cD' ; [mt]cPsi |- [mt]s : .
                                and then
                                     cD' ; cPsi'  |- [s'] ([mt]s) : [mt]cPsi1 *)
      Whnf.cnormSub (Substitution.LF.comp s s', mt)

    | (Shift (_n), CtxVar psi) ->
      (*  cD ; cPsi |- s : psi
          cD' |- mt : cD
          cD'; cPsi' |- s' : [mt]Psi
         ——————————————————————————–
          cD' ; cPsi' |- [s']([mt]s) : [mt] psi
      *)
      let (mt, s') = ss in
      Whnf.cnormSub (Substitution.LF.comp s s', mt)

    | (SVar (sv, (n), sigma), cPsi1) ->
      (*  cD ; cPsi |- sv[sigma] : cPsi1    where sv:cPsi1[cPhi1]
          cD ; cPsi |- sigma : cPhi1
          ** because s must be in nf, sv = None **
      *)
      let _ = dprint (fun () -> "[pruneSubst] SVar case ") in
      let cPsi' = (let (_, _cPhi, cPsi') = Whnf.mctxSDec cD sv in cPsi') in
        SVar(sv, ( n), pruneSubst cD cPsi (sigma, cPsi') ss rOccur)

    | (FSVar (n, (s_name, sigma)), cPsi1) ->
      let _ = dprint (fun () -> "[pruneSubst] Free sv  " ^ R.render_name s_name)        in
      let (_, Decl (_, ClTyp (STyp _cPhi,  cPsi'),_)) = Store.FCVar.get s_name in
        FSVar (n, (s_name, pruneSubst cD cPsi (sigma, cPsi') ss rOccur))

    | (MSVar (n, ((((_ ,({contents=None} as r), _cD, ClTyp (STyp cPhi2, cPhi1), _cnstrs, _) as rho),
                  mt), sigma) ), _cPsi1) ->
        (dprint (fun () -> "[pruneSubst] MSVar   " ^ P.subToString cD cPsi s);
         let (mt', _s') = ss in
        if eq_cvarRef (MMVarRef r) rOccur then
          raise (Failure "Variable occurrence")
        else
          let sigma = Whnf.normSub sigma in
          let sigma' = pruneSubst cD cPsi (sigma, cPhi1) ss rOccur in
          MSVar (n, ((rho, Whnf.mcomp mt mt'), sigma'))
        )
    (* Other heads to be added ??

    | (Dot (Head , s'), DDec(cPsi', _dec)) ->
    *)

    | (Dot (Head (BVar n), s'), DDec(cPsi', _dec)) ->
      let (mt, ssubst) = ss in
        begin match bvarSub n ssubst with
          | Undef -> raise NotInvertible
          | ft    -> Dot (ft , pruneSubst cD cPsi (s', cPsi1) ss rOccur)
        end

    | (Dot (Head (Proj (BVar n, k)), s'), DDec(cPsi', _dec)) ->
      let (mt, ssubst) = ss in
        begin match bvarSub n ssubst with
          | Undef -> raise NotInvertible
            (* let si = invSub cD0 phat (s', cPsi') ss rOccur in
               Dot(Undef, si) *)
          | Head(BVar m)  ->
              Dot (Head (Proj (BVar m, k)) , pruneSubst cD cPsi (s', cPsi1) ss rOccur)
          | _ -> raise NotInvertible
        end

    | (Dot (Head (h), s'), DDec(cPsi', _dec)) ->
        (dprint (fun () -> "[pruneSubst] h = " ^ P.headToString cD cPsi h);
         let Root(_,h',_) = prune cD cPsi (Context.dctxToHat cPsi) (Root(Syntax.Loc.ghost,h,Nil), Substitution.LF.id)  ss  rOccur in
         Dot (Head h', pruneSubst cD cPsi (s', cPsi') ss rOccur))
         (* -ac: verify that this is reasonable. *)

    | (Dot (Obj tM, s'), DDec(cPsi', _dec))        ->
        (* below may raise NotInvertible *)
        (dprint (fun () -> "[pruneSubst] tM = " ^ P.normalToString cD cPsi (tM, Substitution.LF.id));
        let tM' = prune cD cPsi  (Context.dctxToHat cPsi) (tM, Substitution.LF.id)  ss  rOccur in
          dprint (fun () -> "[pruneSubst] tM' = " ^ P.normalToString cD cPsi (tM', Substitution.LF.id));
          Dot (Obj tM', pruneSubst cD cPsi (s', cPsi') ss rOccur))

    | (s, cPsi') ->(dprint (fun () -> "[pruneSubst] other cases not defined? " );
           dprint (fun () -> "[pruneSubst] - substitution ill-typed ?" ) ;
           dprint (fun () -> "             " ^ P.dctxToString cD cPsi ^ " |- "
                     ^ P.subToString cD cPsi s
                     ^ " : " ^ P.dctxToString cD cPsi');
           raise NotInvertible)

  (* pruneSub cD0 cPsi phat (s, cPsi1) ss rOccur = (s', cPsi1')

     if phat = hat(cPsi)  and
        D ; cPsi  |- s <= cPsi1
        D ; cPsi''|- ss <= cPsi
     then  cPsi1 |- s' <= cPsi1'
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
    let (mt, _ ) = ss in
    match (s, cPsi1) with
    | (Shift ( n), DDec(_cPsi', _dec)) ->
        pruneSub' cD0 cPsi phat (Dot (Head (BVar (n + 1)), Shift ( n + 1)), cPsi1) ss rOccur

    | (Shift ( _n), Null) -> (id, Null)
    | (EmptySub, Null) -> (id, Null)
    | (Undefs, Null) -> (id, Null)

    | (Shift n, CtxVar psi) ->
      let (_, ssubst) = ss in
      let rec shiftInvSub n ss = match ss with
	| Undefs -> (EmptySub,Null)
	| Shift k -> (id, CtxVar psi)
        | Dot (ft, ss') -> shiftInvSub (n-1) ss'
      in 
      shiftInvSub n ssubst

    | (SVar (s, cshift, sigma), cPsi1) ->
        (*     D ; cPsi1' | cshift : cPsi1
               D; Psi |- s[sigma] : cPsi1'  where s: cPsi1'[Phi]
               D ;Psi |- sigma : Phi
               D;Psi'' |- ss <= Psi
               [ss] ([s[sigma] ] id ) exists
        *)
      let s' , cPsi1' = (id, cPsi1) in


      let cPsi' = (match applyMSub s mt with
                                           | MV v -> let (_, _cPhi, cPsi') = Whnf.mctxSDec cD0  v in cPsi'
                                           | MUndef -> raise NotInvertible
                    ) in

        let _ = invSub cD0 phat (sigma, cPsi') ss rOccur  in
        let _ = dprint (fun () -> "[pruneSub] result = " ^
                       P.subToString cD0 cPsi (comp s' (SVar (s, cshift, sigma)))) in

          (s',cPsi1')

    | (MSVar (cshift, ((s, _theta),sigma)), cPsi1) ->
      let s' , cPsi1' = (id, cPsi1) in

      let (_ ,{contents=None}, _cD, ClTyp (STyp cPhi2, cPhi1), _cnstrs, _) = s in
      let cPhi1' = Whnf.cnormDCtx (cPhi1, Whnf.m_id) in
      let _ = invSub cD0 phat (sigma, cPhi1') ss rOccur  in
          (s', cPsi1')

    | (FSVar (cshift, (s, sigma)), cPsi1) ->
        (*     D; Psi |- s[sigma] : psi  where s: psi[Phi]
               D ;Psi |- sigma : Phi
               D;Psi'' |- ss <= Psi
               [ss] ([s[sigma] ] id ) exists
        *)
      let s' , cPsi1' = (id, cPsi1) in

        let (_, Decl (_, ClTyp (STyp _cPhi,  cPsi'),_)) = Store.FCVar.get s in
        let _ = invSub cD0 phat (sigma, cPsi') ss rOccur  in
        (s', cPsi1')

    (*(Dot (Head (HClo  .... )  to be added -bp
       SVar case (offset might not be 0 ) and domain is cPsi
     *)
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
    let _u : (msub * sub) = ss in
      pruneTypW cD0 cPsi1 phat (Whnf.whnfTyp sA) ss rOccur

  and pruneTypRec cD0 cPsi phat (typ_rec, s) (mss, ss) rOccur = match (typ_rec, s) with
    | (SigmaLast(n, tA), s) -> SigmaLast(n, (pruneTyp cD0 cPsi phat (tA, s) (mss, ss) rOccur))
    | (SigmaElem (x, tA, typ_rec'), s) ->
      let tA' = pruneTyp cD0 cPsi phat (tA, s) (mss, ss) rOccur in
      let typ_rec'' = pruneTypRec cD0 cPsi phat (typ_rec', dot1 s) (mss, dot1 ss) rOccur in
        SigmaElem (x, tA', typ_rec'')

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
    | (EmptySub, Null) -> (id, Null)
    | (Undefs, Null) -> (id, Null)
    | (Shift (_k), Null) ->
        (id, Null)

    | (Shift ( k), CtxVar psi) ->
        let ( _ , ssubst) = ss in
        let rec check_negshift k ssubst = begin match (k, ssubst) with
          | (k, Dot (Undef, ssubst')) -> check_negshift (k-1) ssubst'
	  | (k, Undefs) -> (EmptySub, Null)
          | (_ , _ ) -> (id, CtxVar psi)
        end
        in
          check_negshift k ssubst

   | (Shift k, DDec (_, TypDecl (_x, _tA))) ->
       pruneCtx' phat (Dot (Head (BVar (k + 1)), Shift (k + 1)), cPsi1) ss


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
       Otherwise, raises exception Failure.

       Postcondition: cD' includes new and possibly updated contextual variables;

       Other effects: MVars in cD' may have been lowered and pruned;
                      Constraints may be added for non-patterns.
  *)

  let rec unifyTerm  mflag cD0 cPsi sN sM = unifyTerm'  mflag cD0 cPsi (Whnf.norm (Whnf.whnf sN)) (Whnf.norm (Whnf.whnf sM))

  and unifyTuple mflag cD0 cPsi sTup1 sTup2 = match (sTup1, sTup2) with
    | ((Last tM, s1) ,  (Last tN, s2)) ->
      unifyTerm mflag cD0 cPsi (tM, s1) (tN, s2)
    | ((Cons (tM, tup1), s1), (Cons (tN, tup2), s2)) ->
      (unifyTerm mflag cD0 cPsi (tM, s1) (tN, s2);
       unifyTuple mflag cD0 cPsi (tup1, s1) (tup2, s2))

  and unifyMVarTerm cD0 cPsi (_n1, r1,  _, ClTyp (_, cPsi1), cnstrs1, mdep1) t1' sM2 = 
    begin try
     let ss1  = invert (Whnf.normSub t1') (* cD ; cPsi1 |- ss1 <= cPsi *) in
     let phat = Context.dctxToHat cPsi in
     let tM2' = trail (fun () -> prune cD0 cPsi1 phat (sM2,id) (MShift 0, ss1) (MMVarRef r1)) in
     instantiateMVar (r1, tM2', !cnstrs1)
     with NotInvertible -> raise (Error.Violation "Pattern substitution  not invertible")
    end 

  and unifyMMVarTerm cD0 cPsi (_, r1, cD1, ClTyp (_, cPsi1), cnstrs1, mdep1) mt1 t1' sM2 = 
    begin try
      let ss1  = invert t1' in
      let ss1  = Whnf.cnormSub (ss1, Whnf.m_id) in
      (* cD ; cPsi1 |- ss1 <= cPsi *)
      let mtt1 = Whnf.m_invert (Whnf.cnormMSub mt1) in
      let phat = Context.dctxToHat cPsi in
      let tM2' = trail (fun () -> prune cD0 cPsi1 phat (sM2,id) (mtt1, ss1) (MMVarRef r1)) in
      instantiateMMVar (r1, Whnf.norm(tM2',id), !cnstrs1);
      with NotInvertible -> raise (Error.Violation "Pattern substitution not invertible")
    end

  and unifyMMVarTermProj cD0 cPsi (((Root (_, MMVar (((_, r1, cD, ClTyp (_, cPsi1), cnstrs1, mdep1), mt1), t1), _))) as sM1) t1' sM2 =
     begin try 
       let mtt1 = Whnf.m_invert (Whnf.cnormMSub mt1) in
       let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cD0 cPsi in
       let phat = Context.dctxToHat flat_cPsi in
       let t_flat = ConvSigma.strans_sub cD0 t1' conv_list in
       let tM2'   = ConvSigma.strans_norm cD0 (sM2,id) conv_list in
       let ss = invert t_flat in
       let sM2' = trail (fun () -> prune cD cPsi1 phat (tM2', id) (mtt1, ss) (MMVarRef r1)) in
       instantiateMMVar (r1, sM2', !cnstrs1)
       with | NotInvertible ->
	(dprint (fun () -> "Add constraint (4)");
         addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, INorm sM1, INorm sM2))))
     end


  and unifyTerm'  mflag cD0 cPsi sN sM = match (sN, sM) with
    | ((Tuple(_ , tup1)) , (Tuple (_ , tup2))) ->
      unifyTuple mflag cD0 cPsi (tup1, id) (tup2, id)

    | ((Lam (_, _, tN)), (Lam (_ , x, tM))) ->
        unifyTerm  mflag cD0 (DDec(cPsi, TypDeclOpt x)) (tN, id) (tM, id)

    (* MVar-MVar case *)
    | (((Root (_, MVar (Inst (_n1, r1,  _, ClTyp (MTyp tP1, cPsi1), cnstrs1, mdep1), t1), _tS1) as _tM1)),
       (((Root (_, MVar (Inst (_n2, r2, _, ClTyp (MTyp tP2, cPsi2), cnstrs2, mdep2), t2), _tS2) as _tM2)))) when r1 == r2 -> begin
         dprnt "(000) MVar-MVar";
        (* by invariant of whnf:
           meta-variables are lowered during whnf, s1 = s2 = id or co-id
           r1 and r2 are uninstantiated  (None)
        *)
            match (isPatSub t1 , isPatSub t2) with
              | (true, true) ->
                    let phat = Context.dctxToHat cPsi in
                    let (s', cPsi') = intersection phat t1 t2 cPsi1 in
                      (* if cD ; cPsi |- t1' <= cPsi1 and cD ; cPsi |- t2' <= cPsi1
                         then cD ; cPsi1 |- s' <= cPsi' *)

                    let ss' = invert (Monitor.timer ("Normalisation", fun () -> Whnf.normSub s')) in
                      (* cD ; cPsi' |- [s']^-1(tP1) <= type *)

                    let w = Whnf.newMVar None (cPsi', TClo(tP1, ss'))  in
                      (* w::[s'^-1](tP1)[cPsi'] in cD'            *)
                      (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tP1)
                         [|w[s']/u|](u[t1]) = [t1](w[s'])
                         [|w[s']/u|](u[t2]) = [t2](w[s'])
                      *)
                      instantiateMVar (r1, Root(Syntax.Loc.ghost, MVar(w, s'),Nil), !cnstrs1)
              | (_, _) ->
                  if Whnf.convDCtx cPsi1 cPsi2 && Whnf.convSub t1 t2 then
                    ()
                  else
		    addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, INorm sN, INorm sM)))
    end 

    (* MVar-normal case *)
    | (Root (_, MVar (Inst i, t), _tS), sM2) 
      when isPatSub t -> unifyMVarTerm cD0 cPsi i t sM2

    | (sM2, (Root (_, MVar (Inst i, t), _tS)))
      when isPatSub t -> unifyMVarTerm cD0 cPsi i t sM2
    
    | ((Root (_, MVar (Inst (_, _, _, _, cnstrs, _), _), _tS)) as sM1, sM2) 
    | (sM2, ((Root (_, MVar (Inst (_, _, _, _, cnstrs, _), _), _tS)) as sM1))
      -> addConstraint (cnstrs, ref (Eqn (cD0, cPsi, INorm sM1, INorm sM2)))

    (* MMVar-MMVar case *)
    | (((Root (_, MMVar (((_n1, r1,  cD1, ClTyp (MTyp tP1, cPsi1), cnstrs1, mdep1), mt1), t1), _tS1))),
       (((Root (_, MMVar (((_n2, r2, _cD2, ClTyp (MTyp tP2,cPsi2), cnstrs2, mdep2), mt2), t2), _tS2))))) when r1 == r2 ->
        dprnt "(010) MMVar-MMVar";
        (* by invariant of whnf:
           meta^2-variables are lowered during whnf, s1 = s2 = id
           r1 and r2 are uninstantiated  (None)
        *)
        let t1' = simplifySub cD0 cPsi (Whnf.normSub t1)    (* cD ; cPsi |- t1' <= cPsi1 *)
        and t2' = simplifySub cD0 cPsi (Whnf.normSub t2)    (* cD ; cPsi |- t2' <= cPsi2 *)
        in begin
            match (isPatMSub mt1, isPatSub t1' , isPatMSub mt2, isPatSub t2') with
              | (true, true, true, true) ->
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


                    let w = Whnf.newMMVar None (cD', cPsi_n, tP1_n)  in
                      (* w::[s'^-1](tP1)[cPsi'] in cD'            *)
                      (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tP1)
                         [|w[s']/u|](u[t1]) = [t1](w[s'])
                         [|w[s']/u|](u[t2]) = [t2](w[s'])
                      *)
                    let _ = instantiateMMVar (r1, Root(Syntax.Loc.ghost, MMVar((w, mt'), s'), Nil), !cnstrs1) in

(*                     dprint (fun () -> "Instantiated with new meta^2-variable " ^
                                        P.normalToString cD0 cPsi sM1)*)
                      ()


              | (_, _, _, _) ->
                  addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, INorm sN, INorm sM)))
       end  
    | (((Root (_, MMVar (((_,_,_,_,cnstrs1,_) as i, mt1), t1), _tS1))) as sM1,
       (((Root (_, MMVar ((i', mt2), t2), _tS2))) as sM2)) ->
        let t1' = simplifySub cD0 cPsi (Whnf.normSub t1)    (* cD ; cPsi |- t1' <= cPsi1 *)
        and t2' = simplifySub cD0 cPsi (Whnf.normSub t2)    (* cD ; cPsi |- t2' <= cPsi2 *)
        in
            begin match (isPatMSub mt1, isPatSub t1' , isPatMSub mt2, isPatSub t2') with
              | (true, true, _, _) ->
		unifyMMVarTerm cD0 cPsi i mt1 t1' sM2
              | (_ , _, true, true) ->
		unifyMMVarTerm cD0 cPsi i' mt2 t2' sM1
              | (_ , _ , _ , _) ->
                  begin match  (isProjPatSub t1' , isProjPatSub t2') with
                    | ( _ , true ) ->
		      unifyMMVarTermProj cD0 cPsi sM2 t2' sM1
                    | ( true, _ ) ->
		      unifyMMVarTermProj cD0 cPsi sM1 t1' sM2

                    | ( _ , _ ) ->
                        (* neither t1' nor t2' are pattern substitutions *)
                        let cnstr = ref (Eqn (cD0, cPsi, INorm sM1, INorm sM2)) in
			let _ = dprint (fun () -> "Add constraint (5)") in
                          addConstraint (cnstrs1, cnstr)
                  end
            end


    (* MMVar-normal case *)
    | ((Root (loc, MMVar (((_n, r, cD,  ClTyp (MTyp tP,cPsi1), cnstrs, mdep), mt), t), _tS)) as sM1, sM2)
    | (sM2, ((Root (loc, MMVar (((_n, r, cD, ClTyp (MTyp tP,cPsi1), cnstrs, mdep), mt), t), _tS)) as sM1)) ->
        dprnt "(011) MMVar-_";
        if blockdeclInDctx (Whnf.cnormDCtx (cPsi1, Whnf.m_id)) then
          (dprnt "(011) - blockinDCtx";
          let tN = genMMVarstr loc cD cPsi1 (tP, id) in
            instantiateMMVar (r, tN,!cnstrs);
            unifyTerm mflag cD0 cPsi (sM1,id) (sM2,id))
        else
        let t' = simplifySub cD0 cPsi (Whnf.normSub t) in
        let _ = dprint (fun () -> "cPsi = " ^ P.dctxToString cD0 cPsi) in
        let _ = dprint (fun () -> "t' = " ^ P.subToString cD0 cPsi t') in
        let _ = dprint (fun () -> "mt = " ^ P.msubToString cD0 mt) in
            if isProjPatSub t' && isPatMSub mt then
              begin try
		unifyMMVarTermProj cD0 cPsi sM1 t' sM2
                with NotInvertible ->
                  (dprint (fun () -> "(010) Add constraints ");
                  addConstraint (cnstrs, ref (Eqn (cD0, cPsi, INorm sM1, INorm sM2))))
              end
          else
             (dprint (fun () -> "(011) Add constraints ");
             addConstraint (cnstrs, ref (Eqn (cD0, cPsi, INorm sM1, INorm sM2))))

    | (Root(_, h1,tS1) as sM1, (Root(_, h2, tS2) as sM2)) ->
        dprnt "(020) Root-Root";
        let _ = dprint (fun () ->
                          "UNIFY: normal - normal (non MVar cases) " ^
                            P.mctxToString cD0 ^ "      |-    " ^
                            P.normalToString cD0 cPsi (sM1,id) ^ "           ==       " ^
                            P.normalToString cD0 cPsi (sM2,id) ^ "\n") in

        (* s1 = s2 = id by whnf *)
        unifyHead  mflag cD0 cPsi h1 h2;
        unifySpine mflag cD0 cPsi (tS1, id) (tS2, id)

    | (_sM1, _sM2) ->
        raise (Failure "Expression clash")

  and unifyHead mflag cD0 cPsi head1 head2 =
    match (head1, head2) with
    | (BVar k1, BVar k2) ->
        if k1 = k2 then
          ()
        else
          raise (Failure "Bound variable clash")

    | (Const ((i, id) as _c1), Const ((i', id') as _c2)) ->
        if i = i' && id = id' then
          ()
        else
          raise (Failure "Constant clash")

    | (FVar x1, FVar x2) ->
        if x1 = x2 then
          ()
        else
          raise (Failure "Free Variable clash")

    | (MVar (Offset k, s) , MVar(Offset k', s')) ->
        if k = k' then unifySub mflag cD0 cPsi s s'
        else raise (Failure "Bound MVar clash")

    | (FMVar (u, s) , FMVar(u', s')) ->
        if u = u' then unifySub mflag cD0 cPsi s s'
        else raise (Failure "Bound MVar clash'")

    | (FPVar (q, s), FPVar (p, s'))
        ->   (if p = q then
                unifySub mflag cD0 cPsi s s'
              else raise (Failure "Front FPVar mismatch"))

    | (PVar (k, s) , PVar(k', s')) ->
        if k = k' then
           unifySub mflag cD0 cPsi s s'
        else raise (Failure "Parameter variable clash")

    (* MPVar - MPVar *)
    | (MPVar (((_n1, q1, cD1, ClTyp (PTyp tA1,cPsi1), cnstr1, mDep1) as q1', mt1), s1) ,
       MPVar (((_n2, q2, cD2, ClTyp (PTyp tA2,cPsi2), cnstr2, mDep2) as q2', mt2), s2) ) ->
        let s1' = simplifySub cD0 cPsi (Whnf.normSub s1) in
        let s2' = simplifySub cD0 cPsi (Whnf.normSub s2) in
        let mt1' = Whnf.cnormMSub mt1 in
        let mt2' = Whnf.cnormMSub mt2 in
        (* check s1' and s2' are pattern substitutions; possibly generate constraints;
           check intersection (s1', s2'); possibly prune *)
        if q1 == q2 then (* cPsi1 = _cPsi2 *)
          (match (isPatMSub mt1', isPatSub s1' ,  isPatMSub mt2', isPatSub s2') with
            | ( true, true, true, true ) ->
                (* if Whnf.convSub s1' s2' && Whnf.convMSub mt1' mt2' then *)
                (*   () *)
                (* else *)
                let phat = Context.dctxToHat cPsi in
                let (s', cPsi') = intersection phat s1' s2' cPsi1 in
                  (* if cD ; cPsi |- s1' <= cPsi1 and cD ; cPsi |- s2' <= cPsi1
                     then cD ; cPsi1 |- s' <= cPsi' *)
                  (* cPsi' =/= Null ! otherwise no instantiation for
                     parameter variables exists *)

                let (mt', cD') = m_intersection (Whnf.cnormMSub mt1) (Whnf.cnormMSub mt2) cD1 in
                      (* if cD |- mt1 <= cD1 and cD |- mt2 <= cD1
                         then cD1 |- mt' <= cD' *)
                let ss'  = invert (Whnf.normSub s') in
                      (* if cD ; cPsi1 |- s' <= cPsi'
                         then cD ; cPsi' |- ss' <= cPsi1 *)
                      (* cD ; cPsi' |- [s']^-1(tA1) <= type *)
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
                let tA1_n  = Whnf.cnormTyp (TClo(tA1,ss'), mtt') in


                let w = Whnf.newMPVar None (cD', cPsi_n, tA1_n)  in
                      (* w::[s'^-1](tA1)[cPsi'] in cD'            *)
                      (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tA1)
                         [|w[s']/u|](u[t1]) = [t1](w[s'])
                         [|w[s']/u|](u[t2]) = [t2](w[s'])
                      *)

                  instantiateMPVar (q2, MPVar((w, mt'), s'), !cnstr2)

            | (true, true, _, false) ->
                addConstraint (cnstr2, ref (Eqn (cD0, cPsi, IHead head1, IHead head2))) (*XXX double-check *)
            | (true, true, false, _) ->
                addConstraint (cnstr2, ref (Eqn (cD0, cPsi, IHead head1, IHead head2))) (*XXX double-check *)
            | (false, _, _, _) ->
                addConstraint (cnstr1, ref (Eqn (cD0, cPsi, IHead head2, IHead head1)))  (*XXX double-check *)
            | (_, false, _, _) ->
                addConstraint (cnstr1, ref (Eqn (cD0, cPsi, IHead head2, IHead head1)))  (*XXX double-check *)
           )
        else
          ((*let _ = dprint (fun () -> "[unifyHead] PVar (PInst) q1 =/= q2 " ) in*)
            match (isPatMSub mt1', isPatSub s1' , isPatMSub mt2', isPatSub s2') with
             | (true, true, true, true) ->
                 (* no occurs check necessary, because s1' and s2' are pattern subs. *)
                 let _ = unifyTyp mflag cD0 cPsi (tA1, s1') (tA2, s2') in
 (*                let _ = dprint (fun () -> "Unification of the types done ... \n") in *)
                 (* at this point: [s1']tA1 = [s2']tA2  ! *)
                 let ss = invert s1' in
                      (* cD ; cPsi1 |- ss1 <= cPsi *)
                 let mtt1 = Whnf.m_invert mt1' in
                      (* cD1 |- mtt1 <= cD *)
                 let phat = Context.dctxToHat cPsi in
                 let (id_sub, cPsi2') = pruneCtx phat (s2', cPsi2) (mtt1, ss) in
                 let (id_msub, cD2') = pruneMCtx cD0 (mt2', cD2) mtt1 in
                   (* if   cPsi  |- s2' <= cPsi2  and cPsi1 |- ss <= cPsi
                      then cPsi2 |- id_sub <= cPsi2' and [ss](s2' (id_sub)) exists *)
                   (* if   cD  |- mt2' <= cD2  and cD1 |- mtt1 <= cD
                      then cD2 |- id_msub <= cD2' and [mtt1](mt2' (id_msub)) exists *)
                   (* cPsi' =/= Null ! otherwise no instantiation for
                      parameter variables exists *)
                 let i_id_sub  = invert id_sub in
                        (* cD; cPsi2' |- i_id_sub : cPsi2 *)
                 let i_msub = Whnf.m_invert id_msub in
                        (* cD2' |- i_msub <= cD2
                         * cD ; cPsi2' |- i_id_sub <= cPsi2
                         * cD2 ; [|i_msub|]cPsi2' |- [|i_msub|]i_id_sub <= [|i_msub|]cPsi2
                         *
                         * and more importantly: cD2 |- [|i_msub|]cPsi2' ctx
                         *
                         * cD2' ; [|i_msub|]cPsi2 |- [|i_msub|]tA2 <= type
                         * cD2' ; [|i_msub|]cPsi2' |- [|i_id_msub|][i_id_sub]tA2 <= type
                        *)
                 let cPsi2'' = Whnf.cnormDCtx (cPsi2', i_msub) in
                 let tA2'    = Whnf.cnormTyp (Whnf.normTyp (tA2, i_id_sub), i_msub) in

                 let v = Whnf.newMPVar None (cD2', cPsi2'', tA2')  in

                   (instantiateMPVar (q2, MPVar((v, id_msub) , id_sub), !cnstr2);

                    instantiateMPVar (q1, MPVar((v, Whnf.mcomp (Whnf.mcomp id_msub mt2') mtt1),
                                                    comp (comp id_sub s2') ss),
                                          !cnstr1))


            | (true, true, _ , _ ) ->
                 let _ =  unifyTyp mflag cD0 cPsi (tA1, s1') (tA2, s2') in
                  (* only s1' is a pattern sub
                     [(s1)^-1](q2[s2']) = q2[(s1)^-1 s2']
                  *)
                 let ss1 = invert s1' in
                 let mtt1 = Whnf.m_invert mt1' in

                 let phat = Context.dctxToHat cPsi in
                 let s' = invSub cD0 phat (s2', cPsi2) (mtt1 , ss1) (MMVarRef q1) in
                 let ms' = invMSub cD0 (mt2', cD2) mtt1 (MMVarRef q1) in
                   instantiateMPVar (q1, MPVar((q2', ms'), s'), !cnstr1)

            | (_, _, true , true ) ->
                 let _ =  unifyTyp mflag cD0 cPsi (tA1, s1') (tA2, s2') in
                  (* only s1' is a pattern sub
                     [(s1)^-1](q2[s2']) = q2[(s1)^-1 s2']
                  *)
                 let ss2 = invert s2' in
                 let mtt2 = Whnf.m_invert mt2' in

                 let phat = Context.dctxToHat cPsi in
                 let s' = invSub cD0 phat (s1', cPsi1) (mtt2 , ss2) (MMVarRef q2) in
                 let ms' = invMSub cD0 (mt1', cD1) mtt2 (MMVarRef q2) in
                   instantiateMPVar (q2, MPVar((q1', ms'), s'), !cnstr2)

             | (false, _, _ , _ ) ->
                 (* neither s1' nor s2' are patsub *)
                 addConstraint (cnstr1, ref (Eqn (cD0, cPsi, IHead head1, IHead head2)))
             | (_, false, _ , _ ) ->
                 (* neither s1' nor s2' are patsub *)
                 addConstraint (cnstr1, ref (Eqn (cD0, cPsi, IHead head1, IHead head2)))
             (* | (_, _, false , _ ) -> *)
             (*     (\* neither s1' nor s2' are patsub *\) *)
             (*     addConstraint (cnstr2, ref (Eqh (cD0, cPsi, head2, head1))) *)
             (* | (_, _, _ , false ) -> *)
             (*     (\* neither s1' nor s2' are patsub *\) *)
             (*     addConstraint (cnstr2, ref (Eqh (cD0, cPsi, head2, head1))) *)
          )


    | (MPVar (((_n1, q1, cD1, ClTyp (PTyp tA1,cPsi1), cnstr1, mDep), mt1), s1) , h) 
    | (h, MPVar (((_n1, q1, cD1, ClTyp (PTyp tA1,cPsi1), cnstr1, mDep), mt1), s1) ) ->
        (* ?#p[mt1, s1] ==  BVar k    or     ?#p[mt1, s1] = PVar (q, s) *)
        dprnt "(013) _-MPVar - head";
      if isVar h && isPatSub s1 && isPatMSub mt1 then
          let ss = invert (Whnf.normSub s1) in
          let mtt = Whnf.m_invert (Whnf.cnormMSub mt1) in
           begin match h with
             | BVar k -> begin match bvarSub k ss with
                         | Head h -> instantiateMPVar (q1, h, !cnstr1)
                         | _ -> raise (Failure ("Looking up " ^ string_of_int k ^ "\n"))
                         end
             | PVar (p,s) -> begin match Whnf.cnormHead (h, mtt) with
                             | PVar(q, s') ->  instantiateMPVar (q1,PVar(q, comp s' s1), !cnstr1)
                             | _ -> raise (Failure "Meta^2-parameter failure")
                             end

             | _ -> raise (Failure "Meta^2-Parameter failure")
           end
        else
          raise (Failure "Cannot instantiate PVar with a head which is not guaranteed to remain a variable")

    | (PVar _  , Proj (PVar _, _))
    | (Proj (PVar _, _), PVar _) ->
        (print_string "[UnifyHead] Projection of a parameter variable\n";
         raise (Failure "PVar i =/= Proj PVar"))

    | (Proj (h1, i1),  Proj (h2, i2)) ->
(*        let _ = dprint (fun () -> "[unifyHead] Proj - Proj ") in *)
        if i1 = i2 then
          ((* dprint (fun () -> "[unifyHead] " ^ P.headToString cD0 cPsi h1 ^ " === " ^ P.headToString cD0 cPsi h2 ) ;*)
          unifyHead mflag cD0 cPsi h1 h2 )
        else
          raise (Failure ("(Proj) Index clash: " ^ string_of_int i1 ^ " /= " ^ string_of_int i2))

    | (FVar _, Proj (PVar _, _)) ->
        (print_string "[UnifyHead] Unify free variable with projection of parameter variable\n";
         raise (Failure "Projection of parameter variable =/= free variable"))

    | (_h1 , _h2 ) ->
        (dprint (fun () -> "[unifyHead'] Head clash");
        raise (Failure "Head clash"))


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
            else exception Failure is raised

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
          (* dprint (fun () -> "[unifySpine] " ^ P.normalToString cD0 cPsi (tM1,s1) ^
                    " == " ^ P.normalToString cD0 cPsi (tM2, s2));*)
          unifyTerm mflag cD0 cPsi (tM1, s1) (tM2, s2);
          unifySpine mflag cD0 cPsi (tS1, s1) (tS2, s2)
      (* Nil/App or App/Nil cannot occur by typing invariants *)

    and unifySub mflag cD0 cPsi s1 s2 =
    unifySub' mflag cD0 cPsi (simplifySub cD0 cPsi (Whnf.cnormSub (s1, Whnf.m_id)))
                             (simplifySub cD0 cPsi (Whnf.cnormSub (s2, Whnf.m_id)))

    and unifySub' mflag cD0 cPsi s1 s2 = match (s1, s2) with
      | (Shift n, Shift k) ->
            if n = k then
              ()
            else
              raise (Error "Substitutions not well-typed")

      | (FSVar (n1, (s1, sigma1)), FSVar (n2, (s2, sigma2)))
        -> if s1 = s2 && n1 = n2 then
          unifySub mflag cD0 cPsi sigma1 sigma2
        else raise (Failure "FSVar mismatch")

      | (SVar(s1, n1, sigma1), Shift ( 0) ) -> ()
      | (Shift ( 0), SVar(s1, n1, sigma1) ) -> ()

      | (SVar(s1, n1, sigma1), SVar(s2, n2, sigma2))
        -> if s1 = s2 && n1 = n2 then
          unifySub mflag cD0 cPsi sigma1 sigma2
        else raise (Failure "SVar mismatch")

      | (Dot (f, s), Dot (f', s'))
        -> (unifyFront mflag cD0 cPsi f f' ;
            unifySub mflag cD0 cPsi s s')

      | (Shift n, Dot(Head BVar _k, _s'))
          ->
           unifySub mflag cD0 cPsi (Dot (Head (BVar (n+1)), Shift (n+1))) s2

      | (Dot(Head BVar _k, _s'), Shift n)
          ->
            unifySub mflag cD0 cPsi s1 (Dot (Head (BVar (n+1)), Shift (n+1)))


      | (MSVar (_n, (((_ ,({contents=None} as r), cD, ClTyp (STyp cPhi2, cPhi1), cnstrs, mDep) , mt), s)) as s1 ,  s2)
      | (s2, (MSVar (_n, (((_ ,({contents=None} as r), cD, ClTyp (STyp cPhi2, cPhi1), cnstrs, mDep), mt), s)) as s1)) ->
        (* cD0 ; cPsi |- s <= cPhi_2
           cD0        |- mt <= cD
         *)
        let s = Whnf.normSub s in
        let mt = Whnf.cnormMSub mt in
        let _ = dprint (fun () -> "[unifySub - a] s2 = " ^ P.subToString cD0 cPsi (Whnf.normSub s2)) in
        let _ = dprint (fun () -> "[unifySub - a] s1 = " ^ P.subToString cD0 cPsi (Whnf.normSub s1)) in
        let _ = dprint (fun () -> "[unifySub - a] cPhi2 = " ^ P.dctxToString cD0 (Whnf.cnormDCtx (cPhi2, mt))) in
        let _ = dprint (fun () -> "[unifySub - a] cPhi1 = " ^ P.dctxToString cD0 (Whnf.cnormDCtx (cPhi1, mt))) in
        let _ = dprint (fun () -> "[unifySub - a] s1 == s2 ?? " ) in
        begin match (isPatSub s, isPatMSub mt) with
          | (true, true) ->
            begin
              try
                let s_i = invert (Whnf.normSub s) in   (* cD0 ; cPhi2 |- s_i : cPsi *)
                let mt_i = Whnf.m_invert (Whnf.cnormMSub mt) in  (*  cD |- mt_i : cD0 *)
                let _ = dprint (fun () -> "[unifySub - a ]  pattern sub case ... calling pruneSubst" ) in
                let _ = dprint (fun () -> "[unifySub - a ] s_i = " ^ P.subToString cD (Whnf.cnormDCtx (cPhi2, mt)) s_i) in
                let _ = dprint (fun () -> "[unifySub - a ] mt_i = " ^
                                  P.msubToString cD mt_i) in
                let s2 = Whnf.normSub (Whnf.cnormSub (s2, mt)) in
                let s2' = pruneSubst cD0 cPsi (s2, (Whnf.cnormDCtx (cPhi2, mt))) (mt_i, s_i) (MMVarRef r) in
                let _ = dprint (fun () -> "[unifySub - a ] pruned s2 = s2' = " ^ P.subToString cD (Whnf.cnormDCtx (cPhi2, mt)) (Whnf.normSub s2')) in
                instantiateMSVar (r, s2', !cnstrs)
              with
                | NotInvertible -> addConstraint (cnstrs, ref (Eqn (cD0, cPsi, ISub s1, ISub s2)))
            end
          | (_ , _ ) -> addConstraint (cnstrs, ref (Eqn (cD0, cPsi, ISub s1, ISub s2)))
        end
      | (EmptySub, _) -> ()
      | (_,EmptySub) -> ()
      | (_,Undefs) -> () (* hopefully only occurs at empty domain.. *)
      | (Undefs,_) -> () 
      |  _
        -> raise (Failure (
                            "Substitution mismatch :\n " ^ P.dctxToString cD0 cPsi
                         ^ "|-" ^ P.subToString cD0 cPsi s1 ^ " =/= " ^ P.subToString cD0 cPsi s2 ^ "\n"))


    and unifyFront mflag cD0 cPsi front1 front2 = match (front1, front2) with
      | (Head (BVar i), Head (BVar k))
        -> if i = k then () else
              raise (Failure "Front BVar mismatch")

      | (Head (Const i), Head (Const k))
        -> if i = k then () else raise (Failure "Front Constant mismatch")

      | (Head (PVar (q, s)), Head (PVar (p, s')))
        -> (if p = q then
            unifySub mflag cD0 cPsi s s'
            else raise (Failure "Front PVar mismatch"))


      | (Head (FPVar (q, s)), Head (FPVar (p, s')))
        ->   (if p = q then
                unifySub mflag cD0 cPsi s s'
              else raise (Failure "Front FPVar mismatch"))

      | (Head (MVar (u, s)), Head (MVar (v, s')))
        ->  (if u = v then
               unifySub mflag cD0 cPsi s s'
             else raise (Failure "Front MVar mismatch"))

      | (Head (FMVar (u, s)), Head (FMVar (v, s')))
        ->    (if u = v then
                 unifySub mflag cD0 cPsi s s'
               else raise (Failure "Front FMVar mismatch"))

      | (Head (Proj (head, k)), Head (Proj (head', k')))
        ->    (if k = k' then
                 unifyFront mflag cD0 cPsi (Head head) (Head head')
               else raise (Failure "Front Proj mismatch"))

      | (Head (FVar x), Head (FVar y))
        -> if x = y then () else raise (Failure "Front FVar mismatch")

      | (Obj tM, Obj tN)
        -> unifyTerm mflag cD0 cPsi (tM, id) (tN, id)

      | (Head head, Obj tN)
      | (Obj tN, Head head)
        -> unifyTerm mflag cD0 cPsi (Root (Syntax.Loc.ghost, head, Nil), id) (tN, id)

      | (Undef, Undef)
        -> ()

      | (_, _)
        -> raise (Failure "Front mismatch")


   and unifyTyp mflag cD0 cPsi sA sB = unifyTypW mflag cD0 cPsi (Whnf.whnfTyp sA) (Whnf.whnfTyp sB)

    and unifyTypW mflag cD0 cPsi sA sB = match (sA, sB) with
      | ((Atom (_, (a, b), tS1), s1),   (Atom (_, (a', b'), tS2), s2))  ->
          if a = a' && b = b' then
            ((* dprint (fun () -> "Unify Atomic types " ^ P.typToString cD0 cPsi sA
                       ^ " == " ^ P.typToString cD0 cPsi sB);*)
            unifySpine mflag cD0 cPsi (tS1, s1) (tS2, s2))
          else
            (dprint (fun () -> "UnifyTyp " ^ P.typToString cD0 cPsi sA ^ " ==== " ^ P.typToString cD0 cPsi sB);
            raise (Failure "Type constant clash"))

      | ((PiTyp ((TypDecl(x, tA1), dep), tA2), s1), (PiTyp ((TypDecl(_x, tB1), _dep), tB2), s2)) ->
          unifyTyp mflag cD0 cPsi (tA1, s1) (tB1, s2) ;
          unifyTyp mflag cD0 (DDec(cPsi, TypDecl(x, tA1))) (tA2, dot1 s1) (tB2, dot1 s2)

      | ((Sigma typ_rec1, s1), (Sigma typ_rec2, s2)) ->
          unifyTypRecW mflag cD0 cPsi (typ_rec1, s1) (typ_rec2, s2)

      | _ ->  raise (Failure "Type mismatch")


    and unifyTypRecW mflag cD0 cPsi srec1 srec2 = match (srec1, srec2) with
      | ((SigmaLast(_, tA1), s1) ,   (SigmaLast(_, tA2), s2)) ->
          (* dprint (fun () -> "[unifyTypRecW] Last "
                          ^ P.typToString cD0 cPsi (tA1, s1)  ^ " == "
                          ^ P.typToString cD0 cPsi (tA2, s2) ^ "\n");*)
          unifyTyp mflag cD0 cPsi (tA1,s1) (tA2,s2)
        (*; dprint (fun () ->  "succeeded   ["
                          ^ P.typRecToString cD0 cPsi srec1
                          ^ "]  ["
                          ^ P.typRecToString cD0 cPsi srec2 ^ "]");*)

      | ((SigmaElem (x1, tA1, trec1),  s1) ,   (SigmaElem (_x2, tA2, trec2), s2))  ->
          ((*dprint (fun () -> "[unifyTypRecW] Elements " ^
                     P.typToString cD0 cPsi (tA1, s1) ^ " == "
                     ^ P.typToString cD0 cPsi (tA2, s2));*)
          unifyTyp mflag cD0 cPsi (tA1,s1) (tA2,s2)
         ;
          let s1' = dot1 s1 in
          let s2' = dot1 s2 in
             unifyTypRecW mflag cD0 (DDec(cPsi, TypDecl(x1, TClo(tA1,s1)))) (trec1,s1') (trec2,s2')
          )

      | ((_, _s1) ,   (_, _s2)) ->
          raise (Failure "TypRec length clash")


   (* Unify pattern fragment, and force constraints after pattern unification
   succeeded *)
    (* Pre-condition: cPsi1, cPsi2 are in normal form *)

    and unifyDCtx1 mflag cD cPsi1 cPsi2 =
    unifyDCtx1' mflag cD (Whnf.cnormDCtx (cPsi1, Whnf.m_id)) (Whnf.cnormDCtx (cPsi2, Whnf.m_id))

 and unifyDCtx1' mflag cD0 cPsi1 cPsi2 = match (cPsi1 , cPsi2) with
      | (Null , Null) -> ()

      | (CtxVar (CInst ((n1, ({contents = None} as cvar_ref1), cD1, CTyp schema1, _, _), theta1)) ,
         CtxVar (CInst ((_n2, ({contents = None} as cvar_ref2), _cD2, CTyp _schema2,  _,_), theta2))) ->
          if cvar_ref1 == cvar_ref2 then
             begin match ( isPatMSub theta1 , isPatMSub theta2) with
                | (true , true ) ->  (if  Whnf.convMSub theta1 theta2 then () else
                   let (mt', cD') = m_intersection (Whnf.cnormMSub theta1)  (Whnf.cnormMSub theta2) cD1 in
                    let cPsi = CtxVar (CInst ((n1, {contents = None}, cD', CTyp schema1, ref [], Maybe), mt')) in
                      instantiateCtxVar (cvar_ref1, cPsi)
                                     )
                | ( _ , _ ) ->
                raise (Error.Violation "Case where we need to unify the same context variables which are associated with different meta-stitutions which are non-patterns is not handled")
              end

          else
            begin match ( isPatMSub theta1 , isPatMSub theta2 ) with
              | (true , true ) ->
                let mtt1 = Whnf.m_invert (Whnf.cnormMSub theta1) in
                  instantiateCtxVar (cvar_ref1, Whnf.cnormDCtx(cPsi2, mtt1))
              | _ -> raise (Error.Violation "Case where both meta-substitutions associated with context variables are not pattern substitutions should not happen and is not implemented for now")
            end

      | (CtxVar (CInst ((_n, ({contents = None} as cvar_ref), _cD, CTyp s_cid, _, _), theta)) , cPsi)
      | (cPsi , CtxVar (CInst ((_n, ({contents = None} as cvar_ref), _cD, CTyp s_cid, _, _), theta) )) ->
          if isPatMSub theta then
            let mtt1 = Whnf.m_invert (Whnf.cnormMSub theta) in
              instantiateCtxVar (cvar_ref, Whnf.cnormDCtx (cPsi, mtt1))
          else
            raise (Error.Violation "Case where both meta-substitutions associated with context variables are not pattern substitutions should not happen and is not implemented for now")

      | (CtxVar cv , CtxVar cv' ) ->
          if cv = cv' then ()
          else
            (dprint (fun () ->" [unifyDCtx] cPsi1 = " ^ P.dctxToString cD0 cPsi1)
          ; dprint (fun () ->" [unifyDCtx] cPsi2 = " ^ P.dctxToString cD0 cPsi2);
             raise (Failure "Bound (named) context variable clash"))

      | (DDec (cPsi1, TypDecl(_y , tA1)) , DDec (cPsi2, TypDecl(_x , tA2))) ->
            (unifyDCtx1' mflag cD0 cPsi1 cPsi2 ;
             dprint (fun () -> "[unifyDCtx] unify type-decl \n");
             dprint (fun () -> "            " ^ P.typToString cD0 cPsi1 (tA1, id)
                       ^ "   ==   " ^ P.typToString cD0 cPsi2 (tA2, id));
            unifyTyp mflag cD0 cPsi1 (tA1, id)   (tA2, id)
            )

      | (DDec (cPsi1, _) , DDec (cPsi2, _ )) ->
            unifyDCtx1' mflag cD0 cPsi1 cPsi2
      | _ ->
          (dprint (fun () -> "Unify Context clash: cPsi1 = " ^
                     P.dctxToString cD0 cPsi1
                     ^ " cPsi2 = " ^ P.dctxToString cD0 cPsi2 ) ;
           raise (Failure "Context clash"))

   (* **************************************************************** *)
  let rec unifyMetaObj cD (mO, t) (mO', t') (cdecl, mt) = 
    let Decl (_u, cT,_) = cdecl in
      unifyMObj cD (mO, t) (mO', t') (cT, mt)

  and unifyClObj' cD mO mO' mT = match (mO, mO', mT) with
    | PObj h , PObj h' , ClTyp (_, cPsi) ->
          unifyHead Unification cD cPsi h h'
    | MObj tR , MObj tR' , ClTyp (_, cPsi) ->
          unifyTerm Unification cD cPsi (tR, id) (tR', id);
    | SObj s , SObj s' , ClTyp (_, cPsi) ->
       unifySub Unification cD cPsi (simplifySub cD cPsi s) (simplifySub cD cPsi s')
    | _ -> (dprint (fun () -> "[unifyMetaObj] fall through");raise (Failure "MetaObj mismatch"))

  and unifyClObj cD (mO, t) (mO', t') (cT, mt) =
   unifyClObj' cD (Whnf.cnormClObj mO t) (Whnf.cnormClObj mO' t') (Whnf.cnormMetaTyp (cT, mt))

  and unifyMFront' cD (mO, t) (mO', t') (cT, mt) = match ((mO, t) , (mO', t')) with
    | (CObj (cPsi), t) , (CObj (cPsi'), t') ->
        unifyDCtx1 Unification cD (Whnf.cnormDCtx (cPsi, t)) (Whnf.cnormDCtx (cPsi', t'))

    | (ClObj (phat, m1), t) , (ClObj (phat', m2) , t') ->
      unifyClObj cD (m1, t) (m2, t') (cT, mt)

    | _ -> (dprint (fun () -> "[unifyMetaObj] fall through");raise (Failure "MetaObj mismatch"))


  and unifyMObj cD (mO, t) (mO', t') (cT, mt) = 
    unifyMFront' cD (Comp.metaObjToMFront mO, t) (Comp.metaObjToMFront mO', t') (cT, mt)

  let rec unifyMetaSpine cD (mS, t) (mS', t') (cK, mt) = match ((mS, t) , (mS', t')) with
    | (Comp.MetaNil, _ ) , (Comp.MetaNil, _ ) -> ()
    | (Comp.MetaApp (mO, mS), t) , (Comp.MetaApp (mO', mS'), t') ->
        let Comp.PiKind (_, cdecl, cK') = cK in
        let mOt = Whnf.cnormMetaObj (mO, t) in
        let _mOt' = Whnf.cnormMetaObj (mO', t') in
          ((* dprint (fun () -> "[unifyMetaObj] BEFORE " ^
                     " cD = " ^ P.mctxToString cD ^ "\n     " ^
                     P.metaObjToString cD mOt' ^ " == " ^
                    P.metaObjToString cD mOt); *)
          unifyMetaObj cD (mO, t) (mO', t') (cdecl, mt);
          (* dprint (fun () -> "[unifyMetaObj] AFTER " ^ P.metaObjToString cD mOt ^ " == " ^
                    P.metaObjToString cD mOt'); *)
          let mt' = MDot (Comp.metaObjToMFront mOt, mt) in
          unifyMetaSpine cD (mS, t) (mS', t') (cK', mt');
          (* dprint (fun () -> "[unifyMetaObj] AFTER UNIFYING SPINES " ^ P.metaObjToString cD mOt ^ " == " ^
                    P.metaObjToString cD mOt') *))

    | _ -> raise (Failure "Meta-Spine mismatch")

 
  let unifyCLFTyp Unification cD ctyp1 ctyp2 = match (ctyp1, ctyp2) with
	  | ClTyp (MTyp tA1, cPsi1) , ClTyp (MTyp tA2, cPsi2) ->
	    unifyDCtx1 Unification cD cPsi1 cPsi2;
	    unifyTyp Unification cD cPsi1 (tA1, id) (tA2, id)
	  | ClTyp (PTyp tA1, cPsi1) , ClTyp (PTyp tA2, cPsi2) ->
	    unifyDCtx1 Unification cD cPsi1 cPsi2;
	    unifyTyp Unification cD cPsi1 (tA1, id) (tA2, id)
	  | ClTyp (STyp cPhi1, cPsi1) , ClTyp (STyp cPhi2, cPsi2) ->
	    unifyDCtx1 Unification cD cPsi1 cPsi2;
	    unifyDCtx1 Unification cD cPhi1 cPhi2
	  | CTyp (schema1) , CTyp (schema2) ->
	    if schema1 = schema2 then () else raise (Failure "CtxPi schema clash")
	  | _ , _ -> raise (Failure "Computation-level Type Clash")


    let rec unifyCompTyp cD tau_t tau_t' =
      unifyCompTypW cD (Whnf.cwhnfCTyp tau_t) (Whnf.cwhnfCTyp tau_t')

    and unifyCompTypW cD tau_t tau_t' = match (tau_t,  tau_t') with
      | ((Comp.TypBase (_, c, mS), t), (Comp.TypBase (_, c', mS'), t')) ->
          if c = c' then
            let tK = (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.kind in
            (unifyMetaSpine cD (mS, t) (mS', t') (tK, Whnf.m_id);
             (* dprint (fun () -> "[unifyCompTyp] " ^
                       P.compTypToString cD (Whnf.cnormCTyp tau_t) ^ " == "  ^
                       P.compTypToString cD (Whnf.cnormCTyp tau_t') )*))

          else
            raise (Failure "Type Constant Clash")

      | ((Comp.TypCobase (_, c, mS), t), (Comp.TypCobase (_, c', mS'), t')) ->
          if c = c' then
            let tK = (Store.Cid.CompCotyp.get c).Store.Cid.CompCotyp.kind in
            (unifyMetaSpine cD (mS, t) (mS', t') (tK, Whnf.m_id);
             (* dprint (fun () -> "[unifyCompTyp] " ^
                       P.compTypToString cD (Whnf.cnormCTyp tau_t) ^ " == "  ^
                       P.compTypToString cD (Whnf.cnormCTyp tau_t') )*) )

          else
            raise (Failure "Type Constant Clash")
      | ((Comp.TypBox (_, ClTyp (MTyp tA, cPsi)), t) , (Comp.TypBox (_, ClTyp (MTyp tA', cPsi')), t')) ->
          let cPsi1 = Whnf.cnormDCtx (cPsi, t) in
          (unifyDCtx1 Unification cD cPsi1 (Whnf.cnormDCtx (cPsi', t'));
           (* dprint (fun () -> "[unifyCompTyp] Unifying contexts done");
           dprint (fun () -> "               cPsi = " ^ P.dctxToString cD cPsi ^
                           "\n               cPsi' = " ^ P.dctxToString cD cPsi');
           dprint (fun () -> "[unifyCompTyp] tA = " ^ P.typToString cD cPsi (Whnf.cnormTyp (tA, t), id));
           dprint (fun () -> "[unifyCompTyp] tA' = " ^ P.typToString cD cPsi' (Whnf.cnormTyp (tA', t'), id)); *)
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

      | ((Comp.TypPiBox ( (Decl(psi, CTyp schema, dep)), tau), t) ,
         (Comp.TypPiBox ( (Decl(_,   CTyp schema', dep')), tau'), t')) ->
          if schema = schema' && dep = dep' then
            unifyCompTyp
              (Dec(cD, Decl (psi, CTyp schema, dep))) (* TODO: Clean this up, merge with case below.
						      Add dep to all Decls? *)
              (tau, Whnf.mvar_dot1 t) (tau', Whnf.mvar_dot1 t')
          else
            raise (Failure "CtxPi schema clash")

      | ((Comp.TypPiBox ((Decl(u, ctyp1,dep)), tau), t),
         (Comp.TypPiBox ((Decl(_, ctyp2,_)), tau'), t')) ->
	let ctyp1n = Whnf.cnormMTyp (ctyp1, t) in
	let ctyp2n = Whnf.cnormMTyp (ctyp2, t') in
	(unifyCLFTyp Unification cD ctyp1n ctyp2n;
	 unifyCompTyp (Dec(cD, Decl(u, ctyp1n,dep))) (tau, Whnf.mvar_dot1 t) (tau', Whnf.mvar_dot1 t'))

      | ((Comp.TypBool, _ ), (Comp.TypBool, _ )) -> ()
      | _ -> raise (Failure "Computation-level Type Clash")


   (* **************************************************************** *)
    let rec unify1 mflag cD0 cPsi sM1 sM2 =
      unifyTerm mflag cD0 cPsi sM1 sM2;
      dprint (fun () -> "Forcing constraint...") ;
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
            | Eqn (cD, cPsi, INorm tM1, INorm tM2) ->
                let _ = solveConstraint cnstr in
(*                let tM1' = Whnf.norm (tM1, id) in
                let tM2' = Whnf.norm (tM2, id) in  *)
                  (dprint (fun () ->  "Solve constraint: " ^ P.normalToString cD cPsi (tM1, id)  ^
                        " = " ^ P.normalToString cD cPsi (tM2, id) ^ "\n");
                   if Whnf.conv (tM1, id) (tM2, id) then dprint (fun () ->  "Constraints are trivial...")
                   else
                     (dprint (fun () ->  "Use unification on them...");
                      unify1 mflag cD cPsi (tM1, id) (tM2, id);
                      dprint (fun () ->  "Solved constraint (DONE): " ^
                                P.normalToString cD cPsi (tM1, id)  ^
                                " = " ^ P.normalToString cD cPsi (tM2, id) ^ "\n"))
                  )
            | Eqn (cD, cPsi, IHead h1, IHead h2)   ->
                let _ = solveConstraint cnstr in
                  (dprint (fun () -> "Solve constraint (H): " ^ P.headToString cD cPsi h1  ^
                        " = " ^ P.headToString cD cPsi h2 ^ "\n");
                  unifyHead mflag cD cPsi h1 h2 ;
                  dprint (fun () -> "Solved constraint (H): " ^ P.headToString cD cPsi h1  ^
                        " = " ^ P.headToString cD cPsi h2 ^ "\n"))
          end )

(*    and forceGlobalCnstr ()      =
      let cnstr = !globalCnstrs in
        (resetGlobalCnstrs ();
        forceGlobalCnstr' cnstr;
        begin match !globalCnstrs with
          | [] -> ()
          | _ -> raise (Failure "Unresolved constraints")
        end)
*)
    and forceGlobalCnstr c_list = match c_list with
      | [ ] -> ()
      | c::cnstrs ->
          match !c with
            | Queued (* in process elsewhere *) -> forceGlobalCnstr cnstrs
            |  Eqn (cD, cPsi, INorm tM1, INorm tM2) ->
                 let _ = solveConstraint c in
                   (dprint (fun () ->  "Solve global constraint:\n") ;
                    dprint (fun () ->  P.normalToString cD cPsi (tM1, id)  ^
                        " = " ^ P.normalToString cD cPsi (tM2, id) ^ "\n");
                    begin try
                      (unify1 Unification cD cPsi (tM1, id) (tM2, id);
                       dprint (fun () ->  "Solved global constraint (DONE): " ^ P.normalToString cD cPsi (tM1, id)  ^
                                 " = " ^ P.normalToString cD cPsi (tM2, id) ^ "\n");
                      forceGlobalCnstr cnstrs)
                    with Failure _ ->
                      let cnstr_string = (P.normalToString cD cPsi (tM1, id)  ^ " =/= " ^ P.normalToString cD cPsi (tM2, id)) in
                      let getLoc tM1 = begin match tM1 with
                        | Root(loc, _, _ ) -> loc
                        | Lam (loc, _ , _ ) -> loc
                        | Tuple (loc, _ ) -> loc  end in
                        raise (GlobalCnstrFailure (getLoc (Whnf.norm (tM1, id)), cnstr_string))
                    end)
            | Eqn (cD, cPsi, IHead h1, IHead h2)   ->
                let _ = solveConstraint c in
                  (dprint (fun () -> "Solve global constraint (H): " ^ P.headToString cD cPsi h1  ^
                        " = " ^ P.headToString cD cPsi h2 ^ "\n");
                   begin try
                     unifyHead Unification cD cPsi h1 h2;
                     dprint (fun () -> "Solved global constraint (H): " ^ P.headToString cD cPsi h1  ^
                            " = " ^ P.headToString cD cPsi h2 ^ "\n");
                      forceGlobalCnstr cnstrs
                   with Failure _ ->
                     let cnstr_string = (P.headToString cD cPsi h1  ^ " =/= " ^ P.headToString cD cPsi h2) in
                     let loc = Syntax.Loc.ghost in
                       raise (GlobalCnstrFailure (loc, cnstr_string))
                   end)
            | Eqn (cD, cPsi, ISub s1, ISub s2) ->
	      let _ = solveConstraint c in
	      begin try
		      (unifySub Unification cD cPsi s1 s2; forceGlobalCnstr cnstrs)
		with Failure _ -> raise (GlobalCnstrFailure (Syntax.Loc.ghost, "s1 =/= s2"))
	      end 


    let unresolvedGlobalCnstrs () =
      begin try
        forceGlobalCnstr (!globalCnstrs);
        resetGlobalCnstrs () ;
        false
      with Failure _ -> resetGlobalCnstrs () ; true
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
       unifyTyp1 mflag cD0 cPsi sA sB;
       dprint (fun () -> "After unifyTyp'");
       dprint (fun () -> "cPsi = " ^ P.dctxToString cD0 cPsi ^ "\n") ;
       dprint (fun () -> "sA = " ^ P.typToString cD0 cPsi sA ^ "\n     ");
       dprint (fun () -> "sB = " ^ P.typToString cD0 cPsi sB))

    let unifyTypRec1 mflag cD0 cPsi sArec sBrec =
      unifyTypRecW mflag cD0 cPsi sArec sBrec;
      forceCnstr mflag (nextCnstr ())

    let unifyTypRec' mflag cD0 cPsi sArec sBrec =
      resetDelayedCnstrs ();
      unifyTypRec1 mflag cD0 cPsi sArec sBrec


    let unify cD0 cPsi sM sN =
      dprint (fun () -> "Unify " ^ P.normalToString cD0 cPsi sM
                      ^ "\n with \n" ^ P.normalToString cD0 cPsi sN);
      unify' Unification cD0 cPsi sM sN;
      dprint (fun () -> "Unify DONE: " ^ P.normalToString cD0 cPsi sM ^ "\n ==  \n" ^ P.normalToString cD0 cPsi sN)

    let unifyH cD phat h h' =
      unifyHead Unification cD (Context.hatToDCtx phat) h h'
   (* **************************************************************** *)


let unify_phat psihat phihat =
  match phihat with
    | (Some (CInst ((n1, ({contents = None} as cref), cD1, CTyp schema1, _, _), theta1 )), d) ->
        begin match psihat with
          | (Some (CInst ((n2, ({contents = None} as cref'), cD2, CTyp schema2, _, _), theta2)) , d') ->
	      if cref == cref' then
                (if  Whnf.convMSub theta1 theta2 then
		   (if d = d' then () else raise (Failure "Hat context mismatch- 1"))
                 else
                   (if isPatMSub theta1 && isPatMSub theta2 then
                      let (mt', cD') = m_intersection (Whnf.cnormMSub theta1)  (Whnf.cnormMSub theta2) cD1 in
                      let cPsi = CtxVar (CInst ((n1, {contents = None}, cD', CTyp schema1, ref [], Maybe), mt')) in
                        instantiateCtxVar (cref, cPsi)
                    else
                      raise (Error.Violation "Case where we need to unify the same context variables which are associated with different meta-stitutions which are non-patterns is not handled")
                ))
	      else
                (if isPatMSub theta1 && isPatMSub theta2 then
                   let mtt1 = Whnf.m_invert (Whnf.cnormMSub theta1) in
		     cref := Some (ICtx (CtxVar (CInst ((n2, cref', cD2, CTyp schema2, ref [], Maybe),  Whnf.mcomp theta2 mtt1 ))))
                 else
                   raise (Error.Violation "Case where we need to unify the context variables which are associated with different meta-stitutions which are non-patterns is not handled"))
          | ((Some (c_var)) , d') ->
              if d = d' then
                cref := Some (ICtx (CtxVar (c_var)))
              else
                (* (Some (cref), d) == (Some cpsi, d')   d' = d0+d  *)
                (if d'< d then raise (Failure "Hat Context's do not unify")
                 else
                   let cPsi = Context.hatToDCtx (Some (c_var), d'-d) in
                     cref := Some (ICtx cPsi))

          | (None , d') ->
              if d = d' then
                cref := Some (ICtx Null)
              else
                (* (Some (cref), d) == (None, d')   d' = d0+d  *)
                (if d'< d then raise (Failure "Hat Context's do not unify")
                 else
                   let cPsi = Context.hatToDCtx (None, d'-d) in
                     cref := Some (ICtx cPsi))

        end

    | _ ->  (if psihat = phihat then () else raise (Failure "Hat context mismatch - 2"))

   (* **************************************************************** *)

    let unifyClObj cPsi m1 m2 = match (m1,m2) with
      | MObj tM1, MObj tM2 -> unify Empty cPsi (tM1, id) (tM2, id)
      | PObj h, PObj h' -> unifyHead Unification Empty cPsi h h'
    let unifyMFront m1 m2 = match (m1,m2) with
      | CObj cPsi, CObj cPhi -> unifyDCtx1 Unification Empty 
         (Whnf.cnormDCtx (cPsi, Whnf.m_id)) (Whnf.cnormDCtx (cPhi, Whnf.m_id))
      | ClObj (phat1, m1), ClObj (phat2, m2) ->
	(* unify_phat phat1 phat2; *)
	unifyClObj (Context.hatToDCtx phat1) m1 m2
    let rec unifyMSub' ms mt = match (ms, mt) with
      | (MShift k, MShift k') ->  if k = k' then ()
        else raise (Failure "Contextual substitutions not of the same length")
      | (MDot (mFt , ms), MShift k) 
      | (MShift k , MDot (mFt, ms)) ->
	  unifyMFront mFt (MV (k+1));
          unifyMSub' ms (MShift (k+1))
      | (MDot (mF1, ms'), MDot (mF2, mt')) ->
          (unifyMFront mF1 mF2 ;
           unifyMSub' ms' mt')

    let unifyMSub ms mt = unifyMSub' (Whnf.cnormMSub ms) (Whnf.cnormMSub mt)

    let unifyTypRec cD0 cPsi sArec sBrec =
        unifyTypRec' Unification cD0 cPsi sArec sBrec

    let unifyTyp cD0 cPsi sA sB =
      unifyTyp' Unification cD0 cPsi sA sB


    let unifyDCtx cD0 cPsi1 cPsi2 =
      let cPsi1' = Whnf.cnormDCtx (cPsi1, Whnf.m_id) in
      let cPsi2' = Whnf.cnormDCtx (cPsi2, Whnf.m_id) in
         unifyDCtx1 Unification cD0 cPsi1' cPsi2'


    let matchTerm cD0 cPsi sM sN =
      unify' Matching cD0 cPsi sM sN

    let matchTypRec cD0 cPsi sArec sBrec =
        unifyTypRec' Matching cD0 cPsi sArec sBrec

    let matchTyp cD0 cPsi sA sB =
      unifyTyp' Matching cD0 cPsi sA sB

    let unifyMetaObj cD (cM, ms) (cM', ms') (mT, mt) = 
      unifyMObj cD (cM, ms) (cM', ms) (mT, mt)

    let unifyMetaTyp cD (mT, ms) (mT', ms') = 
	unifyCLFTyp Unification cD (Whnf.cnormMetaTyp (mT, ms))
 	                           (Whnf.cnormMetaTyp (mT', ms'))


    let unifyCompTyp cD ttau ttau' =
      begin try
        unifyCompTyp cD ttau ttau'
      with Failure msg ->
        (dprint (fun () -> "[unifyCompTyp " ^ msg) ;
         raise (Failure msg))
      end
end


module EmptyTrail = Make (EmptyTrail)
module StdTrail   = Make (StdTrail)
