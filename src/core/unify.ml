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

  (* val unifyCDecl   : mctx -> (ctyp_decl * LF.msub) -> (ctyp_decl * LF.msub) -> unit *)
  (* val unifyMTyp    : mctx -> ctyp  -> ctyp ->  unit *)
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
  val pruneDCtx : mctx -> dctx ->  msub -> cvarRef -> dctx
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
    let _ = dprint (fun () -> "[genMMVarstr] of type " ^ P.typToString cD cPsi (tP,s)) in 
    let _ = dprint (fun () -> "     in context cPsi = " ^ P.dctxToString cD cPsi) in
    let (cPhi, conv_list) = ConvSigma.flattenDCtx cD cPsi in
    let s_proj = ConvSigma.gen_conv_sub conv_list in
    let s_tup    = ConvSigma.gen_conv_sub' conv_list in
    (* let tQ    = ConvSigma.strans_typ cD cPsi (tP, s) conv_list in*)
    let tQ = Whnf.normTyp (tP, Substitution.LF.comp s s_tup) in 
    (*  cPsi |- s_proj : cPhi
        cPhi |- s_tup : cPsi       
        cPhi |- tQ   where  cPsi |- tP  !! tQ = [s_tup]tP !!  *)

    let _ = dprint (fun () -> "[genMMVarstr] flattened type " ^ P.typToString cD cPhi (tQ,Substitution.LF.id)) in 
    let _ = dprint (fun () -> "     in context cPhi = " ^ P.dctxToString cD cPhi) in
    let (ss', cPhi') = Subord.thin' cD a cPhi in
    let _ = dprint (fun () -> "     thinned context cPhi' = " ^ P.dctxToString cD cPhi') in

      (* cPhi |- ss' : cPhi' *)
    let ssi' = Substitution.LF.invert ss' in
      (* cPhi' |- ssi : cPhi *)
      (* cPhi' |- [ssi]tQ    *)
    let u = Whnf.newMMVar None (cD, cPhi', TClo(tQ,ssi')) Maybe in
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
	  | EmptySub                -> true
	  | Undefs                  -> true
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
        | e -> (dprint (fun () -> "?? " ) ; unwind (); raise e )

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

  let expandMVarAtType loc (v,(mt,s)) = function
    | MTyp _ -> INorm (Root (loc, MMVar ((v,mt),s), Nil))
    | PTyp _ -> IHead (MPVar ((v,mt),s))
    | STyp _ -> ISub (MSVar (0, ((v,mt),s)))

  let instantiateMMVarWithMMVar r loc mm tp cnstrL =
    instantiateMMVar' (r, expandMVarAtType loc mm tp, cnstrL)

  let instantiateCtxVar (ctx_ref, cPsi) =
    ctx_ref := Some (ICtx cPsi);
    T.log globalTrail (InstI ctx_ref)

  let instantiateMVar (u, tM, cnstrL) =
    instantiateMMVar' (u, INorm (Whnf.norm (tM, id)), cnstrL)

  let instantiateMMVar (u, tM, cnstrL) =
    instantiateMMVar' (u, INorm tM, cnstrL)

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

  let simplifySub cD0 cPsi sigma = sigma

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

(*    | (EmptySub, EmptySub , Null) -> (EmptySub, Null)  *)
    | (EmptySub, _ , Null) -> (EmptySub, Null) 
    | (_, EmptySub , Null) -> (EmptySub, Null) 

    | (Undefs, _ , _) | (_ , Undefs, _) -> (EmptySub, Null)
    (* all other cases impossible for pattern substitutions *)

    | (_s1, _s2, _cPsi )  -> 
         raise (Error ("Intersection of substitutions is not defined")) 
	 
(*           raise (Error ("Intersection not defined - s1 = " ^ 
			   (P.subToString Empty  (Context.hatToDCtx phat) s1) ^ 
		           "s2 = " ^ 
			   (P.subToString Empty  (Context.hatToDCtx phat) s2)))
*)
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

   (* finds the context variable part of a (inverse) substitution *)
   and shiftInvSub n ss = match ss with
	| Undefs -> raise (Failure "Variable dependency")
	| Shift k -> Shift (n+k)
        | Dot (ft, ss') -> shiftInvSub (n-1) ss'
      
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

    | (Shift n, CtxVar _psi) -> shiftInvSub n ssubst

    | (SVar (s, 0, sigma), CtxVar psi) ->
        (* other cases ? -bp *)
        let (s,cPhi, cPsi') = (match applyMSub s ms with
                                           | MV v -> let (_, cPhi, _, cPsi') =
                                               Whnf.mctxSDec cD0  v in (v, cPhi, cPsi')
                                           | MUndef -> raise NotInvertible
                                        ) in

        let _ = dprint (fun () -> "[invSub]" ^ P.dctxToString cD0 (Context.hatToDCtx phat) ^ " |- "
        ^ P.subToString cD0 (Context.hatToDCtx phat) sigma ^ " : " ^
        P.dctxToString cD0 cPsi') in

        SVar(s, 0, invSub cD0 phat (sigma, cPsi') ss rOccur)
    | (MSVar (0, (((_,{contents=None},cD, ClTyp (STyp (_, cPsi'),cPhi), _, _) as s0, mt),sigma)), CtxVar psi) ->
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
                let (_, cPhi, _, cPsi1) = Whnf.mctxSDec cD0  v  in
                  (* applyMSub to ctx_offset ? *)
                SVar(v, ( n), invSub cD0 phat (t, cPsi1) ss rOccur)
            | MUndef -> raise NotInvertible
          end
    | (FSVar (n, (s_name, t)), cPsi1) ->
        (dprint (fun () -> "invSub FSVar");
        let (_, Decl (_, ClTyp (STyp (LF.Subst , _cPhi),  cPsi'), _)) = Store.FCVar.get s_name in
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
    | (MDot (ClObj (phat, SObj sigma), mt'), Dec(cD', Decl (_ , ClTyp (STyp (_, cPhi), _cPsi), _)))   ->
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
            cD0        |- ms : cD
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
    let (ms,s) = ss in
    dprint (fun () -> "Pruning term: "
		      ^ P.normalToString cD0 (Context.hatToDCtx phat) sM
                    ^ " with inv. sub: " ^ P.subToString cD0 cPsi' s);
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

    | (Root (loc, head, tS), s) ->
      let Shift 0 = s in (* Assert s is supposed to be the identity *)
      let newHead = pruneHead cD0 cPsi' (loc,head) ss rOccur in
      Root (loc, newHead, pruneSpine cD0 cPsi' phat (tS, s) ss rOccur)

  and pruneBoth cD0 cPsi' ((mt,ts), (cD1, cPsi1)) ((ms,_) as ss) rOccur =
    let (id_msub, cD2) = pruneMCtx cD0 (mt, cD1) ms in
    let i_msub = Whnf.m_invert (Whnf.mcomp id_msub mt) in
    let i_id_msub = Whnf.m_invert id_msub in
    let cPsi1' = Whnf.cnormDCtx (cPsi1, i_id_msub) in
    let t'  = Whnf.cnormSub (Whnf.normSub ts, i_msub) in
    let cPsi'' = Whnf.cnormDCtx (cPsi', i_msub) in
    let (idsub, cPsi2) = pruneSub  cD2 cPsi'' (Context.dctxToHat cPsi') (t', cPsi1') ss rOccur in
    let cPsi2' = Whnf.cnormDCtx (cPsi2, i_msub) in
    ((id_msub,idsub), (cD2, cPsi2'))

  and normClTyp2 (tp,(mt,t)) = Whnf.normClTyp (Whnf.cnormClTyp (tp, mt), t)
  and invert2 (mt,t) = (Whnf.m_invert mt, invert t)
  and comp2 (mt,t) (ms,s) = (Whnf.mcomp mt ms, comp (Whnf.cnormSub (t,ms)) s)

  (* Note similarity between the following two functions *)
  and pruneMMVarInst cD0 cPsi' loc (n, r, cD1, ClTyp (tp,cPsi1), cnstrs, mdep) mtt ss rOccur = 
    if eq_cvarRef (MMVarRef r) rOccur then
       raise (Failure "Variable occurrence")
    else
      let (id2,(cD2,cPsi2')) = pruneBoth cD0 cPsi' (mtt,(cD1,cPsi1)) ss rOccur in
      let tP' = normClTyp2 (tp, invert2 id2) in
      let v = Whnf.newMMVar' (Some n) (cD2, ClTyp (tP', cPsi2')) mdep  in
      let _  = instantiateMMVarWithMMVar r loc (v, id2) tP' !cnstrs in
      let (mr,r) = comp2 (comp2 id2 mtt) ss in
      ((v, mr), r)

  and pruneMVarInst cD0 cPsi' loc (n, r, _cD, ClTyp (MTyp tP,cPsi1), cnstrs, mdep) t ((ms, ssubst) as ss) rOccur = 
    if eq_cvarRef (MMVarRef r) rOccur then
      raise (Failure "Variable occurrence")
    else
      let (idsub, cPsi2) = pruneSub  cD0 cPsi' (Context.dctxToHat cPsi') (t, cPsi1) ss rOccur in
      let tP' = Whnf.normTyp (tP, invert idsub) in
      let v = Whnf.newMVar (Some n) (cPsi2, tP')  mdep in
      let _ = instantiateMVar (r, Root (loc, MVar (v, idsub), Nil), !cnstrs) in
      (v, comp (comp idsub t) ssubst)

  and pruneFVar cD0 cPsi (u,t) ((ms, ssubst) as ss) rOccur = 
   let (cD_d, Decl (_, ClTyp (_, cPsi1), _)) = Store.FCVar.get u in
   let d = Context.length cD0 - Context.length cD_d in
   let cPsi1 = if d = 0 then cPsi1 else Whnf.cnormDCtx (cPsi1, MShift d) in
   let t' = simplifySub cD0 cPsi t in
   let s' = invSub cD0 (Context.dctxToHat cPsi) (t', cPsi1) ss rOccur in
   (u, s')

  and pruneBoundMVar cD0 cPsi u t ((ms, ssubst) as ss) rOccur = match applyMSub u ms with
   | MV v ->
     let (_, ClTyp (_, cPsi1)) = Whnf.mctxLookup cD0 v in
     let t' = simplifySub cD0 cPsi t in
     let s' = pruneSubst cD0 cPsi (t' , cPsi1) ss rOccur in
     (v,s')
   | MUndef -> raise (Failure "[Prune] Bound MVar dependency")

  and pruneHead cD0 cPsi' (loc,head) ((ms, ssubst) as ss) rOccur =
   match head with
    | MMVar ((i, mt), t) ->
      MMVar (pruneMMVarInst cD0 cPsi' loc i (mt,t) ss rOccur)
    | MVar (Inst i, t) ->
      MVar (pruneMVarInst cD0 cPsi' loc i (Whnf.normSub t) ss rOccur)
    | MVar (Offset u, t) ->
      let (v,s') = pruneBoundMVar cD0 cPsi' u t ss rOccur in
      MVar (Offset v, s')
    | FMVar ut  -> FMVar (pruneFVar cD0 cPsi' ut ss rOccur)
    | FPVar pt ->
      begin try
       FPVar (pruneFVar cD0 cPsi' pt ss rOccur)
	with  Not_found -> (* Huh? *)
         if isId ssubst && isMId ms  then head
         else raise (Failure ("[Prune] Free parameter variable to be pruned with non-identity substitution"))
      end
    | PVar (p, t) -> PVar (pruneBoundMVar cD0 cPsi' p t ss rOccur)
    | Proj (h, i) -> Proj (pruneHead cD0 cPsi' (loc, h) ss rOccur, i)
    | MPVar ((i, mt), t) -> MPVar (pruneMMVarInst cD0 cPsi' loc i (mt,t) ss rOccur)
    | BVar k ->
       begin match bvarSub k ssubst with
        | Undef -> raise (Failure ("[Prune] Bound variable dependency : " ^
                                                      "head = " ^ P.headToString cD0 cPsi' head))
        | Head (BVar _k as h') -> h'
       end
    | Const _ as h -> h
    | FVar _ as h ->  h

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
    | (Undefs , Null) -> EmptySub
    | (Shift (n), DDec(_cPsi', _dec)) ->
        pruneSubst cD cPsi (Dot (Head (BVar (n + 1)), Shift ( n + 1)), cPsi1) ss rOccur
    | (Shift (_n), Null) -> EmptySub

    | (Shift (n), CtxVar psi) ->
       let (mt, s') = ss in
       shiftInvSub n s'
    | (SVar (sv, (n), sigma), cPsi1) ->
      let (sv', s') = pruneBoundMVar cD cPsi sv sigma ss rOccur in
      SVar (sv', n, s')

    | (FSVar (n, ns), cPsi1) -> FSVar (n, pruneFVar cD cPsi ns ss rOccur)

    | (MSVar (n, ((i,mt),t)), cPsi1) ->
       MSVar (n, pruneMMVarInst cD cPsi Syntax.Loc.ghost i (mt,t) ss rOccur)

    | (Dot (ft, s'), DDec(cPsi', _dec)) ->
       Dot (pruneFront cD cPsi ft ss rOccur, pruneSubst cD cPsi (s', cPsi') ss rOccur)

    | (Dot (_, _), _) | (EmptySub, _)
       -> raise (Error.Violation "Badly typed substitution")


  and pruneFront cD cPsi ft ss rOccur = match ft with
    | Obj tM -> Obj (prune cD cPsi (Context.dctxToHat cPsi) (tM, id) ss rOccur)
    | Head h -> Head (pruneHead cD cPsi (Syntax.Loc.ghost, h) ss rOccur)

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
        | MV v -> let (_, _cPhi, _, cPsi') = Whnf.mctxSDec cD0  v in cPsi'
        | MUndef -> raise NotInvertible
      ) in

      let _ = invSub cD0 phat (sigma, cPsi') ss rOccur  in
      let _ = dprint (fun () -> "[pruneSub] result = " ^
                       P.subToString cD0 cPsi (comp s' (SVar (s, cshift, sigma)))) in

      (s',cPsi1')

    | (MSVar (cshift, ((s, _theta),sigma)), cPsi1) ->
      let s' , cPsi1' = (id, cPsi1) in

      let (_ ,{contents=None}, _cD, ClTyp (STyp (_, cPhi2), cPhi1), _cnstrs, _) = s in
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

        let (_, Decl (_, ClTyp (STyp (_, _cPhi),  cPsi'),_)) = Store.FCVar.get s in
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


  and pruneDCtx cD cPsi ms rOccur = match cPsi with
    | Null -> Null
    | CtxVar (CtxOffset psi) ->
        begin match applyMSub psi ms with
          | CObj (cPsi') -> Whnf.normDCtx cPsi'
          | MV k -> CtxVar (CtxOffset k)
        end

    | CtxVar (CInst ((_n, ({contents = None}), _schema,  _mctx, _cnstr,_ ),_theta)) ->
  	cPsi

    | CtxVar (CInst ((_n, {contents = Some (ICtx cPhi)} ,_schema, _mctx, _cnstr,_),theta)) ->
  	pruneDCtx cD cPhi (Whnf.mcomp theta ms) rOccur

    | CtxVar _ -> cPsi

    | DDec(cPsi, TypDecl (x, tA)) ->
  	let cPsi' = pruneDCtx cD cPsi ms rOccur in
  	let tA' = pruneTyp cD cPsi' (Context.dctxToHat cPsi')
       	                  (tA, Substitution.LF.id) (ms, Substitution.LF.id) rOccur in
  	  DDec (cPsi', TypDecl (x, tA'))


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

  let rec unifyTerm  mflag cD0 cPsi sN sM =
    dprint (fun () -> "Unifying terms: " ^ P.normalToString cD0 cPsi sN ^ " =?= " ^ P.normalToString cD0 cPsi sM);
    unifyTerm'  mflag cD0 cPsi (Whnf.norm (Whnf.whnf sN)) (Whnf.norm (Whnf.whnf sM))

  and unifyTuple mflag cD0 cPsi sTup1 sTup2 = match (sTup1, sTup2) with
    | ((Last tM, s1) ,  (Last tN, s2)) ->
      unifyTerm mflag cD0 cPsi (tM, s1) (tN, s2)
    | ((Cons (tM, tup1), s1), (Cons (tN, tup2), s2)) ->
      (unifyTerm mflag cD0 cPsi (tM, s1) (tN, s2);
       unifyTuple mflag cD0 cPsi (tup1, s1) (tup2, s2))

  and unifyMVarTerm cD0 cPsi (_n1, r1,  cD, ClTyp (_, cPsi1), cnstrs1, mdep1) t1' sM2 = 
    begin try
     let ss1  = invert (Whnf.normSub t1') (* cD ; cPsi1 |- ss1 <= cPsi *) in
     let phat = Context.dctxToHat cPsi in
     let tM2' = trail (fun () -> prune cD0 cPsi1 phat (sM2,id) (MShift 0, ss1) (MMVarRef r1)) in
     instantiateMVar (r1, tM2', !cnstrs1)
     with NotInvertible -> raise (Error.Violation "Unification violation")
       (* This might actually need to add a constraint, in which case "NotInvertible" seems
          the wrong kind of exception... *)
    end 

  and pruneITerm cD cPsi (hat, tm) ss rOccur = match tm with
    | INorm n , _        -> INorm (prune cD cPsi hat (n,id) ss rOccur)
    | IHead h , _        -> IHead (pruneHead cD cPsi (Syntax.Loc.ghost, h) ss rOccur)
    | ISub s , STyp (_, cPhi) -> ISub (pruneSubst cD cPsi (s,cPhi) ss rOccur)

  and unifyMMVarTerm cD0 cPsi (_, r1, cD, ClTyp (tp, cPsi1), cnstrs1, mdep1) mt1 t1' sM2 = 
    begin (* try *)
      let ss1  = invert t1' in
      let ss1  = Whnf.cnormSub (ss1, Whnf.m_id) in
      (* cD ; cPsi1 |- ss1 <= cPsi *)
      let mtt1 = Whnf.m_invert (Whnf.cnormMSub mt1) in
      let tp' = Whnf.cnormClTyp (tp, mt1) in
      let hat = Context.dctxToHat cPsi in 
      let tM2' = trail (fun () -> pruneITerm cD cPsi1 (hat, (sM2,tp')) (mtt1, ss1) (MMVarRef r1)) in

      instantiateMMVar' (r1, tM2', !cnstrs1);
      (* with NotInvertible -> raise (Error.Violation "Unification violation") *)
       (* This might actually need to add a constraint, in which case "NotInvertible" seems
          the wrong kind of exception... *)
    end


  (* unifyMMVarTermProj cD0 cPsi  (_, r1, cD, ClTyp (_, cPsi1),  cnstrs1, mdep1) mt1 t1' sM2 = ()

    Pre-conditions:
        cD0 ; cPsi |- sM2  
        cD0 |- mt : cD
        cD0 ; cPsi |- t1' : cPsi1

            ; cPsi1 |-     : cPsi

   *)
  and unifyMMVarTermProj cD0 cPsi (_, r1, cD, ClTyp (_, cPsi1), cnstrs1, mdep1) mt1 t1' tM2 =
     begin 
       let mtt1 = Whnf.m_invert (Whnf.cnormMSub mt1) in
       (* cD |- mtt1 : cD0 *) 
       let _ = dprint (fun () -> ("[unifyMMVarTermProj] cPsi = " ^ 
				    P.dctxToString cD0 cPsi ^ "\n")) in
       let _ = dprint (fun () -> ("[unifyMMVarTermProj] sM2 = " ^ 
				    P.normalToString cD0 cPsi (tM2,id) ^ "\n")) in
       let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cD0 cPsi in
       let _ = dprint (fun () -> ("[unifyMMVarTermProj] flat_cPsi = " ^ 
				    P.dctxToString cD0 flat_cPsi ^ "\n")) in
       let phat = Context.dctxToHat flat_cPsi in
       let t_flat = ConvSigma.strans_sub cD0 cPsi t1' conv_list in
       (*   flat_cPsi |- t_flat : cPsi   *)
       let tM2'   = ConvSigma.strans_norm cD0 cPsi (tM2,id) conv_list in
       let _ = dprint (fun () -> ("[unifyMMVarTermProj] sM2' = " ^ 
				    P.normalToString cD0 flat_cPsi (tM2', id) ^ "\n")) in
       (*   flat_cPsi |- tM2'    *)
       let ss = invert t_flat in
       (*  cPsi   |- ss : flat_cPsi *) 
       (* let ss1  = invert t1' in
       (*  cPsi1 |- ss1 : cPsi *)
       let _ss1  = Whnf.cnormSub (ss1, Whnf.m_id) in *)
       let sM2' =
	 trail (fun () -> prune cD cPsi1 phat (tM2', id) (mtt1, ss) (MMVarRef r1)) in 
      (* let sM2' =
	 trail (fun () -> prune cD cPsi1 phat (tM2', id) (mtt1, comp ss ss1) (MMVarRef r1)) in *)
       instantiateMMVar (r1, sM2', !cnstrs1)
     end

  and unifyMMVarMMVar cPsi loc (((n1, r1,  cD1, ClTyp (tp1, cPsi1), cnstrs1, _), mt1), t1') 
                               ((_, mt2), t2') =
    let (s', cPsi') = intersection (Context.dctxToHat cPsi) (Whnf.normSub t1') (Whnf.normSub t2') cPsi1 in
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
        * Since we can't create m-closures, we need to normalize here. *)
		    
    let cPsi_n = Whnf.cnormDCtx (cPsi', mtt') in
    let tp1'  = normClTyp2 (tp1, (mtt',ss')) in

    let w = Whnf.newMMVar' (Some n1) (cD', ClTyp (tp1', cPsi_n)) Maybe in
                      (* w::[s'^-1](tP1)[cPsi'] in cD'            *)
                      (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tP1)
                         [|w[s']/u|](u[t1]) = [t1](w[s'])
                         [|w[s']/u|](u[t2]) = [t2](w[s'])
                      *)
     instantiateMMVarWithMMVar r1 loc (w, (mt', s')) tp1' !cnstrs1

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

                    let w = Whnf.newMVar None (cPsi', TClo(tP1, ss')) mdep1 in
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
    | (((Root (loc1, MMVar (((_, r1, _, _, cnstrs1, _), mt1), t1 as q1), Nil))),
       (((Root (_, MMVar (((_, r2, _, _, _, _), mt2), t2 as q2), Nil)))))
       when r1 == r2 ->
        dprnt "(010) MMVar-MMVar";
        (* by invariant of whnf:
           meta^2-variables are lowered during whnf, s1 = s2 = id
           r1 and r2 are uninstantiated  (None)
        *)
       begin
            match (isPatMSub mt1, isPatSub t1 , isPatMSub mt2, isPatSub t2) with
              | (true, true, true, true) ->
		unifyMMVarMMVar cPsi loc1 q1 q2
              | (_, _, _, _) ->
                  addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, INorm sN, INorm sM)))
       end  
    | (((Root (_, MMVar (((_,_,_,_,cnstrs1,_) as i, mt1), t1), Nil))) as sM1,
       (((Root (_, MMVar ((i', mt2), t2), Nil))) as sM2)) -> dprint (fun () -> "(case 0)");
	begin try
            begin match (isPatMSub mt1, isPatSub t1 , isPatMSub mt2, isPatSub t2) with
              | (true, true, _, _) -> dprint (fun () -> "(case 1)");
		unifyMMVarTerm cD0 cPsi i mt1 t1 (INorm sM2)
              | (_ , _, true, true) -> dprint (fun () -> "(case 2)");
		unifyMMVarTerm cD0 cPsi i' mt2 t2 (INorm sM1)
              | (_ , _ , _ , _) -> dprint (fun () -> "(case 3)");
                  begin match (isPatMSub mt1, isProjPatSub t1 , isPatMSub mt2, isProjPatSub t2) with
                    | ( _ , _, true, true ) ->
		      unifyMMVarTermProj cD0 cPsi i' mt2 t2 sM1
                    | ( true, true , _ , _ ) ->
		      unifyMMVarTermProj cD0 cPsi i mt1 t1 sM2
                    | _ -> addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, INorm sM1, INorm sM2)))
                  end
            end
	with NotInvertible -> addConstraint (cnstrs1, ref (Eqn (cD0, cPsi, INorm sM1, INorm sM2)))
	end 

    (* MMVar-normal case *)
    | ((Root (loc, MMVar (((_n, r, cD,  ClTyp (MTyp tP,cPsi1), cnstrs, mdep) as i, mt), t), _tS)) as sM1, sM2)
    | (sM2, ((Root (loc, MMVar (((_n, r, cD, ClTyp (MTyp tP,cPsi1), cnstrs, mdep) as i, mt), t), _tS)) as sM1)) ->
        dprnt "(011) MMVar-_";
        if blockdeclInDctx (Whnf.cnormDCtx (cPsi1, Whnf.m_id)) then
          (dprnt "(011) - blockinDCtx";
          let tN = genMMVarstr loc cD cPsi1 (tP, id) in
            instantiateMMVar (r, tN,!cnstrs);
            unifyTerm mflag cD0 cPsi (sM1,id) (sM2,id))
        else
        let _ = dprint (fun () -> "cPsi = " ^ P.dctxToString cD0 cPsi) in
        let _ = dprint (fun () -> "t' = " ^ P.subToString cD0 cPsi t) in
        let _ = dprint (fun () -> "mt = " ^ P.msubToString cD0 mt) in
            if isProjPatSub t && isPatMSub mt then
              begin try
	       (dprint (fun () -> "Callin unifyMMVarTermProj ...");
		unifyMMVarTermProj cD0 cPsi i mt t sM2)
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
        else 
	  (dprint (fun () -> "[unifyHead] cD0 = " ^ P.mctxToString cD0 );
	   raise (Failure "Bound MVar clash"))

    | (FMVar (u, s) , FMVar(u', s')) ->
        if u = u' then unifySub mflag cD0 cPsi s s'
        else raise (Failure "Bound FMVar clash'")

    | (FPVar (q, s), FPVar (p, s'))
        ->   (if p = q then
                unifySub mflag cD0 cPsi s s'
              else raise (Failure "Front FPVar mismatch"))

    | (PVar (k, s) , PVar(k', s')) ->
        if k = k' then
           unifySub mflag cD0 cPsi s s'
        else raise (Failure "Parameter variable clash")

    (* MPVar - MPVar *)
    | (MPVar (((_, q1, _, _, cnstr1, _), mt1), s1 as i1) ,
       MPVar (((_, q2, _, _, _     , _), mt2), s2 as i2) )
       when q1 == q2 ->
        (* check s1' and s2' are pattern substitutions; possibly generate constraints;
           check intersection (s1', s2'); possibly prune *)
          (match (isPatMSub mt1, isPatSub s1,  isPatMSub mt2, isPatSub s2) with
            | ( true, true, true, true ) -> unifyMMVarMMVar cPsi Syntax.Loc.ghost i1 i2
            | (_, _, _, _) ->
                addConstraint (cnstr1, ref (Eqn (cD0, cPsi, IHead head2, IHead head1)))
           )
    | (MPVar (((_, q1, _, ClTyp (PTyp tA1,cPsi1), cnstr1, _) as q1', mt1), s1) ,
       MPVar (((_, q2, _, ClTyp (PTyp tA2,cPsi2), _     , _) as q2', mt2), s2) ) ->
      begin match (isPatMSub mt1, isPatSub s1, isPatMSub mt2, isPatSub s2) with
            | (true, true, _, _) ->
             unifyTyp mflag cD0 cPsi (tA1, s1) (tA2, s2);
	     unifyMMVarTerm cD0 cPsi q1' mt1 s1 (IHead head2)

            | (_, _, true , true ) ->
              unifyTyp mflag cD0 cPsi (tA1, s1) (tA2, s2);
	      unifyMMVarTerm cD0 cPsi q2' mt2 s2 (IHead head1)

            | (_, _, _ , _ ) ->
                 addConstraint (cnstr1, ref (Eqn (cD0, cPsi, IHead head1, IHead head2)))
      end

    | (MPVar (((_n1, q1, cD1, ClTyp (PTyp tA1,cPsi1), cnstr1, mDep) as i, mt1), s1) , h) 
    | (h, MPVar (((_n1, q1, cD1, ClTyp (PTyp tA1,cPsi1), cnstr1, mDep) as i, mt1), s1) ) ->
        (* ?#p[mt1, s1] ==  BVar k    or     ?#p[mt1, s1] = PVar (q, s) *)
        dprnt "(013) _-MPVar - head";
      if isVar h && isPatSub s1 && isPatMSub mt1 then
	unifyMMVarTerm cD0 cPsi i mt1 s1 (IHead h)
        else
          raise (Failure "Cannot instantiate PVar with a head which is not guaranteed to remain a variable")

    | (PVar _  , Proj (PVar _, _))
    | (Proj (PVar _, _), PVar _) ->
        (print_string "[UnifyHead] Projection of a parameter variable\n";
         raise (Failure "PVar i =/= Proj PVar"))

    | (Proj (h1, i1),  Proj (h2, i2)) ->
        if i1 = i2 then
          unifyHead mflag cD0 cPsi h1 h2
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

      | ( MSVar (_, ((((_, r1, _, _, _, _), mt1), t1) as q1))
        , MSVar (_, ((((_, r2, _, _, _, _), mt2), t2) as q2)))
	  when r1 == r2 && isPatMSub mt1 && isPatSub t1 && isPatMSub mt2 && isPatSub t2 ->
	unifyMMVarMMVar cPsi Syntax.Loc.ghost q1 q2

      | (MSVar (_n, ((q, mt), s)), s2)
	  when isPatSub s && isPatMSub mt -> unifyMMVarTerm cD0 cPsi q mt s (ISub s2)
      | (s2, MSVar (_n, ((q, mt), s)))
          when isPatSub s && isPatMSub mt -> unifyMMVarTerm cD0 cPsi q mt s (ISub s2)
       
      | (MSVar (_, (((_,_,_,_,cnstrs,_),_),_)) , _ )
      | ( _ , MSVar (_, (((_,_,_,_,cnstrs,_),_),_)))
        -> addConstraint (cnstrs, ref (Eqn (cD0, cPsi, ISub s1, ISub s2)))

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
         CtxVar (CInst ((_n2, ({contents = None} as cvar_ref2), _cD2, CTyp schema2,  _,_), theta2))) ->
          if cvar_ref1 == cvar_ref2 then
	    (if schema1 = schema2 then 
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
	      raise (Error.Violation "Schema mismatch")
	    )
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

  let unifyClTyp Unification cD cPsi = function
    | MTyp tA1, MTyp tA2 -> unifyTyp Unification cD cPsi (tA1, id) (tA2, id)
    | PTyp tA1 , PTyp tA2 -> unifyTyp Unification cD cPsi (tA1, id) (tA2, id)
    | STyp (_, cPhi1) , STyp (_, cPhi2) -> unifyDCtx1 Unification cD cPhi1 cPhi2 
  let unifyCLFTyp Unification cD ctyp1 ctyp2 = match (ctyp1, ctyp2) with
    | ClTyp (tp1, cPsi1) , ClTyp (tp2, cPsi2) ->
       unifyDCtx1 Unification cD cPsi1 cPsi2;
       unifyClTyp Unification cD cPsi1 (tp1,tp2)
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
	(unifyTerm mflag cD0 cPsi sM1 sM2;
	dprint (fun () -> "Forcing constraint...") ;
	forceCnstr mflag (nextCnstr ()))


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
                (* let tM1 = Whnf.norm (tM1, id) in
                   let tM2 = Whnf.norm (tM2, id) in   *)
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

    and forceGlobalCnstr cnstr      =
        (resetGlobalCnstrs ();
        forceGlobalCnstr' cnstr;
        begin match !globalCnstrs with
          | [] -> ()
          | _ -> raise (Failure "Unresolved constraints")
        end)

    and forceGlobalCnstr' c_list = match c_list with
      | [ ] -> ()
      | c::cnstrs ->
          match !c with
            | Queued (* in process elsewhere *) -> forceGlobalCnstr cnstrs
            |  Eqn (cD, cPsi, INorm tM1, INorm tM2) ->
                 let _ = solveConstraint c in
		 let l = List.length (!globalCnstrs) in 
                   (dprint (fun () ->  "Solve global constraint:\n") ;
                    dprint (fun () ->  P.normalToString cD cPsi (tM1, id)  ^
                        " = " ^ P.normalToString cD cPsi (tM2, id)
			^ "\n");
		    if Whnf.conv (tM1, id) (tM2, id) then 
		      (* Note: we test whether tM1 and tM2 are 
		         convertible because some terms which fall
                         outside of the pattern fragment are convertible,
                         but not unifiable *)        
		      forceGlobalCnstr' cnstrs
		    else 
                    begin try
                      (unify1 Unification cD cPsi (tM1, id) (tM2, id);
		       if l = List.length (!globalCnstrs) then 
			 (dprint (fun () ->  "Solved global constraint (DONE): " ^ P.normalToString cD cPsi (tM1, id)  ^
				    " = " ^ P.normalToString cD cPsi (tM2, id) ^ "\n");
			  forceGlobalCnstr' cnstrs)
		       else
			 (dprint (fun () -> "New constraints generated?" ^ string_of_int l ^ " vs " ^ string_of_int (List.length (!globalCnstrs)));
			 raise (Failure "Constraints generated")))
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
		 let l = List.length (!globalCnstrs) in 
                  (dprint (fun () -> "Solve global constraint (H): " ^ P.headToString cD cPsi h1  ^
                        " = " ^ P.headToString cD cPsi h2 ^ "\n");
                   begin try
                     (unifyHead Unification cD cPsi h1 h2;
		     if l = List.length (!globalCnstrs) then 
                       (dprint (fun () -> "Solved global constraint (H): " ^ P.headToString cD cPsi h1  ^
				  " = " ^ P.headToString cD cPsi h2 ^ "\n");
			forceGlobalCnstr' cnstrs)
		     else raise (Failure "Constraints generated"))
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
	| GlobalCnstrFailure _ -> resetGlobalCnstrs () ; true 
      end

    let unify' mflag cD0 cPsi sM1 sM2 =
      resetDelayedCnstrs ();
      unify1 mflag cD0 cPsi sM1 sM2

    let unifyTyp1 mflag cD0 cPsi sA sB =
      unifyTyp mflag cD0 cPsi sA sB;
      forceCnstr mflag (nextCnstr ())
(*      dprint (fun () -> "Forcing Cnstr DONE") *)


    let unifyTyp' mflag cD0 cPsi sA sB =
       ((* dprint (fun () -> "\nUnifyTyp' " ^ *)
        (*                  P.typToString cD0 cPsi sA ^ "\n          " ^ *)
        (*                  P.typToString cD0 cPsi sB); *)
       resetDelayedCnstrs ();
       unifyTyp1 mflag cD0 cPsi sA sB;
       (* dprint (fun () -> "After unifyTyp'"); *)
       (* dprint (fun () -> "cPsi = " ^ P.dctxToString cD0 cPsi ^ "\n") ; *)
       (* dprint (fun () -> "sA = " ^ P.typToString cD0 cPsi sA ^ "\n     "); *)
       (* dprint (fun () -> "sB = " ^ P.typToString cD0 cPsi sB ) *) )

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
  let psihat = Whnf.cnorm_psihat psihat (MShift 0) in
  let phihat = Whnf.cnorm_psihat phihat (MShift 0) in
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
