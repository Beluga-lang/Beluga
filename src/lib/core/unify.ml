(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   code walk with Joshua Dunfield, Dec 3 2008
*)


(* The functor itself is called Make (hence Unify.Make to other
   modules); the instantiations UnifyTrail and UnifyNoTrail (hence
   Unify.UnifyTrail and Unify.UnifyNoTrail to other modules) are
   declared at the end of this file.
*)

open Syntax.Int.LF
open Syntax.Int
open Trail

module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [4])

module type UNIFY = sig

  type unifTrail

  exception Error of string

  (* trailing of variable instantiation *)

  val reset  : unit -> unit
  val mark   : unit -> unit
  val unwind : unit -> unit

  val instantiateMVar : normal option ref * normal * cnstr list -> unit
  val instantiatePVar : head   option ref * head   * cnstr list -> unit

  val resetDelayedCnstrs : unit -> unit
  val nextCnstr         : unit -> cnstr option
  val addConstraint     : cnstr list ref * cnstr -> unit
  val solveConstraint   : cnstr -> unit

  val isPatSub          : sub -> bool

  (* unification *)

  val intersection : psi_hat * (sub * sub) * dctx -> (sub * dctx)

  exception Unify of string

  (* All unify* functions return () on success and raise Unify on failure *)
  val unify    : mctx -> psi_hat * nclo * nclo -> unit
  val unifyTyp : mctx -> psi_hat * tclo * tclo -> unit
  val unifyTypRec : mctx -> psi_hat * (typ_rec * sub) * (typ_rec * sub) -> unit
  val unifyDCtx:   mctx -> dctx -> dctx -> unit
  val unifyCompTyp : mctx -> (Comp.typ * LF.msub) -> (Comp.typ * msub) -> unit

  val matchTerm    : mctx -> psi_hat * nclo * nclo -> unit 
  val matchTyp     : mctx -> psi_hat * tclo * tclo -> unit 
  val matchTypRec  : mctx -> psi_hat * (typ_rec * sub) * (typ_rec * sub) -> unit 


  type cvarRef =
    | MMVarRef of normal option ref
    | MVarRef of normal option ref
    | PVarRef of head option ref

  val pruneTyp : mctx -> psi_hat * tclo * (msub * sub) * cvarRef -> typ

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

  let raise_ exn =
    begin match exn with
      | Unify s -> dprint (fun () -> "raise Unify " ^ s)
      | NotInvertible -> dprint (fun () -> "raise NotInvertible")
      | Error s -> dprint (fun () -> "raise Error " ^ s)
      | Not_found -> dprint (fun () -> "raise Not_found")
      | _ -> ()
    end
  ; raise exn

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
    let s = (Whnf.normSub s) in 
    begin match s with
    | Shift (_,_k)              -> true
    | Dot (Head(BVar n), s) ->
        let rec checkBVar s' = match s' with
          | Shift (_ , k)           -> n <= k
          | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
          | Dot (Undef, s)          -> checkBVar s
          | _                       -> false
        in
          checkBVar s && isPatSub s
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
    | Dot (Undef, s)        -> isPatSub s
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
    | Add        of cnstr list ref
    | Solve      of cnstr * constrnt   (* FIXME: names *)

  type unifTrail = action T.t

  let globalTrail : action T.t = T.trail()

  let rec undo action = match action with
    | InstNormal refM         -> refM   := None
    | InstHead   refH         -> refH   := None
    | Add cnstrs              -> cnstrs := List.tl !cnstrs
    | Solve (cnstr, constrnt) -> cnstr  := constrnt

  let rec reset  () = T.reset globalTrail

  let rec mark   () = T.mark globalTrail

  let rec unwind () = T.unwind globalTrail undo

  let rec addConstraint (cnstrs, cnstr) =
    cnstrs := cnstr :: !cnstrs;
    T.log globalTrail (Add cnstrs)

  let rec solveConstraint ({contents=constrnt} as cnstr) =
    cnstr := Queued;
    T.log globalTrail (Solve (cnstr, constrnt))

  (* trail a function;
     if the function raises an exception,
       backtrack and propagate the exception  *)
  let rec trail f =
    let _ = mark   () in
      try f () with e -> (unwind (); raise_ e)

  (* ---------------------------------------------------------------------- *)

  let delayedCnstrs : cnstr list ref = ref []

  let rec resetDelayedCnstrs () = delayedCnstrs := []

  let rec nextCnstr () = match !delayedCnstrs with
    | []              -> None
    | cnstr :: cnstrL ->
        delayedCnstrs := cnstrL;
        Some cnstr

  let rec instantiatePVar (q, head, cnstrL) =
    q := Some head;
    T.log globalTrail (InstHead q);
    delayedCnstrs := cnstrL @ !delayedCnstrs


  let rec instantiateMVar (u, tM, cnstrL) =
    u := Some tM;
    T.log globalTrail (InstNormal u);
    delayedCnstrs := cnstrL @ !delayedCnstrs


  let rec instantiateMMVar (u, tM, cnstrL) =
    u := Some tM;
    T.log globalTrail (InstNormal u);
    delayedCnstrs := cnstrL @ !delayedCnstrs



  (* ---------------------------------------------------------------------- *)
  (* Higher-order unification *)

  (* Preliminaries:

     cD: a context of contextual variables; this is modelled
         implicitly since contextual variables are implemented as
         references.  cD thus describes the current status of
         memory cells for contextual variables.


     phat : a context of LF bound variables, without their typing
          annotations. While technically cPsi (or hat (cPsi) = phat) does
          not play a role in the unification algorithm itself, this
          will allow us to print normal terms and their types if
          they do not unify.

     tM : normal term that only contains MVar (MInst _, t) and
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

  let rec pruneCtx' (phat, (t, cPsi1), ss) = match (t, cPsi1) with
    | (Shift (_psi ,_k), Null) ->
        (id, Null)

    | (Shift (_, _k), CtxVar psi) ->
        (id, CtxVar psi)

   | (Shift (psi, k), DDec (_, TypDecl (_x, _tA))) ->
       pruneCtx' (phat, (Dot (Head (BVar (k + 1)), Shift (psi, k + 1)), cPsi1), ss)

   | (Dot (Head (BVar k), s), DDec (cPsi1, TypDecl (x, tA))) ->
       let (s', cPsi2) = pruneCtx' (phat, (s, cPsi1), ss) in
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
       let (s', cPsi2) = pruneCtx' (phat, (t, cPsi1), ss) in
         (* sP1 |- s' <= cPsi2 *)
         (comp s' shift, cPsi2)

  let pruneCtx (phat, (t, cPsi1), ss) = pruneCtx' (phat, (Whnf.normSub t, cPsi1), ss)


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

   | (MShift k, Dec (_, MDecl (_x, _tA, _cPsi))) ->
       pruneMCtx' cD (MDot (MV (k + 1), MShift (k + 1)), cD1) ms

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

  let pruneMCtx cD (t, cD1) ms = pruneMCtx' cD (Whnf.cnormMSub t, cD1) ms

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

    | (Root (loc, MVar (Inst (r, cPsi1, _tP, _cnstrs) as u, t), _tS (* Nil *)), s) ->
        (* by invariant tM is in whnf and meta-variables are lowered;
           hence tS = Nil and s = id *)
        let ( _ , ssubst) = ss in 
        if eq_cvarRef (MVarRef r) rOccur then
          raise_ NotInvertible
        else
          let t' = comp t s (* t' = t, since s = Id *) in
            (* D ; Psi |- s <= Psi'   D ; Psi' |- t <= Psi1
               t' =  t o s     and    D ; Psi  |-  t' <= Psi1 *)
            if isPatSub t' then
              let (s', _cPsi2) = pruneCtx (phat, (t', cPsi1), ss) in
                (* D ; Psi  |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then
                  Root(loc, MVar(u, comp t' ssubst), Nil)
                else
                  raise_ NotInvertible
            else (* t' not patsub *)
              Root(loc, MVar(u, invSub cD0 (phat, (t', cPsi1), ss, rOccur)), Nil)

   | (Root (loc, MMVar (MInst (r, cD, cPsi1, _tP, _cnstrs) as u, (mt,s')), _tS (* Nil *)), s) -> 
        (* by invariant tM is in whnf and meta-variables are lowered;
           hence tS = Nil and s = id *) 
        if eq_cvarRef (MVarRef r) rOccur then 
          raise NotInvertible 
        else 
          let s0 = comp s' s (* s0 = s', since s = Id *) in  
            (* D ; Psi |- s <= Psi'   D ; Psi' |- t <= Psi1
               s0 =  s' o s     and    D ; Psi  |-  s0 <= Psi1 *)
            if isPatSub s0 && isPatMSub mt then  
              let (s0', _cPsi2) = pruneCtx (phat, (s0, cPsi1), ss) in  
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
                                  invSub cD0 (phat, (s0, cPsi1), ss, rOccur))), Nil)

    | (Root (loc, MVar (Offset u, t), _tS (* Nil *)), s (* id *)) ->
        let t' = comp t s (* t' = t, since s = Id *) in
        let (_, _tA, cPsi1) = Whnf.mctxMDec cD0 u in 
          begin match applyMSub u ms with 
            | MV v -> 
                Root(loc, MVar(Offset v, invSub cD0 (phat, (t', cPsi1), ss, rOccur)), Nil)
            | MUndef -> raise NotInvertible
          end 

    | (Root (loc, FMVar (u, t), _tS (* Nil *)), s (* id *)) ->
        let (_tA, cPsi1) = Store.FMVar.get u in 
        let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
          Root (loc, FMVar (u, s'), Nil)

    | (Root (loc, FPVar (p, t), _tS (* Nil *)), s (* id *)) ->
        let (_tA, cPsi1) = Store.FPVar.get p in 
        let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
          Root (loc, FPVar (p, s'), Nil)

    | (Root (loc, PVar (Offset p, t), _tS (* Nil *)), s (* id *)) ->
        let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
        let t' = comp t s (* t' = t, since s = Id *) in
          begin match applyMSub p ms with
            | MV q -> 
                Root(loc, PVar(Offset q, invSub cD0 (phat, (t', cPsi1), ss, rOccur)), Nil)
            | MUndef -> raise NotInvertible
          end 

    | (Root (loc, PVar (PInst (r, cPsi1, _tA, _cnstrs) as q, t), tS), s) ->
        (* by invariant tM is in whnf and meta-variables are lowered and s = id *)
        let ( _ , ssubst) = ss in 
        if eq_cvarRef (PVarRef r) rOccur then
          raise_ NotInvertible
        else
          let t' = comp t s (* t' = t, since s = Id *) in
            (* D ; Psi |- s <= Psi'   D ; Psi' |- t <= Psi1
               t' =  t o s
               D ; Psi |-  t' <= Psi1 *)
            if isPatSub t' then
              let (s', _cPsi2) = pruneCtx (phat, (t', cPsi1), ss) in
                (* D ; Psi' |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then (* cPsi1 = cPsi2 *)
                  Root (loc, PVar (q, comp t' ssubst), 
                        invSpine cD0 (phat, (tS, s), ss, rOccur))
                else
                  raise_ NotInvertible
            else (* t' not patsub *)
              Root (loc, PVar (q, invSub cD0 (phat, (t', cPsi1), ss, rOccur)),
                    invSpine cD0 (phat, (tS,s), ss, rOccur))

    | (Root (loc, Proj (PVar (PInst (r, cPsi1, _tA, _cnstrs) as q, t), i), tS), s) ->
        let ( _ , ssubst) = ss in 
        if eq_cvarRef (PVarRef r) rOccur then
          raise_ NotInvertible
        else
          let t' = comp t s   (* t' = t, since s = Id *) in
            if isPatSub t' then
              let (s', _cPsi2) = pruneCtx (phat, (t', cPsi1), ss) in
                (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                   t' =  t o s r
                   cD ; cPsi |-  t' <= cPsi1 and
                   cD ; cPsi1 |- s' <= cPsi2 and
                   cD ; cPsi  |- [t']s' <= cPsi2  *)
                if isId s' then (* cPsi1 = cPsi2 *)
                  Root (loc, Proj (PVar(q, comp t' ssubst), i),
                        invSpine cD0 (phat, (tS,s), ss, rOccur))
                else
                  raise_ NotInvertible
            else (* t' not patsub *)
              Root (loc, Proj (PVar (q, invSub cD0 (phat, (t', cPsi1), ss, rOccur)), i),
                    invSpine cD0 (phat, (tS,s), ss, rOccur))

    | (Root (loc, head, tS), s (* = id *)) ->
        Root (loc, invHead  cD0 (phat, head , ss, rOccur),
              invSpine cD0 (phat, (tS, s), ss, rOccur))

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
          | Undef          -> raise_ NotInvertible
          | Head (BVar k') -> BVar k'
        end

    | Const _           ->
        head

    | Proj (BVar k, _i) ->
        let (_ , ssubst) = ss in 
        begin match bvarSub k ssubst with
          | Head (BVar _k' as head) -> head
          | Undef                   -> raise_ NotInvertible
        end

    | FVar _x           -> head
      (* For any free variable x:tA, we have  . |- tA <= type ;
         Occurs check is necessary on tA Dec 15 2008 -bp  :(
       *)

    | MVar (Inst (r, cPsi1, _tP, _cnstrs) as u, t) -> 
        if eq_cvarRef (MVarRef r) rOccur then
          raise NotInvertible
        else
          if isPatSub t then
            let (_ , ssubst) = ss in 
            let (s', _cPsi2) = pruneCtx (phat, (t, cPsi1), ss) in
                (* D ; Psi  |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then
                  MVar(u, comp t ssubst)
                else
                  raise NotInvertible
            else (* t' not patsub *)
              MVar(u, invSub cD0 (phat, (t, cPsi1), ss, rOccur))

    | MVar (Offset u, t) -> 
        let (_, _tA, cPsi1) = Whnf.mctxMDec cD0 u in 
          begin match applyMSub u ms with 
            | MV v -> 
                MVar(Offset v, invSub cD0 (phat, (t, cPsi1), ss, rOccur))
            | MUndef -> raise NotInvertible
          end 


    | PVar (Offset p, t) -> 
        let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
          begin match applyMSub p ms with 
            | MV q -> 
                PVar(Offset q, invSub cD0 (phat, (t, cPsi1), ss, rOccur))
            | MUndef -> raise NotInvertible
          end 


    | PVar (Inst (r, cPsi1, _tP, _cnstrs) as u, t) -> 
        if eq_cvarRef (MVarRef r) rOccur then
          raise NotInvertible
        else
          if isPatSub t then
            let (_ , ssubst) = ss in 
              let (s', _cPsi2) = pruneCtx (phat, (t, cPsi1), ss) in
                (* D ; Psi  |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then
                  PVar(u, comp t ssubst)
                else
                  raise NotInvertible
            else (* t' not patsub *)
              PVar(u, invSub cD0 (phat, (t, cPsi1), ss, rOccur))

    | Proj(PVar (Offset p, t), i) -> 
        let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
          begin match applyMSub p ms with 
            | MV q -> 
                Proj(PVar(Offset q, invSub cD0 (phat, (t, cPsi1), ss, rOccur)), i)
            | MUndef -> raise NotInvertible
          end 


    | Proj(PVar (Inst (r, cPsi1, _tP, _cnstrs) as u, t), i) -> 
        if eq_cvarRef (MVarRef r) rOccur then
          raise NotInvertible
        else
          if isPatSub t then
            let (_ , ssubst) = ss in 
              let (s', _cPsi2) = pruneCtx (phat, (t, cPsi1), ss) in
                (* D ; Psi  |- t' <= Psi1 and
                   D ; Psi1 |- s' <= Psi2 and
                   D ; Psi  |- [t']s' <= Psi2  *)
                if isId s' then
                  Proj(PVar(u, comp t ssubst), i)
                else
                  raise NotInvertible
            else (* t' not patsub *)
              PVar(u, invSub cD0 (phat, (t, cPsi1), ss, rOccur))





  (* invSub cD0 (phat, s, ss, rOccur) = s'

     if phat = hat(Psi)  and
        D ; Psi  |- s <= Psi'
        D ; Psi''|- ss <= Psi
     then s' = [ss]s   if it exists, and
        D ; cPsi'' |- [ss]s <= cPsi'
   *)
  and invSub cD0 (phat, (s, cPsi1), ((_ms , ssubst) as ss), rOccur) = match (s, cPsi1) with
    | (Shift (psi, n), DDec(_cPsi', _dec)) ->
        invSub cD0 (phat, (Dot (Head (BVar (n + 1)), Shift (psi, n + 1)), cPsi1), ss, rOccur)

    | (Shift (psi, n), Null) -> comp (Shift (psi, n)) ssubst  
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
              let si = invSub cD0 (phat, (s', cPsi'), ss, rOccur) in 
                Dot(Undef, si) 
                  (* Mon Feb  9 14:37:27 2009 -bp : previously raise NotInvertible) *)
          | ft    -> Dot (ft, invSub cD0 (phat, (s', cPsi'), ss, rOccur))
        end

    | (Dot (Obj tM, s'), DDec(cPsi', _dec))        ->
        (* below may raise NotInvertible *)

        let tM' = invNorm cD0 (phat, (tM, id), ss, rOccur) in 
          Dot (Obj tM', invSub cD0 (phat, (s', cPsi'), ss, rOccur))




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





  (* intersection (phat, (s1, s2), cPsi') = (s', cPsi'')
     s' = s1 /\ s2 (see JICSLP'96 and Pientka's thesis)

     Invariant:
     If   D ; Psi  |- s1 : Psi'    s1 patsub
     and  D ; Psi  |- s2 : Psi'    s2 patsub
     then D ; Psi' |- s' : Psi'' for some Psi'' which is a subset of Psi'
     and  s' patsub   s.t.  [s1]s'  = [s2]s' 
  *)
  let rec intersection (phat, (subst1, subst2), cPsi') = match (subst1, subst2, cPsi') with
    | (Dot (Head (BVar k1), s1), Dot (Head (BVar k2), s2), DDec (cPsi', TypDecl (x, tA))) ->
        let (s', cPsi'') = intersection (phat, (s1, s2), cPsi') in
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


    | (Dot (Undef, s1), Dot (Head (BVar _k2), s2), DDec (cPsi', TypDecl _)) ->
        let (s', cPsi'') = intersection (phat, (s1, s2), cPsi') in
            (comp s' shift, cPsi'')

    | (Dot (Head (BVar _k), s1), Dot (Undef, s2), DDec (cPsi', TypDecl _ )) ->
        let (s', cPsi'') = intersection (phat, (s1, s2), cPsi') in
            (comp s' shift, cPsi'')


    | (Dot (Undef, s1), Dot (Undef, s2), DDec (cPsi', TypDecl _)) ->
        let (s', cPsi'') = intersection (phat, (s1, s2), cPsi') in
            (comp s' shift, cPsi'')

    | ((Dot _ as s1), Shift (psi, n2), cPsi) ->
        intersection (phat, (s1, Dot (Head (BVar (n2 + 1)), Shift (psi, n2 + 1))), cPsi)

    | (Shift (psi, n1), (Dot _ as s2), cPsi) ->
        intersection (phat, (Dot (Head (BVar (n1 + 1)), Shift (psi, n1 + 1)), s2), cPsi)

    | (Shift (NoCtxShift, _k), Shift (NoCtxShift, _k'), cPsi) -> (id, cPsi) 
        (* both substitutions are the same number of shifts by invariant *)

    | (Shift (CtxShift _psi, _k), Shift (CtxShift _psi', _k'), cPsi) -> (id, cPsi)
        (* psi = psi' and k = k' by invariant *)

    | (Shift (NegCtxShift _psi, _k), Shift (NegCtxShift _psi', _k'), cPsi) -> (id, cPsi)
        (* psi = psi' and k = k' by invariant *)

    (* all other cases impossible for pattern substitutions *)

    | (_s1, _s2, _cPsi )  -> 
           raise_ (Error "Intersection not defined")


  (* m_intersection (mt1, mt2) cD' = (mt', cD'')
     (adapted from intersection code above)

     Invariant:
     If   D    |- mt1 : cD'    mt1 patsub
     and  D    |- mt2 : cD'    mt2 patsub
     then  cD' |- mt' : cD'' for some cD'' which is a subset of cD'
     and  mt' patsub   s.t.  [mt1]mt'  = [mt2]mt' 
  *)
  let rec m_intersection  (subst1, subst2) cD' = match (subst1, subst2, cD') with
    | (MDot (MV k1, mt1), MDot (MV k2, mt2), Dec (cD', MDecl (x, tA, cPsi))) ->
        let (mt', cD'') = m_intersection  (mt1, mt2) cD' in
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
        let (mt', cD'') = m_intersection  (mt1, mt2) cD' in
            (Whnf.mcomp mt' (MShift 1), cD'')

    | (MDot (MUndef, mt1), MDot (MV _k2, mt2), Dec (cD', PDecl _)) ->
        let (mt', cD'') = m_intersection  (mt1, mt2) cD' in
            (Whnf.mcomp mt' (MShift 1), cD'')

    | (MDot (MV _k, mt1), MDot (MUndef, mt2), Dec (cD', _ )) ->
        let (mt', cD'') = m_intersection (mt1, mt2) cD' in
            (Whnf.mcomp mt' (MShift 1), cD'')


    | (MDot (MUndef, mt1), MDot (MUndef, mt2), Dec (cD', _)) ->
        let (mt', cD'') = m_intersection (mt1, mt2) cD' in
            (Whnf.mcomp mt' (MShift 1), cD'')

    | (MDot _ as mt1, MShift  n2, cD) ->
        m_intersection  (mt1, MDot (MV (n2 + 1), MShift  (n2 + 1))) cD

    | (MShift n1, (MDot _ as mt2), cD) ->
        m_intersection (MDot (MV (n1+1), MShift (n1 + 1)), mt2) cD

    | (MShift _k, MShift _k', cD) -> (Whnf.m_id, cD)
        (* both substitutions are the same number of shifts by invariant *)

    (* all other cases impossible for pattern substitutions *)

    | (_mt1, _mt2, _cC )  -> 
           raise (Error "m-intersection not defined")


  (* prune cD0 (phat, (tM, s), ss, rOccur) = tM'

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

  let rec prune  cD0 (phat, sM, ss, rOccur) =
    let _qq : (msub * sub) = ss in 
      prune' cD0 (phat, Whnf.whnf sM, ss, rOccur)

  and prune' cD0 ((cvar, offset) as phat, sM, ss, rOccur) = match sM with
    | (Lam (loc, x, tM),   s) ->
        let (ms, ssubst) = ss in 
        let tM' = prune cD0 ((cvar, offset + 1), (tM, dot1 s), (ms, dot1 ssubst), rOccur) in
          Lam (loc, x, tM')

    | (Tuple (loc, tuple),   s) ->
        let tuple' = pruneTuple cD0 (phat, (tuple, s), ss, rOccur) in
          Tuple (loc, tuple')

    | (Root (loc, head, tS),   s) ->
        let (ms , ssubst) = ss in 
        let returnHead newHead =
          let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in 
            Root (loc, newHead, tS')
        in
          match head with
            | MMVar (MInst (r, cD1, cPsi1, tP, cnstrs) as _u, (mt, t)) ->  (* s = id *)
                let tM = Root(loc, head, tS) in
                  (* by invariant: MVars are lowered since tM is in whnf *)
                  if eq_cvarRef (MMVarRef r) rOccur then
                    raise (Unify "Variable occurrence")
                  else
                    if isPatSub t && isPatMSub mt then
                      let (id_sub, cPsi2) = pruneCtx (phat, (comp t s, cPsi1), ss) in
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
                         Clo(tM, comp s ssubst)
                        )
                          (* [|v[id_msub, id_sub] / u|] *)
                    else (* (mt, t) are not patsub *)
                      (* cD ; cPsi' |- u[t] <= [t]tP, and u::tP[cPsi1]  and 
                         cD ; cPsi' |- t <= cPsi1
                         cD ; cPsi  |- s <= cPsi'
                         CD ; cPsi  |- comp t s <= cPsi1  and cD ; cPsi''|- ssubst <= cPsi
                         s' = [ssubst]([s]t) and  cD ; cPsi'' |- s' <= cPsi1  *)
                      (* Mon Feb  9 14:38:08 2009 -bp : instead of simply computing the inverted
                         substitution, we now actually prune the substitution *)
                      (* let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                         Root (loc, MVar (u, s'), Nil) *)
                      
                      let (idsub, cPsi2) = pruneSub  cD0 (phat, (Whnf.normSub (comp t s), cPsi1), ss, rOccur) in
                      (* Psi1 |- idsub   : Psi2 
                         Psi2 |- idsub_i : Psi1
                       *)
                      let idsub_i = invert idsub in 
                      let v = Whnf.newMVar(cPsi2, TClo(tP, invert idsub_i)) in
                        
                      let _ = instantiateMVar (r, Root (loc, MVar (v, idsub), Nil), !cnstrs) in 
                        Clo(tM, comp s ssubst) 
                          (* may raise NotInvertible *)
                          

            | MVar (Inst (r, cPsi1, tP, cnstrs) as _u, t) ->  (* s = id *)
                let tM = Root(loc, head, tS) in
                  (* by invariant: MVars are lowered since tM is in whnf *)
                  if eq_cvarRef (MVarRef r) rOccur then
                    raise_ (Unify "Variable occurrence")
                  else
                    if isPatSub t then
                      let (idsub, cPsi2) = pruneCtx (phat, (comp t s, cPsi1), ss) in
                        (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                           cD ; cPsi |-  t o s <= cPsi1 and
                           cD ; cPsi1 |- idsub <= cPsi2 and
                           cD ; cPsi |- t o s o idsub <= cPsi2 *)
                      let v = Whnf.newMVar(cPsi2, TClo(tP, invert idsub)) in
                        (instantiateMVar (r, Root (loc, MVar (v, idsub), Nil), !cnstrs);
                         Clo(tM, comp s ssubst)
                        )
                          (* [|v[idsub] / u|] *)
                    else (* s not patsub *)
                      (* cD ; cPsi' |- u[t] <= [t]tP, and u::tP[cPsi1]  and 
                         cD ; cPsi' |- t <= cPsi1
                         cD ; cPsi  |- s <= cPsi'
                         CD ; cPsi  |- comp t s <= cPsi1  and cD ; cPsi''|- ssubst <= cPsi
                         s' = [ssubst]([s]t) and  cD ; cPsi'' |- s' <= cPsi1  *)
                      (* Mon Feb  9 14:38:08 2009 -bp : instead of simply computing the inverted
                         substitution, we now actually prune the substitution *)
                      (* let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                         Root (loc, MVar (u, s'), Nil) *)
                      
                      let (idsub, cPsi2) = pruneSub  cD0 (phat, (Whnf.normSub (comp t s), cPsi1), ss, rOccur) in
                      (* Psi1 |- idsub   : Psi2 
                         Psi2 |- idsub_i : Psi1
                       *)
                      let idsub_i = invert idsub in 
                      let v = Whnf.newMVar(cPsi2, TClo(tP, invert idsub_i)) in
                        (* why invert idsub_i ?? This would simply be idsub ... Fri Apr 17 20:14:02 2009 -bp *)
                        
                      let _ = instantiateMVar (r, Root (loc, MVar (v, idsub), Nil), !cnstrs) in 
                        Clo(tM, comp s ssubst) 
                          (* may raise NotInvertible *)
                          

            | MVar (Offset u, t)   (* tS = Nil,   s = id *) ->
                begin match applyMSub u ms with 
                  | MV v -> 
                      begin try 
                        let (_, _tA, cPsi1) = Whnf.mctxMDec cD0 u in 
                        let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                          returnHead (MVar (Offset v, s'))
                      with 
                          _ -> raise_ (Unify ("ERROR: prune: Looking for " ^ R.render_cvar cD0 u ^ 
                                               "\n in context " ^ P.mctxToString Empty cD0))
                      end
                  | MUndef -> raise_ (Unify "Bound MVar dependency")
                end 
                  
            | FMVar (u, t)   (* tS = Nil,   s = id *) ->
                let (_tA, cPsi1) = Store.FMVar.get u in 
                let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                  returnHead (FMVar (u, s'))
                    
            | FPVar (p, t)   (* tS = Nil,   s = id *) ->
                let (_tA, cPsi1) = Store.FPVar.get p in 
                let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                  returnHead (FPVar (p, s'))
                    
            | PVar (Offset p, t)   (* tS = Nil,   s = id *) ->
                begin match applyMSub p ms with 
                  | MV q -> 
                      let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
                      let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                        returnHead (PVar (Offset q, s'))
                  | MUndef -> raise (Unify "Bound PVar dependency")
                end

            | Proj (PVar (Offset p, t), i)   (* tS = Nil,   s = id *) ->
                begin match applyMSub p ms with 
                  | MV q ->                       
                      let (_, _tA, cPsi1) = Whnf.mctxPDec cD0 p in 
                      let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                        returnHead (Proj (PVar (Offset q, s'), i))
                  | MUndef -> raise (Unify "Bound PVar dependency in projection")
                end 

            | PVar (PInst (r, cPsi1, tA, cnstrs) as q, t) (* tS *)   (* s = id *) ->
                if eq_cvarRef (PVarRef r) rOccur then
                  raise_ (Unify "Parameter variable occurrence")
                else
                  if isPatSub t then
                    let (idsub, cPsi2) = pruneCtx(phat, (comp t s, cPsi1), ss) in
                      (* cD ; cPsi1 |- idsub <= cPsi2 *)
                    let p = Whnf.newPVar (cPsi2, TClo(tA, invert idsub)) (* p::([(idsub)^-1]tA)[cPsi2] *) in
                    let _ = instantiatePVar (r, PVar (p, idsub), !cnstrs) in
                      (* [|p[idsub] / q|] *)
                      (* h = p[[ssubst] ([t] idsub)] *)
                      returnHead (PVar(p, comp ssubst (comp t idsub)))
                  else (* s not patsub *)
                    let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                      returnHead (PVar (q, s'))
                        
            | Proj (PVar (PInst (r, cPsi1, tA, cnstrs) as q, t), i)  (* s = id *) ->
                if eq_cvarRef (PVarRef r) rOccur then
                  raise_ (Unify "Parameter variable occurrence")
                else
                  if isPatSub t then
                    let (idsub, cPsi2) = pruneCtx(phat, (comp t s, cPsi1), ss) in
                      (* cD ; cPsi1 |- idsub <= cPsi2 *)
                    let p = Whnf.newPVar(cPsi2, TClo(tA, invert idsub)) (* p::([(idsub)^-1] tA)[cPsi2] *) in
                    let _ = instantiatePVar (r, PVar (p, idsub), !cnstrs) (* [|p[idsub] / q|] *) in
                      returnHead (Proj (PVar(p, comp ssubst (comp t idsub)), i))
                  else (* s not patsub *)
                    let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                      returnHead (Proj (PVar (q, s'), i))
                        
            | Proj (FPVar(p,t), i)   (* tS = Nil,   s = id *) ->
                let (_tA, cPsi1) = Store.FPVar.get p in 
                let _ = dprint (fun () -> "before invSub") in
                let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
                let _ = dprint (fun () -> "after invSub") in
                  returnHead (Proj (FPVar(p,s'), i))
                    
            | BVar k  (* s = id *) ->
                begin match bvarSub k ssubst with
                  | Undef                -> raise_ (Unify "Bound variable dependency")
                  | Head (BVar _k as h') ->
                      returnHead h'
                end
                  
            | Const _ as h  (* s = id *)  ->  returnHead h
                  
            | FVar _ as h  (* s = id *)  ->  returnHead h
                  
            | Proj (BVar k, i)  (* s = id *) ->
                begin match bvarSub k ssubst with
                  | Head (BVar _k' as h') -> returnHead (Proj (h', i))
                  | _                     -> raise_ (Unify "Bound variable dependency")
                end

  and pruneTuple cD0 (phat, sTuple, ss, rOccur) = match sTuple with
    | (Last tM, s) ->
        let tM' = prune cD0 (phat, (tM, s), ss, rOccur) in
          Last tM'

    | (Cons (tM, rest), s) ->
        let tM' = prune cD0 (phat, (tM, s), ss, rOccur) in
        let rest' = pruneTuple cD0 (phat, (rest, s), ss, rOccur) in
          Cons (tM', rest')

  
  and pruneSpine cD0 (phat, spine, ss, rOccur) = match spine with
    | (Nil, _s)           -> Nil

    | (App (tM, tS), s)   ->
        let tM' = prune cD0 (phat, (tM, s), ss, rOccur) in
        let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
          App (tM', tS')

    | (SClo (tS, s'), s) ->
        pruneSpine cD0 (phat, (tS, comp s' s), ss, rOccur)

  (* pruneSub cD0 (phat, s, ss, rOccur) = (s', cPsi')

     if phat = hat(Psi)  and
        D ; Psi  |- s <= Psi1
        D ; Psi''|- ss <= Psi
     then  cPsi1 |- s' <= Psi1'
           ss' = [ss](s   if it exists, and
        D ; cPsi'' |- [ss]s <= cPsi1'
   *)

  and pruneSub cD0 (phat, (s, cPsi1), ss, rOccur) = match (s, cPsi1) with
    | (Shift (psi, n), DDec(_cPsi', _dec)) ->       
        pruneSub cD0 (phat, (Dot (Head (BVar (n + 1)), Shift (psi, n + 1)), cPsi1), ss, rOccur)

    | (Shift (_psi, _n), Null) -> (id, Null)

    | (Shift (_psi', _n), CtxVar psi) -> (id, CtxVar psi)

    | (Dot (Head (BVar n), s'), DDec(cPsi', TypDecl(x, tA))) ->
        let (_, ssubst) = ss in 
        begin match bvarSub n ssubst with
          | Undef -> 
              let (s1', cPsi1') = pruneSub cD0 (phat, (s', cPsi'), ss, rOccur)  in 
                (comp s1' shift, cPsi1')

           | Head (BVar _n) ->
              let (s1', cPsi1') = pruneSub cD0 (phat, (s', cPsi'), ss, rOccur) in
              let s1_i = invert (Whnf.normSub s1') in      (* cPsi1' |- s1_i <= cPsi' *)
               (dot1 s1' ,  DDec(cPsi1', TypDecl(x, TClo (tA, s1_i))))
        end


    | (Dot (Head (Proj (BVar n, _projIndex)), s'), DDec(cPsi', TypDecl(x, tA))) ->
      (* copied immediately preceding case for Head (BVar _)...is this right?  -jd *)
      let (_ , ssubst) = ss in 
        begin match bvarSub n ssubst with
          | Undef -> 
              let (s1', cPsi1') = pruneSub cD0 (phat, (s', cPsi'), ss, rOccur)  in 
                (comp s1' shift, cPsi1')

           | Head (BVar _n) ->
              let (s1', cPsi1') = pruneSub cD0 (phat, (s', cPsi'), ss, rOccur) in
              let s1_i = invert (Whnf.normSub s1') in      (* cPsi1' |- s1_i <= cPsi' *)
               (dot1 s1' ,  DDec(cPsi1', TypDecl(x, TClo (tA, s1_i))))
        end

    | (Dot (Obj tM, s'), DDec(cPsi', TypDecl(x, tA)))        ->
        (* below may raise NotInvertible *)
        (* let _tM' = invNorm cD0 (phat, (tM, id), ss, rOccur) in    *)
        let _tM' = prune cD0 (phat, (tM, id), ss, rOccur) in     

        let (s1', cPsi1')  = pruneSub cD0 (phat, (s', cPsi'), ss, rOccur) in 
        let s1_i = invert (Whnf.normSub s1') in      (* cPsi1' |- s1_i <= cPsi' *)
        (* We need to prune the type here as well;  Feb  9  2009 -bp *)
        let tA' = pruneTyp cD0 (phat, (tA, id), (MShift 0, s1_i), rOccur) in  
          (dot1 s1'  , DDec(cPsi1', TypDecl(x, tA'))) 

   | (Dot (Undef, t), DDec (cPsi1, _)) ->
       let (s1', cPsi1') = pruneSub cD0 (phat, (t, cPsi1), ss, rOccur) in
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
        let _tM' = prune cD0 (phat, (tM, id), (mtt, id), rOccur) in     

        let (t1', cD1')  = pruneMSub cD0 (t', cD') mtt rOccur in 
        let t1_i = Whnf.m_invert (Whnf.cnormMSub t1') in      (* cD1' |- t1_i <= cD' *)
        (* We need to prune the type here as well;  -bp *)
        let tA' = pruneTyp cD0 (phat, (tA, id), (t1_i, id), rOccur) in  
        let cPsi' = pruneDCtx cD0 cPsi  t1_i rOccur in  
          (Whnf.mvar_dot1 t1'  , Dec(cD1', MDecl(x, tA', cPsi'))) 

   | (MDot (MUndef, t), Dec (cD1, _)) ->
       let (t1', cD1') = pruneMSub cD0 (t, cD1) mtt rOccur in
         (Whnf.mcomp t1' (MShift 1), cD1')

  and pruneTypW cD0 (phat, sA, ss, rOccur) = match sA with
    | (Atom(loc, a, tS) , s) -> Atom(loc, a, pruneSpine cD0 (phat, (tS, s), ss, rOccur)) 
    | (PiTyp((TypDecl(x, tA), dep), tB), s) -> 
        let tA' = pruneTyp cD0 (phat, (tA, s), ss, rOccur) in 
        let tB' = pruneTyp cD0 (phat, (tB, dot1 s), ss, rOccur) in 
          PiTyp((TypDecl(x, tA'), dep), tB')

  and pruneTyp cD0 (phat, sA, ss, rOccur) = 
    let _ : (msub * sub) = ss in 
      pruneTypW cD0 (phat, Whnf.whnfTyp sA, ss, rOccur)


  and pruneDCtx cD0 cPsi mtt rOccur = match cPsi with
    | Null -> Null
    | DDec (cPsi', TypDecl(x, tA)) -> 
        let cPsi'' = pruneDCtx cD0 cPsi mtt rOccur in 
        let phat   = Context.dctxToHat cPsi' in 
        let tA''   = pruneTyp cD0 (phat, (tA, id), (mtt, id), rOccur) in 
          DDec (cPsi'', TypDecl (x, tA''))
    

  (* Unification:

       Precondition: D describes the current contextual variables

       Given cD ; cPsi1 |- tN <= tA1    and cD ; cPsi |- s1 <= cPsi1
             cD ; cPsi2 |- tM <= tA2    and cD ; cPsi |- s2 <= cPsi2
             cD ; cPsi  |- [s1]tA1 = [s2]tA2 <= type

             hat(cPsi) = phat

        unify (phat, (tN,s), (tM,s')) succeeds if there exists a
        contextual substitution theta s.t.

        [|theta|]([s1]tN) = [|theta|]([s2]tM) where cD' |- theta <= cD.

       instantiation theta is applied as an effect and () is returned.
       otherwise exception Unify is raised.

       Post-Condition: cD' includes new and possibly updated
                       contextual variables;

       Other effects: MVars in cD' may have been lowered and pruned; Constraints
       may be added for non-patterns.
  *)


  let rec unifyTerm  mflag cD0 (phat, sN, sM) = unifyTerm'  mflag cD0 (phat, Whnf.whnf sN, Whnf.whnf sM)

  and unifyTerm'  mflag cD0 (((psi, offset) as phat), sN, sM) = match (sN, sM) with
    | ((Lam (_, _, tN), s1), (Lam (_, _, tM), s2)) ->
        unifyTerm  mflag cD0 ((psi, offset + 1), (tN, dot1 s1), (tM, dot1 s2))

    (* MVar-MVar case *)
    | (((Root (_, MVar (Inst (r1,  cPsi1,  tP1, cnstrs1), t1), _tS1) as _tM1), s1) as sM1,
       (((Root (_, MVar (Inst (r2, _cPsi2, _tP2, cnstrs2), t2), _tS2) as _tM2), s2) as sM2)) ->
        (* by invariant of whnf:
           meta-variables are lowered during whnf, s1 = s2 = id
           r1 and r2 are uninstantiated  (None)
        *)
        let t1' = comp t1 s1    (* cD ; cPsi |- t1' <= cPsi1 *)
        and t2' = comp t2 s2 in (* cD ; cPsi |- t2' <= cPsi2 *)
        in
          if r1 == r2 then (* by invariant:  cPsi1 = cPsi2, tP1 = tP2, cnstr1 = cnstr2 *)
            match (isPatSub t1' , isPatSub t2') with                
              | (true, true) ->                 
                  let (s', cPsi') = intersection (phat, (Whnf.normSub t1', Whnf.normSub t2'), cPsi1) in
                    (* if cD ; cPsi |- t1' <= cPsi1 and cD ; cPsi |- t2' <= cPsi1
                       then cD ; cPsi1 |- s' <= cPsi' *)                  

                  let ss' = invert (Whnf.normSub s') in
                    (* cD ; cPsi' |- [s']^-1(tP1) <= type *)

                  let w = Whnf.newMVar (cPsi', TClo(tP1, ss')) in
                    (* w::[s'^-1](tP1)[cPsi'] in cD'            *)
                    (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tP1)
                       [|w[s']/u|](u[t1]) = [t1](w[s'])
                       [|w[s']/u|](u[t2]) = [t2](w[s'])
                    *)
                    instantiateMVar (r1, Root(None, MVar(w, s'),Nil), !cnstrs1)

              | (true, false) ->
                  addConstraint (cnstrs2, ref (Eqn (cD0, phat, Clo sM, Clo sN))) (* XXX double-check *)
              | (false, _) ->
                  addConstraint (cnstrs1, ref (Eqn (cD0, phat, Clo sN, Clo sM)))  (* XXX double-check *)
          else
            begin match (isPatSub t1' , isPatSub t2') with
              | (true, _) ->
                  (* cD ; cPsi' |- t1 <= cPsi1 and cD ; cPsi |- t1 o s1 <= cPsi1 *)
                  begin try

                    let ss1  = invert (Whnf.normSub t1') (* cD ; cPsi1 |- ss1 <= cPsi *) in

                    let _ = dprint (fun () -> let cPsi = Context.hatToDCtx phat in 
                                      "UNIFY(1): " ^ 
                                              P.mctxToString Empty cD0 ^ "\n" ^
                                              P.normalToString Empty cD0 cPsi sM1 ^ "\n    " ^
                                              P.normalToString Empty cD0 cPsi sM2 ^ "\n") in 
                    let tM2' = trail (fun () -> prune cD0 (phat, sM2, (MShift 0, ss1), MVarRef r1)) in 
                    (* sM2 = [ss1][s2]tM2 *) 

                    instantiateMVar (r1, tM2', !cnstrs1) 
                  with
                    | NotInvertible ->
                        (Printf.printf "Added constraints: NotInvertible: \n "
                        ; addConstraint (cnstrs1, ref (Eqn (cD0, phat, Clo sM1, Clo sM2))))
                  end
              | (false, true) ->
                  begin try
                    let ss2 = invert (Whnf.normSub t2')(* cD ; cPsi2 |- ss2 <= cPsi *) in
                    let tM1' = trail (fun () -> prune cD0 (phat, sM1, (MShift 0, ss2), MVarRef r2)) in
                      instantiateMVar (r2, tM1', !cnstrs2)                       
                  with
                    | NotInvertible ->
                        (Printf.printf "Added constraints: NotInvertible: \n" 
                        ; addConstraint (cnstrs2, ref (Eqn (cD0, phat, Clo sM2, Clo sM1))))
                  end
              | (false , false) ->
                  (* neither t1' nor t2' are pattern substitutions *)
                  let cnstr = ref (Eqn (cD0, phat, Clo sM1, Clo sM2)) in                    
                   addConstraint (cnstrs1, cnstr)
            end

    (* MVar-normal case *)
    | ((Root (_, MVar (Inst (r, _cPsi, _tP, cnstrs), t), _tS), s1) as sM1, ((_tM2, _s2) as sM2)) ->
        let t' = comp t s1 in
          if isPatSub t' then
            try
              let ss = invert (Whnf.normSub t') in
              let _ = dprint (fun () -> let cPsi = Context.hatToDCtx phat in 
                                          "UNIFY(2): " ^
                                            P.mctxToString Empty cD0 ^ "\n    " ^
                                            P.normalToString Empty cD0 cPsi sM1 ^ "\n    " ^
                                            P.normalToString Empty cD0 cPsi sM2 ^ "\n") in
              
              let sM2' = trail (fun () -> prune cD0 (phat, sM2, (MShift 0, ss), MVarRef r)) in
              in
                instantiateMVar (r, sM2', !cnstrs)
            with
              | NotInvertible ->
                  Printf.printf "Added constraints: NotInvertible: \n"
                ; addConstraint (cnstrs, ref (Eqn (cD0, phat, Clo sM1, Clo sM2)))
          else
             addConstraint (cnstrs, ref (Eqn (cD0, phat, Clo sM1, Clo sM2)))
    
    (* normal-MVar case *)
    | ((_tM1, _s1) as sM1, ((Root (_, MVar (Inst (r, _cPsi, _tP, cnstrs), t), _tS), s2) as sM2)) ->
        let t' = comp t s2 in
          if isPatSub t' then
            try
              let _ = dprint (fun () -> let cPsi = Context.hatToDCtx phat in 
                                "UNIFY(3): " ^ 
                                  P.mctxToString Empty cD0 ^ "\n" ^
                                  P.normalToString Empty cD0 cPsi sM1 ^ "\n    " ^
                                  P.normalToString Empty cD0 cPsi sM2 ^ "\n") in 
                
              let ss = invert (Whnf.normSub t') in
              let sM1' = trail (fun () -> prune cD0 (phat, sM1, (MShift 0, ss), MVarRef r)) in
                instantiateMVar (r, sM1', !cnstrs) 
            with
              | NotInvertible ->
                  (Printf.printf "Added constraints: NotInvertible: \n" ;
                  addConstraint (cnstrs, ref (Eqn (cD0, phat, Clo sM1, Clo sM2))))
          else            
             addConstraint (cnstrs, ref (Eqn (cD0, phat, Clo sM1, Clo sM2)))



    (* MMVar-MMVar case *)
    | (((Root (_, MMVar (MInst (r1,  cD1, cPsi1,  tP1, cnstrs1), (mt1, t1)), _tS1) as _tM1), s1) as sM1,
       (((Root (_, MMVar (MInst (r2, _cD2, _cPsi2, _tP2, cnstrs2), (mt2, t2)), _tS2) as _tM2), s2) as sM2)) ->
        (* by invariant of whnf:
           meta^2-variables are lowered during whnf, s1 = s2 = id
           r1 and r2 are uninstantiated  (None)
        *)
        let t1' = comp t1 s1    (* cD ; cPsi |- t1' <= cPsi1 *)
        and t2' = comp t2 s2 in (* cD ; cPsi |- t2' <= cPsi2 *)
        in
          if r1 == r2 then (* by invariant:  cD1 = cD2, cPsi1 = cPsi2, tP1 = tP2, cnstr1 = cnstr2 *)
            match (isPatMSub mt1, isPatSub t1' , isPatMSub mt2, isPatSub t2') with                
              | (true, true, true, true) ->                 
                  let (s', cPsi') = intersection (phat, (Whnf.normSub t1', Whnf.normSub t2'), cPsi1) in
                    (* if cD ; cPsi |- t1' <= cPsi1 and cD ; cPsi |- t2' <= cPsi1
                       then cD ; cPsi1 |- s' <= cPsi' *)
                  let (mt', cD') = m_intersection (Whnf.cnormMSub mt1, Whnf.cnormMSub mt2) cD1 in              
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
                    instantiateMMVar (r1, Root(None, MMVar(w, (mt', s')), Nil), !cnstrs1)

              | (true, true, _, false) ->
                  addConstraint (cnstrs2, ref (Eqn (cD0, phat, Clo sM, Clo sN))) (* XXX double-check *)

              | (true, true, false, _ ) ->
                  addConstraint (cnstrs2, ref (Eqn (cD0, phat, Clo sM, Clo sN))) (* XXX double-check *)

              | (false, _, _, _) ->
                  addConstraint (cnstrs1, ref (Eqn (cD0, phat, Clo sN, Clo sM)))  (* XXX double-check *)

              | (_, false, _, _) ->
                  addConstraint (cnstrs1, ref (Eqn (cD0, phat, Clo sN, Clo sM)))  (* XXX double-check *)

          else
            begin match (isPatMSub mt1, isPatSub t1' , isPatMSub mt2, isPatSub t2') with
              | (true, true, _, _) ->
                  (* since   cD ; cPsi' |- t1 <= cPsi1 and cD ; cPsi |- t1 o s1 <= cPsi1,
                   * we have cD ; cPsi |- t1' <= cPsi1 and cD  |- mt1 <= cD1
                   *)
                  
                  begin try

                    let ss1  = invert (Whnf.normSub t1') in
                      (* cD ; cPsi1 |- ss1 <= cPsi *)
                    let mtt1 = Whnf.m_invert (Whnf.cnormMSub mt1) in 
                      (* cD1 |- mtt1 <= cD *)
                    let _ = dprint (fun () -> let cPsi = Context.hatToDCtx phat in 
                                      "UNIFY(1): " ^ 
                                              P.mctxToString Empty cD0 ^ "\n" ^
                                              P.normalToString Empty cD0 cPsi sM1 ^ "\n    " ^
                                              P.normalToString Empty cD0 cPsi sM2 ^ "\n") in 
                    let tM2' = trail (fun () -> prune cD0 (phat, sM2, (mtt1, ss1), MVarRef r1)) in 
                    (* sM2 = [ss1][s2]tM2 *) 

                    instantiateMMVar (r1, tM2', !cnstrs1) 
                  with
                    | NotInvertible ->
                        (Printf.printf "Added constraints: NotInvertible: \n "
                        ; addConstraint (cnstrs1, ref (Eqn (cD0, phat, Clo sM1, Clo sM2))))
                  end
              | (_ , _, true, true) ->
                  begin try
                    let ss2 = invert (Whnf.normSub t2')(* cD ; cPsi2 |- ss2 <= cPsi *) in
                    let mtt2 = Whnf.m_invert (Whnf.cnormMSub mt2) in 
                      (* cD1 |- mtt1 <= cD *)

                    let tM1' = trail (fun () -> prune cD0 (phat, sM1, (mtt2, ss2), MVarRef r2)) in
                      instantiateMMVar (r2, tM1', !cnstrs2)                       
                  with
                    | NotInvertible ->
                        (Printf.printf "Added constraints: NotInvertible: \n" 
                        ; addConstraint (cnstrs2, ref (Eqn (cD0, phat, Clo sM2, Clo sM1))))
                  end
              | (_ , _ , _ , _) ->
                  (* neither t1' nor t2' are pattern substitutions *)
                  let cnstr = ref (Eqn (cD0, phat, Clo sM1, Clo sM2)) in                    
                   addConstraint (cnstrs1, cnstr)
            end


    (* MMVar-normal case *)
    | ((Root (_, MMVar (MInst (r, _cD,  _cPsi, _tP, cnstrs), (mt, t)), _tS), s1) as sM1, ((_tM2, _s2) as sM2)) ->
        let t' = comp t s1 in
          if isPatSub t' && isPatMSub mt then
            try
              let ss  = invert (Whnf.normSub t') in
              let mtt = Whnf.m_invert (Whnf.cnormMSub mt) in 
              let _ = dprint (fun () -> let cPsi = Context.hatToDCtx phat in 
                                "UNIFY(2): " ^ 
                                  P.mctxToString Empty cD0 ^ "\n" ^
                                  P.normalToString Empty cD0 cPsi sM1 ^ "\n    " ^
                                  P.normalToString Empty cD0 cPsi sM2 ^ "\n") in 

              let sM2' = trail (fun () -> prune cD0 (phat, sM2, (mtt, ss), MVarRef r)) in
                instantiateMVar (r, sM2', !cnstrs) 
            with
              | NotInvertible ->
                  (Printf.printf "Added constraints: NotInvertible: \n"
                  ; addConstraint (cnstrs, ref (Eqn (cD0, phat, Clo sM1, Clo sM2))))
          else            
             addConstraint (cnstrs, ref (Eqn (cD0, phat, Clo sM1, Clo sM2)))


    (* normal-MMVar case *)
    | ((_tM1, _s1) as sM1, ((Root (_, MMVar (MInst (r, _cD, _cPsi, _tP, cnstrs), (mt, t)), _tS), s2) as sM2)) ->
        let t' = comp t s2 in
          if isPatSub t' && isPatMSub mt then
            try
              let _ = dprint (fun () -> let cPsi = Context.hatToDCtx phat in 
                                "UNIFY(3): " ^ 
                                  P.mctxToString Empty cD0 ^ "\n" ^
                                  P.normalToString Empty cD0 cPsi sM1 ^ "\n    " ^
                                  P.normalToString Empty cD0 cPsi sM2 ^ "\n") in 
                
              let ss = invert (Whnf.normSub t') in
              let mtt = Whnf.m_invert (Whnf.cnormMSub mt) in 
              let sM1' = trail (fun () -> prune cD0 (phat, sM1, (mtt, ss), MVarRef r)) in
                instantiateMVar (r, sM1', !cnstrs) 
            with
              | NotInvertible ->
                  (Printf.printf "Added constraints: NotInvertible: \n" ;
                  addConstraint (cnstrs, ref (Eqn (cD0, phat, Clo sM1, Clo sM2))))
          else            
             addConstraint (cnstrs, ref (Eqn (cD0, phat, Clo sM1, Clo sM2)))


    | ((Root(_, h1,tS1), s1), (Root(_, h2, tS2), s2)) ->
        (* s1 = s2 = id by whnf *)
        unifyHead  mflag cD0 (phat, h1, h2);
        unifySpine mflag cD0 (phat, (tS1, s1), (tS2, s2))

    | (_sM1, _sM2) ->
        raise_ (Unify "Expression clash")

  and unifyHead mflag cD0 (phat, head1, head2) = 
    let print = P.headToString Empty cD0 (Context.hatToDCtx phat) in
    let _ = dprint (fun () -> "unifyHead  " ^ print head1 ^ "\n"
                            ^ "           " ^ print head2) in
    match (head1, head2) with
    | (BVar k1, BVar k2) ->
        if k1 = k2 then
          ()
        else
          raise_ (Unify "Bound variable clash")

    | (Const c1, Const c2) ->
        if c1 = c2 then
          ()
        else
          raise_ (Unify "Constant clash")

    | (FVar x1, FVar x2) ->
        if x1 = x2 then
          ()
        else
          raise_ (Unify "Free Variable clash")

    | (MVar (Offset k, s) , MVar(Offset k', s')) -> 
        if k = k' then unifySub mflag cD0 phat s s' 
        else raise_ (Unify "Bound MVar clash")

    | (FMVar (u, s) , FMVar(u', s')) ->         
        if u = u' then unifySub mflag cD0 phat s s' 
        else raise_ (Unify "Bound MVar clash") 

    | (PVar (Offset k, s) , PVar(Offset k', s')) -> 
        if k = k' then unifySub mflag cD0 phat s s' 
        else raise_ (Unify "Parameter variable clash")

    | (PVar (PInst (q, _, _, cnstr), s1) as h1, BVar k2) ->
        if isPatSub s1 then
          match bvarSub k2 (invert (Whnf.normSub s1)) with
            | Head (BVar k2') -> instantiatePVar (q, BVar k2', !cnstr)
            | _               -> raise_ (Unify "Parameter violation")
        else
          (* example: q[q[x,y],y] = x  should succeed
                      q[q[x,y],y] = y  should fail
             This will be dealt with when solving constraints.
          *)
          addConstraint (cnstr, ref (Eqh (cD0, phat, h1, BVar k2)))

    | (BVar k1, (PVar (PInst (q, _, _, cnstr), s2) as h1)) ->
        if isPatSub s2 then
          match bvarSub k1 (invert (Whnf.normSub s2)) with
            | Head (BVar k1') -> instantiatePVar (q, BVar k1', !cnstr)
            | _               -> raise_ (Unify "Parameter violation")
        else
          addConstraint (cnstr, ref (Eqh (cD0, phat, BVar k1, h1)))

    | (PVar (PInst (q1, cPsi1, tA1, cnstr1) as q1', s1'),
       PVar (PInst (q2, cPsi2, tA2, cnstr2) as q2', s2')) ->
        (* check s1', and s2' are pattern substitutions; possibly generate constraints
           check intersection (s1', s2'); possibly prune;
           check q1 = q2 *)
        if q1 == q2 then (* cPsi1 = _cPsi2 *)
          match (isPatSub s1' ,  isPatSub s2') with
            | (true, true) ->
                let (s', cPsi') = intersection (phat, (s1', s2'), cPsi1) in
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
                addConstraint (cnstr2, ref (Eqh (cD0, phat, head1, head2))) (*XXX double-check *)
            | (false, _) ->
                addConstraint (cnstr1, ref (Eqh (cD0, phat, head2, head1)))  (*XXX double-check *)
        else
          (match (isPatSub s1' , isPatSub s2') with
             | (true, true) ->
                 (* no occurs check necessary, because s1' and s2' are pattern subs. *)
                 let ss = invert (Whnf.normSub s1') in
                 let (s', cPsi') = pruneCtx (phat, (s2', cPsi2), (MShift 0, ss)) in
                   (* if   cPsi  |- s2' <= cPsi2  and cPsi1 |- ss <= cPsi
                      then cPsi2 |- s' <= cPsi' and [ss](s2' (s')) exists *)
                   (* cPsi' =/= Null ! otherwise no instantiation for
                      parameter variables exists *)
                 let p = Whnf.newPVar (cPsi', TClo(tA2, invert (Whnf.normSub s'))) in
                   (* p::([s'^-1]tA2)[cPsi'] and
                      [|cPsi2.p[s'] / q2 |](q2[s2']) = p[[s2'] s']

                      and   cPsi |- [s2'] s' : cPsi'
                      and   cPsi |- p[[s2'] s'] : [s2'][s'][s'^-1] tA2
                      and [s2'][s'][s'^-1] tA2  = [s2']tA2 *)
                   (instantiatePVar (q2, PVar(p, s'), !cnstr2);
                    instantiatePVar (q1, PVar(p, comp ss (comp s2' s')), !cnstr1))

             | (true, false) ->
                  (* only s1' is a pattern sub
                     [(s1)^-1](q2[s2']) = q2[(s1)^-1 s2']
                  *)
                 let ss1 = invert (Whnf.normSub s1') in 
                 let s' = invSub cD0 (phat, (s2', cPsi2), (MShift 0 , ss1) , PVarRef q1) in
                   instantiatePVar (q1, PVar(q2',s'), !cnstr1)

             | (false, true) ->
                 (* only s2' is a pattern sub *)
                 let ss2 = invert (Whnf.normSub s2') in 
                 let s' = invSub cD0 (phat, (s1', cPsi1), (MShift 0, ss2), PVarRef q2) in
                   instantiatePVar (q2, PVar(q1', s'), !cnstr2)

             | (false, false) ->
                 (* neither s1' nor s2' are patsub *)
                 addConstraint (cnstr1, ref (Eqh (cD0, phat, head1, head2))))

    | (Proj (h1, i1),  Proj (h2, i2)) ->
        if i1 = i2 then
          unifyHead mflag cD0 (phat, h1, h2)
        else
          raise_ (Unify ("(Proj) Index clash: " ^ string_of_int i1 ^ " /= " ^ string_of_int i2))

    | (Proj (PVar (PInst (q, _, _, cnstr), s1), projIndex) as h1, BVar k2) ->
        let _ = (q, cnstr, s1, projIndex, h1, k2) in
          (print_string "humped1\n"; raise_ (Unify "111"))

    | (BVar k2, Proj (PVar (PInst (q, _, _, cnstr), s1), projIndex) as h1) ->
        let _ = (q, cnstr, s1, projIndex, h1, k2) in
          (print_string "humped2\n"; raise_ (Unify "1112"))

    | (FVar _, Proj (PVar _, _)) ->
        (print_string "humped3\n"; raise_ (Unify "333"))

    | (_, Proj (PVar _, _)) ->
        (print_string "humped4\n"; raise_ (Unify "333"))


    | (h1 , h2 ) ->
        (dprint (fun () -> "UNIFY: " ^ P.headToString Empty cD0 (Context.hatToDCtx phat) h1 ^ " == " 
                   ^ P.headToString Empty cD0 (Context.hatToDCtx phat) h2) ; 
         raise_ (Unify "Head clash"))


    (* unifySpine mflag cD0 (phat, (tS1, s1), (tS2, s2)) = ()

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
    and unifySpine mflag cD0 (phat, spine1, spine2) = match (spine1, spine2) with
      | ((Nil, _), (Nil, _)) ->
          ()

      | ((SClo (tS1, s1'), s1), sS) ->
          unifySpine mflag cD0 (phat, (tS1, comp s1' s1), sS)

      | (sS, (SClo (tS2, s2'), s2)) ->
          unifySpine mflag cD0 (phat, sS, (tS2, comp s2' s2))

      | ((App (tM1, tS1), s1), (App (tM2, tS2), s2)) ->
          unifyTerm mflag cD0 (phat, (tM1, s1), (tM2, s2));
          unifySpine mflag cD0 (phat, (tS1, s1), (tS2, s2))
      (* Nil/App or App/Nil cannot occur by typing invariants *)


    and unifySub mflag cD0 phat s1 s2 = match (s1, s2) with 
      | (Shift (psi, n), Shift (phi, k)) -> 
          if n = k && psi = phi then () else raise_ (Error "Substitutions not well-typed")

      | (SVar(Offset s1, sigma1), SVar(Offset s2, sigma2)) 
        -> if s1 = s2 then 
          unifySub mflag cD0 phat sigma1 sigma2
        else raise_ (Error "SVar mismatch")

      | (Dot (f, s), Dot (f', s'))
        -> (unifyFront mflag cD0 phat f f' ;
            unifySub mflag cD0 phat s s')
      
      | (Shift (psi, n), Dot(Head BVar _k, _s')) 
          -> 
           unifySub mflag cD0 phat (Dot (Head (BVar (n+1)), Shift (psi, n+1))) s2

      | (Dot(Head BVar _k, _s'), Shift (psi, n)) 
          ->  
            unifySub mflag cD0 phat s1 (Dot (Head (BVar (n+1)), Shift (psi, n+1)))
          
      |  _
        -> raise_ (Error "Substitution mismatch")


    and unifyFront mflag cD0 phat front1 front2 = match (front1, front2) with
      | (Head (BVar i), Head (BVar k))
        -> if i = k then () else 
              raise_ (Error "Front BVar mismatch")

      | (Head (Const i), Head (Const k))
        -> if i = k then () else raise_ (Error "Front Constant mismatch")

      | (Head (PVar (q, s)), Head (PVar (p, s')))
        -> (if p = q then
            unifySub mflag cD0 phat s s'
            else raise_ (Error "Front PVar mismatch"))


      | (Head (FPVar (q, s)), Head (FPVar (p, s')))
        ->   (if p = q then 
                unifySub mflag cD0 phat s s' 
              else raise_ (Error "Front FPVar mismatch"))

      | (Head (MVar (u, s)), Head (MVar (v, s')))
        ->  (if u = v then
               unifySub mflag cD0 phat s s'
             else raise_ (Error "Front MVar mismatch"))

      | (Head (FMVar (u, s)), Head (FMVar (v, s')))
        ->    (if u = v then
                 unifySub mflag cD0 phat s s'
               else raise_ (Error "Front FMVar mismatch"))

      | (Head (Proj (head, k)), Head (Proj (head', k')))
        ->    (if k = k' then
                 unifyFront mflag cD0 phat (Head head) (Head head')
               else raise_ (Error "Front Proj mismatch"))

      | (Head (FVar x), Head (FVar y)) 
        -> if x = y then () else raise_ (Error "Front FVar mismatch")

      | (Obj tM, Obj tN)
        -> unifyTerm mflag cD0 (phat, (tM, id), (tN, id))

      | (Head head, Obj tN)
        -> unifyTerm mflag cD0 (phat, (Root (None, head, Nil), id), (tN, id))

      | (Obj tN, Head head)
        -> unifyTerm mflag cD0 (phat, (tN, id), (Root (None, head, Nil), id))

      | (Undef, Undef)
        -> ()

      | (_, _)
        -> raise_ (Error "Front mismatch")


    let rec unifyTyp' mflag cD0 (phat, sA, sB) = unifyTypW mflag cD0 (phat, Whnf.whnfTyp sA, Whnf.whnfTyp sB)

    and unifyTypW mflag cD0 (phat, sA, sB) = match (sA, sB) with
      | ((Atom (_, a, tS1), s1),   (Atom (_, b, tS2), s2))  ->
          if a = b then
            unifySpine mflag cD0 (phat, (tS1, s1), (tS2, s2))
          else
            raise_ (Unify "Type constant clash")

      | ((PiTyp ((TypDecl (_x, tA1), _), tB1), s1),   (PiTyp ((TypDecl (_y, tA2), _ ), tB2), s2)) ->
          unifyTyp' mflag cD0 (phat, (tA1, s1), (tA2, s2)) ;
          unifyTyp' mflag cD0 (phat, (tB1, dot1 s1), (tB2, dot1 s2))

      | ((Sigma typrec1, s1),   (Sigma typrec2, s2)) -> 
          begin 
            dprint (fun () -> "**** typrecs " ^
                     "\n" ^ P.typRecToString Empty cD0 Null (typrec1, s1) ^
                     "\n" ^ P.typRecToString Empty cD0 Null (typrec2, s2))
          ; unifyTypRecW mflag cD0 (phat, (typrec1, s1) ,  (typrec2, s2))
          end

      | _ ->
          raise_ (Unify "Type clash")


    and unifyTypRecW mflag cD0 (phat, srec1, srec2) = match (srec1, srec2) with
      | ((SigmaLast t1, s1) ,   (SigmaLast t2, s2)) ->
          dprint (fun () -> "unifyTypRecW ["
                          ^ P.typRecToString Empty cD0 Null srec1
                          ^ "]  ["
                          ^ P.typRecToString Empty cD0 Null srec2 ^ "]");
          unifyTyp' mflag cD0 (phat, (t1,s1), (t2,s2))
        ; dprint (fun () -> "succeeded   ["
                          ^ P.typRecToString Empty cD0 Null srec1
                          ^ "]  ["
                          ^ P.typRecToString Empty cD0 Null srec2 ^ "]");
      
      | ((SigmaElem (_x1, t1, rec1),  s1) ,   (SigmaElem (_x2, t2, rec2),  s2))  ->
           unifyTyp' mflag cD0 (phat, (t1,s1), (t2,s2))
         ; let phat' = Context.addToHat phat
           and s1' = dot1 s1
           and s2' = dot1 s2 in
             unifyTypRecW mflag cD0 (phat', (rec1,s1'), (rec2,s2'))
      
      | ((_, _s1) ,   (_, _s2)) ->
          raise_ (Unify "TypRec length clash")
   

   (* Unify pattern fragment, and force constraints after pattern unification succeeded *)
    let rec unifyDCtx' mflag cD0 cPsi1 cPsi2 = match (cPsi1 , cPsi2) with
      | (Null , Null) -> ()

      | (CtxVar (CtxOffset psi1) , CtxVar (CtxOffset psi2)) -> 
          if psi1 = psi2 then () 
          else raise_ (Unify "CtxVar clash")
      | (DDec (cPsi1, TypDecl(_ , tA1)) , DDec (cPsi2, TypDecl(_ , tA2))) -> 
          let phat  = Context.dctxToHat cPsi1 in 
            unifyDCtx' mflag cD0 cPsi1 cPsi2 ; 
            unifyTyp' mflag cD0 (phat, (tA1, id) ,  (tA2, id))
      | _ -> raise_ (Unify "Context clash")


   (* **************************************************************** *)
    let rec unifyCompTyp cD tau_t tau_t' = 
      unifyCompTypW cD (Whnf.cwhnfCTyp tau_t) (Whnf.cwhnfCTyp tau_t')

    and unifyCompTypW cD tau_t tau_t' = match (tau_t,  tau_t') with
      | ((Comp.TypBox (_, tA, cPsi), t) , (Comp.TypBox (_, tA', cPsi'), t')) -> 
          let phat = Context.dctxToHat cPsi in 
          (unifyDCtx' Unification cD (Whnf.cnormDCtx (cPsi, t)) (Whnf.cnormDCtx (cPsi', t'));
           unifyTyp' Unification cD (phat, (Whnf.cnormTyp (tA, t), id),  (Whnf.cnormTyp (tA', t'), id))
          )

      | ((Comp.TypArr (tau1, tau2), t), (Comp.TypArr (tau1', tau2'), t')) -> 
          (unifyCompTyp cD (tau1, t) (tau1', t') ; 
           unifyCompTyp cD (tau2, t) (tau2', t')
          )


      | ((Comp.TypCross (tau1, tau2), t), (Comp.TypCross (tau1', tau2'), t')) -> 
          (unifyCompTyp cD (tau1, t) (tau1', t') ; 
           unifyCompTyp cD (tau2, t) (tau2', t')
          )

      | ((Comp.TypCtxPi ( _, tau), t) , (Comp.TypCtxPi ( _, tau'), t')) -> 
          unifyCompTyp cD (tau, t) (tau', t')

      | ((Comp.TypPiBox ((MDecl(u, tA, cPsi), _ ), tau), t), 
         (Comp.TypPiBox ((MDecl(_, tA', cPsi'), _ ), tau'), t')) -> 
          let  tAn   = Whnf.cnormTyp (tA, t)  in
          let  tAn'  = Whnf.cnormTyp (tA', t') in 
          let cPsin  = Whnf.cnormDCtx (cPsi, t) in 
          let cPsin' = Whnf.cnormDCtx (cPsi', t') in 
          let phat   = Context.dctxToHat cPsin in 
            (unifyDCtx' Unification cD cPsin cPsin' ; 
             unifyTyp' Unification cD (phat, (tAn, id),  (tAn', id))   ;
             unifyCompTyp (Dec(cD, MDecl(u, tAn, cPsin))) (tau, Whnf.mvar_dot1 t) (tau', Whnf.mvar_dot1 t')
            )



   (* **************************************************************** *)

    let rec unify1 mflag cD0 (phat, sM1, sM2) =
      unifyTerm mflag cD0 (phat, sM1, sM2);
      forceCnstr mflag (nextCnstr ())

    (* NOTE: We sometimes flip the position when we generate constraints
       if matching requires that the first argument is fixed then this may
       become problematic if we are outside the pattern fragment -bp *)
    and forceCnstr mflag constrnt = match constrnt with
      | None       -> ()   (* all constraints are forced *)
      | Some cnstr ->
          match !cnstr with
            | Queued (* in process elsewhere *) ->  forceCnstr mflag (nextCnstr ())
            | Eqn (cD, phat, tM1, tM2) ->
                let _ = solveConstraint cnstr in 
                unify1 mflag cD (phat, (tM1, id), (tM2, id))
            | Eqh (cD, phat, h1, h2)   ->
                let _ = solveConstraint cnstr in 
                  unifyHead mflag cD (phat, h1, h2) 
    
    let unify' mflag cD0 (phat, sM1, sM2) =
      resetDelayedCnstrs ();
      unify1 mflag cD0 (phat, sM1, sM2)

    let unifyTyp1 mflag cD0 (phat, sA, sB) = 
      let _ = unifyTyp' mflag cD0 (phat, sA, sB) in 
      let _ = dprint (fun () -> "unifyTyp1: AWAKEN CONSTRAINTS") in 
        forceCnstr mflag (nextCnstr ())

    let unifyTyp' mflag cD0 (phat, sA, sB) =
      let _ = dprint (fun () -> "CALLING UNIFYTYP" ) in 
      let cPsi = phatToDCtx phat in 
      let _ = dprint (fun () -> "unifyTyp:\n" ^  "  |- " ^ 
         P.typToString Empty cD0 cPsi sA ^ "\n     " ^ 
         P.typToString Empty cD0 cPsi sB  ^ "\n") in 
       let _ = (resetDelayedCnstrs ();
                unifyTyp1 mflag cD0 (phat, sA, sB)) in  
         ()

    let unifyTypRec1 mflag cD0 (phat, sArec, sBrec) = 
      unifyTypRecW mflag cD0 (phat, sArec, sBrec);
      forceCnstr mflag (nextCnstr ())

    let unifyTypRec' mflag cD0 (phat, sArec, sBrec) =
      resetDelayedCnstrs ();
      unifyTypRec1 mflag cD0 (phat, sArec, sBrec)


    let unify cD0 (phat, sM, sN) = 
      unify' Unification cD0 (phat, sM, sN)

    let unifyTypRec cD0 (phat, sArec, sBrec) =
        unifyTypRec' Unification cD0 (phat, sArec, sBrec) 

    let unifyTyp cD0 (phat, sA, sB) = 
      unifyTyp' Unification cD0 (phat, sA, sB)


    let unifyDCtx cD0 cPsi1 cPsi2 =
      unifyDCtx' Unification cD0 cPsi1 cPsi2

    let matchDCtx cD0 cPsi1 cPsi2 = 
      unifyDCtx' Matching cD0 cPsi1 cPsi2

    let matchTerm cD0 (phat, sM, sN) = 
      unify' Matching cD0 (phat, sM, sN)

    let matchTypRec cD0 (phat, sArec, sBrec) =
        unifyTypRec' Matching cD0 (phat, sArec, sBrec) 

    let matchTyp cD0 (phat, sA, sB) = 
      unifyTyp' Matching cD0 (phat, sA, sB)

 
      
end

module EmptyTrail = Make (EmptyTrail)
module StdTrail   = Make (StdTrail)
