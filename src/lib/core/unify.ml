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

open Context
open Syntax.Int.LF
open Syntax.Int
open Trail

module P = Pretty.Int.DefaultPrinter

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

  val unify    : mctx -> psi_hat * nclo * nclo -> unit (* raises  Unify *)
  val unifyTyp : mctx -> psi_hat * tclo * tclo -> unit (* raises Unify *)
  val unifyDCtx:   mctx -> dctx -> dctx -> unit (* raises Unify *)
  val unifyCompTyp : mctx -> (Comp.typ * Comp.msub) -> (Comp.typ * Comp.msub) -> unit (* raises Unify *)
end

(* Unification *)
(* Author: Brigitte Pientka *)
(* Trailing is taken from Twelf 1.5 *)

module Make (T : TRAIL) : UNIFY = struct

  open Substitution.LF
  module Print = Pretty.Int.DefaultPrinter

  exception Unify of string

  exception NotInvertible

  exception Error of string

  type cvarRef =
    | MVarRef of normal option ref
    | PVarRef of head option ref


  let eq_cvarRef cv cv' = match (cv, cv') with
    | (MVarRef r, MVarRef r') -> r == r'
    | (PVarRef r, PVarRef r') -> r == r'
    | (_, _)                  -> false

  let rec raiseType cPsi tA = match cPsi with
    | Null -> tA
    | DDec (cPsi', decl) ->
        raiseType cPsi' (PiTyp (decl, tA))

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
      try f () with e -> (unwind (); raise e)


  (* initial success continuation used in prune *)
  let idsc = fun () -> ()
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


  (* pruneCtx (phat, (t, Psi1), ss) = (s', cPsi2)

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
         begin match bvarSub k ss with
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
    invNorm' cD0 (phat, Whnf.whnf sM, ss, rOccur)

  and invNorm' cD0 ((cvar, offset) as phat, sM, ss, rOccur) = match sM with
    | (Lam (loc, x, tM), s) ->
        Lam (loc, x, invNorm cD0 ((cvar, offset + 1), (tM, dot1 s), dot1 ss, rOccur))

    | (Root (loc, MVar (Inst (r, cPsi1, _tP, _cnstrs) as u, t), _tS (* Nil *)), s) ->
        (* by invariant tM is in whnf and meta-variables are lowered;
           hence tS = Nil and s = id *)
        if eq_cvarRef (MVarRef r) rOccur then
          raise NotInvertible
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
                  Root(loc, MVar(u, comp t' ss), Nil)
                else
                  raise NotInvertible
            else (* t' not patsub *)
              Root(loc, MVar(u, invSub cD0 (phat, (t', cPsi1), ss, rOccur)), Nil)

    | (Root (loc, MVar (Offset u, t), _tS (* Nil *)), s (* id *)) ->
        let t' = comp t s (* t' = t, since s = Id *) in
        let (_tA, cPsi1) = Cwhnf.mctxMDec cD0 u in 
          Root(loc, MVar(Offset u, invSub cD0 (phat, (t', cPsi1), ss, rOccur)), Nil)

    | (Root (loc, FMVar (u, t), _tS (* Nil *)), s (* id *)) ->
        let (_tA, cPsi1) = Store.FMVar.get u in 
        let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
          Root (loc, FMVar (u, s'), Nil)

    | (Root (loc, FPVar (p, t), _tS (* Nil *)), s (* id *)) ->
        let (_tA, cPsi1) = Store.FPVar.get p in 
        let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
          Root (loc, FPVar (p, s'), Nil)

    | (Root (loc, PVar (Offset p, t), _tS (* Nil *)), s (* id *)) ->
        let (_tA, cPsi1) = Cwhnf.mctxPDec cD0 p in 
        let t' = comp t s (* t' = t, since s = Id *) in
          Root(loc, PVar(Offset p, invSub cD0 (phat, (t', cPsi1), ss, rOccur)), Nil)

    | (Root (loc, PVar (PInst (r, cPsi1, _tA, _cnstrs) as q, t), tS), s) ->
        (* by invariant tM is in whnf and meta-variables are lowered and s = id *)
        if eq_cvarRef (PVarRef r) rOccur then
          raise NotInvertible
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
                  Root (loc, PVar (q, comp t' ss), 
                        invSpine cD0 (phat, (tS, s), ss, rOccur))
                else
                  raise NotInvertible
            else (* t' not patsub *)
              Root (loc, PVar (q, invSub cD0 (phat, (t', cPsi1), ss, rOccur)),
                    invSpine cD0 (phat, (tS,s), ss, rOccur))

    | (Root (loc, Proj (PVar (PInst (r, cPsi1, _tA, _cnstrs) as q, t), i), tS), s) ->
        if eq_cvarRef (PVarRef r) rOccur then
          raise NotInvertible
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
                  Root (loc, Proj (PVar(q, comp t' ss), i),
                        invSpine cD0 (phat, (tS,s), ss, rOccur))
                else
                  raise NotInvertible
            else (* t' not patsub *)
              Root (loc, Proj (PVar (q, invSub cD0 (phat, (t', cPsi1), ss, rOccur)), i),
                    invSpine cD0 (phat, (tS,s), ss, rOccur))

    | (Root (loc, head, tS), s (* = id *)) ->
        Root (loc, invHead  cD0 (phat, head   , ss, rOccur),
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
  and invHead _cD0 (_phat, head, ss, _rOccur) = match head with
    | BVar k            ->
        begin match bvarSub k ss with
          | Undef          -> raise NotInvertible
          | Head (BVar k') -> BVar k'
        end

    | Const _           ->
        head

    | Proj (BVar k, _i) ->
        begin match bvarSub k ss with
          | Head (BVar _k' as head) -> head
          | Undef                   -> raise NotInvertible
        end

    | FVar _x           -> head
      (* For any free variable x:tA, we have  . |- tA <= type ;
         Occurs check is necessary on tA Dec 15 2008 -bp  :(
       *)

  (* invSub cD0 (phat, s, ss, rOccur) = s'

     if phat = hat(Psi)  and
        D ; Psi  |- s <= Psi'
        D ; Psi''|- ss <= Psi
     then s' = [ss]s   if it exists, and
        D ; cPsi'' |- [ss]s <= cPsi'
   *)
  and invSub cD0 (phat, (s, cPsi1), ss, rOccur) = match (s, cPsi1) with
    | (Shift (psi, n), DDec(_cPsi', _dec)) ->
        invSub cD0 (phat, (Dot (Head (BVar (n + 1)), Shift (psi, n + 1)), cPsi1), ss, rOccur)

    | (Shift (psi, n), Null) -> comp (Shift (psi, n)) ss  
      (* Sat Dec 27 15:45:18 2008 -bp DOUBLE CHECK *)
      (* must be defined -- n = offset
       * otherwise it is undefined 
       *)

    | (Shift (psi, n), CtxVar _psi) -> comp (Shift (psi, n)) ss  
        (* Sat Dec 27 15:45:18 2008 -bp DOUBLE CHECK *)
        (* must be defined -- n = offset
         * otherwise it is undefined 
         *)

    | (Dot (Head (BVar n), s'), DDec(cPsi', _dec)) ->
        begin match bvarSub n ss with
          | Undef -> raise NotInvertible
          | ft    -> Dot (ft, invSub cD0 (phat, (s', cPsi'), ss, rOccur))
        end

    | (Dot (Obj tM, s'), DDec(cPsi', _dec))        ->
        (* below may raise NotInvertible *)
        Dot (Obj (invNorm cD0 (phat, (tM, id), ss, rOccur)), invSub cD0 (phat, (s', cPsi'), ss, rOccur))


  (* intersection (phat, (s1, s2), cPsi') = (s', cPsi'')
     s' = s1 /\ s2 (see JICSLP'96 and Pientka's thesis)

     Invariant:
     If   D ; Psi  |- s1 : Psi'    s1 patsub
     and  D ; Psi  |- s2 : Psi'    s2 patsub
     then D ; Psi' |- s' : Psi'' for some Psi'' which is a subset of Psi'
     and  s' patsub
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

    | (s1, s2, cPsi )  -> 
        (Printf.printf "Intersection of: \n s1 = %s \n s2 = %s \n in context cPsi = %s not defined. \n\n"
           (Pretty.Int.DefaultPrinter.subToString s1)
           (Pretty.Int.DefaultPrinter.subToString s2)
           (Pretty.Int.DefaultPrinter.dctxToString cPsi);
           raise (Error "Intersection not defined"))


  (* prune cD0 (phat, (tM, s), ss, rOccur) = tM'

     Given: a success continuation sc
            cD ; cPsi  |- s <= cPsi'  and
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
    let _qq : sub = ss in
      prune' cD0 (phat, Whnf.whnf sM, ss, rOccur)

  and prune' cD0 ((cvar, offset) as phat, sM, ss, rOccur) = match sM with
    | (Lam (loc, x, tM), s) ->
        let tM' = prune cD0 ((cvar, offset + 1), (tM, dot1 s), dot1 ss, rOccur) in
          Lam (loc, x, tM')

    | (Root (loc, MVar (Inst (r, cPsi1, tP, cnstrs) as u, t), _tS (* Nil *)) as tM, s (* id *)) ->
      (* by invariant: MVars are lowered since tM is in whnf *)
        if eq_cvarRef (MVarRef r) rOccur then
          raise (Unify "Variable occurrence")
        else
          if isPatSub t then
            let (idsub, cPsi2) = pruneCtx (phat, (comp t s, cPsi1), ss) in
              (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                 cD ; cPsi |-  t o s <= cPsi1 and
                 cD ; cPsi1 |- idsub <= cPsi2 and
                 cD ; cPsi |- t o s o idsub <= cPsi2 *)
            let v = Whnf.newMVar(cPsi2, TClo(tP, invert idsub)) in
              (instantiateMVar (r, Root (loc, MVar (v, idsub), Nil), !cnstrs);
               Clo(tM, comp s ss)
              )
                (* [|v[idsub] / u|] *)
          else (* s not patsub *)
            (* cD ; cPsi' |- u[t] <= [t]tP, and u::tP[cPsi1]  and 
               cD ; cPsi' |- t <= cPsi1
               cD ; cPsi  |- s <= cPsi'
               CD ; cPsi  |- comp t s <= cPsi1  and cD ; cPsi''|- ss <= cPsi
               s' = [ss]([s]t) and  cD ; cPsi'' |- s' <= cPsi'  *)
            let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
              Root (loc, MVar (u, s'), Nil)
                (* may raise NotInvertible *)

    | (Root (loc, MVar (Offset u, t), _tS (* Nil *)), s (* id *)) ->
        let (_tA, cPsi1) = Cwhnf.mctxMDec cD0 u in 
        let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
          Root (loc, MVar (Offset u, s'), Nil)


    | (Root (loc, FMVar (u, t), _tS (* Nil *)), s (* id *)) ->
        let (_tA, cPsi1) = Store.FMVar.get u in 
        let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
          Root (loc, FMVar (u, s'), Nil)

    | (Root (loc, FPVar (p, t), _tS (* Nil *)), s (* id *)) ->
        let (_tA, cPsi1) = Store.FPVar.get p in 
        let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
          Root (loc, FPVar (p, s'), Nil)

    | (Root (loc, PVar (Offset p, t), _tS (* Nil *)), s (* id *)) ->
        let (_tA, cPsi1) = Cwhnf.mctxPDec cD0 p in 
        let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
          Root (loc, PVar (Offset p, s'), Nil)

    | (Root (loc, PVar (PInst (r, cPsi1, tA, cnstrs) as q, t), tS), s (* id *)) ->
        if eq_cvarRef (PVarRef r) rOccur then
          raise (Unify "Parameter variable occurrence")
        else
          if isPatSub t then
            let (idsub, cPsi2) = pruneCtx(phat, (comp t s, cPsi1), ss) in
              (* cD ; cPsi1 |- idsub <= cPsi2 *)
            let p = Whnf.newPVar (cPsi2, TClo(tA, invert idsub)) (* p::([(idsub)^-1]tA)[cPsi2] *) in
            let _ = instantiatePVar (r, PVar (p, idsub), !cnstrs) in
              (* [|p[idsub] / q|] *)
            let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
              (* h = p[[ss] ([t] idsub)] *)
              Root (loc, PVar(p, comp ss (comp t idsub)), tS')
          else (* s not patsub *)
            let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur)
            and tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
              Root (loc, PVar (q, s'), tS')


    | (Root (loc, Proj (PVar (PInst (r, cPsi1, tA, cnstrs) as q, t), i), tS), s (* id *)) ->
        if eq_cvarRef (PVarRef r) rOccur then
          raise (Unify "Parameter variable occurrence")
        else
          if isPatSub t then
            let (idsub, cPsi2) = pruneCtx(phat, (comp t s, cPsi1), ss) in
              (* cD ; cPsi1 |- idsub <= cPsi2 *)
            let p = Whnf.newPVar(cPsi2, TClo(tA, invert idsub)) (* p::([(idsub)^-1] tA)[cPsi2] *) in
            let _ = instantiatePVar (r, PVar (p, idsub), !cnstrs) (* [|p[idsub] / q|] *) in
            let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
              Root(loc, PVar(p, comp ss (comp t idsub)), tS')
          else (* s not patsub *)
            let s' = invSub cD0 (phat, (comp t s, cPsi1), ss, rOccur) in
            let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
              Root (loc, Proj (PVar (q, s'), i), tS')

    | (Root (loc, (*H as*) BVar k, tS), s (* = id *)) ->
        begin match bvarSub k ss with
          | Undef                -> raise (Unify "Bound variable dependency")
          | Head (BVar _k as h') ->
              let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
                Root (loc, h', tS')
        end

    | (Root (loc, (Const _ as h), tS), s (* id *)) ->
        let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
          Root(loc, h, tS')

    | (Root (loc, (FVar _ as h), tS), s (* id *)) ->
        let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
          Root(loc, h, tS')

    | (Root (loc, Proj (BVar k, i), tS), s (* id *)) ->
        let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
          begin match bvarSub k ss with
            | Head (BVar _k' as h') -> Root (loc, Proj (h', i), tS')
            | _                     -> raise (Unify "Bound variable dependency")
          end


  and pruneSpine cD0 (phat, spine, ss, rOccur) = match spine with
    | (Nil, _s)           -> Nil

    | (App (tM, tS), s)   ->
        let tM' = prune cD0 (phat, (tM, s), ss, rOccur) in
        let tS' = pruneSpine cD0 (phat, (tS, s), ss, rOccur) in
          App (tM', tS')

    | (SClo (tS, s'), s) ->
        pruneSpine cD0 (phat, (tS, comp s' s), ss, rOccur)


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


  let rec unifyTerm cD0 (phat, sN, sM) = unifyTerm' cD0 (phat, Whnf.whnf sN, Whnf.whnf sM)

  and unifyTerm' cD0 (((psi, offset) as phat), sN, sM) = match (sN, sM) with
    | ((Lam (_, _, tN), s1), (Lam (_, _, tM), s2)) ->
        unifyTerm cD0 ((psi, offset + 1), (tN, dot1 s1), (tM, dot1 s2))

    (* MVar-MVar case *)
    (* remove sM1, sM2 -bp *)
    | ((((Root (_, MVar (Inst (r1,  cPsi1,  tP1, cnstrs1), t1), _tS1) as _tM1), s1)  as sM1),
       ((((Root (_, MVar (Inst (r2, _cPsi2, _tP2, cnstrs2), t2), _tS2) as _tM2), s2)) as sM2)) ->
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
                  addConstraint (cnstrs2, ref (Eqn (phat, Clo sM, Clo sN))) (* XXX double-check *)
              | (false, _) ->
                  addConstraint (cnstrs1, ref (Eqn (phat, Clo sN, Clo sM)))  (* XXX double-check *)
          else
            begin match (isPatSub t1' , isPatSub t2') with
              | (true, _) ->
                  (* cD ; cPsi' |- t1 <= cPsi1 and cD ; cPsi |- t1 o s1 <= cPsi1 *)
                  begin try

                    let ss1  = invert (Whnf.normSub t1') (* cD ; cPsi1 |- ss1 <= cPsi *) in
                    let tM2' = trail (fun () -> prune cD0 (phat, sM2, ss1, MVarRef r1)) in 
                    (* sM2 = [ss1][s2]tM2 *) 

                    instantiateMVar (r1, tM2', !cnstrs1) 
                  with
                    | NotInvertible ->
                        addConstraint (cnstrs1, ref (Eqn (phat, Clo sM1, Clo sM2)))
                  end
              | (false, true) ->
                  begin try
                    let ss2 = invert (Whnf.normSub t2')(* cD ; cPsi2 |- ss2 <= cPsi *) in
                    let tM1' = trail (fun () -> prune cD0 (phat, sM1, ss2, MVarRef r2)) in
                      instantiateMVar (r2, tM1', !cnstrs2)                       
                  with
                    | NotInvertible ->
                        addConstraint (cnstrs2, ref (Eqn (phat, Clo sM2, Clo sM1)))
                  end
              | (false , false) ->
                  (* neither t1' nor t2' are pattern substitutions *)
                  let cnstr = ref (Eqn (phat, Clo sM1, Clo sM2)) in
                    addConstraint (cnstrs1, cnstr)
            end
    (* MVar-normal case *)
    | ((Root (_, MVar (Inst (r, _cPsi, _tP, cnstrs), t), _tS), s1) as sM1, ((_tM2, _s2) as sM2)) ->
        let t' = comp t s1 in
          if isPatSub t' then
            try
              let ss = invert (Whnf.normSub t') in
              let sM2' = trail (fun () -> prune cD0 (phat, sM2, ss, MVarRef r)) in
                instantiateMVar (r, sM2', !cnstrs) 
            with
              | NotInvertible ->
                  addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))
          else
            addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))

    (* normal-MVar case *)
    | ((_tM1, _s1) as sM1, ((Root (_, MVar (Inst (r, _cPsi, _tP, cnstrs), t), _tS), s2) as sM2)) ->
        let t' = comp t s2 in
          if isPatSub t' then
            try

              let ss = invert (Whnf.normSub t') in
              let sM1' = trail (fun () -> prune cD0 (phat, sM1, ss, MVarRef r)) in
                instantiateMVar (r, sM1', !cnstrs) 
            with
              | NotInvertible ->
                  (let _ = Printf.printf "Raised NotInvertible! – Left-over constraints...\n" in 
                  addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2))))
          else
            addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))

    | ((Root(_, h1,tS1), s1), (Root(_, h2, tS2), s2)) ->
        (* s1 = s2 = id by whnf *)
        unifyHead  cD0 (phat, h1, h2);
        unifySpine cD0 (phat, (tS1, s1), (tS2, s2))

    | (_sM1, _sM2) ->
        raise (Unify "Expression clash")

  and unifyHead cD0 (phat, head1, head2) = match (head1, head2) with
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
        if k = k' then unifySub cD0 phat s s' 
        else raise (Unify "Bound MVar clash")

    | (FMVar (u, s) , FMVar(u', s')) ->         
        if u = u' then unifySub cD0 phat s s' 
        else raise (Unify "Bound MVar clash") 

    | (PVar (Offset k, s) , PVar(Offset k', s')) -> 
        if k = k' then unifySub cD0 phat s s' 
        else raise (Unify "Bound MVar clash")


    | (PVar (PInst (q, _, _, cnstr), s1) as h1, BVar k2) ->
        if isPatSub s1 then
          match bvarSub k2 (invert (Whnf.normSub s1)) with
            | Head (BVar k2') -> instantiatePVar (q, BVar k2', !cnstr)
            | _               -> raise (Unify "Parameter violation")
        else
          (* example: q[q[x,y],y] = x  should succeed
                      q[q[x,y],y] = y  should fail
             This will be dealt with when solving constraints.
          *)
          addConstraint (cnstr, ref (Eqh (phat, h1, BVar k2)))

    | (BVar k1, (PVar (PInst (q, _, _, cnstr), s2) as h1)) ->
        if isPatSub s2 then
          match bvarSub k1 (invert (Whnf.normSub s2)) with
            | Head (BVar k1') -> instantiatePVar (q, BVar k1', !cnstr)
            | _               -> raise (Unify "Parameter violation")
        else
          addConstraint (cnstr, ref (Eqh (phat, BVar k1, h1)))

    | (PVar (PInst (q1, cPsi1, tA1, cnstr1) as q1', s1'),
       PVar (PInst (q2, cPsi2, tA2, cnstr2) as q2', s2')) ->
        (* check s1', and s2' are pattern substitutions; possibly generate constraints
           check intersection (s1', s2'); possibly prune;
           check q1 = q2 *)
        if q1 == q2 then (* cPsi1 = _cPsi2 *)
          match (isPatSub s1' ,  isPatSub s2' ) with
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
                addConstraint (cnstr2, ref (Eqh (phat, head1, head2))) (*XXX double-check *)
            | (false, _) ->
                addConstraint (cnstr1, ref (Eqh (phat, head2, head1)))  (*XXX double-check *)
        else
          (match (isPatSub s1' , isPatSub s2') with
             | (true , true) ->
                 (* no occurs check necessary, because s1' and s2' are pattern subs. *)
                 let ss = invert (Whnf.normSub s1') in
                 let (s', cPsi') = pruneCtx (phat, (s2', cPsi2), ss) in
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
                 let s' = invSub cD0 (phat, (s2', cPsi2), invert (Whnf.normSub s1'), PVarRef q1) in
                   instantiatePVar (q1, PVar(q2',s'), !cnstr1)

             | (false , true) ->
                 (* only s2' is a pattern sub *)
                 let s' = invSub cD0 (phat, (s1', cPsi1), invert (Whnf.normSub s2'), PVarRef q2) in
                   instantiatePVar (q2, PVar(q1', s'), !cnstr2)

             | (false , false) ->
                 (* neither s1' nor s2' are patsub *)
                 addConstraint (cnstr1, ref (Eqh (phat, head1, head2))))

    | (_ , _ ) -> raise (Unify "Head clash")

    (* Not Implemented: Cases for projections

            Proj(BVar k, i), Proj(BVar k', i)
            Proj(BVar k, i), Proj(PVar(q, _,_, cnstr), i)
            Proj(PVar(q, _,_, cnstr), i), Proj(BVar k, i)

     *)

    (* unifySpine cD0 (phat, (tS1, s1), (tS2, s2)) = ()

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
    and unifySpine cD0 (phat, spine1, spine2) = match (spine1, spine2) with
      | ((Nil, _), (Nil, _)) ->
          ()

      | ((SClo (tS1, s1'), s1), sS) ->
          unifySpine cD0 (phat, (tS1, comp s1' s1), sS)

      | (sS, (SClo (tS2, s2'), s2)) ->
          unifySpine cD0 (phat, sS, (tS2, comp s2' s2))

      | ((App (tM1, tS1), s1), (App (tM2, tS2), s2)) ->
          unifyTerm cD0 (phat, (tM1, s1), (tM2, s2));
          unifySpine cD0 (phat, (tS1, s1), (tS2, s2))
      (* Nil/App or App/Nil cannot occur by typing invariants *)


    and unifySub cD0 phat s1 s2 = match (s1, s2) with 
      | (Shift (psi, n), Shift (phi, k)) -> 
          if n = k && psi = phi then () else raise (Error "Substitutions not well-typed")

      | (SVar(Offset s1, sigma1), SVar(Offset s2, sigma2)) 
        -> if s1 = s2 then 
          unifySub cD0 phat sigma1 sigma2
        else raise (Error "SVar mismatch")

      | (Dot (f, s), Dot (f', s'))
        -> (unifyFront cD0 phat f f' ;
            unifySub cD0 phat s s')
      
      | (Shift (psi, n), Dot(Head BVar _k, _s')) 
          -> 
           unifySub cD0 phat (Dot (Head (BVar (n+1)), Shift (psi, n+1))) s2

      | (Dot(Head BVar _k, _s'), Shift (psi, n)) 
          ->  
            unifySub cD0 phat s1 (Dot (Head (BVar (n+1)), Shift (psi, n+1)))
          
      |  _
        -> raise (Error "Substitution mismatch")


    and unifyFront cD0 phat front1 front2 = match (front1, front2) with
      | (Head (BVar i), Head (BVar k))
        -> (if i = k then () else 
              raise (Error ("Front BVar mismatch: "^ (P.headToString (BVar i)) ^ " and " ^ (P.headToString (BVar k))) ))

      | (Head (Const i), Head (Const k))
        -> if i = k then () else raise (Error "Front Constant mismatch")

      | (Head (PVar (q, s)), Head (PVar (p, s')))
        -> (if p = q then
            unifySub cD0 phat s s'
            else raise (Error "Front PVar mismatch"))


      | (Head (FPVar (q, s)), Head (FPVar (p, s')))
        ->   (if p = q then 
                unifySub cD0 phat s s' 
              else raise (Error "Front FPVar mismatch"))

      | (Head (MVar (u, s)), Head (MVar (v, s')))
        ->  (if u = v then
               unifySub cD0 phat s s'
             else raise (Error "Front MVar mismatch"))

      | (Head (FMVar (u, s)), Head (FMVar (v, s')))
        ->    (if u = v then
                 unifySub cD0 phat s s'
               else raise (Error "Front FMVar mismatch"))

      | (Head (Proj (head, k)), Head (Proj (head', k')))
        ->    (if k = k' then
                 unifyFront cD0 phat (Head head) (Head head')
               else raise (Error "Front Proj mismatch"))

      | (Head (FVar x), Head (FVar y)) 
        -> if x = y then () else raise (Error "Front FVar mismatch")

      | (Obj tM, Obj tN)
        -> unifyTerm cD0 (phat, (tM, id), (tN, id))

      | (Head head, Obj tN)
        -> unifyTerm cD0 (phat, (Root (None, head, Nil), id), (tN, id))

      | (Obj tN, Head head)
        -> unifyTerm cD0 (phat, (tN, id), (Root (None, head, Nil), id))

      | (Undef, Undef)
        -> ()

      | (_, _)
        -> raise (Error "Front mismatch")


    let rec unifyTyp' cD0 (phat, sA, sB) = unifyTypW cD0 (phat, Whnf.whnfTyp sA, Whnf.whnfTyp sB)

    and unifyTypW cD0 (phat, sA, sB) = match (sA, sB) with
      | ((Atom (a, tS1), s1), (Atom (b, tS2), s2))  ->
          if a = b then
            unifySpine cD0 (phat, (tS1, s1), (tS2, s2))
          else
            raise (Unify "Type constant clash")

      | ((PiTyp (TypDecl (_x, tA1), tB1), s1), (PiTyp (TypDecl (_y, tA2), tB2), s2)) -> (
          unifyTyp' cD0 (phat, (tA1, s1), (tA2, s2));
          unifyTyp' cD0 (phat, (tB1, dot1 s1), (tB2, dot1 s2))
        )

      | _ ->
          raise (Unify "Type clash")


   (* Unify pattern fragment, and force constraints after pattern unification succeeded *)


    let rec unifyDCtx cD0 cPsi1 cPsi2 = match (cPsi1 , cPsi2) with
      | (Null , Null) -> ()
      | (CtxVar (CtxOffset psi1) , CtxVar (CtxOffset psi2)) -> 
          if psi1 = psi2 then () 
          else raise (Unify "CtxVar clash")
      | (DDec (cPsi1, TypDecl(_ , tA1)) , DDec (cPsi2, TypDecl(_ , tA2))) -> 
          let phat  = Context.dctxToHat cPsi1 in 
          (unifyDCtx cD0 cPsi1 cPsi2 ; 
           unifyTyp' cD0 (phat, (tA1, id) ,  (tA2, id)))
      | _ -> raise (Unify "Context clash")


   (* **************************************************************** *)
    let rec unifyCompTyp cD tau_t tau_t' = 
      unifyCompTypW cD (Cwhnf.cwhnfCTyp tau_t) (Cwhnf.cwhnfCTyp tau_t')

    and unifyCompTypW cD tau_t tau_t' = match (tau_t,  tau_t') with
      | ((Comp.TypBox (tA, cPsi), t) , (Comp.TypBox (tA', cPsi'), t')) -> 
          let phat = Context.dctxToHat cPsi in 
          (unifyDCtx cD (Cwhnf.cnormDCtx (cPsi, t)) (Cwhnf.cnormDCtx (cPsi', t'));
           unifyTyp' cD (phat, (Cwhnf.cnormTyp (tA, t), id),  (Cwhnf.cnormTyp (tA', t'), id))
          )

      | ((Comp.TypArr (tau1, tau2), t), (Comp.TypArr (tau1', tau2'), t')) -> 
          (unifyCompTyp cD (tau1, t) (tau1', t') ; 
           unifyCompTyp cD (tau2, t) (tau2', t')
          )

      | ((Comp.TypCtxPi (_, tau), t) , (Comp.TypCtxPi (_, tau'), t')) -> 
          unifyCompTyp cD (tau, t) (tau', t')

      | ((Comp.TypPiBox ((MDecl(u, tA, cPsi), _ ), tau), t), (Comp.TypPiBox ((MDecl(_, tA', cPsi'), _ ), tau'), t')) -> 
          let  tAn   = Cwhnf.cnormTyp (tA, t)  in
          let  tAn'  = Cwhnf.cnormTyp (tA', t') in 
          let cPsin  = Cwhnf.cnormDCtx (cPsi, t) in 
          let cPsin' = Cwhnf.cnormDCtx (cPsi', t') in 
          let phat   = Context.dctxToHat cPsin in 
            (unifyDCtx cD cPsin cPsin' ; 
             unifyTyp'  cD (phat, (tAn, id),  (tAn', id))   ;
             unifyCompTyp (Dec(cD, MDecl(u, tAn, cPsin))) (tau, t) (tau', t')
            )



   (* **************************************************************** *)

    let rec unify1 cD0 (phat, sM1, sM2) =
      unifyTerm cD0 (phat, sM1, sM2);
      forceCnstr cD0 (nextCnstr ())

    and forceCnstr cD0 constrnt = match constrnt with
      | None       -> ()   (* all constraints are forced *)
      | Some cnstr ->
          match !cnstr with
            | Queued (* in process elsewhere *) ->  forceCnstr cD0 (nextCnstr ())
            | Eqn (phat, tM1, tM2) ->
                solveConstraint cnstr;
                unify1 cD0 (phat, (tM1, id), (tM2, id))
            | Eqh (phat, h1, h2)   ->
                solveConstraint cnstr;
                unifyHead cD0 (phat, h1, h2)

    let unify cD0 (phat, sM1, sM2) =
      resetDelayedCnstrs ();
      unify1 cD0 (phat, sM1, sM2)

    let unifyTyp cD0 (phat, sA, sB) =
      resetDelayedCnstrs ();
      unifyTyp' cD0 (phat, sA, sB)
end

module EmptyTrail = Make (EmptyTrail)
module StdTrail   = Make (StdTrail)
