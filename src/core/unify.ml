open Support
open Equality

(**
   @author Brigitte Pientka
   code walk with Joshua Dunfield, Dec 3 2008
*)


(* The functor itself is called Make (hence Unify.Make to other modules);
   the instantiations EmptyTrail and StdTrail (hence Unify.EmptyTrail and Unify.StdTrail
   to other modules) are declared at the end of this file.
*)
open Store
open Syntax.Int.LF
open Syntax.Int
open Trail

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
module Loc = Location

let (dprintf, dprint, dprnt) = Debug.makeFunctions' (Debug.toFlags [15])
open Debug.Fmt

(** Call when creating a new constraint so constraints can have a
    recognizable identity in debug messages.
 *)
let next_constraint_id =
  let counter = ref 0 in
  fun () ->
  incr counter;
  !counter

let numPruneSub = ref 0

(* let print_trail () =
   Printf.printf "\nPruneSub failed because notInvertible : %d times.\n" !numPruneSub *)


module type UNIFY = sig
  type unifTrail

  exception Error of string

(*  val disallowUndefineds : (unit -> 'a) -> 'a *)

  (* trailing of variable instantiation *)

  val reset : unit -> unit
  val mark : unit -> unit
  val unwind : unit -> unit

  val instantiateMVar : iterm option ref * normal * cnstr list -> unit
  val instantiateCtxVar : iterm option ref * dctx -> unit

  val resetDelayedCnstrs : unit -> unit
  val resetGlobalCnstrs : unit -> unit
  val globalCnstrs : cnstr list ref
  val unresolvedGlobalCnstrs : unit -> bool

  val nextCnstr : unit -> cnstr option
  val addConstraint : cnstr list ref * cnstr -> unit
  val forceGlobalCnstr : unit -> unit
  val solveConstraint : cnstr -> unit

  val isVar : head -> bool
  val isPatSub : sub -> bool
  val isProjPatSub : sub -> bool
  val isPatMSub : msub -> bool

  (* unification *)

  val intersection : dctx_hat -> sub -> sub -> dctx -> (sub * dctx)

  exception Failure of string
  exception GlobalCnstrFailure of Loc.t * string
  exception NotInvertible

  (* All unify* functions return () on success and raise Failure on failure *)
  val unify : mctx -> dctx -> nclo -> nclo -> unit
  val unifyH : mctx -> dctx_hat -> head -> head -> unit
  val unifySub : mctx -> dctx -> sub -> sub -> unit
  val unifyTyp : mctx -> dctx -> tclo -> tclo -> unit
  val unifyTypRec : mctx -> dctx -> typ_rec * sub -> typ_rec * sub -> unit
  val unifyDCtx : mctx -> dctx -> dctx -> unit
  val unify_phat : dctx_hat -> dctx_hat -> unit

  val unifyCompTyp : mctx -> Comp.typ * LF.msub -> Comp.typ * msub -> unit
  val unifyMSub : msub -> msub -> unit
  val unifyMetaTyp : mctx -> Comp.meta_typ * msub -> Comp.meta_typ * msub -> unit
  val unifyMetaObj : mctx -> Comp.meta_obj * msub -> Comp.meta_obj * msub
                     -> Comp.meta_typ * msub -> unit

  val matchTerm : mctx -> dctx -> nclo -> nclo -> unit
  val matchTyp : mctx -> dctx -> tclo -> tclo -> unit
  val matchTypRec : mctx -> dctx -> typ_rec * sub -> typ_rec * sub -> unit


  type cvarRef =
    | MMVarRef of iterm option ref


  val pruneTyp : mctx -> dctx -> dctx_hat -> tclo -> msub * sub -> cvarRef -> typ
  val pruneDCtx : mctx -> dctx -> msub -> cvarRef -> dctx
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

  let fail s = raise (Failure s)

  exception Error of string

  type matchFlag = Matching | Unification

  (* Matching not fully implemented yet -bp *)

  type cvarRef =
    | MMVarRef of iterm option ref


  let eq_cvarRef (MMVarRef r) (MMVarRef r') = r == r'

(* Printing of constraints *)
  let rec blockdeclInDctx =
    function
    | Null -> false
    | CtxVar psi -> false
    | DDec (cPsi', TypDecl (x, tA)) ->
       begin match Whnf.whnfTyp (tA, id) with
       | (Sigma _, _) -> true
       | _ -> blockdeclInDctx cPsi'
       end
    | _ -> false

  (* expandPatSub is unused as of commit c899234fe2caf15a42699db013ce9070de54c9c8 -osavary*)
  (* let rec _expandPatSub t cPsi =
   *   match (t, cPsi) with
   *   | (Shift k, Null) -> t
   *   | (Shift k, CtxVar _) -> t
   *   | (Shift k, DDec (cPsi, TypDecl (x, tA))) ->
   *      Dot (Head (BVar (k + 1)), _expandPatSub (Shift (k + 1)) cPsi)
   *   | (Dot (h, s), DDec (cPsi, tdec)) ->
   *      Dot (h, _expandPatSub s cPsi) *)

  (* genMMVarstr cD cPsi (tP, s) = Y[ss_proj]

     if  cD ; cPsi |- [s]tP    and  let X be a mmvar of this type
     then Y[ss_proj] is a new mmvar of type
          cD ; cPhi' |- tQ'  where

          cPsi  |- ss_proj : cPhi'
   *)
  let genMMVarstr loc cD cPsi (Atom (_, a, _) as tP, s) =
    dprintf
      begin fun p ->
      p.fmt "@[<v 6>[genMMVarstr] of type @[%a@]@,in context cPsi = @[%a@]@]"
        (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp (tP, s))
        (P.fmt_ppr_lf_dctx cD P.l0) cPsi
      end;
    let (cPhi, lazy s_proj, lazy s_tup) = ConvSigma.gen_flattening cD cPsi in
    (* let tQ = ConvSigma.strans_typ cD cPsi (tP, s) conv_list in*)
    let tQ = Whnf.normTyp (tP, Substitution.LF.comp s s_tup) in
    (*  cPsi |- s_proj : cPhi
        cPhi |- s_tup : cPsi
        cPhi |- tQ   where  cPsi |- tP  !! tQ = [s_tup]tP !!  *)

    let (ss', cPhi') = Subord.thin' cD a cPhi in
    dprintf
      begin fun p ->
      p.fmt "@[<v 6>[genMMVarstr] flattened type %a@,in context cPhi = %a@,thinned context cPhi' = %a"
        (P.fmt_ppr_lf_typ cD cPhi P.l0) tQ
        (P.fmt_ppr_lf_dctx cD P.l0) cPhi
        (P.fmt_ppr_lf_dctx cD P.l0) cPhi'
      end;

    (* cPhi |- ss' : cPhi' *)
    let ssi' = Substitution.LF.invert ss' in
    (* cPhi' |- ssi : cPhi *)
    (* cPhi' |- [ssi]tQ    *)
    let u = Whnf.newMMVar None (cD, cPhi', TClo (tQ, ssi')) Maybe in
    (* cPhi |- ss'    : cPhi'
         cPsi |- s_proj : cPhi
         cPsi |- comp  ss' s_proj   : cPhi' *)
    let ss_proj = Substitution.LF.comp ss' s_proj in
    Root (loc, MMVar ((u, Whnf.m_id), ss_proj), Nil, `explicit)

  (* isPatSub s = B

     Invariant:

     If    Psi |- s : Psi'
     and   s = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
     and  ni <= k or ni = _ for all 1 <= i <= m
   *)
  let rec isPatSub =
    (* let s = (Whnf.normSub s) in *)
    function
    | EmptySub -> true
    | Undefs -> true
    | Shift _ -> true
    | Dot (Head (BVar n), s) ->
       let rec checkBVar =
         function
         | Shift k -> n <= k
         | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
         | Dot (Head (Proj (BVar n', _)), s) -> n <> n' && checkBVar s
         | Dot (Undef, s) -> checkBVar s
         | EmptySub -> true
         | Undefs -> true
         | _ -> false
       in
       checkBVar s && isPatSub s

    | Dot (Undef, s) -> isPatSub s

    | _ -> false

  (* isProjPatSub s = B

     Invariant:

     If    Psi |- s : Psi'
     and   s = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
     and  ni <= k or ni = _ for all 1 <= i <= m

     *** includes possibly projections ***
  *)
  let rec isProjPatSub =
    (* let s = (Whnf.normSub s) in *)
    function
    | EmptySub -> true
    | Undefs -> true
    | Shift _ -> true
    | Dot (Head (BVar n), s) ->
       let rec checkBVar =
         function
         | Shift k -> n <= k
         | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
         | Dot (Head (Proj (BVar n', _)), s) -> n <> n' && checkBVar s
         | Dot (Undef, s) -> checkBVar s
         | EmptySub -> true
         | Undefs -> true
         | _ -> false
       in
       checkBVar s && isProjPatSub s

    | Dot (Head (Proj (BVar n, index)), s) ->
       let rec checkBVar =
         function
         | Shift k -> n <= k
         | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
         | Dot (Head (Proj (BVar n', index')), s) -> (n <> n' || index' <> index) && checkBVar s
         | Dot (Undef, s) -> checkBVar s
         | EmptySub -> true
         | Undefs -> true
         | _ -> false
       in
       checkBVar s && isProjPatSub s

    | Dot (Undef, s) -> isProjPatSub s
    | _ -> false


  (* isPatMSub t = B

     Invariant:

     If    cD |- t : cD'
     and   t = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
     and  ni <= k or ni = _ for all 1 <= i <= m
  *)
  let rec isPatMSub t =
    let t = Whnf.cnormMSub t in
    match t with
    | MShift _ -> true
    | MDot (MV n, t) ->
       let rec checkMVar =
         function
         | MShift k -> n <= k
         | MDot (MV n', s) -> n <> n' && checkMVar s
         | _ -> false
       in
       checkMVar t && isPatMSub t

    (* | Dot (Obj tM, s) ->
     *    begin match tM with
     *    | Root (BVar n, tS) ->
     *       let rec checkBVar =
     *         function
     *         | Shift k -> n <= k
     *         | Dot (Head (BVar n'), s) -> n <> n' && checkBVar s
     *         | Dot (Undef, s) -> checkBVar s
     *         | _ -> false
     *       in
     *       emptySpine tS && checkBVar s && isPatSub s
     *    | _ -> false
     *    end *)
    | MDot (MUndef, s) -> isPatMSub s
    | _ -> false



  let isVar =
    function
    | BVar _ -> true
    | Proj (BVar _, _) -> true
    | PVar (_, sigma) -> isProjPatSub sigma
    | FPVar (_, sigma) -> isProjPatSub sigma
    | MPVar ((_, theta), sigma) ->
       isProjPatSub sigma && isPatMSub theta
    | Proj (PVar (_, sigma), _) -> isProjPatSub sigma
    | Proj (FPVar (_, sigma), _) -> isProjPatSub sigma
    | Proj (MPVar ((_, theta), sigma), _) ->
       isProjPatSub sigma && isPatMSub theta
    | _ -> false


  let rec isRenameSub cD =
    function
    | SVar (offset, _, _) ->
       let (_, _, cl', _) = Whnf.mctxSDec cD offset in
       begin match cl' with
       | Ren -> true
       | _ -> false
       end
    | MSVar (_, (({ typ = ClTyp (STyp (Ren, _), _); _ }, ms), s)) ->
       isPatSub s && isPatMSub ms
    | Shift _ -> true
    | Dot (Head (BVar _), s) -> isRenameSub cD s
    | _ -> false

  let rec ground_sub cD =
    function (* why is parameter cD is unused? -je *)
    | SVar _
      | Shift _ ->
       true
    | Dot (Head (BVar _), s) -> ground_sub cD s
    | _ -> false


  (*-------------------------------------------------------------------------- *)
  (* Trailing and Backtracking infrastructure *)

  type action =
    | InstI of iterm option ref
    | Add of cnstr list ref
    | Solve of cnstr * constrnt (* FIXME: names *)

  type unifTrail = action T.t

  let globalTrail : action T.t = T.trail ()

  let undo action =
    dprint (fun () -> "Call to UNDO\n");
    match action with
    | InstI refH -> refH := None
    | Add cnstrs -> cnstrs := List.tl !cnstrs
    | Solve (cnstr, constrnt) -> cnstr := constrnt

  let reset () = T.reset globalTrail

  let mark () = T.mark globalTrail

  let unwind () = T.unwind globalTrail undo

  let solvedCnstrs cnstrs =
    List.for_all
      begin fun c ->
      match !c with
      | Queued _ -> true
      | _ -> false
      end
      cnstrs

  let solveConstraint cnstr =
    let constrnt = !cnstr in
    (* Trying to solve a constraint that is already being solved is a
       no-op. *)
    match constrnt with
    | Queued id ->
       dprintf
         begin fun p ->
         p.fmt "[solveConstraint] @[<v>id = %d\
                @,@[%a@]@]"
           id
           Format.pp_print_string
           "WARNING trying to solve constraint that is already being \
            solved."
         end
    | _ ->
       let id = get_constraint_id constrnt in
       cnstr := Queued id; (* replace the constraint with a queued counterpart *)
       T.log globalTrail (Solve (cnstr, constrnt))

  (* trail a function;
     if the function raises an exception,
       backtrack and propagate the exception *)
  let trail f =
    mark ();
    try
      f ()
    with
    | NotInvertible ->
       dprnt "Unwind trail - exception notInvertible";
       unwind ();
       raise NotInvertible
    | Failure msg ->
       dprnt ("Unwind trail - exception Failure " ^ msg);
       unwind ();
       fail msg
    | Error msg ->
       dprnt ("Unwind trail - exception Error " ^ msg);
       unwind ();
       raise (Error msg)
    | GlobalCnstrFailure (loc, msg) ->
       dprnt ("Unwind trail - exception GlobalCnstrFailure " ^ msg);
       unwind ();
       raise (GlobalCnstrFailure (loc, msg))
    | e ->
       dprnt "[unify] [trail] unknown exception ??";
       unwind ();
       raise e

  (* ---------------------------------------------------------------------- *)

  let delayedCnstrs : cnstr list ref = ref []
  let globalCnstrs : cnstr list ref = ref []

  let resetDelayedCnstrs () =
    delayedCnstrs := []
  let resetGlobalCnstrs () =
    globalCnstrs := []

  let is_trivial_constraint =
    function
    | Queued _ -> true
    | Eqn (_, _, _, itM1, itM2)
         when Whnf.convITerm itM1 itM2 -> true
    | _ -> false

  let addConstraint (cnstrs, cnstr) =
    match !cnstr with
    | c when is_trivial_constraint c ->
       dprintf
         begin fun p ->
         p.fmt "[addConstraint] @[<v>skipping trivial constraint\
                @,@[%a@]@]"
           P.fmt_ppr_lf_constraint c
         end;
    | _ ->
       dprintf
         begin fun p ->
         p.fmt "[addConstraint] @[<v 2>adding nontrivial constraint@,@[%a@]@]"
           P.fmt_ppr_lf_constraint !cnstr
         end;
       cnstrs := cnstr :: !cnstrs;
       globalCnstrs := cnstr :: !globalCnstrs;
       T.log globalTrail (Add cnstrs)

  let nextCnstr () =
    match !delayedCnstrs with
    | [] -> None
    | cnstr :: cnstrL ->
       delayedCnstrs := cnstrL;
       Some cnstr

  let instantiateMMVar' (u, t, cnstrL) =
    u := Some t;
    T.log globalTrail (InstI u);
    dprint
      (fun _ ->
        "[instantiateMMVar] added " ^ string_of_int (List.length cnstrL) ^ " constraints.");
    delayedCnstrs := cnstrL @ !delayedCnstrs;
    globalCnstrs := cnstrL @ !globalCnstrs

  let expandMVarAtType loc (v, (mt, s)) =
    function
    | MTyp _ -> INorm (Root (loc, MMVar ((v, mt), s), Nil, `explicit))
    | PTyp _ -> IHead (MPVar ((v, mt), s))
    | STyp _ -> ISub (MSVar (0, ((v, mt), s)))

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
          annotations. While technically cPsi (or hat(cPsi) = phat) does
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

  let rec pruneMCtx' cD (t, cD1) ms =
    match (t, cD1) with
    | (MShift _, Empty) -> (Whnf.m_id, Empty)

   | (MShift k, Dec _) ->
       pruneMCtx' cD (MDot (MV (k + 1), MShift (k + 1)), cD1) ms

   | (MDot (MV k, mt), Dec (cD1, Decl (n, ctyp, dep))) ->
      let (mt', cD2) = pruneMCtx' cD (mt, cD1) ms in
      (* cD1 |- mt' <= cD2 *)
      begin match applyMSub k ms with
      | MUndef ->
         (* Psi1, x:tA |- s' <= Psi2 *)
         (Whnf.mcomp mt' (MShift 1), cD2)

      | MV _ ->
         (* cD1, u:A[Psi] |- mt' <= cD2, u:([mt']^-1 (A[cPsi])) since
                  A = [mt']([mt']^-1 A)  and cPsi = [mt']([mt']^-1 cPsi *)
         let mtt' = Whnf.m_invert (Whnf.cnormMSub mt') in
         (Whnf.mvar_dot1 mt', Dec (cD2, (Decl (n, Whnf.cnormMTyp (ctyp, mtt'), dep))))
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
  let rec intersection phat subst1 subst2 cPsi' =
    match (subst1, subst2, cPsi') with
    | (Dot (Head (BVar k1), s1), Dot (Head (BVar k2), s2), DDec (cPsi', TypDecl (x, tA))) ->
       let (s', cPsi'') = intersection phat s1 s2 cPsi' in
       (* D ; Psi' |- s' : Psi'' where Psi'' =< Psi' *)
       if k1 = k2
       then
         begin
           let ss' = invert (Whnf.normSub s') in
           (* cD ; cPsi'' |- ss' <= cPsi' *)
           (* by assumption:
                 cD ; cPsi' |- tA <= type *)
           (* tA'' = [(s')^-1]tA   and cPsi'' |- tA'' <= type *)

           (* let tA'' = TClo (tA, ss') in *)
           let tA'' = TClo (tA, ss') in

           (dot1 s', DDec (cPsi'', TypDecl (x, tA'')))
         end
       else
         (comp s' shift, cPsi'')

    | (Dot (Head (Proj (BVar k1, index1)), s1), Dot (Head (Proj (BVar k2, index2)), s2), DDec (cPsi', TypDecl (x, tA))) ->
       let (s', cPsi'') = intersection phat s1 s2 cPsi' in
       (* D ; Psi' |- s' : Psi'' where Psi'' =< Psi' *)
       if k1 = k2 && index1 = index2
       then
         begin
           let ss' = invert (Whnf.normSub s') in
           (* cD ; cPsi'' |- ss' <= cPsi' *)
           (* by assumption:
                 cD ; cPsi' |- tA <= type *)
           (* tA'' = [(s')^-1]tA   and cPsi'' |- tA'' <= type *)

           (* let tA'' = TClo (tA, ss') in *)
           let tA'' = TClo (tA, ss') in

           (dot1 s', DDec (cPsi'', TypDecl (x, tA'')))
         end
       else
         (comp s' shift, cPsi'')

    | (Dot (Undef, s1), Dot (Head (BVar _), s2), DDec (cPsi', TypDecl _))
      | (Dot (Undef, s1), Dot (Head (Proj (BVar _, _)), s2), DDec (cPsi', TypDecl _))
      | (Dot (Head (BVar _), s1), Dot (Undef, s2), DDec (cPsi', TypDecl _))
      | (Dot (Head (Proj (BVar _, _)), s1), Dot (Undef, s2), DDec (cPsi', TypDecl _))
      | (Dot (Undef, s1), Dot (Undef, s2), DDec (cPsi', TypDecl _)) ->
       let (s', cPsi'') = intersection phat s1 s2 cPsi' in
       (comp s' shift, cPsi'')

    | (Dot _ as s1, Shift n2, cPsi) ->
       intersection phat s1 (Dot (Head (BVar (n2 + 1)), Shift (n2 + 1))) cPsi

    | (Shift n1, (Dot _ as s2), cPsi) ->
       intersection phat (Dot (Head (BVar (n1 + 1)), Shift (n1 + 1))) s2 cPsi

    | (Shift _, Shift _, cPsi) -> (id, cPsi)
    (* both substitutions are the same number of shifts by invariant *)

    (*    | (EmptySub, EmptySub, Null) -> (EmptySub, Null)  *)
    | (EmptySub, _, Null)
      | (_, EmptySub, Null)
      | (Undefs, _, _)
      | (_, Undefs, _) ->
       (EmptySub, Null)
    (* all other cases impossible for pattern substitutions *)

    | _ ->
       raise (Error "Intersection of substitutions is not defined")
       (* raise (Error ("Intersection not defined - s1 = " ^
        *                 (P.subToString Empty (Context.hatToDCtx phat) s1) ^
        *                   "s2 = " ^
        *                     (P.subToString Empty (Context.hatToDCtx phat) s2))) *)

  (* m_intersection (mt1, mt2) cD' = (mt', cD'')
     (adapted from intersection code above)

     Invariant:
     If   D    |- mt1 : cD'    mt1 patsub
     and  D    |- mt2 : cD'    mt2 patsub
     then  cD' |- mt' : cD'' for some cD'' which is a subset of cD'
     and  mt' patsub   s.t.  [mt1]mt'  = [mt2]mt'
  *)
  let rec m_intersection subst1 subst2 cD' =
    match (subst1, subst2, cD') with
    | (MDot (MV k1, mt1), MDot (MV k2, mt2), Dec (cD', Decl (x, ctyp, dep))) ->
       let (mt', cD'') = m_intersection mt1 mt2 cD' in
       (* cD' |- mt' : cD'' where cD'' =< cD' *)
       if k1 = k2
       then
         begin
           let mtt' = Whnf.m_invert (Whnf.cnormMSub mt') in
           (* cD'' |- mtt' <= cD' *)
           (* NOTE: Can't create m-closures CtxMClo (cPsi, mtt') and TMClo (tA'', mtt') *)
           (Whnf.mvar_dot1 mt', Dec (cD'', Decl (x, Whnf.cnormMTyp (ctyp, mtt'), dep)))
         end
       else
         (Whnf.mcomp mt' (MShift 1), cD'')

    | (MDot (MUndef, mt1), MDot (MV _, mt2), Dec (cD', _))
      | (MDot (MV _, mt1), MDot (MUndef, mt2), Dec (cD', _))
      | (MDot (MUndef, mt1), MDot (MUndef, mt2), Dec (cD', _)) ->
       let (mt', cD'') = m_intersection mt1 mt2 cD' in
       (Whnf.mcomp mt' (MShift 1), cD'')

    | (MDot _ as mt1, MShift n2, cD) ->
       m_intersection mt1 (MDot (MV (n2 + 1), MShift (n2 + 1))) cD

    | (MShift n1, (MDot _ as mt2), cD) ->
       m_intersection (MDot (MV (n1 + 1), MShift (n1 + 1))) mt2 cD

    | (MShift _, MShift _, cD) -> (MShift 0, cD)
    (* both substitutions are the same number of shifts by invariant *)

    (* all other cases impossible for pattern substitutions *)

    | _ ->
       raise (Error "m-intersection not defined")


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

  and invNorm' cD0 ((cvar, offset) as phat, sM, ((ms, ssubst) as ss), rOccur) =
    match sM with
    | (Lam (loc, x, tM), s) ->
       Lam (loc, x, invNorm cD0 ((cvar, offset + 1), (tM, dot1 s), (ms, dot1 ssubst), rOccur))

    | (Root (loc, MVar (Inst u, t), tS, plicity), s) ->
       invNorm' cD0 (phat, (Root (loc, MMVar ((u, MShift 0), t), tS, plicity), s), ss, rOccur)

    | (Root (loc, MMVar (({instantiation; cD; typ = ClTyp (_, cPsi1); _} as u, mt), s'), _ (* Nil *), plicity), s) ->
       (* by invariant tM is in whnf and meta-variables are lowered;
           hence tS = Nil and s = id *)
       if eq_cvarRef (MMVarRef instantiation) rOccur
       then raise NotInvertible
       else
         begin
           let s0 =
             Monitor.timer
               ( "Normalisation"
               , fun () ->
                 Whnf.normSub (comp s' s) (* s0 = s', since s = Id *)
               )
           in
           (* D ; Psi |- s <= Psi'   D ; Psi' |- t <= Psi1
               s0 =  s' o s     and    D ; Psi  |-  s0 <= Psi1 *)
           if isPatSub s0 && isPatMSub mt
           then
             begin
               let (s0', _) = pruneCtx phat (s0, cPsi1) ss in
               let (mt0, _) = pruneMCtx cD0 (mt, cD) ms in
               (* cD ; cPsi  |- s0  <= cPsi1 and
                * cD ; cPsi1 |- s0' <= cPsi2 and
                * cD ; cPsi  |- [s0]s0' <= cPsi2
                *
                * cD  |- mt  <= cD1  and
                * cD1 |- mt0 <= cD2  and
                * cD  |- [mt]mt0 <= cD2
                *)

               if isId s0' && isMId mt0
               then
                 Root
                   ( loc
                   , MMVar ((u, Whnf.mcomp mt ms), comp s0 ssubst)
                   , Nil
                   , plicity
                   )
               else
                 raise NotInvertible
             end
           else (* s0 not patsub *)
             Root
               ( loc
               , MMVar
                   ( (u, invMSub cD0 (mt, cD) ms rOccur)
                   , invSub cD0 phat (s0, cPsi1) ss rOccur
                   )
               , Nil
               , plicity
               )
         end

    | (Root (loc, MVar (Offset u, t), _ (* Nil *), plicity), s (* id *)) ->
       let t' = comp t s (* t' = t, since s = Id *) in
       let (_, _, cPsi1) = Whnf.mctxMDec cD0 u in
       begin match applyMSub u ms with
       | MV v ->
          Root
            ( loc
            , MVar (Offset v, invSub cD0 phat (t', cPsi1) ss rOccur)
            , Nil
            , plicity
            )
       | MUndef -> raise NotInvertible
       end

    | (Root (loc, FMVar (u, t), _ (* Nil *), plicity), s (* id *)) ->
       let (cD_d, Decl (_, ClTyp (_, cPsi1), _)) = Store.FCVar.get u in
       let d = Context.length cD0 - Context.length cD_d in
       let cPsi1 =
         if d = 0
         then cPsi1
         else Whnf.cnormDCtx (cPsi1, MShift d)
       in
       let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
       Root (loc, FMVar (u, s'), Nil, plicity)

    | (Root (loc, FPVar (p, t), _ (* Nil *), plicity), s (* id *)) ->
       let (cD_d, Decl (_, ClTyp (_, cPsi1), _)) = Store.FCVar.get p in
       let d = Context.length cD0 - Context.length cD_d in
       let cPsi1 =
         if d = 0
         then cPsi1
         else Whnf.cnormDCtx (cPsi1, MShift d)
       in
       let s' = invSub cD0 phat (comp t s, cPsi1) ss rOccur in
       Root (loc, FPVar (p, s'), Nil, plicity)

    | (Root (loc, PVar (p, t), _ (* Nil *), plicity), s (* id *)) ->
       let (_, _, cPsi1) = Whnf.mctxPDec cD0 p in
       let t' = comp t s (* t' = t, since s = Id *) in
       begin match applyMSub p ms with
       | MV q ->
          Root (loc, PVar (q, invSub cD0 phat (t', cPsi1) ss rOccur), Nil, plicity)
       | MUndef -> raise NotInvertible
       end


    | (Root (loc, tH, tS, plicity), s (* = id *)) ->
       Root
         ( loc
         , invHead cD0 (phat, tH, ss, rOccur)
         , invSpine cD0 (phat, (tS, s), ss, rOccur)
         , plicity
         )

    | (Tuple (loc, trec), s) ->
       Tuple (loc, invTuple cD0 (phat, (trec, s), ss, rOccur))

  and invTuple cD0 (phat, trec, ss, rOccur) =
    match trec with
    | (Last tM, s) -> Last (invNorm cD0 (phat, (tM, s), ss, rOccur))
    | (Cons (tM, trec'), s) ->
       let tN = invNorm cD0 (phat, (tM, s), ss, rOccur) in
       let trec'' = invTuple cD0 (phat, (trec', s), ss, rOccur) in
       Cons (tN, trec'')

  and invSpine cD0 (phat, spine, ss, rOccur) =
    match spine with
    | (Nil, _) -> Nil
    | (App (tM, tS), s) ->
       App (invNorm cD0 (phat, (tM, s), ss, rOccur),
            invSpine cD0 (phat, (tS, s), ss, rOccur))
    | (SClo (tS, s'), s) ->
       invSpine cD0 (phat, (tS, comp s' s), ss, rOccur)


  (* invHead (phat, head, ss, rOccur) = h'
     cases for parameter variable and meta-variables taken
     care in invNorm' *)
  and invHead cD0 (phat, head, ((ms, ssubst) as ss), rOccur) =
    match head with
    | BVar k ->
       begin match bvarSub k ssubst with
       | Undef -> raise NotInvertible
       | Head (BVar k') -> BVar k'
       end
    | Const _ -> head
    | Proj (BVar k, _) ->
       begin match bvarSub k ssubst with
       | Head (BVar _ as head) -> head
       | Undef -> raise NotInvertible
       end

    | FVar _ -> head
      (* For any free variable x:tA, we have . |- tA <= type ;
         Occurs check is necessary on tA Dec 15 2008 -bp  :(
       *)

    | MVar (Inst ({ instantiation; typ = ClTyp (_, cPsi1); _ }) as u, t) ->
       if eq_cvarRef (MMVarRef instantiation) rOccur
       then raise NotInvertible
       else
         begin
           let t =
             Monitor.timer
               ( "Normalisation"
               , fun () -> Whnf.normSub t
               )
           in
           if isPatSub t
           then
             begin
               let (s', _) = pruneCtx phat (t, cPsi1) ss in
               (* D ; Psi  |- t' <= Psi1 and
                  D ; Psi1 |- s' <= Psi2 and
                  D ; Psi  |- [t']s' <= Psi2  *)
               if isId s'
               then MVar (u, comp t ssubst)
               else raise NotInvertible
             end
           else (* t' not patsub *)
             MVar (u, invSub cD0 phat (t, cPsi1) ss rOccur)
         end

    | MVar (Offset u, t) ->
       let (_, _, cPsi1) = Whnf.mctxMDec cD0 u in
       begin match applyMSub u ms with
       | MV v ->
          MVar (Offset v, invSub cD0 phat (t, cPsi1) ss rOccur)
       | MUndef -> raise NotInvertible
       end

    | PVar (p, t) ->
       let (_, _, cPsi1) = Whnf.mctxPDec cD0 p in
       begin match applyMSub p ms with
       | MV q ->
          PVar (q, invSub cD0 phat (t, cPsi1) ss rOccur)
       | MUndef -> raise NotInvertible
       end

    | Proj (PVar (p, t), i) ->
       let (_, _, cPsi1) = Whnf.mctxPDec cD0 p in
       begin match applyMSub p ms with
       | MV q ->
          Proj (PVar (q, invSub cD0 phat (t, cPsi1) ss rOccur), i)
       | MUndef -> raise NotInvertible
       end

   (* finds the context variable part of a (inverse) substitution *)
  and shiftInvSub n =
    function
    | Undefs -> raise (Failure "Variable dependency")
    | Shift k -> Shift (n + k)
    | Dot (ft, ss') -> shiftInvSub (n - 1) ss'

  (* invSub cD0 (phat, s, ss, rOccur) = s'

     if phat = hat(Psi)  and
        D ; Psi  |- s <= Psi'
        D ; Psi''|- ss <= Psi
     then s' = [ss]s   if it exists, and
        D ; cPsi'' |- [ss]s <= cPsi'
   *)
  and invSub cD0 phat (s, cPsi1) ((ms, ssubst) as ss) rOccur =
    match (s, cPsi1) with
    | (EmptySub, Null) -> EmptySub
    | (Undefs, Null) -> EmptySub
    | (Shift n, DDec _) ->
       invSub cD0 phat (Dot (Head (BVar (n + 1)), Shift (n + 1)), cPsi1) ss rOccur
    | (Shift n, Null) -> EmptySub
    | (Shift n, CtxVar _) -> shiftInvSub n ssubst

    | (SVar (s, 0, sigma), CtxVar psi) ->
       (* other cases ? -bp *)
       let (s, cPhi, cPsi') =
         match applyMSub s ms with
         | MV v ->
            let (_, cPhi, _, cPsi') = Whnf.mctxSDec cD0 v in
            (v, cPhi, cPsi')
         | MUndef -> raise NotInvertible
       in

       dprintf
         begin fun p ->
         let cPsi = Context.hatToDCtx phat in
         p.fmt "[invSub] %a |- %a : %a"
           (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi
           (P.fmt_ppr_lf_sub cD0 cPsi P.l0) sigma
           (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi'
         end;

       SVar (s, 0, invSub cD0 phat (sigma, cPsi') ss rOccur)
    | ( MSVar (0, (({ instantiation = { contents = None }; cD; typ = ClTyp (STyp (_, cPsi'), _); _ } as s0, mt), sigma))
      , CtxVar psi
      ) ->
       MSVar (0, ((s0, invMSub cD0 (mt, cD) ms rOccur), invSub cD0 phat (sigma, cPsi') ss rOccur))

    | (Dot (Head (BVar n), s'), DDec (cPsi', _)) ->
       begin match bvarSub n ssubst with
       | Undef -> raise NotInvertible
       | ft -> Dot (ft, invSub cD0 phat (s', cPsi') ss rOccur)
       end

    | (Dot (Head (Proj (BVar n, k)), s'), DDec (cPsi', _)) ->
       begin match bvarSub n ssubst with
       | Undef -> raise NotInvertible
       | Head (BVar m) ->
          Dot (Head (Proj (BVar m, k)), invSub cD0 phat (s', cPsi') ss rOccur)
       | _ -> raise NotInvertible
       end

    | (Dot (Obj tM, s'), DDec (cPsi', _)) ->
       (* below may raise NotInvertible *)
       let tM' = invNorm cD0 (phat, (tM, id), ss, rOccur) in
       Dot (Obj tM', invSub cD0 phat (s', cPsi') ss rOccur)

    | (SVar (s, n, t), cPsi1) -> (* This is probably
      buggy. Need to deal with the n *)
       begin match applyMSub s ms with
       | MV v ->
          let (_, cPhi, _, cPsi1) = Whnf.mctxSDec cD0 v in
          (* applyMSub to ctx_offset ? *)
          SVar (v, n, invSub cD0 phat (t, cPsi1) ss rOccur)
       | MUndef -> raise NotInvertible
       end
    | (FSVar (n, (s_name, t)), cPsi1) ->
       dprint (fun () -> "invSub FSVar");
       let (_, Decl (_, ClTyp (STyp (LF.Subst, _), cPsi'), _)) = Store.FCVar.get s_name in
       FSVar (n, (s_name, invSub cD0 phat (t, cPsi') ss rOccur))
       (* if ssubst = id
        * then s
        * else
        *  begin
        *    dprint (fun () -> "invSub FSVar -- undefined");
        *    raise (Error "invSub for free substitution variables -- not defined")
        *  end *)

    | (s, _) ->
       dprintf
         begin fun p ->
         p.fmt "[unify] @[<v>invSub -- undefined: s = %a@,in domain cPsi1 = %a@]"
           (P.fmt_ppr_lf_sub cD0 (Context.hatToDCtx phat) P.l0) s
           (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi1
         end;
       raise (Error "invSub --   undefined")




  (* invMSub cD0 (mt, cD') ms rOccur = mt'

     if cD  |- mt <= cD'
        cD''|- ms <= cD
     then mt' = [ms]mt   if it exists, and
        D'' |- [ms]mt <= cD'
   *)
  and invMSub cD0 (mt, cD1) ms rOccur =
    match (mt, cD1) with
    | (MShift n, _) -> checkDefined (Whnf.mcomp (MShift n) ms)
    | (MDot (ClObj (phat, SObj sigma), mt'), Dec (cD', Decl (_, ClTyp (STyp (_, cPhi), _), _))) ->
       let sigma' = invSub cD0 phat (sigma, cPhi) (ms, id) rOccur in
       MDot (ClObj (phat, SObj sigma'), invMSub cD0 (mt', cD') ms rOccur)
    | (MDot (mobj, mt'), Dec (cD', _)) ->
       MDot (invMObj cD0 mobj ms rOccur, invMSub cD0 (mt', cD') ms rOccur)

  and invMObj cD0 mobj ms rOccur =
    match mobj with
    | MV n ->
       begin match applyMSub n ms with
       | MUndef -> raise NotInvertible
       | ft -> ft
       end
    | ClObj (phat, MObj tM) -> ClObj (phat, MObj (invNorm cD0 (phat, (tM, id), (ms, id), rOccur)))
    | CObj cPsi -> raise (Error.Violation "Not implemented")
    | ClObj (phat, PObj h) -> ClObj (phat, PObj (invHead cD0 (phat, h, (ms, id), rOccur)))
  (* | SObj (phat, sigma) -> SObj (phat, invSub cD0 phat (sigma, *)

  and checkDefined =
    function
    | MShift n -> MShift n
    | MDot (MUndef, _) -> raise NotInvertible
    | MDot (m, mt) -> MDot (m, checkDefined mt)

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

  and prune cD0 cPsi' phat sM (ms, s) rOccur =
    prune' cD0 cPsi' phat (Whnf.whnf sM) (ms, s) rOccur

  and prune' cD0 cPsi' ((cvar, offset) as phat) sM ss rOccur =
    match sM with
    | (LFHole _ as n, _) -> n
    | (Lam (loc, x, tM), s) ->
       dprintf
         begin fun p ->
         p.fmt "[prune] @[<v>Lam@,sM = %a@,sM' = %a@]"
           (P.fmt_ppr_lf_normal cD0 (Context.hatToDCtx phat) P.l0)
           (Whnf.norm sM)
           (P.fmt_ppr_lf_normal cD0 (Context.hatToDCtx (cvar, offset + 1)) P.l0)
           (Whnf.norm (tM, dot1 s))
         end;
       let (ms, ssubst) = ss in
       let tM' =
         prune
           cD0
           (DDec (cPsi', TypDeclOpt (Id.mk_name Id.NoName)))
           (cvar, offset + 1)
           (tM, dot1 s)
           (ms, dot1 ssubst)
           rOccur
       in
       Lam (loc, x, tM')

    | (Tuple (loc, tuple), s) ->
       let tuple' = pruneTuple cD0 cPsi' phat (tuple, s) ss rOccur in
       Tuple (loc, tuple')

    | (Root (loc, head, tS, plicity), s) ->
       let Shift 0 = s in (* Assert s is supposed to be the identity *)
       let newHead = pruneHead cD0 cPsi' (loc, head) ss rOccur in
       Root (loc, newHead, pruneSpine cD0 cPsi' phat (tS, s) ss rOccur, plicity)

  and pruneBoth cD0 cPsi' ((mt, ts), (cD1, cPsi1)) ((ms, _) as ss) rOccur =
    let (id_msub, cD2) = pruneMCtx cD0 (mt, cD1) ms in
    let i_msub = Whnf.m_invert (Whnf.mcomp id_msub mt) in
    let i_id_msub = Whnf.m_invert id_msub in
    let cPsi1' = Whnf.cnormDCtx (cPsi1, i_id_msub) in
    let t' = Whnf.cnormSub (Whnf.normSub ts, i_msub) in
    let cPsi'' = Whnf.cnormDCtx (cPsi', i_msub) in
    let (idsub, cPsi2) = pruneSub cD2 cPsi'' (Context.dctxToHat cPsi') (t', cPsi1') ss rOccur in
    let cPsi2' = Whnf.cnormDCtx (cPsi2, i_msub) in
    ((id_msub, idsub), (cD2, cPsi2'))

  and normClTyp2 (tp, (mt, t)) = Whnf.normClTyp (Whnf.cnormClTyp (tp, mt), t)
  and invert2 (mt, t) = (Whnf.m_invert mt, invert t)
  and comp2 (mt, t) (ms, s) = (Whnf.mcomp mt ms, comp (Whnf.cnormSub (t, ms)) s)

  (* Note similarity between the following two functions *)
  and pruneMMVarInst cD0 cPsi' loc mmvar (* (n, r, cD1, ClTyp (tp, cPsi1), cnstrs, mdep) *) mtt ss rOccur =
    let ClTyp (tp, cPsi1) = mmvar.typ in
    if eq_cvarRef (MMVarRef mmvar.instantiation) rOccur
    then raise (Failure "Variable occurrence")
    else
      begin
        let (id2, (cD2, cPsi2')) = pruneBoth cD0 cPsi' (mtt, (mmvar.cD, cPsi1)) ss rOccur in
        let tP' = normClTyp2 (tp, invert2 id2) in
        let v = Whnf.newMMVar' (Some mmvar.name) (cD2, ClTyp (tP', cPsi2')) mmvar.depend in
        instantiateMMVarWithMMVar mmvar.instantiation loc (v, id2) tP' mmvar.constraints.contents;
        let (mr, r) = comp2 (comp2 id2 mtt) ss in
        ((v, mr), r)
      end

  and pruneMVarInst cD0 cPsi' loc mmvar (* (n, r, _, ClTyp (MTyp tP, cPsi1), cnstrs, mdep) *) t ((_, ssubst) as ss) rOccur =
    let ClTyp (MTyp tP, cPsi1) = mmvar.typ in
    if eq_cvarRef (MMVarRef mmvar.instantiation) rOccur
    then raise (Failure "Variable occurrence")
    else
      let (idsub, cPsi2) = pruneSub cD0 cPsi' (Context.dctxToHat cPsi') (t, cPsi1) ss rOccur in
      let tP' = Whnf.normTyp (tP, invert idsub) in
      let v = Whnf.newMVar (Some mmvar.name) (cPsi2, tP') mmvar.depend in
      instantiateMVar
        ( mmvar.instantiation
        , Root (loc, MVar (v, idsub), Nil, `explicit)
        , mmvar.constraints.contents
        );
      (v, comp (comp idsub t) ssubst)

  and pruneFVar cD0 cPsi (u, t) ss rOccur =
   let (cD_d, Decl (_, ClTyp (_, cPsi1), _)) = Store.FCVar.get u in
   let d = Context.length cD0 - Context.length cD_d in
   let cPsi1 =
     if d = 0
     then cPsi1
     else Whnf.cnormDCtx (cPsi1, MShift d)
   in
   let t' = simplifySub cD0 cPsi t in
   let s' = invSub cD0 (Context.dctxToHat cPsi) (t', cPsi1) ss rOccur in
   (u, s')

  and pruneBoundMVar cD0 cPsi u t ((ms, _) as ss) rOccur =
    match applyMSub u ms with
    | MV v ->
       let (_, ClTyp (_, cPsi1)) = Whnf.mctxLookup cD0 v in
       let t' = simplifySub cD0 cPsi t in
       let s' = pruneSubst cD0 cPsi (t', cPsi1) ss rOccur in
       (v, s')
    | MUndef -> raise (Failure "[Prune] Bound MVar dependency")

  and pruneHead cD0 cPsi' (loc, head) ((ms, ssubst) as ss) rOccur =
    match head with
    | MMVar ((i, mt), t) ->
       MMVar (pruneMMVarInst cD0 cPsi' loc i (mt, t) ss rOccur)
    | MVar (Inst i, t) ->
       MVar (pruneMVarInst cD0 cPsi' loc i (Whnf.normSub t) ss rOccur)
    | MVar (Offset u, t) ->
       let (v, s') = pruneBoundMVar cD0 cPsi' u t ss rOccur in
       MVar (Offset v, s')
    | FMVar ut -> FMVar (pruneFVar cD0 cPsi' ut ss rOccur)
    | FPVar pt ->
       begin
         try
           FPVar (pruneFVar cD0 cPsi' pt ss rOccur)
         with
         | Not_found -> (* Huh? *)
            if isId ssubst && isMId ms
            then head
            else raise (Failure ("[Prune] Free parameter variable to be pruned with non-identity substitution"))
       end
    | PVar (p, t) -> PVar (pruneBoundMVar cD0 cPsi' p t ss rOccur)
    | Proj (h, i) -> Proj (pruneHead cD0 cPsi' (loc, h) ss rOccur, i)
    | MPVar ((i, mt), t) -> MPVar (pruneMMVarInst cD0 cPsi' loc i (mt, t) ss rOccur)
    | BVar k ->
       begin match bvarSub k ssubst with
       | Undef ->
          let s =
            let open Format in
            fprintf str_formatter "[Prune] Bound variable dependency : head = %a"
              (P.fmt_ppr_lf_head cD0 cPsi' P.l0) head;
            flush_str_formatter ()
          in
          raise (Failure s)
       | Head (BVar _ as h') -> h'
       end

    | Const _
      | FVar _ ->
       head

  and pruneTuple cD0 cPsi phat sTuple ss rOccur =
    match sTuple with
    | (Last tM, s) ->
       let tM' = prune cD0 cPsi phat (tM, s) ss rOccur in
       Last tM'
    | (Cons (tM, rest), s) ->
       let tM' = prune cD0 cPsi phat (tM, s) ss rOccur in
       let rest' = pruneTuple cD0 cPsi phat (rest, s) ss rOccur in
       Cons (tM', rest')


  and pruneSpine cD0 cPsi1 phat spine ss rOccur =
    match spine with
    | (Nil, _) -> Nil
    | (App (tM, tS), s) ->
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
  and pruneSubst cD cPsi (s, cPsi1) ss rOccur =
    match (s, cPsi1) with
    | (EmptySub, Null) -> EmptySub
    | (Undefs, Null) -> EmptySub
    | (Shift n, DDec _) ->
       pruneSubst cD cPsi (Dot (Head (BVar (n + 1)), Shift (n + 1)), cPsi1) ss rOccur
    | (Shift _, Null) -> EmptySub

    | (Shift n, CtxVar psi) ->
       let (mt, s') = ss in
       shiftInvSub n s'
    | (SVar (sv, n, sigma), cPsi1) ->
       let (sv', s') = pruneBoundMVar cD cPsi sv sigma ss rOccur in
       SVar (sv', n, s')

    | (FSVar (n, ns), cPsi1) -> FSVar (n, pruneFVar cD cPsi ns ss rOccur)

    | (MSVar (n, ((i, mt), t)), cPsi1) ->
       MSVar (n, pruneMMVarInst cD cPsi Syntax.Loc.ghost i (mt, t) ss rOccur)

    | (Dot (ft, s'), DDec (cPsi', _)) ->
       Dot (pruneFront cD cPsi ft ss rOccur, pruneSubst cD cPsi (s', cPsi') ss rOccur)

    | (Dot _, _)
      | (EmptySub, _)
      -> raise (Error.Violation "Badly typed substitution")


  and pruneFront cD cPsi ft ss rOccur =
    match ft with
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
    try
      pruneSub' cD0 cPsi phat (s, cPsi1) ss rOccur
    with NotInvertible ->
      numPruneSub := !numPruneSub + 1;
      raise NotInvertible

  and pruneSub' cD0 cPsi phat (s, cPsi1) ss rOccur =
    match (s, cPsi1) with
    | (Shift n, DDec _) ->
       pruneSub' cD0 cPsi phat (Dot (Head (BVar (n + 1)), Shift (n + 1)), cPsi1) ss rOccur
    | (Shift _, Null)
      | (EmptySub, Null)
      | (Undefs, Null) ->
       (id, Null)

    | (Shift n, CtxVar psi) ->
       let (_, ssubst) = ss in
       let rec shiftInvSub n =
         function
         | Undefs -> (EmptySub, Null)
         | Shift k -> (id, CtxVar psi)
         | Dot (ft, ssubst') -> shiftInvSub (n - 1) ssubst'
       in
       shiftInvSub n ssubst

    | (SVar (s, cshift, sigma), cPsi1) ->
       (*     D ; cPsi1' |  cshift : cPsi1
              D ; Psi    |- s[sigma] : cPsi1'  where s: cPsi1'[Phi]
              D ; Psi    |- sigma : Phi
              D ; Psi''  |- ss <= Psi
              [ss] ([s[sigma] ] id) exists
        *)
       let (mt, _) = ss in
       let cPsi' =
         match applyMSub s mt with
         | MV v ->
            let (_, _, _, cPsi') = Whnf.mctxSDec cD0 v in
            cPsi'
         | MUndef -> raise NotInvertible
       in
       ignore (invSub cD0 phat (sigma, cPsi') ss rOccur);
       dprintf
         begin fun p ->
         p.fmt "[pruneSub] result = %a"
           (P.fmt_ppr_lf_sub cD0 cPsi P.l0)
           (comp id (SVar (s, cshift, sigma)))
         end;
       (id, cPsi1)

    | (MSVar (cshift, ((mmvar, _), sigma)), cPsi1) ->
       assert (Maybe.is_none mmvar.instantiation.contents);
       let ClTyp (STyp (_, cPhi2), cPhi1) = mmvar.typ in
       let cPhi1' = Whnf.cnormDCtx (cPhi1, Whnf.m_id) in
       ignore (invSub cD0 phat (sigma, cPhi1') ss rOccur);
       (id, cPsi1)

    | (FSVar (cshift, (s, sigma)), cPsi1) ->
       (*     D ; Psi   |- s[sigma] : psi  where s: psi[Phi]
              D ; Psi   |- sigma : Phi
              D ; Psi'' |- ss <= Psi
              [ss] ([s[sigma] ] id) exists
        *)
       let (_, Decl (_, ClTyp (STyp _, cPsi'), _)) = Store.FCVar.get s in
       ignore (invSub cD0 phat (sigma, cPsi') ss rOccur);
       (id, cPsi1)

    (*(Dot (Head (HClo  ....)  to be added -bp
       SVar case (offset might not be 0) and domain is cPsi
     *)
    | (Dot (Head (BVar n), s'), DDec (cPsi', TypDecl (x, tA))) ->
       let (_, ssubst) = ss in
       begin match bvarSub n ssubst with
       | Undef ->
          let (s1', cPsi1') = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur in
          (comp s1' shift, cPsi1')

       | Head (BVar _) ->
          let (s1', cPsi1') = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur in
          (* prune tA with respect to s1_i since we have constraints and we cannot guarantee
                 in the presence of constraints that [s1_i]A really exists *)
          let s1_i =
            invert
              (Monitor.timer
                 ( "Normalisation"
                 , fun () -> Whnf.normSub s1'
                 )
              )
          in
          (* cPsi1' |- s1_i <= cPsi' *)
          (dot1 s1', DDec (cPsi1', TypDecl (x, TClo (tA, s1_i))))
       end

    | (Dot (Head (Proj (BVar n, _)), s'), DDec (cPsi', TypDecl (x, tA))) ->
       (* copied immediately preceding case for Head (BVar _)...is this right?  -jd *)
       let (_, ssubst) = ss in
       begin match bvarSub n ssubst with
       | Undef ->
          let (s1', cPsi1') = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur in
          (comp s1' shift, cPsi1')

       | Head (BVar _) ->
          let (s1', cPsi1') = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur in
          let s1_i =
            invert
              (Monitor.timer
                 ( "Normalisation"
                 , fun () -> Whnf.normSub s1'
                 )
              )
          in
          (* cPsi1' |- s1_i <= cPsi' *)
          (dot1 s1', DDec (cPsi1', TypDecl (x, TClo (tA, s1_i))))
       end

    | (Dot (Obj tM, s'), DDec (cPsi', TypDecl (x, tA))) ->
       (* below may raise NotInvertible *)
       (* ignore (invNorm cD0 (phat, (tM, id), ss, rOccur)); *)
       ignore (prune cD0 cPsi1 phat (tM, id) ss rOccur);

       let (s1', cPsi1') = pruneSub' cD0 cPsi phat (s', cPsi') ss rOccur in
       let s1_i =
         invert
           (Monitor.timer
              ( "Normalisation"
              , fun () -> Whnf.normSub s1'
              )
           )
       in
       (* cPsi1' |- s1_i <= cPsi' *)
       (* We need to prune the type here as well;  Feb  9  2009 -bp *)
       let tA' = pruneTyp cD0 cPsi1' phat (tA, id) (MShift 0, s1_i) rOccur in
       (dot1 s1', DDec (cPsi1', TypDecl (x, tA')))

    | (Dot (Undef, t), DDec (cPsi1, _)) ->
       let (s1', cPsi1') = pruneSub' cD0 cPsi phat (t, cPsi1) ss rOccur in
       (comp s1' shift, cPsi1')

  and pruneTypW cD0 cPsi phat sA (mss, ss) rOccur =
    match sA with
    | (Atom (loc, a, tS), s) -> Atom (loc, a, pruneSpine cD0 cPsi phat (tS, s) (mss, ss) rOccur)
    | (PiTyp ((TypDecl (x, tA), dep), tB), s) ->
       let tA' = pruneTyp cD0 cPsi phat (tA, s) (mss, ss) rOccur in
       let tB' = pruneTyp cD0 cPsi phat (tB, dot1 s) (mss, dot1 ss) rOccur in
       PiTyp ((TypDecl (x, tA'), dep), tB')

    | (PiTyp ((TypDeclOpt x, dep), tB), s) ->
       let tB' = pruneTyp cD0 cPsi phat (tB, dot1 s) (mss, dot1 ss) rOccur in
       PiTyp ((TypDeclOpt x, dep), tB')

    | (Sigma typ_rec, s) ->
       let typ_rec' = pruneTypRec cD0 cPsi phat (typ_rec, s) (mss, ss) rOccur in
       Sigma typ_rec'

  and pruneTyp cD0 cPsi1 phat sA ss rOccur =
    pruneTypW cD0 cPsi1 phat (Whnf.whnfTyp sA) ss rOccur

  and pruneTypRec cD0 cPsi phat (typ_rec, s) (mss, ss) rOccur =
    match (typ_rec, s) with
    | (SigmaLast (n, tA), s) -> SigmaLast (n, (pruneTyp cD0 cPsi phat (tA, s) (mss, ss) rOccur))
    | (SigmaElem (x, tA, typ_rec'), s) ->
       let tA' = pruneTyp cD0 cPsi phat (tA, s) (mss, ss) rOccur in
       let typ_rec'' = pruneTypRec cD0 cPsi phat (typ_rec', dot1 s) (mss, dot1 ss) rOccur in
       SigmaElem (x, tA', typ_rec'')

  and pruneDCtx cD cPsi ms rOccur =
    match cPsi with
    | Null -> Null
    | CtxVar (CtxOffset psi) ->
       begin match applyMSub psi ms with
       | CObj (cPsi') -> Whnf.normDCtx cPsi'
       | MV k -> CtxVar (CtxOffset k)
       end

    | CtxVar (CInst (mmvar, theta)) ->
       begin match mmvar.instantiation.contents with
       | None -> cPsi
       | Some (ICtx cPhi) ->
          pruneDCtx cD cPhi (Whnf.mcomp theta ms) rOccur
       end

    | CtxVar _ -> cPsi

    | DDec (cPsi, TypDecl (x, tA)) ->
       let cPsi' = pruneDCtx cD cPsi ms rOccur in
       let tA' =
         pruneTyp
           cD
           cPsi'
           (Context.dctxToHat cPsi')
           (tA, Substitution.LF.id)
           (ms, Substitution.LF.id)
           rOccur
       in
       DDec (cPsi', TypDecl (x, tA'))


  (* pruneCtx cD (phat, (t, Psi1), ss) = (s', cPsi2)

     Invariant:

     If phat = hat(Psi)  and
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

  and pruneCtx' phat (t, cPsi1) ss =
    match (t, cPsi1) with
    | (EmptySub, Null)
      | (Undefs, Null)
      | (Shift _, Null) ->
       (id, Null)

    | (Shift k, CtxVar psi) ->
       let (_, ssubst) = ss in
       let rec check_negshift k =
         function
         | Dot (Undef, ssubst') -> check_negshift (k - 1) ssubst'
         | Undefs -> (EmptySub, Null)
         | _ -> (id, CtxVar psi)
       in
       check_negshift k ssubst

    | (Shift k, DDec (_, TypDecl _)) ->
       pruneCtx' phat (Dot (Head (BVar (k + 1)), Shift (k + 1)), cPsi1) ss

    | (Dot (Head (BVar k), s), DDec (cPsi1, TypDecl (x, tA))) ->
       let (s', cPsi2) = pruneCtx' phat (s, cPsi1) ss in
       (* Ps1 |- s' <= Psi2 *)
       let (_, ssubst) = ss in
       begin match bvarSub k ssubst with
       | Undef ->
          (* Psi1, x:tA |- s' <= Psi2 *)
          (comp s' shift, cPsi2)

       | Head (BVar _) ->
          (* Psi1, x:A |- s' <= Psi2, x:([s']^-1 A) since
                  A = [s']([s']^-1 A) *)
          (dot1 s', DDec (cPsi2, TypDecl (x, TClo (tA, invert (Whnf.normSub s')))))
       end


    | (Dot (Head (Proj (BVar k, index)), s), DDec (cPsi1, TypDecl (x, tA))) ->
       let (s', cPsi2) = pruneCtx' phat (s, cPsi1) ss in
       (* Ps1 |- s' <= Psi2 *)
       let (_, ssubst) = ss in
       begin match bvarSub k ssubst with
       | Undef ->
          (* Psi1, x:tA |- s' <= Psi2 *)
          (comp s' shift, cPsi2)

       | Head (BVar _) ->
          (* Psi1, x:A |- s' <= Psi2, x:([s']^-1 A) since
                  A = [s']([s']^-1 A) *)
          (dot1 s', DDec (cPsi2, TypDecl (x, TClo (tA, invert (Whnf.normSub s')))))
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

        unify phat (tN, s) (tM, s') succeeds if there exists a
        contextual substitution theta such that

        [|theta|]([s1]tN) = [|theta|]([s2]tM) where cD' |- theta <= cD.

       Also, applies instantiation theta as an effect, and returns ().
       Otherwise, raises exception Failure.

       Postcondition: cD' includes new and possibly updated contextual variables;

       Other effects: MVars in cD' may have been lowered and pruned;
                      Constraints may be added for non-patterns.
  *)

  let rec unifyTerm mflag cD0 cPsi sN sM =
    dprintf
      begin fun p ->
      p.fmt "[unifyTerm] @[<v>unifying:@,\
             @[  @[<hov>@[%a@]@ =?=@ @[%a@]@]@]@]"
        (P.fmt_ppr_lf_normal cD0 cPsi P.l0) (Whnf.norm sN)
        (P.fmt_ppr_lf_normal cD0 cPsi P.l0) (Whnf.norm sM)
      end;
    unifyTerm' mflag cD0 cPsi (Whnf.norm (Whnf.whnf sN)) (Whnf.norm (Whnf.whnf sM))

  and unifyTuple mflag cD0 cPsi sTup1 sTup2 =
    match (sTup1, sTup2) with
    | ((Last tM, s1), (Last tN, s2)) ->
       unifyTerm mflag cD0 cPsi (tM, s1) (tN, s2)
    | ((Cons (tM, tup1), s1), (Cons (tN, tup2), s2)) ->
       (unifyTerm mflag cD0 cPsi (tM, s1) (tN, s2);
        unifyTuple mflag cD0 cPsi (tup1, s1) (tup2, s2))

  and unifyMVarTerm cD0 cPsi mmvar t1' sM2 =
    let ClTyp (_, cPsi1) = mmvar.typ in
    if isId t1'
    then instantiateMVar (mmvar.instantiation, sM2, mmvar.constraints.contents)
    else
      begin
        try
          let ss1 = invert (Whnf.normSub t1') (* cD ; cPsi1 |- ss1 <= cPsi *) in
          let phat = Context.dctxToHat cPsi in
          let tM2' =
            trail
              begin fun () ->
              prune
                cD0
                cPsi1
                phat
                (sM2, id)
                (MShift 0, ss1)
                (MMVarRef mmvar.instantiation)
              end
          in
          instantiateMVar (mmvar.instantiation, tM2', mmvar.constraints.contents)
        with
        | NotInvertible ->
           (* This might actually need to add a constraint, in which case
           "NotInvertible" seems the wrong kind of exception... *)
           raise (Error.Violation "Unification violation")
      end

  and craftMVTerm cD0 cPsi mmvar sM2 =
    let ClTyp (_, cPsi1) = mmvar.typ in
    match sM2 with
    | Root (loc, Const c, _, plicity) ->
       let tA = (Store.Cid.Term.get c).Store.Cid.Term.Entry.typ in
       dprintf
         (fun p ->
           p.fmt "[craftMVTerm] @[<v>cPsi = %a@,cPsi1= %a@]"
             (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi
             (P.fmt_ppr_lf_dctx mmvar.cD P.l0) cPsi1);

       let rec genSpine cD1 cPsi1 sA =
         match Whnf.whnfTyp sA with
         | (LF.PiTyp ((LF.TypDecl (n, tA), _), tB), s) ->
            (* cPsi' |- Pi x:A.B <= typ
               cPsi  |- s <= cPsi'
               cPsi  |- tN <= [s]tA
               cPsi |- tN . s <= cPsi', x:A
             *)
            let tN = Whnf.etaExpandMV cPsi1 (tA, s) n id LF.Maybe in
            let tS = genSpine cD1 cPsi1 (tB, LF.Dot (LF.Obj tN, s)) in
            LF.App (tN, tS)

         | (LF.Atom _, _) -> LF.Nil
       in
       let tM1 = Root (loc, Const c, genSpine mmvar.cD cPsi1 (tA, id), plicity) in
       instantiateMVar (mmvar.instantiation, tM1, mmvar.constraints.contents);
       Some tM1
    | _ -> None


  and craftMMVTerm cD0 cPsi mmvar sM2 =
    let ClTyp (MTyp tB, cPsi1) = mmvar.typ in
    let rec genSpine cD1 cPsi1 sA =
      match Whnf.whnfTyp sA with
      | (LF.PiTyp ((LF.TypDecl (n, tA), _), tB), s) ->
         (* cPsi' |- Pi x:A.B <= typ
            cPsi  |- s <= cPsi'
            cPsi  |- tN <= [s]tA
            cPsi |- tN . s <= cPsi', x:A
          *)
         let tN =
           ConvSigma.etaExpandMMVstr Loc.ghost cD1 cPsi1 (tA, s) Maybe (Some n)
             Context.(names_of_dctx cPsi @ names_of_mctx cD0)
         in
         let tS = genSpine cD1 cPsi1 (tB, LF.Dot (LF.Obj tN, s)) in
         LF.App (tN, tS)
      | (LF.Atom _, _) -> LF.Nil
    in
    match sM2 with
    | Root (loc, Const c, _, plicity) ->
       let tA = (Store.Cid.Term.get c).Store.Cid.Term.Entry.typ in
       dprintf
         begin fun p ->
         p.fmt "[craftMMVTerm] @[<v>cPsi = %a@,cPsi1 = %a@]"
           (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi
           (P.fmt_ppr_lf_dctx mmvar.cD P.l0) cPsi1
         end;
       let tM1 =
         Root (loc, Const c, genSpine mmvar.cD cPsi1 (tA, id), plicity)
       in
       (* cD1 ; cPsi1 |- tM1 : tP and there is a renaming cPsi |- rho : cPsi1 *)
       instantiateMMVar (mmvar.instantiation, tM1, mmvar.constraints.contents);
       Some tM1

    | Root (loc, MPVar _, _, plicity) ->
       dprnt "[craftMMVTerm] MPVar ...";
       let p = Whnf.newMPVar None (mmvar.cD, cPsi1, tB) Maybe in
       let tM1 =
         Root
           ( loc
           , MPVar ((p, Whnf.m_id), Substitution.LF.id)
           , genSpine mmvar.cD cPsi1 (tB, id)
           , plicity
           )
       in
       (* cD1 ; cPsi1 |- tM1 : tP and there is a renaming cPsi |- rho : cPsi1 *)
       instantiateMMVar (mmvar.instantiation, tM1, mmvar.constraints.contents);
       Some tM1

    | _ -> None


  and pruneITerm cD cPsi (hat, tm) ss rOccur =
    match tm with
    | (INorm n, _) -> INorm (prune cD cPsi hat (n, id) ss rOccur)
    | (IHead h, _) -> IHead (pruneHead cD cPsi (Syntax.Loc.ghost, h) ss rOccur)
    | (ISub s, STyp (_, cPhi)) -> ISub (pruneSubst cD cPsi (s, cPhi) ss rOccur)

  and unifyMMVarTerm cD0 cPsi mmvar mt1 t1' sM2 =
    let ClTyp (tp, cPsi1) = mmvar.typ in
    if isId t1' && isMId mt1
    then
      begin
        dprint (fun () -> "[unifyMMVarTerm] 200 - id/m_id");
        instantiateMMVar' (mmvar.instantiation, sM2, mmvar.constraints.contents)
      end
    else
      begin (* try *)
        let ss1 = invert (Whnf.cnormSub (t1', Whnf.m_id)) in
        (* cD ; cPsi1 |- ss1 <= cPsi *)
        let mtt1 = Whnf.m_invert (Whnf.cnormMSub mt1) in
        let tp' = Whnf.cnormClTyp (tp, mt1) in
        let hat = Context.dctxToHat cPsi in
        let tM2' =
          trail
            begin fun () ->
            pruneITerm mmvar.cD cPsi1 (hat, (sM2, tp')) (mtt1, ss1) (MMVarRef mmvar.instantiation)
            end
        in
        instantiateMMVar' (mmvar.instantiation, tM2', mmvar.constraints.contents);
        (* with | NotInvertible -> raise (Error.Violation "Unification violation") *)
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
  and unifyMMVarTermProj cD0 cPsi mmvar mt1 t1' tM2 =
    let ClTyp (_, cPsi1) = mmvar.typ in
    let mtt1 = Whnf.m_invert (Whnf.cnormMSub mt1) in
    (* cD |- mtt1 : cD0 *)
    let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cD0 cPsi in
    dprintf
      begin fun p ->
      p.fmt "[unifyMMVarTermProj] \
             @[<v>cPsi = @[%a@]\
             @,sM2 = @[%a@]\
             @,flat_cPsi = @[%a@]\
             @,conv_list = @[%a@]@]"
        (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi
        (P.fmt_ppr_lf_normal cD0 cPsi P.l0) tM2
        (P.fmt_ppr_lf_dctx cD0 P.l0) flat_cPsi
        ConvSigma.fmt_ppr_conv_list conv_list
      end;
    let phat = Context.dctxToHat flat_cPsi in
    let t_flat = ConvSigma.strans_sub cD0 cPsi t1' conv_list in
    (* flat_cPsi |- t_flat : cPsi *)
    (* flat_cPsi |- t_flat : cPsi1 ** new *)
    dprintf
      begin fun p ->
      p.fmt "[unifyMMVarTermProj] t_flat = %a"
        (P.fmt_ppr_lf_sub cD0 flat_cPsi P.l0) t_flat
      end;
    let tM2' = ConvSigma.strans_norm cD0 cPsi (tM2, id) conv_list in
    dprintf
      begin fun p ->
      p.fmt "[unifyMMVarTermProj] sM2' = %a"
        (P.fmt_ppr_lf_normal cD0 flat_cPsi P.l0) tM2'
      end;
    (* flat_cPsi |- tM2' *)
    let ss = invert t_flat in
    (* cPsi1  |- ss : flat_cPsi
       Inversion of t_flat will only succeed if t_flat is a variable substitution;
       it can happen that it contains projections as complete flattening was impossible
       because not enough typing information was available in cPsi (i.e. cPsi was obtained by hattoDctx)
     *)
    let sM2' =
      trail
        begin fun () ->
        prune mmvar.cD cPsi1 phat (tM2', id) (mtt1, ss) (MMVarRef mmvar.instantiation)
        end
    in
    dprintf
      begin fun p ->
      p.fmt "[unifyMMVarTermProj] - done: %a"
        (P.fmt_ppr_lf_normal cD0 flat_cPsi P.l0) tM2'
      end;
    instantiateMMVar (mmvar.instantiation, sM2', mmvar.constraints.contents)

  and unifyMMVarMMVar cPsi loc ((mmvar1, mt1), t1') ((mmvar2, mt2), t2') =
    let ClTyp (tp1, cPsi1) = mmvar1.typ in
    let (s', cPsi') = intersection (Context.dctxToHat cPsi) (Whnf.normSub t1') (Whnf.normSub t2') cPsi1 in
    (* if cD ; cPsi |- t1' <= cPsi1 and cD ; cPsi |- t2' <= cPsi1
         then cD ; cPsi1 |- s' <= cPsi' *)
    let (mt', cD') = m_intersection (Whnf.cnormMSub mt1) (Whnf.cnormMSub mt2) mmvar1.cD in
    (* if cD |- mt1 <= cD1 and cD |- mt2 <= cD1
          then cD1 |- mt' <= cD' *)
    let ss' = invert (Whnf.normSub s') in
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
     * We want        cD' ; [mtt']cPsi' |- [mss'][mtt']tP1 <= type
     *
     * Since we can't create m-closures, we need to normalize here. *)

    let cPsi_n = Whnf.cnormDCtx (cPsi', mtt') in
    let tp1' = normClTyp2 (tp1, (mtt', ss')) in

    let dep = Depend.max mmvar1.depend mmvar2.depend in
    let w = Whnf.newMMVar' (Some mmvar1.name) (cD', ClTyp (tp1', cPsi_n)) dep in
    (* w :: [s'^-1](tP1)[cPsi'] in cD'            *)
    (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tP1)
       [|w[s']/u|](u[t1]) = [t1](w[s'])
       [|w[s']/u|](u[t2]) = [t2](w[s'])
     *)
    instantiateMMVarWithMMVar mmvar1.instantiation loc (w, (mt', s')) tp1' mmvar1.constraints.contents

  and unifyTerm' mflag cD0 cPsi sN sM =
    match (sN, sM) with
    | ((Tuple (_, tup1)), (Tuple (_, tup2))) ->
       unifyTuple mflag cD0 cPsi (tup1, id) (tup2, id)

    | ((Lam (_, _, tN)), (Lam (_, x, tM))) ->
       unifyTerm mflag cD0 (DDec (cPsi, TypDeclOpt x)) (tN, id) (tM, id)

    (* MVar-MVar case *)
    | ( (Root (_, MVar (Inst mmvar1, t1), _, _))
      , (Root (_, MVar (Inst mmvar2, t2), _, _))
      )
         when mmvar1.instantiation == mmvar2.instantiation ->
       let ClTyp (MTyp tP1, cPsi1) = mmvar1.typ in
       let ClTyp (MTyp tP2, cPsi2) = mmvar2.typ in
       dprnt "(000) MVar-MVar";
       (* by invariant of whnf:
          meta-variables are lowered during whnf, s1 = s2 = id or co-id
          r1 and r2 are uninstantiated  (None)
        *)
       if isPatSub t1 && isPatSub t2
       then
         begin
           let phat = Context.dctxToHat cPsi in
           let (s', cPsi') = intersection phat t1 t2 cPsi1 in
           (* if cD ; cPsi |- t1' <= cPsi1 and cD ; cPsi |- t2' <= cPsi1
             then cD ; cPsi1 |- s' <= cPsi' *)

           let ss' =
             invert
               (Monitor.timer
                  ( "Normalisation"
                  , fun () -> Whnf.normSub s'
                  )
               )
           in
           (* cD ; cPsi' |- [s']^-1(tP1) <= type *)

           let w = Whnf.newMVar None (cPsi', TClo (tP1, ss')) mmvar1.depend in
           (* w::[s'^-1](tP1)[cPsi'] in cD'            *)
           (* cD' ; cPsi1 |- w[s'] <= [s']([s'^-1] tP1)
             [|w[s']/u|](u[t1]) = [t1](w[s'])
             [|w[s']/u|](u[t2]) = [t2](w[s'])
            *)
           instantiateMVar
             ( mmvar1.instantiation
             , Root (Syntax.Loc.ghost, MVar (w, s'), Nil, `explicit)
             , mmvar1.constraints.contents
             )
         end
       else if not (Whnf.convDCtx cPsi1 cPsi2 && Whnf.convSub t1 t2)
       then
         begin
           let id = next_constraint_id () in
           addConstraint (mmvar1.constraints, ref (Eqn (id, cD0, cPsi, INorm sN, INorm sM)))
         end

    (* MVar-normal case *)
    | (Root (_, MVar (Inst i, t), _, _), sM2)
         when isPatSub t ->
       unifyMVarTerm cD0 cPsi i t sM2
    | (sM2, (Root (_, MVar (Inst i, t), _, _)))
         when isPatSub t ->
       unifyMVarTerm cD0 cPsi i t sM2

    | (Root (_, MVar (Inst i, t), _, _) as sM1, sM2)
         when isRenameSub cD0 t ->
       dprintf
         begin fun p ->
         p.fmt "01 - craftMVTerm ... in cPsi = %a"
           (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi
         end;
       begin match craftMVTerm cD0 cPsi i sM2 with
       | Some _ ->
          dprintf
            begin fun p ->
            p.fmt "crafted MV Term %a"
              (P.fmt_ppr_lf_normal cD0 cPsi P.l0) sM1
            end;
          unifyTerm mflag cD0 cPsi (sM1, id) (sM2, id)
       | None ->
          let id = next_constraint_id () in
          addConstraint (i.constraints, ref (Eqn (id, cD0, cPsi, INorm sM1, INorm sM2)))
       end

    | (sM2, ((Root (_, MVar (Inst i, t), _, _)) as sM1))
         when isRenameSub cD0 t ->
       dprintf
         begin fun p ->
         p.fmt "02 - craftMVTerm ... in cPsi = %a"
           (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi
         end;
       begin match craftMVTerm cD0 cPsi i sM2 with
       | Some _ ->
          dprintf
            begin fun p ->
            p.fmt "crafted MV Term %a"
              (P.fmt_ppr_lf_normal cD0 cPsi P.l0) sM1
            end;
          unifyTerm mflag cD0 cPsi (sM1, id) (sM2, id)
       | None ->
          let id = next_constraint_id () in
          addConstraint (i.constraints, ref (Eqn (id, cD0, cPsi, INorm sM1, INorm sM2)))
       end


    | (Root (_, MVar (Inst mmvar, _), _, _) as sM1, sM2)
      | (sM2, (Root (_, MVar (Inst mmvar, _), _, _) as sM1)) ->
       let id = next_constraint_id () in
       addConstraint (mmvar.constraints, ref (Eqn (id, cD0, cPsi, INorm sM1, INorm sM2)))

    (* MMVar-MMVar case *)

    | (((Root (loc1, MMVar ((mmvar1, mt1), t1 as q1), Nil, _))),
       (((Root (_, MMVar ((mmvar2, mt2), t2 as q2), Nil, _)))))
         when mmvar1.instantiation == mmvar2.instantiation ->
       dprnt "(010) MMVar-MMVar";
       (* by invariant of whnf:
           meta^2-variables are lowered during whnf, s1 = s2 = id
           r1 and r2 are uninstantiated  (None)
        *)
       if isPatMSub mt1 && isPatSub t1 && isPatMSub mt2 && isPatSub t2
       then unifyMMVarMMVar cPsi loc1 q1 q2
       else
         begin
           let id = next_constraint_id () in
           addConstraint (mmvar1.constraints, ref (Eqn (id, cD0, cPsi, INorm sN, INorm sM)))
         end

    | ( Root (loc', MMVar (((mmvar1, MShift 0) as mv), (MSVar _ as s1)), tS', _) as sM1
      , (Root (loc, MMVar ((mmvar2, MShift 0), EmptySub), _, _) as sM2)
      )
      | ( Root (loc, MMVar ((mmvar2, MShift 0), EmptySub), _, _) as sM2
        , (Root (loc', MMVar (((mmvar1, MShift 0) as mv), (MSVar _ as s1)), tS', _) as sM1)
        ) ->
       begin
         try
           dprnt "unifyMMVar -- EmptySub";
           unifySub mflag cD0 cPsi s1 EmptySub;
           dprintf
             begin fun p ->
             let f = P.fmt_ppr_lf_normal cD0 cPsi P.l0 in
             p.fmt "@[<v 2>MMVar -EmptySub Case : Unifying terms:@,%a =?= %a@]"
               f sM2 f sM1
             end;
           instantiateMMVar
             ( mmvar2.instantiation
             , Root (loc', MMVar (mv, id), tS', `explicit)
             , mmvar2.constraints.contents
             );
           dprintf
             begin fun p ->
             let f = P.fmt_ppr_lf_normal cD0 cPsi P.l0 in
             p.fmt
               "@[<v 2>MMVar - EmptySub Case: Unified term (after instantiation)@,%a =?= %a@]"
               f sM2 f sM1
             end
         with
         | _ ->
            let id = next_constraint_id () in
            addConstraint
              ( mmvar2.constraints
              , ref (Eqn (id, cD0, cPsi, INorm sM1, INorm sM2))
              )
       end

    | ( Root (_, MMVar ((i, mt1), t1), Nil, _) as sM1
      , (Root (_, MMVar ((i', mt2), t2), Nil, _) as sM2)
      ) ->
       dprint (fun () -> "(case 0)");
       begin
         try
           if isPatMSub mt1 && isPatSub t1
           then
             begin
               dprint (fun () -> "(case 1)");
               unifyMMVarTerm cD0 cPsi i mt1 t1 (INorm sM2)
             end
           else if isPatMSub mt2 && isPatSub t2
           then
             begin
                dprint (fun () -> "(case 2)");
                unifyMMVarTerm cD0 cPsi i' mt2 t2 (INorm sM1)
             end
           else
             begin
               dprint (fun () -> "(case 3)");
               if isPatMSub mt2 && isProjPatSub t2
               then unifyMMVarTermProj cD0 cPsi i' mt2 t2 sM1
               else if isPatMSub mt1 && isProjPatSub t1
               then unifyMMVarTermProj cD0 cPsi i mt1 t1 sM2
               else
                 begin
                   let id = next_constraint_id () in
                   addConstraint (i.constraints, ref (Eqn (id, cD0, cPsi, INorm sM1, INorm sM2)))
                 end
             end
         with
         | NotInvertible ->
            let id = next_constraint_id () in
            addConstraint (i.constraints, ref (Eqn (id, cD0, cPsi, INorm sM1, INorm sM2)))
       end

    (* MMVar-normal case *)
    (* Special case to handle: ?N[] = ?M[#?S[]] *)
    | ( Root (loc, MMVar (({ instantiation; typ = ClTyp (MTyp _, Null); constraints; _ }, MShift 0), (MSVar _ as s1)), _, _) as sM1
      , (Root (loc', MVar (Offset u, EmptySub), tS', _) as sM2)
      )
      | ( Root (loc', MVar (Offset u, EmptySub), tS', _) as sM2
        , (Root (loc, MMVar (({ instantiation; typ = ClTyp (MTyp _, Null); constraints; _ }, MShift 0), (MSVar _ as s1)), _, _) as sM1)
        ) ->
       begin
         try
           unifySub mflag cD0 cPsi s1 EmptySub;
           instantiateMMVar (instantiation, Root (loc', MVar (Offset u, id), tS', `explicit), !constraints)
         with _ ->
           let id = next_constraint_id () in
           addConstraint (constraints, ref (Eqn (id, cD0, cPsi, INorm sM1, INorm sM2)))
       end

    (* Special case to handle: M[#S[]] = ?M[#?S[]] *)
    | ( Root (loc, MMVar (({ instantiation; cD; typ = ClTyp (MTyp tP, cPsi1); constraints; _ }, MShift 0), (MSVar _ as s1)), _, _) as sM1
      , (Root (loc', MVar (Offset u, (SVar _ as s2)), tS', _) as sM2)
      )
      | ( Root (loc', MVar (Offset u, (SVar _ as s2)), tS', _) as sM2
        , (Root (loc, MMVar (({ instantiation; cD; typ = ClTyp (MTyp tP, cPsi1); constraints; _ }, MShift 0), (MSVar _ as s1)), _, _) as sM1)
        )
      | ( Root (loc, MMVar (({ instantiation; cD; typ = ClTyp (MTyp tP, cPsi1); constraints; _ }, MShift 0), (SVar _ as s1)), _, _) as sM1
        , (Root (loc', MVar (Offset u, (SVar _ as s2)), tS', _) as sM2)
        )
      | ( Root (loc', MVar (Offset u, (SVar _ as s2)), tS', _) as sM2
        , (Root (loc, MMVar (({ instantiation; cD; typ = ClTyp (MTyp tP, cPsi1); constraints; _ }, MShift 0), (SVar _ as s1)), _, _) as sM1)
        ) ->
       let (_, tQ, cPsi) = Whnf.mctxMDec cD0 u in
       dprintf
         begin fun p ->
         p.fmt "[unify] MMVar[SVar] @[<v>tP = %a@,cPsi1 = %a@,tQ = %a@,cPsi = %a@]"
           (P.fmt_ppr_lf_typ cD cPsi1 P.l0) tP
           (P.fmt_ppr_lf_dctx cD P.l0) cPsi1
           (P.fmt_ppr_lf_typ cD0 cPsi P.l0) tQ
           (P.fmt_ppr_lf_dctx cD P.l0) cPsi
         end;
       (* if Whnf.convTyp (tP, id) (tQ, id) && Whnf.convDCtx cPsi1 cPsi then  *)
       begin
         try
           unifyDCtx1 mflag cD0 cPsi1 cPsi;unifyTyp mflag cD0 cPsi (tP, id) (tQ, id);
           unifySub mflag cD0 cPsi s1 s2;
           instantiateMMVar (instantiation, Root (loc', MVar (Offset u, id), tS', `explicit), !constraints)
         with _ ->
           let id = next_constraint_id () in
           addConstraint (constraints, ref (Eqn (id, cD0, cPsi, INorm sM1, INorm sM2)))
       end

    | ( Root (loc, MMVar (({ instantiation; cD; typ = ClTyp (MTyp tP, cPsi1); constraints; _ } as i, mt), s), _, plicity) as tM1
      , tM2
      )
      | ( tM2
        , (Root (loc, MMVar (({ instantiation; cD; typ = ClTyp (MTyp tP, cPsi1); constraints; _ } as i, mt), s), _, plicity) as tM1)
        ) ->
       dprintf
         begin fun p ->
         p.fmt "[unifyTerm] @[<v>MMVar with anything else\
                @,cPsi = %a\
                @,t' = %a\
                @,mt = %a\
                @,plicity = %a@]"
           (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi
           (P.fmt_ppr_lf_sub cD0 cPsi P.l0) s
           (P.fmt_ppr_lf_msub cD0 P.l0) mt
           P.fmt_ppr_plicity plicity
         end;
       begin match () with
       | () when isId s && isMId mt && not (blockdeclInDctx cPsi) ->
          dprintf
            begin fun p ->
            p.fmt "[unifyTerm] @[<v>instantiating immediately:@, mmvar := @[%a@]@]"
              (P.fmt_ppr_lf_normal cD cPsi P.l0) tM2
            end;
          instantiateMMVar (instantiation, tM2, !constraints)
       | () when blockdeclInDctx (Whnf.cnormDCtx (cPsi1, Whnf.m_id)) ->
          dprnt "[unifyTerm] there's a block decl in cPsi";
          let tN = genMMVarstr loc cD cPsi1 (tP, id) in
          instantiateMMVar (instantiation, tN, !constraints);
          unifyTerm mflag cD0 cPsi (tM1, id) (tM2, id)
       | () when isProjPatSub s && isPatMSub mt ->
          begin
            try
              dprint (fun () -> "Calling unifyMMVarTermProj ...");
              unifyMMVarTermProj cD0 cPsi i mt s tM2
            with NotInvertible ->
              let id = next_constraint_id () in
              dprint (fun () -> "(010) Add constraints ");
              addConstraint (constraints, ref (Eqn (id, cD0, cPsi, INorm tM1, INorm tM2)))
          end
       | () when isRenameSub cD0 s && isPatMSub mt ->
          begin match (ground_sub cD0 s, tM2, mt) with
          | (false, Root (loc, MVar (Offset u, s'), tS, _), MShift k) ->
             let (_, tP0, cPsi0) = Whnf.mctxMDec cD0 u in
             let tP1' = Whnf.cnormTyp (tP, mt) in
             unifyDCtx1 mflag cD0 cPsi0 (Whnf.cnormDCtx (cPsi1, mt));
             unifyTyp mflag cD0 cPsi0 (tP0, Substitution.LF.id) (tP1', Substitution.LF.id);
             instantiateMMVar
               ( instantiation
               , Root (loc, MVar (Offset (u - k), Substitution.LF.id), tS, `explicit)
               , !constraints
               );
             unifySub mflag cD0 cPsi0 s s'
          | (true, Root (loc, MVar (Offset u, s'), tS, _), MShift k) ->
             let (_, tP0, cPsi0) = Whnf.mctxMDec cD0 u in
             if Whnf.convSub s s' then
               let tP1' = Whnf.cnormTyp (tP, mt) in
               dprintf
                 begin fun p ->
                 let f = P.fmt_ppr_lf_normal cD0 cPsi P.l0 in
                 p.fmt "craftMMV ... @[<v>substitutions are convertible:@,%a = %a@]"
                   f tM1 f tM2
                 end;
               unifyDCtx1 mflag cD0 cPsi0 (Whnf.cnormDCtx (cPsi1, mt));
               unifyTyp mflag cD0 cPsi0 (tP0, Substitution.LF.id) (tP1', Substitution.LF.id);
               instantiateMMVar
                 ( instantiation
                 , Root (loc, MVar (Offset (u - k), Substitution.LF.id), tS, `explicit)
                 , !constraints
                 )
             else
               begin
                 dprintf
                   begin fun p ->
                   let f = P.fmt_ppr_lf_normal cD0 cPsi P.l0 in
                   p.fmt "(0110) @[<v>Add constraints:@,%a = %a@]"
                     f tM1
                     f tM2
                   end;
                 let id = next_constraint_id () in
                 addConstraint (constraints, ref (Eqn (id, cD0, cPsi, INorm tM1, INorm tM2)))
               end
          | _ ->
             dprnt "craftMMV...";
             begin match craftMMVTerm cD0 cPsi i tM2 with
             | Some _ ->
                dprintf
                  begin fun p ->
                  let f = P.fmt_ppr_lf_normal cD0 cPsi P.l0 in
                  p.fmt "crafted MMV Term @[<v>%a@,%a =?= %a@]"
                    f tM1 f tM1 f tM2
                  end;
                unifyTerm mflag cD0 cPsi (tM1, id) (tM2, id)
             | None ->
                dprintf
                  begin fun p ->
                  let f = P.fmt_ppr_lf_normal cD0 cPsi P.l0 in
                  p.fmt "(0111) Add constraints - @[<v>craftMMV failed:@,%a = %a@]"
                    f tM1 f tM2
                  end;
                let id = next_constraint_id () in
                addConstraint (constraints, ref (Eqn (id, cD0, cPsi, INorm tM1, INorm tM2)))
             end
          end
       | _ ->
          dprintf
            begin fun p ->
            let f = P.fmt_ppr_lf_normal cD0 cPsi P.l0 in
            p.fmt "(011) @[<v>Add constraints:@,%a = %a@]"
              f tM1 f tM2
            end;
          let id = next_constraint_id () in
          addConstraint (constraints, ref (Eqn (id, cD0, cPsi, INorm tM1, INorm tM2)))
       end

    | (Root (_, h1, tS1, _) as sM1, (Root (_, h2, tS2, _) as sM2)) ->
       dprintf
         begin fun p ->
         let f = P.fmt_ppr_lf_normal cD0 cPsi P.l0 in
         p.fmt "UNIFY: @[<v>normal - normal (non MVar cases)@,\
                @[  @[<hov 2>@[%a@] |-@ @[<hov>@[%a@]@ ==@ @[%a@]@]@]@]@]"
           (P.fmt_ppr_lf_mctx P.l0) cD0
           f sM1
           f sM2
         end;

       (* s1 = s2 = id by whnf *)
       unifyHead mflag cD0 cPsi h1 h2;
       unifySpine mflag cD0 cPsi (tS1, id) (tS2, id)

    | _ -> raise (Failure "Expression clash")

  and unifyHead mflag cD0 cPsi head1 head2 =
    match (head1, head2) with
    | (BVar k1, BVar k2) ->
       if not (k1 = k2)
       then raise (Failure "Bound variable clash")

    | (Const (i, id), Const (i', id')) ->
       if not (i = i' && id = id')
       then raise (Failure "Constant clash")

    | (FVar x1, FVar x2) ->
       if not (Id.equals x1 x2)
       then raise (Failure "Free Variable clash")

    | (MVar (Offset k, s), MVar (Offset k', s')) ->
       if k = k'
       then unifySub mflag cD0 cPsi s s'
       else raise (Failure (Format.sprintf "Bound MVar clash: %d with %d" k k'))

    | (FMVar (u, s), FMVar (u', s')) ->
       if Id.equals u u'
       then unifySub mflag cD0 cPsi s s'
       else raise (Failure "Bound FMVar clash'")

    | (FPVar (q, s), FPVar (p, s')) ->
       if Id.equals p q
       then unifySub mflag cD0 cPsi s s'
       else raise (Failure "Front FPVar mismatch")

    | (PVar (k, s), PVar (k', s')) ->
       if k = k'
       then unifySub mflag cD0 cPsi s s'
       else raise (Failure "Parameter variable clash")

    (* MPVar - MPVar *)
    | ( MPVar ((mmvar1, mt1), s1 as i1)
      , MPVar ((mmvar2, mt2), s2 as i2)
      )
         when mmvar1.instantiation == mmvar2.instantiation ->
       (* check s1' and s2' are pattern substitutions; possibly generate constraints;
           check intersection (s1', s2'); possibly prune *)
       if isPatMSub mt1 && isPatSub s1 && isPatMSub mt2 && isPatSub s2
       then unifyMMVarMMVar cPsi Syntax.Loc.ghost i1 i2
       else
         begin
           let id = next_constraint_id () in
           addConstraint (mmvar1.constraints, ref (Eqn (id, cD0, cPsi, IHead head2, IHead head1)))
         end

    | ( MPVar (({ typ = ClTyp (PTyp tA1, cPsi1); _ } as i1, mt1), s1)
      , MPVar (({ typ = ClTyp (PTyp tA2, cPsi2); _ } as i2, mt2), s2)
      ) ->
       if isPatMSub mt1 && isPatSub s1
       then
         begin
           unifyTyp mflag cD0 cPsi (tA1, s1) (tA2, s2);
           unifyMMVarTerm cD0 cPsi i1 mt1 s1 (IHead head2)
         end
       else if isPatMSub mt2 && isPatSub s2
       then
         begin
           unifyTyp mflag cD0 cPsi (tA1, s1) (tA2, s2);
           unifyMMVarTerm cD0 cPsi i2 mt2 s2 (IHead head1)
         end
       else
         begin
           let id = next_constraint_id () in
           addConstraint
             ( i1.constraints
             , ref (Eqn (id, cD0, cPsi, IHead head1, IHead head2))
             )
         end

    | (MPVar (({ typ = ClTyp (PTyp _, _); _ } as i, mt1), s1), h)
      | (h, MPVar (({ typ = ClTyp (PTyp _, _); _ } as i, mt1), s1)) ->
       (* ?#p[mt1, s1] ==  BVar k    or     ?#p[mt1, s1] = PVar (q, s) *)
       dprnt "(013) _-MPVar - head";
       let b1 = isVar h in
       let b2 = isPatSub s1 in
       let b3 = isPatMSub mt1 in
       if b1 && b2 && b3
       then unifyMMVarTerm cD0 cPsi i mt1 s1 (IHead h)
       else
         begin
           dprintf
             begin fun p ->
             p.fmt "[unifyH] @[<v>isVar h: %b\
                    @,isPatSub s1: %b\
                    @,isPatMSub mt1: %b@]"
               b1
               b2
               b3
             end;
           raise (Failure "Cannot instantiate PVar with a head which is not guaranteed to remain a variable")
         end

    | (PVar _, Proj (PVar _, _))
      | (Proj (PVar _, _), PVar _) ->
        print_string "[UnifyHead] Projection of a parameter variable\n";
        raise (Failure "PVar i =/= Proj PVar")

    | (Proj (h1, i1), Proj (h2, i2)) ->
       if i1 = i2
       then unifyHead mflag cD0 cPsi h1 h2
       else
         raise (Failure ("(Proj) Index clash: " ^ string_of_int i1 ^ " /= " ^ string_of_int i2))

    | (FVar _, Proj (PVar _, _)) ->
       print_string "[UnifyHead] Unify free variable with projection of parameter variable\n";
       raise (Failure "Projection of parameter variable =/= free variable")

    | _ ->
       dprint (fun () -> "[unifyHead'] Head clash");
       raise (Failure "Head clash")


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
  and unifySpine mflag cD0 cPsi spine1 spine2 =
    match (spine1, spine2) with
    | ((Nil, _), (Nil, _)) -> ()

    | ((SClo (tS1, s1'), s1), sS) ->
       unifySpine mflag cD0 cPsi (tS1, comp s1' s1) sS

    | (sS, (SClo (tS2, s2'), s2)) ->
       unifySpine mflag cD0 cPsi sS (tS2, comp s2' s2)

    | ((App (tM1, tS1), s1), (App (tM2, tS2), s2)) ->
       (* dprint (fun () -> "[unifySpine] " ^ P.normalToString cD0 cPsi (tM1, s1) ^
                    " == " ^ P.normalToString cD0 cPsi (tM2, s2));*)
       unifyTerm mflag cD0 cPsi (tM1, s1) (tM2, s2);
       unifySpine mflag cD0 cPsi (tS1, s1) (tS2, s2)
  (* Nil/App or App/Nil cannot occur by typing invariants *)

  and unifySub mflag cD0 cPsi s1 s2 =
    unifySub'
      mflag
      cD0
      cPsi
      (simplifySub cD0 cPsi (Whnf.cnormSub (s1, Whnf.m_id)))
      (simplifySub cD0 cPsi (Whnf.cnormSub (s2, Whnf.m_id)))

  and unifySub' mflag cD0 cPsi s1 s2 =
    match (s1, s2) with
    | (Shift n, Shift k) ->
       if n <> k
       then raise (Error "Substitutions not well-typed")

    | (FSVar (n1, (s1, sigma1)), FSVar (n2, (s2, sigma2))) ->
       if Id.equals s1 s2 && n1 = n2
       then unifySub mflag cD0 cPsi sigma1 sigma2
       else raise (Failure "FSVar mismatch")

    | (SVar (s1, n1, sigma1), Shift 0)
      | (Shift 0, SVar (s1, n1, sigma1)) -> ()

    | (SVar (s1, n1, sigma1), SVar (s2, n2, sigma2)) ->
       if s1 = s2 && n1 = n2
       then unifySub mflag cD0 cPsi sigma1 sigma2
       else raise (Failure "SVar mismatch")

    | (Dot (f, s), Dot (f', s')) ->
       unifyFront mflag cD0 cPsi f f';
       unifySub mflag cD0 cPsi s s'

    | (Shift n, Dot (Head (BVar _), _)) ->
       unifySub mflag cD0 cPsi (Dot (Head (BVar (n + 1)), Shift (n + 1))) s2

    | (Dot (Head (BVar _), _), Shift n) ->
       unifySub mflag cD0 cPsi s1 (Dot (Head (BVar (n + 1)), Shift (n + 1)))

    | ( MSVar (_, ((mmvar1, mt1), t1 as q1))
      , MSVar (_, ((mmvar2, mt2), t2 as q2))
      )
         when mmvar1.instantiation == mmvar2.instantiation
              && isPatMSub mt1
              && isPatSub t1
              && isPatMSub mt2
              && isPatSub t2 ->
       unifyMMVarMMVar cPsi Syntax.Loc.ghost q1 q2

    | (MSVar (_, ((q, mt), s)), s2)
         when isPatSub s && isPatMSub mt ->
       unifyMMVarTerm cD0 cPsi q mt s (ISub s2)
    | (s2, MSVar (_, ((q, mt), s)))
         when isPatSub s && isPatMSub mt ->
       unifyMMVarTerm cD0 cPsi q mt s (ISub s2)

    | (MSVar (_, ((mmvar, _), _)), _)
      | (_, MSVar (_, ((mmvar, _), _))) ->
       let id = next_constraint_id () in
       addConstraint (mmvar.constraints, ref (Eqn (id, cD0, cPsi, ISub s1, ISub s2)))

    | (EmptySub, _)
      | (_, EmptySub)
      | (_, Undefs)
      | (Undefs, _) -> ()

    | _ ->
       let s =
         let open Format in
         let f = P.fmt_ppr_lf_sub cD0 cPsi P.l0 in
         fprintf str_formatter "@[<v>Substitution mismatch:@,%a |- %a =/= %a@]"
           (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi
           f s1 f s2;
         flush_str_formatter ()
       in
       raise (Failure s)

  and unifyFront mflag cD0 cPsi front1 front2 =
    match (front1, front2) with
    | (Head (BVar i), Head (BVar k)) ->
       if i <> k
       then raise (Failure "Front BVar mismatch")

    | (Head (Const i), Head (Const k)) ->
       if not (Id.cid_equals i k)
       then raise (Failure "Front Constant mismatch")

    | (Head (PVar (q, s)), Head (PVar (p, s'))) ->
       if p = q
       then unifySub mflag cD0 cPsi s s'
       else raise (Failure "Front PVar mismatch")

    | (Head (FPVar (q, s)), Head (FPVar (p, s'))) ->
       if Id.equals p q
       then unifySub mflag cD0 cPsi s s'
       else raise (Failure "Front FPVar mismatch")

    | (Head (MVar (u, s)), Head (MVar (v, s'))) ->
       (* XXX THIS IS SKETCHY!
            It is very suspicious to me that here we just check
            structural equality of the cvars.
            Should they not be unified? What if they're actually
            mmvars inside?
            -je *)
       if Stdlib.(=) u v
       then unifySub mflag cD0 cPsi s s'
       else raise (Failure "Front MVar mismatch")

    | (Head (FMVar (u, s)), Head (FMVar (v, s'))) ->
       if Id.equals u v
       then unifySub mflag cD0 cPsi s s'
       else raise (Failure "Front FMVar mismatch")

    | (Head (Proj (head, k)), Head (Proj (head', k'))) ->
       if k = k'
       then unifyFront mflag cD0 cPsi (Head head) (Head head')
       else raise (Failure "Front Proj mismatch")

    | (Head (FVar x), Head (FVar y)) ->
       if not (Id.equals x y)
       then raise (Failure "Front FVar mismatch")

    | (Obj tM, Obj tN) ->
       unifyTerm mflag cD0 cPsi (tM, id) (tN, id)

    | (Head head, Obj tN) | (Obj tN, Head head) ->
       unifyTerm
         mflag
         cD0
         cPsi
         (Root (Syntax.Loc.ghost, head, Nil, `explicit), id)
         (tN, id)

    | (Undef, Undef) -> ()

    | _ -> raise (Failure "Front mismatch")


  and unifyTyp mflag cD0 cPsi sA sB = unifyTypW mflag cD0 cPsi (Whnf.whnfTyp sA) (Whnf.whnfTyp sB)

  and unifyTypW mflag cD0 cPsi sA sB =
    match (sA, sB) with
    | ( (Atom (_, (a, b), tS1), s1)
      , (Atom (_, (a', b'), tS2), s2)
      )
         when a = a' && b = b' ->
       unifySpine mflag cD0 cPsi (tS1, s1) (tS2, s2)

    | ((Atom _, _), (Atom _, _)) ->
       dprintf
         begin fun p ->
         let f ppf x =
           P.fmt_ppr_lf_typ cD0 cPsi P.l0 ppf (Whnf.normTyp x)
         in
         p.fmt "UnifyTyp %a ==== %a"
           f sA
           f sB
         end;
       raise (Failure "Type constant clash")

    | ((PiTyp ((TypDecl (x, tA1), dep), tA2), s1), (PiTyp ((TypDecl (_, tB1), _), tB2), s2)) ->
       unifyTyp mflag cD0 cPsi (tA1, s1) (tB1, s2);
       unifyTyp mflag cD0 (DDec (cPsi, TypDecl (x, tA1))) (tA2, dot1 s1) (tB2, dot1 s2)

    | ((Sigma typ_rec1, s1), (Sigma typ_rec2, s2)) ->
       unifyTypRecW mflag cD0 cPsi (typ_rec1, s1) (typ_rec2, s2)

    | _ -> raise (Failure "Type mismatch")

  and unifyTypRecW mflag cD0 cPsi srec1 srec2 =
    match (srec1, srec2) with
    | ((SigmaLast (_, tA1), s1), (SigmaLast (_, tA2), s2)) ->
       (* dprint (fun () -> "[unifyTypRecW] Last "
                          ^ P.typToString cD0 cPsi (tA1, s1) ^ " == "
                          ^ P.typToString cD0 cPsi (tA2, s2) ^ "\n");*)
       unifyTyp mflag cD0 cPsi (tA1, s1) (tA2, s2)
    (*; dprint (fun () -> "succeeded   ["
                          ^ P.typRecToString cD0 cPsi srec1
                          ^ "]  ["
                          ^ P.typRecToString cD0 cPsi srec2 ^ "]");*)

    | ((SigmaElem (x1, tA1, trec1), s1), (SigmaElem (_, tA2, trec2), s2)) ->
       (*dprint (fun () -> "[unifyTypRecW] Elements " ^
                     P.typToString cD0 cPsi (tA1, s1) ^ " == "
                     ^ P.typToString cD0 cPsi (tA2, s2));*)
       unifyTyp mflag cD0 cPsi (tA1, s1) (tA2, s2);
       let s1' = dot1 s1 in
       let s2' = dot1 s2 in
       unifyTypRecW mflag cD0 (DDec (cPsi, TypDecl (x1, TClo (tA1, s1)))) (trec1, s1') (trec2, s2')

    | _ -> raise (Failure "TypRec length clash")


  (* Unify pattern fragment, and force constraints after pattern unification
   succeeded *)
  (* Pre-condition: cPsi1, cPsi2 are in normal form *)

  and unifyDCtx1 mflag cD cPsi1 cPsi2 =
    unifyDCtx1' mflag cD (Whnf.cnormDCtx (cPsi1, Whnf.m_id)) (Whnf.cnormDCtx (cPsi2, Whnf.m_id))

  and unifyDCtx1' mflag cD0 cPsi1 cPsi2 =
    match (cPsi1, cPsi2) with
    | (Null, Null) -> ()

    | ( CtxVar (CInst (mmvar1 (* (n1, ({contents = None} as cvar_ref1), cD1, CTyp schema1, _, _) *), theta1))
      , CtxVar (CInst (mmvar2 (* (_, ({contents = None} as cvar_ref2), _, CTyp schema2, _, _) *), theta2))
      )
         when not (is_mmvar_instantiated mmvar1) && not (is_mmvar_instantiated mmvar2) ->
       let CTyp schema1, CTyp schema2 = mmvar1.typ, mmvar2.typ in
       if mmvar1.instantiation == mmvar2.instantiation
       then
         if Maybe.equals Id.cid_equals schema1 schema2
         then
           if isPatMSub theta1 && isPatMSub theta2
           then
             begin
               if not (Whnf.convMSub theta1 theta2)
               then
                 begin
                   let (mt', cD') =
                     m_intersection
                       (Whnf.cnormMSub theta1)
                       (Whnf.cnormMSub theta2)
                       mmvar1.cD
                   in
                   let mmvar =
                     { mmvar1 with
                       instantiation = ref None;
                       cD = cD';
                       constraints = ref [];
                       depend = Maybe
                     }
                   in
                   let cPsi = CtxVar (CInst (mmvar, mt')) in
                   instantiateCtxVar (mmvar1.instantiation, cPsi)
                 end
             end
           else
             Error.violation
               "Case where we need to unify the same context \
                variables which are associated with different \
                meta-stitutions which are non-patterns is not \
                handled"
         else
           Error.violation "Schema mismatch"
       else if isPatMSub theta1 && isPatMSub theta2
       then
         begin
           let mtt1 = Whnf.m_invert (Whnf.cnormMSub theta1) in
           instantiateCtxVar
             ( mmvar1.instantiation
             , Whnf.cnormDCtx (cPsi2, mtt1)
             )
         end
       else
         Error.violation
           "Case where both meta-substitutions associated with \
            context variables are not pattern substitutions \
            should not happen and is not implemented for now"

    | (CtxVar (CInst (mmvar, theta)), cPsi)
      | (cPsi, CtxVar (CInst (mmvar, theta))) ->
       let CTyp s_cid = mmvar.typ in
       if isPatMSub theta
       then
         begin
           let mtt1 = Whnf.m_invert (Whnf.cnormMSub theta) in
           instantiateCtxVar
             ( mmvar.instantiation
             , Whnf.cnormDCtx (cPsi, mtt1)
             );
           match Context.ctxVar cPsi with
           | Some (CtxName psi) ->
              begin
                try
                  ignore (FCVar.get psi)
                with
                | Not_found ->
                   FCVar.add psi (cD0, Decl (psi, CTyp s_cid, Maybe))
              end
           | _ -> ()
         end
       else
         Error.violation
           "Case where both meta-substitutions associated with \
            context variables are not pattern substitutions \
            should not happen and is not implemented for now"

    | (CtxVar (CtxName c1), CtxVar (CtxName c2)) when Id.equals c1 c2 -> ()
    | (CtxVar (CtxOffset k1), CtxVar (CtxOffset k2)) when k1 = k2 -> ()
    | (CtxVar _, CtxVar _) -> (* else, the variables are unequal *)
       dprintf
         begin fun p ->
         let f = P.fmt_ppr_lf_dctx cD0 P.l0 in
         p.fmt "[unifyDCtx] @[<v>cPsi1 = %a@,cPsi2 = %a@]"
           f cPsi1 f cPsi2
         end;
       fail "Bound (named) context variable clash"

    | (DDec (cPsi1, TypDecl (_, tA1)), DDec (cPsi2, TypDecl (_, tA2))) ->
       unifyDCtx1' mflag cD0 cPsi1 cPsi2;
       dprintf
         begin fun p ->
         let f psi = P.fmt_ppr_lf_typ cD0 psi P.l0 in
         p.fmt "[unifyDCtx] @[<v>unify type-decl@,%a == %a@]"
           (f cPsi1) tA1
           (f cPsi2) tA2
         end;
       unifyTyp mflag cD0 cPsi1 (tA1, id) (tA2, id)

    | (DDec (cPsi1, _), DDec (cPsi2, _)) ->
       unifyDCtx1' mflag cD0 cPsi1 cPsi2

    | _ ->
       dprintf
         begin fun p ->
         let f = P.fmt_ppr_lf_dctx cD0 P.l0 in
         p.fmt "Unify Context clash: @[<v>cPsi1 = %a@,cPsi2 = %a@]"
           f cPsi1 f cPsi2
         end;
       fail "Context clash"

  (* **************************************************************** *)
  let rec unifyMetaObj cD (mO, t) (mO', t') (cdecl, mt) =
    let Decl (_, cT, _) = cdecl in
    unifyMObj cD (mO, t) (mO', t') (cT, mt)

  and unifyClObj' cD mO mO' mT =
    match (mO, mO', mT) with
    | (PObj h, PObj h', ClTyp (_, cPsi)) ->
       unifyHead Unification cD cPsi h h'
    | (MObj tR, MObj tR', ClTyp (_, cPsi)) ->
       unifyTerm Unification cD cPsi (tR, id) (tR', id);
    | (SObj s, SObj s', ClTyp (_, cPsi)) ->
       unifySub Unification cD cPsi (simplifySub cD cPsi s) (simplifySub cD cPsi s')
    | _ ->
       dprint (fun () -> "[unifyClObj'] fall through");
       raise (Failure "MetaObj mismatch")

  and unifyClObj cD (mO, t) (mO', t') (cT, mt) =
    unifyClObj' cD (Whnf.cnormClObj mO t) (Whnf.cnormClObj mO' t') (Whnf.cnormMTyp (cT, mt))

  and unifyMFront' cD (mO, t) (mO', t') (cT, mt) =
    match (mO, mO') with
    | (CObj cPsi, CObj cPsi') ->
       unifyDCtx1 Unification cD (Whnf.cnormDCtx (cPsi, t)) (Whnf.cnormDCtx (cPsi', t'))
    | (ClObj (phat, m1), ClObj (phat', m2)) ->
       unifyClObj cD (m1, t) (m2, t') (cT, mt)
    | _ ->
       dprint (fun () -> "[unifyMetaObj] fall through");
       raise (Failure "MetaObj mismatch")

  and unifyMObj cD (mO, t) (mO', t') (cT, mt) =
    unifyMFront' cD (Comp.metaObjToMFront mO, t) (Comp.metaObjToMFront mO', t') (cT, mt)

  let rec unifyMetaSpine cD (mS, t) (mS', t') (cK, mt) =
    match (mS, mS') with
    | (Comp.MetaNil, Comp.MetaNil) -> ()
    | (Comp.MetaApp (mO, mT, mS, _), Comp.MetaApp (mO', mT', mS', _)) ->
       let Comp.PiKind (_, cdecl, cK') = cK in
       let mOt = Whnf.cnormMetaObj (mO, t) in
       (* let mOt' = Whnf.cnormMetaObj (mO', t') in *)
       unifyMetaObj cD (mO, t) (mO', t') (cdecl, mt);
       let mt' = MDot (Comp.metaObjToMFront mOt, mt) in
       dprintf
         begin fun p ->
         p.fmt "[unifyMetaSpine] @[<v>@[%a@] ===@ @[%a@]@]"
           P.(fmt_ppr_cmp_meta_typ cD) (Whnf.cnormMTyp (mT, t))
           P.(fmt_ppr_cmp_meta_typ cD) (Whnf.cnormMTyp (mT', t'))
         end;
       unifyMetaTyp cD (mT, t) (mT', t');
       unifyMetaSpine cD (mS, t) (mS', t') (cK', mt')

    | _ -> raise (Failure "Meta-Spine mismatch")

  and unifyClTyp Unification cD cPsi =
    function
    | (MTyp tA1, MTyp tA2) -> unifyTyp Unification cD cPsi (tA1, id) (tA2, id)
    | (PTyp tA1, PTyp tA2) -> unifyTyp Unification cD cPsi (tA1, id) (tA2, id)
    | (STyp (_, cPhi1), STyp (_, cPhi2)) -> unifyDCtx1 Unification cD cPhi1 cPhi2

  and unifyCLFTyp Unification cD ctyp1 ctyp2 =
    match (ctyp1, ctyp2) with
    | (ClTyp (tp1, cPsi1), ClTyp (tp2, cPsi2)) ->
       unifyDCtx1 Unification cD cPsi1 cPsi2;
       unifyClTyp Unification cD cPsi1 (tp1, tp2)
    | (CTyp schema1, CTyp schema2) ->
       if not (Maybe.equals Id.cid_equals schema1 schema2)
       then raise (Failure "CtxPi schema clash")
    | _ -> raise (Failure "Computation-level Type Clash")

  and unifyMetaTyp cD (mT, ms) (mT', ms') =
    unifyCLFTyp Unification cD (Whnf.cnormMTyp (mT, ms)) (Whnf.cnormMTyp (mT', ms'))

  let rec unifyCompTyp cD tau_t tau_t' =
    (unifyCompTypW cD (Whnf.cwhnfCTyp tau_t) (Whnf.cwhnfCTyp tau_t');
     dprint (fun () -> "[unifyCompTyp] - done"))

  and unifyCompTypW cD tau_t tau_t' =
    match (tau_t, tau_t') with
    | (Comp.TypInd tau, t), tau_t' -> unifyCompTyp cD (tau, t) tau_t'
    | tau_t, (Comp.TypInd tau', t') -> unifyCompTyp cD tau_t (tau', t')

    | ((Comp.TypBase (_, c, mS), t), (Comp.TypBase (_, c', mS'), t')) ->
       if Id.cid_equals c c'
       then
         let tK = (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.Entry.kind in
         unifyMetaSpine cD (mS, t) (mS', t') (tK, Whnf.m_id)
         (* dprint (fun () -> "[unifyCompTyp] " ^
                       P.compTypToString cD (Whnf.cnormCTyp tau_t) ^ " == " ^
                       P.compTypToString cD (Whnf.cnormCTyp tau_t'))*)

       else
         raise (Failure "Type Constant Clash")

    | ((Comp.TypCobase (_, c, mS), t), (Comp.TypCobase (_, c', mS'), t')) ->
       if Id.cid_equals c c'
       then
         let tK = (Store.Cid.CompCotyp.get c).Store.Cid.CompCotyp.Entry.kind in
         unifyMetaSpine cD (mS, t) (mS', t') (tK, Whnf.m_id);
         (* dprint (fun () -> "[unifyCompTyp] " ^
                       P.compTypToString cD (Whnf.cnormCTyp tau_t) ^ " == " ^
                       P.compTypToString cD (Whnf.cnormCTyp tau_t')) *)

       else
         raise (Failure "Type Constant Clash")
    (* !!
      | ((Comp.TypBox (_, ClTyp (MTyp tA, cPsi)), t), (Comp.TypBox (_, ClTyp (MTyp tA', cPsi')), t')) ->
          let cPsi1 = Whnf.cnormDCtx (cPsi, t) in
          (unifyDCtx1 Unification cD cPsi1 (Whnf.cnormDCtx (cPsi', t'));
           (* dprint (fun () -> "[unifyCompTyp] Unifying contexts done");
           dprint (fun () -> "               cPsi = " ^ P.dctxToString cD cPsi ^
                           "\n               cPsi' = " ^ P.dctxToString cD cPsi');
           dprint (fun () -> "[unifyCompTyp] tA = " ^ P.typToString cD cPsi (Whnf.cnormTyp (tA, t), id));
           dprint (fun () -> "[unifyCompTyp] tA' = " ^ P.typToString cD cPsi' (Whnf.cnormTyp (tA', t'), id)); *)
           unifyTyp Unification cD cPsi1 (Whnf.cnormTyp (tA, t), id) (Whnf.cnormTyp (tA', t'), id)
          )
     *)

    | ((Comp.TypBox (_, mT), t), (Comp.TypBox (_, mT'), t')) ->
       unifyCLFTyp Unification cD (Whnf.cnormMTyp (mT, t)) (Whnf.cnormMTyp (mT', t'))

    | ((Comp.TypArr (_, tau1, tau2), t), (Comp.TypArr (_, tau1', tau2'), t')) ->
       unifyCompTyp cD (tau1, t) (tau1', t');
       unifyCompTyp cD (tau2, t) (tau2', t')


    | ((Comp.TypCross (_, tau1, tau2), t), (Comp.TypCross (_, tau1', tau2'), t')) ->
       unifyCompTyp cD (tau1, t) (tau1', t');
       unifyCompTyp cD (tau2, t) (tau2', t')

    (* !!      | ((Comp.TypPiBox ((Decl (psi, CTyp schema, dep)), tau), t)
         , (Comp.TypPiBox ((Decl (_, CTyp schema', dep')), tau'), t')) ->
          if schema = schema' && dep = dep' then
            unifyCompTyp
              (Dec (cD, Decl (psi, CTyp schema, dep))) (* TODO: Clean this up, merge with case below.
                                                      Add dep to all Decls? *)
              (tau, Whnf.mvar_dot1 t) (tau', Whnf.mvar_dot1 t')
          else
            raise (Failure "CtxPi schema clash")
     *)
    | ( (Comp.TypPiBox (_, (Decl (u, ctyp1, dep)), tau), t)
      , (Comp.TypPiBox (_, (Decl (_, ctyp2, _)), tau'), t')
      ) ->
       let ctyp1n = Whnf.cnormMTyp (ctyp1, t) in
       let ctyp2n = Whnf.cnormMTyp (ctyp2, t') in
       unifyCLFTyp Unification cD ctyp1n ctyp2n;
       unifyCompTyp
         (Dec (cD, Decl (u, ctyp1n, dep)))
         (tau, Whnf.mvar_dot1 t)
         (tau', Whnf.mvar_dot1 t')

    | _ -> raise (Failure "Computation-level Type Clash")


  (* **************************************************************** *)
  let unifyITerm cD cPsi itM1 itM2 =
    match (itM1, itM2) with
    | (INorm tM1, INorm tM2) -> unifyTerm Unification cD cPsi (tM1, id) (tM2, id)
    | (IHead tH1, IHead tH2) -> unifyHead Unification cD cPsi tH1 tH2
    | (ISub s1, ISub s2) -> unifySub Unification cD cPsi s1 s2

  (* NOTE: We sometimes flip the position when we generate constraints;
       if matching requires that the first argument is fixed then this may
       become problematic if we are outside the pattern fragment -bp *)
  let rec forceCnstr mflag constrnt =
    match constrnt with
    | None -> ()
    | Some cnstr ->
       begin match !cnstr with
       | Queued id ->
          forceCnstr mflag (nextCnstr ())
       | Eqn (c_id, cD, cPsi, INorm tM1, INorm tM2) ->
          solveConstraint cnstr;
          if not (Whnf.conv (tM1, id) (tM2, id))
          then unifyTerm mflag cD cPsi (tM1, id) (tM2, id);
          forceCnstr mflag (nextCnstr ())
       | Eqn (id, cD, cPsi, IHead h1, IHead h2) ->
          solveConstraint cnstr;
          unifyHead mflag cD cPsi h1 h2;
          forceCnstr mflag (nextCnstr ())
       end

  and forceGlobalCnstr () =
    let constrs = !globalCnstrs in
    resetGlobalCnstrs ();
    forceGlobalCnstr' constrs;
    match !globalCnstrs with
    | [] -> ()
    | cs ->
       Format.fprintf Format.str_formatter "Unresolved constraints@,@[<v 2>  %a@]@."
         P.fmt_ppr_lf_constraints cs;
       raise (Failure (Buffer.contents Format.stdbuf))

  and forceGlobalCnstr' c_list =
    match c_list with
    | [] -> ()
    | c :: cnstrs
         when is_trivial_constraint !c ->
       solveConstraint c;
       dprintf
         begin fun p ->
         p.fmt "[forceGlobalCnstr'] @[<v>processing trivial constraint\
                @,@[%a@]@]"
           P.fmt_ppr_lf_constraint !c
         end;
       forceGlobalCnstr' cnstrs
    (* constraints that are Queued are considered trivial, so this
         time we must have an outstanding Eqn whose terms are not
         convertible *)
    | c :: cnstrs ->
       let Eqn (_, cD, cPsi, itM1, itM2) as c' = !c in
       solveConstraint c;
       dprintf
         begin fun p ->
         p.fmt "[forceGlobalCnstr'] @[<v>processing nontrivial constraint\
                @,@[%a@]@]"
           P.fmt_ppr_lf_constraint c'
         end;
       begin
         try
           unifyITerm cD cPsi itM1 itM2;
           forceCnstr Unification (nextCnstr ())
         with
         | Failure msg ->
            let cnstr_string =
              let open Format in
              fprintf str_formatter "@[<v>@[%a@]@,@[%a@]@]"
                P.fmt_ppr_lf_constraint c'
                pp_print_string msg;
              flush_str_formatter ()
            in
            raise (GlobalCnstrFailure (Loc.ghost, cnstr_string))
       end;
       (* Unification could succeed by postponing the constraint
            we just tried to solve, so now we need to check that
            that didn't happen.
            To do this, we can just check that there are no
            unsolved global constraints.
            Since forceGlobalCnstr' has the precondition that the
            list of global constraints be empty (this is ensured by
            getting the list and then calling resetGlobalCnstrs)
            and since it maintains this invariant, if there are any
            *unsolved* constraints at this point, then it's because
            the unification we just called added it.
        *)
       if solvedCnstrs (!globalCnstrs)
       then (resetGlobalCnstrs (); forceGlobalCnstr' cnstrs)
       else raise (GlobalCnstrFailure (Loc.ghost, "[forceGlobalCnstr'] Constraints generated"))

  let unresolvedGlobalCnstrs () =
    try
      forceGlobalCnstr ();
      resetGlobalCnstrs ();
      false
    with
    | Failure _ -> resetGlobalCnstrs (); true
    | GlobalCnstrFailure _ -> resetGlobalCnstrs (); true

  let unify' mflag cD0 cPsi sM1 sM2 =
    resetDelayedCnstrs ();
    unifyTerm mflag cD0 cPsi sM1 sM2;
    forceCnstr mflag (nextCnstr ())

  let unifyTyp1 mflag cD0 cPsi sA sB =
    unifyTyp mflag cD0 cPsi sA sB;
    forceCnstr mflag (nextCnstr ())
  (*      dprint (fun () -> "Forcing Cnstr DONE") *)


  let unifyTyp' mflag cD0 cPsi sA sB =
    (* dprint (fun () -> "\nUnifyTyp' " ^ *)
    (*                  P.typToString cD0 cPsi sA ^ "\n          " ^ *)
    (*                  P.typToString cD0 cPsi sB); *)
    resetDelayedCnstrs ();
    unifyTyp1 mflag cD0 cPsi sA sB
    (* dprint (fun () -> "After unifyTyp'"); *)
    (* dprint (fun () -> "cPsi = " ^ P.dctxToString cD0 cPsi ^ "\n"); *)
    (* dprint (fun () -> "sA = " ^ P.typToString cD0 cPsi sA ^ "\n     "); *)
    (* dprint (fun () -> "sB = " ^ P.typToString cD0 cPsi sB) *)

  let unifyTypRec1 mflag cD0 cPsi sArec sBrec =
    unifyTypRecW mflag cD0 cPsi sArec sBrec;
    forceCnstr mflag (nextCnstr ())

  let unifyTypRec' mflag cD0 cPsi sArec sBrec =
    resetDelayedCnstrs ();
    unifyTypRec1 mflag cD0 cPsi sArec sBrec

  let unify cD0 cPsi sM sN =
    let f ppf x = P.fmt_ppr_lf_normal cD0 cPsi P.l0 ppf (Whnf.norm x) in
    dprintf
      begin fun p ->
      p.fmt "[unify] @[<v>%a@,with@,%a@]"
        f sM
        f sN
      end;
    unify' Unification cD0 cPsi sM sN;
    dprintf
      begin fun p ->
      p.fmt "[unify] @[<v>DONE:@,%a == %a@]"
        f sM
        f sN
      end

  let unifyH cD phat h h' =
    unifyHead Unification cD (Context.hatToDCtx phat) h h'

  let unifySub cD cPsi s1 s2 =
    unifySub Unification cD cPsi s1 s2
  (* **************************************************************** *)

  let unify_phat psihat phihat =
    let psihat = Whnf.cnorm_psihat psihat (MShift 0) in
    let phihat = Whnf.cnorm_psihat phihat (MShift 0) in
    match phihat with
    | (Some (CInst (mmvar1, theta1)), d)
         when not (is_mmvar_instantiated mmvar1) ->
       begin match psihat with
       | (Some (CInst (mmvar2, theta2)), d')
            when not (is_mmvar_instantiated mmvar2) ->
          if mmvar1.instantiation == mmvar2.instantiation
          then
            if Whnf.convMSub theta1 theta2 && not (d = d')
            then fail "Hat context mismatch- 1"
            else if isPatMSub theta1 && isPatMSub theta2
            then
              begin
                let (mt', cD') =
                  m_intersection
                    (Whnf.cnormMSub theta1)
                    (Whnf.cnormMSub theta2)
                    mmvar1.cD
                in
                let mmvar1' =
                  { mmvar1 with
                    instantiation = ref None;
                    cD = cD';
                    depend = Maybe;
                    constraints = ref []
                  }
                in
                let cPsi = CtxVar (CInst (mmvar1', mt')) in
                instantiateCtxVar (mmvar1.instantiation, cPsi)
              end
            else
              Error.violation
                "Case where we need to unify the same context \
                 variables which are associated with different \
                 meta-stitutions which are non-patterns is not \
                 handled"
          else if isPatMSub theta1 && isPatMSub theta2
          then
            begin
              let mtt1 = Whnf.m_invert (Whnf.cnormMSub theta1) in
              let mmvar2' = { mmvar2 with depend = Maybe; constraints = ref [] } in
              (* why do we drop the constraints here ? -je *)
              let i = CInst (mmvar2', Whnf.mcomp theta2 mtt1) in
              mmvar1.instantiation := Some (ICtx (CtxVar i))
            end
          else
            Error.violation
               "Case where we need to unify the context variables \
                which are associated with different meta-stitutions \
                which are non-patterns is not handled"

       | (Some c_var, d') ->
          if d = d'
          then mmvar1.instantiation := Some (ICtx (CtxVar (c_var)))
          else if d' < d
          then fail "Hat Context's do not unify"
          else
            begin
              let cPsi = Context.hatToDCtx (Some c_var, d' - d) in
              mmvar1.instantiation := Some (ICtx cPsi)
            end

       | (None, d') ->
          if d = d'
          then mmvar1.instantiation := Some (ICtx Null)
          else if d' < d
          then
            (* (Some (cref), d) == (None, d') d' = d0+d *)
            fail "Hat Context's do not unify"
          else
            begin
              let cPsi = Context.hatToDCtx (None, d' - d) in
              mmvar1.instantiation := Some (ICtx cPsi)
            end
       end

    | _ ->
       if not (Whnf.convDCtxHat psihat phihat)
       then fail "Hat context mismatch - 2"

   (* **************************************************************** *)

  let unifyClObj cPsi m1 m2 =
    match (m1, m2) with
    | (MObj tM1, MObj tM2) -> unify Empty cPsi (tM1, id) (tM2, id)
    | (PObj h, PObj h') -> unifyHead Unification Empty cPsi h h'

  let unifyMFront m1 m2 =
    match (m1, m2) with
    | (CObj cPsi, CObj cPhi) ->
       unifyDCtx1
         Unification
         Empty
         (Whnf.cnormDCtx (cPsi, Whnf.m_id))
         (Whnf.cnormDCtx (cPhi, Whnf.m_id))
    | (ClObj (phat1, m1), ClObj (phat2, m2)) ->
       (* unify_phat phat1 phat2; *)
       unifyClObj (Context.hatToDCtx phat1) m1 m2

  let rec unifyMSub' ms mt =
    match (ms, mt) with
    | (MShift k, MShift k') ->
       if k <> k'
       then raise (Failure "Contextual substitutions not of the same length")

    | (MDot (mFt, ms), MShift k)
      | (MShift k, MDot (mFt, ms)) ->
       unifyMFront mFt (MV (k + 1));
       unifyMSub' ms (MShift (k + 1))

    | (MDot (mF1, ms'), MDot (mF2, mt')) ->
       unifyMFront mF1 mF2;
       unifyMSub' ms' mt'

  let unifyMSub ms mt = unifyMSub' (Whnf.cnormMSub ms) (Whnf.cnormMSub mt)

  let unifyTypRec cD0 cPsi sArec sBrec =
    unifyTypRec' Unification cD0 cPsi sArec sBrec

  let unifyTyp cD0 cPsi sA sB =
    dprintf
      begin fun p ->
      p.fmt "[unifyTyp] @[<v>unifying LF types:@,\
             s_1[A] = @[%a@]@,\
             s_2[B] = @[%a@]@,\
             in cD = @[%a@]@,\
             and cPsi = @[%a@]@]"
        P.(fmt_ppr_lf_typ cD0 cPsi l0) (Whnf.normTyp sA)
        P.(fmt_ppr_lf_typ cD0 cPsi l0) (Whnf.normTyp sB)
        P.(fmt_ppr_lf_mctx l0) cD0
        P.(fmt_ppr_lf_dctx cD0 l0) cPsi
      end;
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

  let unifyCompTyp cD ttau ttau' =
    try
      unifyCompTyp cD ttau ttau'
    with
    | Failure msg ->
      dprint (fun () -> "[unifyCompTyp] " ^ msg);
      raise (Failure msg)
end


module EmptyTrail = Make (EmptyTrail)
module StdTrail = Make (StdTrail)
