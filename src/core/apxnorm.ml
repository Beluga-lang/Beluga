open Support
open Syntax

(* ********************************************************************************)
(* Pretty printing                                                                *)
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
module RR = Store.Cid.NamedRenderer

let (dprintf, dprint, _) = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt
(* ********************************************************************************)

(* exception NotImplemented *)

type error =
  | CtxOverGeneral
  | IndexInvariantFailed of (Format.formatter -> unit -> unit)

exception Error of Syntax.Loc.t * error

let _ =
  Error.register_printer
    begin fun (Error (loc, err)) ->
    Error.print_with_location loc
      begin fun ppf ->
      let open Format in
      match err with
      | CtxOverGeneral ->
         fprintf ppf "context in the body appears to be more general than the context supplied\n"
      | IndexInvariantFailed f ->
         fprintf ppf "Indexing invariant failed: %a@."
           f ()
      end
    end

let throw loc e = raise (Error (loc, e))

(* ********************************************************************************)
let lengthApxMCtx = Context.length

(* -------------------------------------------------------------*)
(* EtaExpansion of approximate terms *)
let rec shiftApxTerm k =
  function
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam(loc, x, shiftApxTerm (k+1) m')
  | Apx.LF.Root (loc, h , spine) ->
     let h' = shiftApxHead k h in
     let spine' = shiftApxSpine k spine in
     Apx.LF.Root(loc, h', spine')

and shiftApxHead k =
  function
  | Apx.LF.BVar x -> Apx.LF.BVar (x+k)
  | Apx.LF.FMVar (u, s) ->
     Apx.LF.FMVar (u, Option.(s $> fun s -> shiftApxSub k s))
  | Apx.LF.FPVar (p, s) ->
     Apx.LF.FMVar (p, Option.(s $> fun s -> shiftApxSub k s))
  | Apx.LF.MVar (u, s) ->
     Apx.LF.MVar (u, Option.(s $> fun s -> shiftApxSub k s))
  | h -> h

and shiftApxSpine k =
  function
  | Apx.LF.Nil -> Apx.LF.Nil
  | Apx.LF.App (m, spine') ->
     let spine'' = shiftApxSpine k spine' in
     Apx.LF.App (shiftApxTerm k m, spine'')

and shiftApxSub k =
  function
  | Apx.LF.EmptySub -> Apx.LF.EmptySub
  | Apx.LF.Id -> Apx.LF.Id
  | Apx.LF.Dot (Apx.LF.Head h, s) ->
     let h' = shiftApxHead k h in
     let s' = shiftApxSub k s in
     Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) ->
     let m' = shiftApxTerm k m in
     let s' = shiftApxSub k s in
     Apx.LF.Dot (Apx.LF.Obj m', s')


(* ******************************************************************* *)
(* Shift mvars in approximate expression by k *)
(* Apply modal substitution t to approximate term
   where cD1 contains all the free modal variables in m

   cnormApxExp e t  = e'

   if  cD1''      |- t <= cD @ delta  and
       cD @ delta |- e <= apx_exp
   the cD1''  |- |[t]|e <= apx_exp

*)

let rec cnormApxTerm cD delta m (cD'', t) =
  match m with
  | Apx.LF.Lam (loc, x, m') ->
     Apx.LF.Lam (loc, x, cnormApxTerm cD delta m' (cD'', t))

  | Apx.LF.Root (loc, h, s) ->
     let h' = cnormApxHead cD delta h (cD'', t) in
     let s' = cnormApxSpine cD delta s (cD'', t) in
     Apx.LF.Root (loc, h', s')

  | Apx.LF.Tuple (loc, tuple) ->
     Apx.LF.Tuple(loc, cnormApxTuple cD delta tuple (cD'', t))

  | Apx.LF.Ann (loc, m', a) ->
     Apx.LF.Ann (loc, cnormApxTerm cD delta m' (cD'', t), a)

  | Apx.LF.LFHole _ ->
     m

and cnormApxTuple cD delta tuple (cD'', t) =
  match tuple with
  | Apx.LF.Last m -> Apx.LF.Last (cnormApxTerm cD delta m (cD'' , t))
  | Apx.LF.Cons (m, tuple) ->
     Apx.LF.Cons
       ( cnormApxTerm cD delta m (cD'' , t)
       , cnormApxTuple cD delta tuple (cD'', t)
       )

and cnormApxObj cD l_delta offset t =
  let rec drop t l_delta =
    match (l_delta, t) with
    | (0, t) -> t
    | (k, Int.LF.MDot(_ , t')) -> drop t' (k - 1)
  in
  if offset > l_delta
  then
    begin
      let offset' = (offset - l_delta) in
      match Substitution.LF.applyMSub offset t with
      | Int.LF.MV u -> Apx.LF.Offset u
      | Int.LF.ClObj (_, clobj) ->
         let (u, mtyp) = Whnf.mctxLookup cD offset' in
         dprintf
           begin fun p ->
           p.fmt "[cnormApxObj] @[<v>instantiated with reconstructed object\
                  @,%a : @[%a@]\
                  @,from index %d = %d (offset) - %d (l_delta) in the msub@]"
             Id.print u
             P.(fmt_ppr_cmp_meta_typ cD) mtyp
             offset'
             offset
             l_delta
           end;
         let t' = drop t l_delta in
         let mtyp' = Whnf.cnormMTyp (mtyp, t')in
         Apx.LF.MInst (clobj, mtyp')
    end
  else
    Apx.LF.Offset offset

and cnormApxCVar' cD l_delta cv t =
  match cv with
  | Apx.LF.Offset offset ->
     cnormApxObj cD l_delta offset t
  | Apx.LF.MInst (clobj, mtyp) ->
     Apx.LF.MInst
       ( Whnf.cnormClObj clobj t
       , Whnf.cnormMTyp (mtyp, t)
       )

and cnormApxCVar cD delta cv (cD'', t) =
  cnormApxCVar' cD (lengthApxMCtx delta) cv t

and cnormApxHead cD delta h (cD'', t) =
  match h with
  | Apx.LF.MVar (cv, s) ->
     Apx.LF.MVar
       ( cnormApxCVar cD delta cv (cD'', t)
       , cnormApxSubOpt cD delta s (cD'', t)
       )

  | Apx.LF.PVar (cv, s) ->
     Apx.LF.PVar
       ( cnormApxCVar cD delta cv (cD'', t)
       , cnormApxSubOpt cD delta s (cD'', t)
       )

  | Apx.LF.Proj (pv, j) ->
     Apx.LF.Proj (cnormApxHead cD delta pv (cD'', t), j)

  | Apx.LF.FMVar(u, s) ->
     Apx.LF.FMVar(u, cnormApxSubOpt cD delta s (cD'', t))

  | Apx.LF.FPVar(u, s) ->
     Apx.LF.FPVar(u, cnormApxSubOpt cD delta s (cD'', t))

  | _ -> h

and cnormApxSubOpt cD delta s (cD'', t) =
  Option.(s $> fun s -> cnormApxSub cD delta s (cD'', t))

and cnormApxSub cD delta (s : Apx.LF.sub) (cD'', t) =
  match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id -> s

  | Apx.LF.Dot (Apx.LF.Head h, s) ->
     let h' = cnormApxHead cD delta h (cD'', t) in
     let s' = cnormApxSub cD delta s (cD'', t) in
     Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) ->
     let m' = cnormApxTerm cD delta m (cD'', t) in
     let s' = cnormApxSub cD delta s (cD'', t) in
     Apx.LF.Dot (Apx.LF.Obj m', s')

  | Apx.LF.SVar (cv, sigma) ->
     let sigma' = cnormApxSubOpt cD delta sigma (cD'', t) in
     Apx.LF.SVar (cnormApxCVar cD delta cv (cD'', t), sigma')

  | Apx.LF.FSVar (s, sigma) ->
     let sigma' = cnormApxSubOpt cD delta sigma (cD'', t) in
     Apx.LF.FSVar (s, sigma')

and cnormApxSpine cD delta s (cD'', t) =
  match s with
  | Apx.LF.Nil -> s
  | Apx.LF.App (m, s) ->
     let s' = cnormApxSpine cD delta s (cD'', t) in
     let m' = cnormApxTerm cD delta m (cD'', t) in
     Apx.LF.App (m' , s')

let rec cnormApxTyp cD delta a (cD'', t) =
  match a with
  | Apx.LF.Atom (loc, c, spine) ->
     Apx.LF.Atom (loc, c, cnormApxSpine cD delta spine (cD'', t))

  | Apx.LF.PiTyp ((t_decl, dep), a) ->
     let t_decl' = cnormApxTypDecl cD delta t_decl (cD'', t) in
     let a' = cnormApxTyp cD delta a (cD'', t) in
     Apx.LF.PiTyp ((t_decl', dep), a')

  | Apx.LF.Sigma typ_rec ->
     let typ_rec' = cnormApxTypRec cD delta typ_rec (cD'', t) in
     Apx.LF.Sigma typ_rec'

and cnormApxTypDecl cD delta t_decl cDt =
  match t_decl with
  | Apx.LF.TypDecl (x, a) ->
     Apx.LF.TypDecl(x, cnormApxTyp cD delta a cDt)

  | Apx.LF.TypDeclOpt x -> Apx.LF.TypDeclOpt x

and cnormApxTypRec cD delta t_rec (cD'', t) =
  match t_rec with
  | Apx.LF.SigmaLast(n, a) -> Apx.LF.SigmaLast (n, cnormApxTyp cD delta a (cD'', t))
  | Apx.LF.SigmaElem (x, a, t_rec) ->
     let a' = cnormApxTyp cD delta a (cD'', t) in
     let t_rec' = cnormApxTypRec cD delta t_rec (cD'', t) in
     Apx.LF.SigmaElem (x, a', t_rec')

let rec cnormApxDCtx loc cD delta psi ((_ , t) as cDt) =
  match psi with
  | Apx.LF.CtxHole -> Apx.LF.CtxHole
  | Apx.LF.Null -> psi
  | Apx.LF.CtxVar (Apx.LF.CtxOffset offset) ->
     let l_delta = lengthApxMCtx delta in
     dprint (fun () -> "[cnormApxDCtx] CtxOffset = " ^ string_of_int offset ^ "\n");
     (* let offset' = (offset - l_delta) in *)
     if offset > l_delta
     then
       begin match Substitution.LF.applyMSub offset t with
       | Int.LF.CObj (Int.LF.CtxVar (Int.LF.CtxOffset psi0)) ->
          Apx.LF.CtxVar (Apx.LF.CtxOffset psi0)
       | Int.LF.CObj Int.LF.Null ->
          Apx.LF.Null
       | Int.LF.CObj (Int.LF.DDec _) ->
          raise (Error (loc, CtxOverGeneral))
       (* Apx.LF.CtxVar (Apx.LF.CInst cPsi) *)
       | Int.LF.MV offset' -> Apx.LF.CtxVar (Apx.LF.CtxOffset offset')
       end
     else psi

  | Apx.LF.CtxVar (Apx.LF.CtxName x) -> psi

  | Apx.LF.DDec (psi, t_decl) ->
     let psi' = cnormApxDCtx loc cD delta psi cDt in
     let t_decl' = cnormApxTypDecl cD delta t_decl cDt in
     Apx.LF.DDec (psi', t_decl')


let rec cnormApxExp cD delta e (cD'', t) =
  match e with
  | Apx.Comp.Syn (loc, i) -> Apx.Comp.Syn (loc, cnormApxExp' cD delta i (cD'', t))
  | Apx.Comp.Fn (loc, f, e) ->
     Apx.Comp.Fn (loc, f, cnormApxExp cD delta e (cD'', t))
  | Apx.Comp.Fun (loc, fbr) ->
     Apx.Comp.Fun (loc, cnormApxFBranches cD delta fbr (cD'', t))
  | Apx.Comp.MLam (loc, u, e) ->
     dprint (fun () -> "cnormApxExp -- MLam (or could be PLam)");
     let e' =
       cnormApxExp cD (Apx.LF.Dec(delta, Apx.LF.DeclOpt u)) e
         (Int.LF.Dec (cD'', Int.LF.DeclOpt (u, `explicit)), Whnf.mvar_dot1 t)
     in
     Apx.Comp.MLam (loc, u, e')

  | Apx.Comp.Pair (loc, e1, e2) ->
     let e1' = cnormApxExp cD delta e1 (cD'', t) in
     let e2' = cnormApxExp cD delta e2 (cD'', t) in
     Apx.Comp.Pair (loc, e1', e2')

  | Apx.Comp.LetPair (loc, i, (x,y, e)) ->
     let i' = cnormApxExp' cD delta i (cD'', t) in
     let e' = cnormApxExp cD delta e (cD'', t) in
     Apx.Comp.LetPair (loc, i', (x,y, e'))

  | Apx.Comp.Let (loc, i, (x, e)) ->
     let i' = cnormApxExp' cD delta i (cD'', t) in
     let e' = cnormApxExp cD delta e (cD'', t) in
     Apx.Comp.Let (loc, i', (x, e'))

  | Apx.Comp.Box (loc, m) ->
     dprint (fun () -> "[cnormApxExp] BOX");
     let m' = cnormApxMetaObj cD delta m (cD'', t) in
     Apx.Comp.Box (loc, m')

  | Apx.Comp.Impossible (loc, i) ->
     let i' = cnormApxExp' cD delta i (cD'', t) in
     Apx.Comp.Impossible (loc, i')

  | Apx.Comp.Case (loc, prag, i, branch) ->
     dprint (fun () -> "[cnormApxExp] Case Scrutinee ... ");
     dprintf
       begin fun p ->
       p.fmt "[cnormApxExp] cD = %a"
         (P.fmt_ppr_lf_mctx P.l0) cD
       end;
     let e' = cnormApxExp' cD delta i (cD'', t) in
     dprint (fun () -> "[cnormApxExp] Case Scrutinee done");
     let bs' = cnormApxBranches cD delta branch (cD'', t) in
     dprint (fun () -> "[cnormApxExp] Case Body done ");
     let c = Apx.Comp.Case (loc, prag, e', bs') in
     dprint (fun () -> "[cnormApxExp] Case done");
     c

  | Apx.Comp.Hole (loc, name) -> Apx.Comp.Hole (loc, name)

  | Apx.Comp.BoxHole loc -> Apx.Comp.BoxHole loc

and cnormApxExp' cD delta i cDt =
  match i with
  | Apx.Comp.Var _ -> i
  | Apx.Comp.DataConst _ -> i
  | Apx.Comp.Obs (loc, e, obs) ->
     let e' = cnormApxExp cD delta e cDt in
     Apx.Comp.Obs (loc, e', obs)
  | Apx.Comp.Const _ -> i
  | Apx.Comp.PairVal (loc, i1, i2) ->
     let i1' = cnormApxExp' cD delta i1 cDt in
     let i2' = cnormApxExp' cD delta i2 cDt in
     Apx.Comp.PairVal (loc, i1', i2')

  | Apx.Comp.Apply (loc, i, e) ->
     let i' = cnormApxExp' cD delta i cDt in
     let e' = cnormApxExp cD delta e cDt in
     Apx.Comp.Apply (loc, i', e')

  | Apx.Comp.BoxVal (loc, mobj) ->
     let mobj' = cnormApxMetaObj cD delta mobj cDt in
     Apx.Comp.BoxVal (loc, mobj')

and cnormApxMetaObj cD delta (loc,mobj) cDt =
  ( loc
  , match mobj with
    | Apx.Comp.ClObj (psi, sigma) ->
       let psi' = cnormApxDCtx loc cD delta psi cDt in
       let sigma' = cnormApxSub cD delta sigma cDt in
       Apx.Comp.ClObj (psi', sigma')

    | Apx.Comp.CObj psi -> Apx.Comp.CObj (cnormApxDCtx loc cD delta psi cDt)
  )

and cnormApxBranches cD delta branches cDt =
  List.map (fun b -> cnormApxBranch cD delta b cDt) branches

and cnormApxBranch cD delta b (cD'', t) =
  let rec mvar_dot_apx t =
    function
    | Apx.LF.Empty -> t
    | Apx.LF.Dec (delta', _) ->
       mvar_dot_apx (Whnf.mvar_dot1 t) delta'
  in

  let rec append delta1 =
    function
    | Apx.LF.Empty -> delta1
    | Apx.LF.Dec (delta2', dec) ->
       let delta1' = append delta1 delta2' in
       Apx.LF.Dec (delta1', dec)
  in

  let rec append_mctx cD'' =
    function
    | Apx.LF.Empty -> cD''
    | Apx.LF.Dec (delta2', Apx.LF.Decl(x, _, dep)) ->
       let cD1'' = append_mctx cD'' delta2' in
       Int.LF.Dec (cD1'', Int.LF.DeclOpt (x, Int.LF.Depend.to_plicity dep))
  in

  match b with
  | Apx.Comp.Branch (loc, delta', Apx.Comp.PatMetaObj (loc', mO), e) ->
     let e' =
       cnormApxExp cD (append delta delta') e
         (append_mctx cD'' delta', mvar_dot_apx t delta')
     in
     Apx.Comp.Branch (loc, delta', Apx.Comp.PatMetaObj (loc', mO), e')

  | Apx.Comp.Branch (loc, delta', pat, e) ->
     let e' =
       cnormApxExp cD (append delta delta') e
         (append_mctx cD'' delta', mvar_dot_apx t delta')
     in
     Apx.Comp.Branch (loc, delta', pat, e')

and cnormApxFBranches cD delta fbr (cD'', t) =
  match fbr with
  | Apx.Comp.NilFBranch loc -> fbr
  | Apx.Comp.ConsFBranch (loc, (patS, e), fbr') ->
     let e' = cnormApxExp cD delta e (cD'', t) in
     Apx.Comp.ConsFBranch (loc, (patS, e'), cnormApxFBranches cD delta fbr' (cD'', t))

(* ******************************************************************* *)
(* Collect FMVars and FPVars in a given LF object                      *)

let rec collectApxTerm fMVs =
  function
  | Apx.LF.Lam (_, _, m') -> collectApxTerm fMVs m'

  | Apx.LF.Root (_, h, s) ->
     let fMVs' = collectApxHead fMVs h in
     collectApxSpine fMVs' s

  | Apx.LF.Tuple (_, tuple) ->
     collectApxTuple fMVs tuple

  | Apx.LF.LFHole _ -> fMVs

and collectApxTuple fMVs =
  function
  | Apx.LF.Last m -> collectApxTerm fMVs m
  | Apx.LF.Cons (m, tuple) ->
     let fMVs' = collectApxTerm fMVs m in
     collectApxTuple fMVs' tuple

and collectApxHead fMVs =
  function
  | Apx.LF.FPVar (p, s) ->
     collectApxSubOpt (p :: fMVs) s

  | Apx.LF.FMVar (u, s) ->
     collectApxSubOpt (u :: fMVs) s

  | Apx.LF.MVar (Apx.LF.Offset _, s) ->
     collectApxSubOpt fMVs s

  | Apx.LF.PVar (Apx.LF.Offset _, s) ->
     collectApxSubOpt fMVs s

  | Apx.LF.Proj (h, _) ->
     collectApxHead fMVs h

  | _ -> fMVs

and collectApxSubOpt fMVs =
  function
  | Some s -> collectApxSub fMVs s
  | None -> fMVs

and collectApxSub fMVs =
  function
  | Apx.LF.EmptySub -> fMVs
  | Apx.LF.Id -> fMVs
  | Apx.LF.Dot (Apx.LF.Head h, s) ->
     let fMVs' = collectApxHead fMVs h in
     collectApxSub fMVs' s

  | Apx.LF.Dot (Apx.LF.Obj m, s) ->
     let fMVs' = collectApxTerm fMVs m in
     collectApxSub fMVs' s
  | Apx.LF.SVar (i,s) ->
     collectApxSubOpt fMVs s
  | Apx.LF.FSVar (n,s) ->
     collectApxSubOpt (n::fMVs) s

and collectApxSpine fMVs =
  function
  | Apx.LF.Nil -> fMVs
  | Apx.LF.App (m, s) ->
     let fMVs' = collectApxSpine fMVs s in
     collectApxTerm fMVs' m

and collectApxTyp fMVs =
  function
  | Apx.LF.Atom (_, _, spine) -> collectApxSpine fMVs spine
  | Apx.LF.PiTyp ((tdecl, _), a) ->
     let fMVs' = collectApxTypDecl fMVs tdecl in
     collectApxTyp fMVs' a
  | Apx.LF.Sigma t_rec -> collectApxTypRec fMVs t_rec

and collectApxTypRec fMVs =
  function
  | Apx.LF.SigmaLast(_, a) -> collectApxTyp fMVs a
  | Apx.LF.SigmaElem (_, a, t_rec) ->
     let fMVs' = collectApxTyp fMVs a in
     collectApxTypRec fMVs' t_rec

and collectApxTypDecl fMVs (Apx.LF.TypDecl (_, a))=
  collectApxTyp fMVs a

and collectApxDCtx fMVs =
  function
  | Apx.LF.CtxHole -> fMVs
  | Apx.LF.Null -> fMVs
  | Apx.LF.CtxVar (Apx.LF.CtxName psi) -> (psi :: fMVs)
  | Apx.LF.CtxVar (Apx.LF.CtxOffset _) -> fMVs
  | Apx.LF.DDec (c_psi', t_decl) ->
     let fMVs' = collectApxDCtx fMVs c_psi' in
     collectApxTypDecl fMVs' t_decl

and collectApxHat fMVs =
  function
  | (None, _) -> fMVs
  | (Some (Int.LF.CtxName psi), _) -> psi :: fMVs
  | (Some _, _) -> fMVs


and collectApxMCtx fMVs =
  function
  | Apx.LF.Empty -> fMVs
  | Apx.LF.Dec (c_mctx', ct_decl) ->
     let fMVs' = collectApxMCtx fMVs c_mctx' in
     collectApxCTypDecl fMVs' ct_decl

and collectApxCTypDecl fMVs =
  function
  | Apx.LF.Decl(_, Apx.LF.ClTyp (Apx.LF.MTyp a, c_psi), _)
    | Apx.LF.Decl(_, Apx.LF.ClTyp (Apx.LF.PTyp a, c_psi), _) ->
     let fMVs' = collectApxDCtx fMVs c_psi in
     collectApxTyp fMVs' a
  | Apx.LF.Decl(_, Apx.LF.ClTyp (Apx.LF.STyp (_, c_phi), c_psi), _) ->
     let fMVs' = collectApxDCtx fMVs c_psi in
     collectApxDCtx fMVs' c_phi
  | Apx.LF.Decl(_, Apx.LF.CTyp _, _) -> fMVs

and collectApxMetaObj fMVs (_loc, mO) =
  match mO with
  | Apx.Comp.CObj (cPsi) ->
     collectApxDCtx fMVs cPsi
  | Apx.Comp.ClObj (psi, sub) ->
     let fMVh = collectApxDCtx fMVs psi in
     collectApxSub fMVh sub

and collectApxMetaSpine fMVs =
  function
  | Apx.Comp.MetaNil -> fMVs
  | Apx.Comp.MetaApp (mO, mS) ->
     let fMVs1 = collectApxMetaObj fMVs mO in
     collectApxMetaSpine fMVs1 mS

let rec collectApxTyp fMVd =
  function
  | Apx.LF.Atom (loc, c, tS) ->
     collectApxSpine fMVd tS
  | Apx.LF.PiTyp ((Apx.LF.TypDecl (x, tA),_ ), tB) ->
     let fMVd1 = collectApxTyp fMVd tA in
     collectApxTyp fMVd1 tB
  | Apx.LF.Sigma trec ->
     collectApxTypRec fMVd trec

and collectApxTypRec fMVd =
  function
  | Apx.LF.SigmaLast(n, tA) -> collectApxTyp fMVd tA
  | Apx.LF.SigmaElem (_, tA, trec) ->
     let fMVd1 = collectApxTyp fMVd tA in
     collectApxTypRec fMVd1 trec

let collectApxCDecl fMVd =
  function
  | Apx.LF.Decl(_, Apx.LF.ClTyp (Apx.LF.STyp(_, cPhi), cPsi), _) ->
     let fMVd1 = collectApxDCtx fMVd cPsi in
     collectApxDCtx fMVd1 cPhi
  | Apx.LF.Decl(_, Apx.LF.ClTyp (Apx.LF.MTyp tA, cPsi), _)
    | Apx.LF.Decl(_, Apx.LF.ClTyp (Apx.LF.PTyp tA, cPsi), _) ->
     let fMVd1 = collectApxDCtx fMVd cPsi in
     collectApxTyp fMVd1 tA
  | Apx.LF.Decl (_,Apx.LF.CTyp _,_) -> fMVd

let rec collectApxCompTyp fMVd =
  function
  | Apx.Comp.TypArr (_, tau1, tau2) ->
     let fMVd1 = collectApxCompTyp fMVd tau1 in
     collectApxCompTyp fMVd1 tau2
  | Apx.Comp.TypCross (_, tau1, tau2) ->
     let fMVd1 = collectApxCompTyp fMVd tau1 in
     collectApxCompTyp fMVd1 tau2
  | Apx.Comp.TypPiBox (_, cdecl, tau) ->
     let fMVd1 = collectApxCDecl fMVd cdecl in
     collectApxCompTyp fMVd1 tau
  | Apx.Comp.TypBox (loc, (loc',Apx.LF.ClTyp(Apx.LF.MTyp tA, cPsi)))
    | Apx.Comp.TypBox (loc, (loc',Apx.LF.ClTyp(Apx.LF.PTyp tA, cPsi))) ->
     let fMVd1 = collectApxDCtx fMVd cPsi in
     collectApxTyp fMVd1 tA
  | Apx.Comp.TypBox (loc, (loc',Apx.LF.ClTyp(Apx.LF.STyp (_ , cPhi), cPsi))) ->
     let fMVd1 = collectApxDCtx fMVd cPsi in
     collectApxDCtx fMVd1 cPhi
  | Apx.Comp.TypBase (_loc, _c, mS) ->
     collectApxMetaSpine fMVd mS

let rec collectApxPattern fMVd =
  function
  | Apx.Comp.PatMetaObj (loc, mO) ->
     collectApxMetaObj fMVd mO
  | Apx.Comp.PatConst (loc, c, pat_spine) ->
     collectApxPatSpine fMVd pat_spine
  | Apx.Comp.PatVar (loc, n, offset) -> fMVd
  | Apx.Comp.PatPair (loc, pat1, pat2) ->
     let fMVs1 = collectApxPattern fMVd pat1 in
     collectApxPattern fMVs1 pat2
  | Apx.Comp.PatAnn (loc, pat, tau) ->
     let fMVd1 = collectApxCompTyp fMVd tau in
     collectApxPattern fMVd1 pat

and collectApxPatSpine fMVd =
  function
  | Apx.Comp.PatNil _ -> fMVd
  | Apx.Comp.PatApp (loc, pat, pat_spine) ->
     let fMVs1 = collectApxPattern fMVd pat in
     collectApxPatSpine fMVs1 pat_spine
  | Apx.Comp.PatObs (loc, cid, pat_spine) ->
     collectApxPatSpine fMVd pat_spine

(* Replace FMVars with appropriate de Bruijn index
 * If a FMVar (of FPVar) occurs in fMVs do not replace it
 * since it is bound in some inner branch of a case-expression
 *
 *)
let rec fmvApxTerm fMVs cD d_param =
  function
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam (loc, x, fmvApxTerm fMVs cD d_param m')

  | Apx.LF.Root (loc, h, s) ->
     let h' = fmvApxHead fMVs cD d_param h in
     let s' = fmvApxSpine fMVs cD d_param s in
     Apx.LF.Root (loc, h', s')

  | Apx.LF.Tuple (loc, tuple) ->
     Apx.LF.Tuple(loc, fmvApxTuple fMVs cD d_param tuple)

  | Apx.LF.Ann (loc, m', a) ->
     Apx.LF.Ann (loc, fmvApxTerm fMVs cD d_param m', a)

  | Apx.LF.LFHole _ as m -> m

and fmvApxTuple fMVs cD d_param =
  function
  | Apx.LF.Last m -> Apx.LF.Last (fmvApxTerm fMVs cD d_param m)
  | Apx.LF.Cons (m, tuple) ->
     Apx.LF.Cons
       ( fmvApxTerm fMVs cD d_param m
       , fmvApxTuple fMVs cD d_param tuple
       )

and fmvApxCvar' cD (l_cd1, l_deltak) i =
  let rec mvar_dot t =
    function
    | 0 -> t
    | l_delta ->
       mvar_dot (Whnf.mvar_dot1 t) (l_delta - 1)
  in
  let r = mvar_dot (Int.LF.MShift l_cd1) (l_deltak) in
  cnormApxCVar' cD l_deltak i r

and fmvApxCvar fMVs cD (l_cd1, l_delta, k) i =
  fmvApxCvar' cD (l_cd1, l_delta + k) i

(* TODO: Refactor this function *)
and fmvApxHead fMVs cD ((_, _, k) as d_param) =
  function
  (* free meta-variables / parameter variables *)
  | Apx.LF.FPVar (p, s) ->
     let s' = fmvApxSubOpt fMVs cD d_param s in
     if List.exists (Id.equals p) fMVs then
       Apx.LF.FPVar (p, s')
     else
       let (offset, _) = Whnf.mctxMVarPos cD p in
       Apx.LF.PVar (Apx.LF.Offset (offset + k), s')

  | Apx.LF.FMVar (u, s) ->
     let s' = fmvApxSubOpt fMVs cD d_param s in
     if List.exists (Id.equals u) fMVs
     then Apx.LF.FMVar (u, s')
     else
       begin
         let (offset, _) = Whnf.mctxMVarPos cD u in
         dprintf
           begin fun p ->
           p.fmt "[fmvApxHead] FMVar %a --> index %d"
             Id.print u
             offset
           end;
         Apx.LF.MVar (Apx.LF.Offset (offset + k), s')
       end

  | Apx.LF.Proj (pv, j) -> Apx.LF.Proj(fmvApxHead fMVs cD d_param pv, j)

  (* bound meta-variables / parameters *)
  | Apx.LF.MVar (i, s) ->
     let s' = fmvApxSubOpt fMVs cD d_param s in
     Apx.LF.MVar (fmvApxCvar fMVs cD d_param i, s')

  | Apx.LF.PVar (i, s) ->
     let s' = fmvApxSubOpt fMVs cD d_param s in
     Apx.LF.PVar (fmvApxCvar fMVs cD d_param i, s')

  | h -> h

and fmvApxSubOpt fMVs cD d_param s =
  Option.(s $> fmvApxSub fMVs cD d_param)

and fmvApxSub fMVs cD ((_, _, k) as d_param) =
  function
  | Apx.LF.EmptySub -> Apx.LF.EmptySub
  | Apx.LF.Id -> Apx.LF.Id

  | Apx.LF.Dot (Apx.LF.Head h, s) ->
     let h' = fmvApxHead fMVs cD d_param h in
     let s' = fmvApxSub fMVs cD d_param s in
     Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) ->
     let m' = fmvApxTerm fMVs cD d_param m in
     let s' = fmvApxSub fMVs cD d_param s in
     Apx.LF.Dot (Apx.LF.Obj m', s')

  | Apx.LF.FSVar (u, sigma) ->
     let sigma' = fmvApxSubOpt fMVs cD d_param sigma in
     if List.exists (Id.equals u) fMVs
     then Apx.LF.FSVar (u, sigma')
     else
       begin
         let (offset, _) = Whnf.mctxMVarPos cD u in
         (* cPsi |- s : cPhi *)
         Apx.LF.SVar (Apx.LF.Offset (offset + k), sigma')
       end

  | Apx.LF.SVar (i, sigma) ->
     let sigma' = fmvApxSubOpt fMVs cD d_param sigma in
     Apx.LF.SVar (fmvApxCvar fMVs cD d_param i, sigma')

and fmvApxSpine fMVs cD d_param =
  function
  | Apx.LF.Nil -> Apx.LF.Nil
  | Apx.LF.App (m, s) ->
     let s' = fmvApxSpine fMVs cD d_param s in
     let m' = fmvApxTerm fMVs cD d_param m in
     Apx.LF.App (m' , s')

let rec fmvApxTyp fMVs cD d_param =
  function
  | Apx.LF.Atom (loc, c, spine) ->
     Apx.LF.Atom (loc, c, fmvApxSpine fMVs cD d_param spine)

  | Apx.LF.PiTyp ((t_decl, dep), a) ->
     let t_decl' = fmvApxTypDecl fMVs cD d_param t_decl in
     let a' = fmvApxTyp fMVs cD d_param a in
     Apx.LF.PiTyp ((t_decl', dep), a')

  | Apx.LF.Sigma typ_rec ->
     let typ_rec' = fmvApxTypRec fMVs cD d_param typ_rec in
     Apx.LF.Sigma typ_rec'

and fmvApxTypDecl fMVs cD d_param =
  function
  | Apx.LF.TypDecl (x, a) ->
     Apx.LF.TypDecl(x, fmvApxTyp fMVs cD d_param a)
  | Apx.LF.TypDeclOpt x -> Apx.LF.TypDeclOpt x

and fmvApxTypRec fMVs cD d_param =
  function
  | Apx.LF.SigmaLast (n, a) -> Apx.LF.SigmaLast (n, fmvApxTyp fMVs cD d_param a)
  | Apx.LF.SigmaElem (x, a, t_rec) ->
     let a' = fmvApxTyp fMVs cD d_param a in
     let t_rec' = fmvApxTypRec fMVs cD d_param t_rec in
     Apx.LF.SigmaElem (x, a', t_rec')

let rec fmvApxDCtx loc fMVs cD ((l_cd1, l_delta, k) as d_param) =
  function
  | Apx.LF.CtxHole -> Apx.LF.CtxHole
  | Apx.LF.Null -> Apx.LF.Null
  | Apx.LF.CtxVar (Apx.LF.CtxOffset offset) as psi ->
     if offset > (l_delta + k)
     then Apx.LF.CtxVar (Apx.LF.CtxOffset (offset + l_cd1))
     else psi

  | Apx.LF.CtxVar (Apx.LF.CtxName x) as psi ->
     if List.exists (Id.equals x) fMVs
     then psi
     else
       begin
         try
           let (offset, _w) = Whnf.mctxMVarPos cD x in
           Apx.LF.CtxVar (Apx.LF.CtxOffset (offset + k))
         with
         | Whnf.Fmvar_not_found ->
            throw loc
              (IndexInvariantFailed
                 (fun ppf () ->
                   Format.fprintf ppf "unbound context %s" (Id.render_name x)))
       end

  | Apx.LF.DDec (psi, t_decl) ->
     let psi' = fmvApxDCtx loc fMVs cD d_param psi in
     let t_decl' = fmvApxTypDecl fMVs cD d_param t_decl in
     Apx.LF.DDec (psi', t_decl')

let fmvApxHat loc fMVs cD (l_cd1, l_delta, k) phat =
  match phat with
  | (Some (Int.LF.CtxOffset offset), d) ->
     if offset > (l_delta + k)
     then (Some (Int.LF.CtxOffset (offset + l_cd1)), d)
     else phat
  | (Some (Int.LF.CtxName psi), d) ->
     if List.exists (Id.equals psi) fMVs
     then phat
     else
       begin
         try
           let (offset, _) = Whnf.mctxMVarPos cD psi in
           (Some (Int.LF.CtxOffset (offset + k)), d)
         with
         | Whnf.Fmvar_not_found ->
            throw loc
              (IndexInvariantFailed
                 (fun ppf () ->
                   Format.fprintf ppf "unbound context variable %s" (Id.render_name psi)))
       end
  | _ -> phat

let rec fmvApxExp fMVs cD ((l_cd1, l_delta, k) as d_param) =
  function
  | Apx.Comp.Syn (loc, i) -> Apx.Comp.Syn (loc, fmvApxExp' fMVs cD d_param i)
  | Apx.Comp.Fn (loc, f, e) ->
     Apx.Comp.Fn (loc, f, fmvApxExp fMVs cD d_param e)
  | Apx.Comp.Fun (loc, fbr) ->
     Apx.Comp.Fun (loc, fmvApxFBranches fMVs cD d_param fbr)
  | Apx.Comp.MLam (loc, u, e) ->
     Apx.Comp.MLam (loc, u, fmvApxExp fMVs cD (l_cd1, l_delta, (k + 1)) e)
  | Apx.Comp.Pair (loc, e1, e2) ->
     let e1' = fmvApxExp fMVs cD d_param e1 in
     let e2' = fmvApxExp fMVs cD d_param e2 in
     Apx.Comp.Pair (loc, e1', e2')
  | Apx.Comp.LetPair (loc, i, (x,y, e)) ->
     let i' = fmvApxExp' fMVs cD d_param i in
     let e' = fmvApxExp fMVs cD d_param e in
     Apx.Comp.LetPair (loc, i', (x,y, e'))
  | Apx.Comp.Let (loc, i, (x, e)) ->
     let i' = fmvApxExp' fMVs cD d_param i in
     let e' = fmvApxExp fMVs cD d_param e in
     Apx.Comp.Let (loc, i', (x, e'))

  | Apx.Comp.Box(loc, m) ->
     let m' = fmvApxMetaObj fMVs cD d_param m in
     Apx.Comp.Box (loc, m')

  | Apx.Comp.Impossible (loc, i) ->
     Apx.Comp.Impossible (loc, fmvApxExp' fMVs cD d_param i)

  | Apx.Comp.Case (loc, prag, i, branch) ->
     Apx.Comp.Case (loc, prag, fmvApxExp' fMVs cD d_param i,
                    fmvApxBranches fMVs cD d_param branch)

  | Apx.Comp.Hole (loc, name) -> Apx.Comp.Hole (loc, name)

  | Apx.Comp.BoxHole loc -> Apx.Comp.BoxHole loc

and fmvApxExp' fMVs cD d_param =
  function
  | Apx.Comp.Var _ as i -> i
  | Apx.Comp.DataConst _ as i -> i
  | Apx.Comp.Obs (loc, e, obs) ->
     let e' = fmvApxExp fMVs cD d_param e in
     Apx.Comp.Obs (loc, e', obs)
  | Apx.Comp.Const _ as i -> i
  | Apx.Comp.Apply (loc, i, e) ->
     let i' = fmvApxExp' fMVs cD d_param i in
     let e' = fmvApxExp fMVs cD d_param e in
     Apx.Comp.Apply (loc, i', e')

  | Apx.Comp.BoxVal (loc, mobj) ->
     let mobj' = fmvApxMetaObj fMVs cD d_param mobj in
     Apx.Comp.BoxVal (loc, mobj')

  | Apx.Comp.PairVal (loc, i1, i2) ->
     let i1' = fmvApxExp' fMVs cD d_param i1 in
     let i2' = fmvApxExp' fMVs cD d_param i2 in
     Apx.Comp.PairVal (loc, i1', i2')

and fmvApxMetaObj fMVs cD d_param (loc, mobj) =
  ( loc
  , match mobj with
    | Apx.Comp.ClObj (psi, sigma) ->
       let psi' = fmvApxDCtx loc fMVs cD d_param psi in
       let sigma' = fmvApxSub fMVs cD d_param sigma in
       Apx.Comp.ClObj (psi', sigma')

    | Apx.Comp.CObj psi ->
       Apx.Comp.CObj (fmvApxDCtx loc fMVs cD d_param psi)
  )

and fmvApxBranches fMVs cD d_param branches =
  List.map (fmvApxBranch fMVs cD d_param) branches

and fmvApxBranch fMVs cD (l_cd1, l_delta, k) =
  function
  | Apx.Comp.Branch (loc, delta, Apx.Comp.PatMetaObj (loc', mO), e) ->
     let fMVd = collectApxMCtx [] delta in
     let fMVb = collectApxMetaObj fMVd mO in
     let l = lengthApxMCtx delta in
     let pat = Apx.Comp.PatMetaObj (loc', mO) in
     let e' = fmvApxExp (fMVs @ fMVb) cD (l_cd1, l_delta, (k + l)) e in
     Apx.Comp.Branch (loc, delta, pat, e')

  | Apx.Comp.Branch (loc, delta, pat, e) ->
     let fMVd = collectApxMCtx [] delta in
     let fMVb = collectApxPattern fMVd pat in
     let l = lengthApxMCtx delta in
     let e' = fmvApxExp (fMVs @ fMVb) cD (l_cd1, l_delta, (k + l)) e in
     Apx.Comp.Branch (loc, delta, pat, e')

and fmvApxFBranches fMVs cD d_param =
  function
  | Apx.Comp.NilFBranch _ as fbr -> fbr
  | Apx.Comp.ConsFBranch (loc, (patS, e), fbr') ->
     let fMVs' = collectApxPatSpine fMVs patS in
     Apx.Comp.ConsFBranch
       ( loc
       , (patS, fmvApxExp fMVs' cD d_param e)
       , fmvApxFBranches fMVs cD d_param fbr'
       )
