
open Syntax

(* ********************************************************************************)
(* Pretty printing                                                                *)
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
module RR = Store.Cid.NamedRenderer

let (dprint, _dprnt) = Debug.makeFunctions (Debug.toFlags [11])
(* ********************************************************************************)

(* exception NotImplemented *)

type error =
  | CtxOverGeneral

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | CtxOverGeneral ->
          Format.fprintf ppf
            "context  in the body appears to be more general than the context supplied\n"
                                  ))

(* ********************************************************************************)
let rec lengthApxMCtx cD = match cD with
  | Apx.LF.Empty -> 0
  | Apx.LF.Dec (cD, _) -> 1 + lengthApxMCtx cD



(* -------------------------------------------------------------*)
(* EtaExpansion of approximate terms *)
let rec shiftApxTerm k m = begin match m with
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam(loc, x, shiftApxTerm (k+1) m')
  | Apx.LF.Root (loc, h , spine) ->
      let h' = shiftApxHead k h in
      let spine' = shiftApxSpine k spine in
        Apx.LF.Root(loc, h', spine')
end

and shiftApxHead k h = begin match h with
  | Apx.LF.BVar x -> Apx.LF.BVar (x+k)
  | Apx.LF.FMVar (u, s) -> Apx.LF.FMVar (u, shiftApxSub k s)
  | Apx.LF.FPVar (p, s) -> Apx.LF.FMVar (p, shiftApxSub k s)
  | Apx.LF.MVar (u, s) -> Apx.LF.MVar (u, shiftApxSub k s)
  | _ -> h
end

and shiftApxSpine k spine = begin match spine with
  | Apx.LF.Nil -> spine
  | Apx.LF.App (m, spine') ->
      let spine'' = shiftApxSpine k spine' in
        Apx.LF.App (shiftApxTerm k m, spine'')
end

and shiftApxSub k s = begin match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id _ -> s
  | Apx.LF.Dot(Apx.LF.Head h, s) ->
      let h' = shiftApxHead k h in
      let s' = shiftApxSub k s in
        Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot(Apx.LF.Obj m, s) ->
      let m' = shiftApxTerm k m in
      let s' = shiftApxSub k s in
        Apx.LF.Dot (Apx.LF.Obj m', s')
end


(* ******************************************************************* *)
(* Shift mvars in approximate expression by k *)
(* Apply modal substitution t to approximate term
   where cD1 contains all the free modal variables in m

   cnormApxExp e t  = e'

   if  cD1''      |- t <= cD @ delta  and
       cD @ delta |- e <= apx_exp
   the cD1''  |- |[t]|e <= apx_exp

*)

let rec cnormApxTerm cD delta m (cD'', t) = match m with
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam (loc, x, cnormApxTerm cD delta m' (cD'', t))

  | Apx.LF.Root (loc, h, s) ->
      let h' = cnormApxHead cD delta h (cD'', t) in
      let s' = cnormApxSpine cD delta s (cD'', t) in
        Apx.LF.Root (loc, h', s')
  | Apx.LF.Tuple (loc, tuple) ->
      Apx.LF.Tuple(loc, cnormApxTuple cD delta tuple (cD'', t))

  | Apx.LF.Ann (loc, m', a) ->
    Apx.LF.Ann (loc, cnormApxTerm cD delta m' (cD'', t), a)

and cnormApxTuple cD delta tuple (cD'', t) = match tuple with
  | Apx.LF.Last m -> Apx.LF.Last (cnormApxTerm cD delta m (cD'' , t))
  | Apx.LF.Cons (m, tuple) ->
      Apx.LF.Cons (cnormApxTerm cD delta m (cD'' , t),
                   cnormApxTuple cD delta tuple (cD'', t))

(*
   cD, delta ; cPsi |- h
   cD'' |- t <= cD, delta

*)
and cnormApxHead cD delta h (cD'', t) = match h with
  | Apx.LF.MVar (Apx.LF.Offset offset, s) ->
      let _ = dprint (fun () -> "[cnormApxHead] MVar " ^ (RR.render_cvar cD offset)) in
      let l_delta = lengthApxMCtx delta in
      let offset' = (offset - l_delta)  in
        if offset > l_delta then
          begin match Substitution.LF.applyMSub offset  t with
            | Int.LF.MV u ->
                Apx.LF.MVar (Apx.LF.Offset u, cnormApxSub cD delta s (cD'', t))
            | Int.LF.MObj (_phat, tM) ->
                let (_u, tP, cPhi) = Whnf.mctxMDec cD offset' in
                 (* Bug fix -- drop elements l_delta elements from t -bp, Aug 24, 2009
                    Given cD'' |- t : cD, l_delta
                    produce t' s.t. cD'' |- t' : cD   and t',t_delta = t

                    Must do the same for PVARs
                  *)
(*                let (tP, cPhi) = (Ctxsub.ctxnorm_typ (tP,), Ctxsub.ctxnorm_dctx (cPhi,)) in  *)
                let rec drop t l_delta = match (l_delta, t) with
                  | (0, t) -> t
                  | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in

                let t' = drop t l_delta in
		let _ = dprint (fun () -> "[cnormApxHead] l_delta " ^
				  string_of_int l_delta) in
		let _  = dprint (fun () -> "[cnormApxHead] MVar has type ") in
		let _  = dprint (fun () -> "              " ^
				   P.typToString cD cPhi (tP, Substitution.LF.id) ^ " [ " ^
				   P.dctxToString cD cPhi ^ " ]") in
		let _ = dprint (fun () -> "              tM / u = " ^
				  P.normalToString cD cPhi (tM, Substitution.LF.id)) in
		let _ = dprint (fun () -> "               cD (domain of cPhi) = "
				  ^ P.mctxToString cD) in
		let _ = dprint (fun () -> "[cnormApxHead] t = " ^
				  P.msubToString cD'' t) in
		let _ = dprint (fun () -> "[cnormApxHead] t' = " ^
				  P.msubToString cD'' t') in

                let (tP', cPhi')  = (Whnf.cnormTyp (tP, t'), Whnf.cnormDCtx  (cPhi, t')) in
		let _ = dprint (fun () -> "[cnormApxHead] done") in
                  Apx.LF.MVar (Apx.LF.MInst (tM, tP', cPhi'),
                               cnormApxSub cD delta s (cD'', t))
          end
        else
	  let _ = dprint (fun () -> "[cnormApxTerm] MVar offset = " ^
                  R.render_offset offset ) in
          Apx.LF.MVar (Apx.LF.Offset offset, cnormApxSub cD delta s (cD'', t))

  | Apx.LF.MVar (Apx.LF.MInst (tM, tP, cPhi), s) ->
      let tM' = Whnf.cnorm (tM,t) in
      (* let (tP, cPhi) = (Ctxsub.ctxnorm_typ (tP, cs) , Ctxsub.ctxnorm_dctx   (cPhi, cs)) in  *)
      let _  = dprint (fun () -> "[cnormApxHead] MVar MInst") in
      let (tP', cPhi')  = (Whnf.cnormTyp (tP, t), Whnf.cnormDCtx (cPhi, t)) in

      let s' = cnormApxSub cD delta s (cD'', t) in
        Apx.LF.MVar (Apx.LF.MInst (tM', tP', cPhi'), s')

  | Apx.LF.PVar (Apx.LF.Offset offset, s) ->
      let l_delta = lengthApxMCtx delta in
      let offset' = (offset - l_delta)  in
        if offset > l_delta then
          begin match Substitution.LF.applyMSub offset t with
            | Int.LF.MV offset' ->  Apx.LF.PVar (Apx.LF.Offset offset', cnormApxSub cD delta s (cD'', t))
            | Int.LF.PObj (_phat, h) ->
                let _ = dprint (fun () -> "[cnormApxTerm] ApplyMSub done -- resulted in PObj") in
                let (_ , tP, cPhi) = Whnf.mctxPDec cD offset' in
                  (* Bug fix -- drop elements l_delta elements from t -bp, Aug 24, 2009
                     Given cD'' |- t : cD, l_delta
                     produce t' s.t. cD'' |- t' : cD   and t',t_delta = t
                  *)
                let rec drop t l_delta = match (l_delta, t) with
                  | (0, t) -> t
                  | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in

                let t' = drop t l_delta in
                  Apx.LF.PVar (Apx.LF.PInst (h, Whnf.cnormTyp (tP,t'), Whnf.cnormDCtx (cPhi,t')),
                               cnormApxSub cD delta s (cD'', t))
          end
        else
          Apx.LF.PVar (Apx.LF.Offset offset, cnormApxSub cD delta s (cD'', t))


  | Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s) ->
      let (tA', cPhi')  = (Whnf.cnormTyp (tA, t), Whnf.cnormDCtx (cPhi, t)) in
      let s' = cnormApxSub cD delta s (cD'', t) in
      let h' = begin match h with
               | Int.LF.BVar _ -> h
               | Int.LF.PVar (Int.LF.Offset q, s1) ->
                   begin match Substitution.LF.applyMSub q t with
                     | Int.LF.MV q' ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (Int.LF.Offset q', s1')
                     | Int.LF.PObj (_hat, Int.LF.PVar (Int.LF.Offset q', s2)) ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (Int.LF.Offset q', Substitution.LF.comp s1' s2)
                   end
               end in
        Apx.LF.PVar (Apx.LF.PInst (h', tA', cPhi'), s')

  | Apx.LF.FMVar(u, s) ->
      Apx.LF.FMVar(u, cnormApxSub cD delta s (cD'', t))

  | Apx.LF.FPVar(u, s) ->
      Apx.LF.FPVar(u, cnormApxSub cD delta s (cD'', t))

  | Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset, s), j) ->
      let l_delta = lengthApxMCtx delta in
      let offset' = (offset - l_delta)  in
      let _ = dprint (fun () -> "[cnormApxTerm] Proj (PVar _ ) . " ^ string_of_int j ^ " : offset = " ^ string_of_int offset ) in
      let _ = dprint (fun () -> "[cnormApxTerm] Proj (PVar _ ) . " ^ string_of_int j ^ " : offset' = " ^ string_of_int offset' ) in
      let _ = dprint (fun () -> "[cnormApxTerm] l_delta = " ^ string_of_int l_delta ) in
      let _ = dprint (fun () -> "[cnormApxTerm] t = " ^ P.msubToString cD'' t ^ "\n") in
      let _ = dprint (fun () -> "[cnormApxTerm] (original) cD = " ^ P.mctxToString cD ^ "\n") in
        if offset > l_delta then
          begin match Substitution.LF.applyMSub offset t with
            | Int.LF.MV offset' ->
                Apx.LF.Proj(Apx.LF.PVar (Apx.LF.Offset offset',
                                         cnormApxSub cD delta s (cD'', t)),
                            j)
            | Int.LF.PObj (_phat, h) ->
                let _ = dprint (fun () -> "[cnormApxTerm] Proj - case: ApplyMSub done -- resulted in PObj  ") in

                let _ = dprint (fun () -> "[cnormApxTerm] offset' = " ^ string_of_int offset' ^ "\n") in
                let _ = dprint (fun () -> "[cnormApxTerm] offset = " ^ string_of_int offset ^ "\n") in
                let (_ , tP, cPhi) = Whnf.mctxPDec cD offset' in
                let _ = dprint (fun () -> "[cnormApxTerm] tP = " ^ P.typToString cD cPhi (tP, Substitution.LF.id) ^ "\n") in
                  (* Bug fix -- drop elements l_delta elements from t -bp, Aug 24, 2009
                     Given cD'' |- t : cD, l_delta
                     produce t' s.t. cD'' |- t' : cD   and t',t_delta = t
                  *)
                let rec drop t l_delta = match (l_delta, t) with
                  | (0, t) -> t
                  | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in

                let t' = drop t l_delta in
                  Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h, Whnf.cnormTyp (tP,t'), Whnf.cnormDCtx (cPhi,t')),
                                           cnormApxSub cD delta s (cD'', t)),
                              j)

            | Int.LF.MObj (phat, tM) ->
                (dprint (fun () -> "[cnormApxTerm] MObj :" ^
                           P.normalToString cD (Context.hatToDCtx phat) (tM, Substitution.LF.id) ^ "\n") ;
                 raise (Error.Violation "MObj found -- expected PObj"))
          end
        else
          Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset, cnormApxSub cD delta s (cD'', t)), j)

  | Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s), j) ->
      let (tA', cPhi')  = (Whnf.cnormTyp (tA, t), Whnf.cnormDCtx (cPhi, t)) in
      let s' = cnormApxSub cD delta s (cD'', t) in
      let h' = begin match h with
               | Int.LF.BVar _ -> h
               | Int.LF.PVar (Int.LF.Offset q, s1) ->
                   begin match Substitution.LF.applyMSub q t with
                     | Int.LF.MV q' ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (Int.LF.Offset q', s1')
                     | Int.LF.PObj (_phat, Int.LF.PVar (p,s')) ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (p, s1')
                   end
               | Int.LF.PVar (Int.LF.PInst (_, {contents = _ }, _cPsi, _tA, _ ) as p ,s1) ->
                   Int.LF.PVar (p, Whnf.cnormSub (s1, t))

               end in
        Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h', tA', cPhi'), s'), j)

  | _ -> h

and cnormApxSub cD delta s (cD'', t) = match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id ctx   ->
      begin match (ctx, t) with
          (* to be fixed -bp *)
        | Apx.LF.CtxOffset 1 , Int.LF.MDot (Int.LF.CObj(Int.LF.Null), _ ) -> Apx.LF.EmptySub
        | _ -> s
      end

  | Apx.LF.Dot (Apx.LF.Head h, s) ->
      let h' = cnormApxHead cD delta h (cD'', t) in
      let s' = cnormApxSub cD delta s (cD'', t) in
        Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) ->
      let m' = cnormApxTerm cD delta m (cD'', t) in
      let s' = cnormApxSub cD delta s (cD'', t) in
        Apx.LF.Dot (Apx.LF.Obj m', s')


and cnormApxSpine cD delta s (cD'', t) = match s with
  | Apx.LF.Nil -> s
  | Apx.LF.App (m, s) ->
      let s' = cnormApxSpine cD delta s (cD'', t) in
      let m' = cnormApxTerm cD delta m (cD'', t) in
        Apx.LF.App (m' , s')

let rec cnormApxTyp cD delta a (cD'', t) = match a with
  | Apx.LF.Atom (loc, c, spine) ->
      Apx.LF.Atom (loc, c, cnormApxSpine cD delta spine (cD'', t))

  | Apx.LF.PiTyp ((t_decl, dep), a) ->
      let t_decl' = cnormApxTypDecl cD delta t_decl (cD'', t) in
      let a' = cnormApxTyp cD delta a (cD'', t) in
        Apx.LF.PiTyp ((t_decl', dep), a')

  | Apx.LF.Sigma typ_rec ->
      let typ_rec' = cnormApxTypRec cD delta typ_rec (cD'', t) in
        Apx.LF.Sigma typ_rec'

and cnormApxTypDecl cD delta t_decl cDt = match t_decl with
  | Apx.LF.TypDecl (x, a) ->
      Apx.LF.TypDecl(x, cnormApxTyp cD delta a cDt)

and cnormApxTypRec cD delta t_rec (cD'', t) = match t_rec with
  | Apx.LF.SigmaLast a -> Apx.LF.SigmaLast (cnormApxTyp cD delta a (cD'', t))
  | Apx.LF.SigmaElem (x, a, t_rec) ->
      let a' = cnormApxTyp cD delta a (cD'', t) in
      let t_rec' = cnormApxTypRec cD delta t_rec (cD'', t) in
        Apx.LF.SigmaElem (x, a', t_rec')

(* NOTE THERE IS A BUG IN OCAML: we are allowed to name _ cD !*)
let rec cnormApxDCtx loc cD delta psi ((_ , t) as cDt) = match psi with
  | Apx.LF.Null -> psi
  | Apx.LF.CtxVar (Apx.LF.CtxOffset offset) ->
      let l_delta = lengthApxMCtx delta in
      let _ = dprint (fun () -> "[cnormApxDCtx] CtxOffset = " ^ string_of_int offset ^ "\n") in
      (* let offset' = (offset - l_delta)  in *)
        if offset > l_delta then
          begin match Substitution.LF.applyMSub offset t with
            | Int.LF.CObj (Int.LF.CtxVar (Int.LF.CtxOffset psi0)) ->
                Apx.LF.CtxVar (Apx.LF.CtxOffset psi0)
            | Int.LF.CObj(Int.LF.Null) ->
                Apx.LF.Null
            | Int.LF.CObj(Int.LF.DDec _ ) ->
                raise (Error (loc, CtxOverGeneral))
                  (* Apx.LF.CtxVar (Apx.LF.CInst cPsi) *)
	    | Int.LF.MV offset' -> Apx.LF.CtxVar (Apx.LF.CtxOffset  offset')
          end
        else
          psi

  | Apx.LF.CtxVar (Apx.LF.CtxName x) -> psi

  | Apx.LF.DDec (psi, t_decl) ->
      let psi' = cnormApxDCtx loc cD delta psi cDt in
      let t_decl' = cnormApxTypDecl cD delta t_decl cDt in
        Apx.LF.DDec (psi', t_decl')


let rec cnormApxExp cD delta e (cD'', t) = match e with
  | Apx.Comp.Syn (loc, i)       -> Apx.Comp.Syn (loc, cnormApxExp' cD delta i (cD'', t))
  | Apx.Comp.Fun (loc, f, e)    ->
      (dprint (fun () -> "[cnormApxExp] Fun ");
      Apx.Comp.Fun (loc, f, cnormApxExp cD delta e (cD'', t)))
  | Apx.Comp.CtxFun (loc, g, e) ->
      (dprint (fun () -> "cnormApxExp -- CtxFun ") ;
      Apx.Comp.CtxFun (loc, g, cnormApxExp cD (Apx.LF.Dec(delta, Apx.LF.CDeclOpt g)) e
                         (Int.LF.Dec (cD'', Int.LF.CDeclOpt g), Whnf.mvar_dot1 t))
      )
  | Apx.Comp.MLam (loc, u, e)   ->
      (dprint (fun () -> "cnormApxExp -- MLam (or could be PLam)") ;
      Apx.Comp.MLam (loc, u, cnormApxExp cD (Apx.LF.Dec(delta, Apx.LF.MDeclOpt u)) e
                       (Int.LF.Dec (cD'', Int.LF.MDeclOpt u), Whnf.mvar_dot1 t)))

  | Apx.Comp.Pair (loc, e1, e2) ->
      let e1' = cnormApxExp cD delta e1 (cD'', t) in
      let e2' = cnormApxExp cD delta e2 (cD'', t) in
        Apx.Comp.Pair (loc, e1', e2')

  | Apx.Comp.LetPair (loc, i, (x,y, e)) ->
      let i' = cnormApxExp' cD delta i (cD'', t) in
      let e' = cnormApxExp  cD delta e (cD'', t) in
        Apx.Comp.LetPair (loc, i', (x,y, e'))

  | Apx.Comp.Let (loc, i, (x, e)) ->
      let i' = cnormApxExp' cD delta i (cD'', t) in
      let e' = cnormApxExp  cD delta e (cD'', t) in
        Apx.Comp.Let (loc, i', (x, e'))

  | Apx.Comp.Box(loc, phat, m) ->
      let _ = dprint (fun () -> "[cnormApxExp] BOX") in
      let phat' = Whnf.cnorm_psihat phat t in
      let _ = dprint (fun () ->
			let s = match phat' with
			  | (None, _ ) -> ""
			  | (Some (Int.LF.CtxName psi) , _ ) -> R.render_name  psi
			  | (Some (Int.LF.CtxOffset k) , _ ) -> R.render_offset   k in
			  "[cnormApxExp] phat' = " ^ s ) in
      Apx.Comp.Box (loc, phat', cnormApxTerm cD delta m (cD'', t))

  | Apx.Comp.SBox(loc, phat, s) ->
      let phat' = Whnf.cnorm_psihat phat t in
      Apx.Comp.SBox (loc, phat', cnormApxSub cD delta s (cD'', t))


  | Apx.Comp.Case (loc, prag, i, branch) ->
      let _  = dprint (fun () -> "[cnormApxExp] Case Scrutinee ... ") in
      let _ = dprint (fun () -> "[cnormApxExp] cD = " ^ P.mctxToString cD) in
      let e' = cnormApxExp' cD delta i (cD'', t) in
      let _  = dprint (fun () -> "[cnormApxExp] Case Scrutinee done") in
      let bs' = cnormApxBranches cD delta branch (cD'', t) in
      let _  = dprint (fun () -> "[cnormApxExp] Case Body done ") in
      let c   = Apx.Comp.Case (loc, prag, e', bs') in
	(dprint (fun () -> "[cnormApxExp] Case done");
	c)


  | Apx.Comp.If(loc, i, e1, e2) ->
      let i' =  cnormApxExp' cD delta i (cD'', t) in
      let e1' = cnormApxExp cD delta e1 (cD'', t) in
      let e2' = cnormApxExp cD delta e2 (cD'', t) in
        Apx.Comp.If(loc, i', e1', e2')

  | Apx.Comp.Hole (loc) -> Apx.Comp.Hole (loc)

  | Apx.Comp.Cofun (loc, bs) ->
      (dprint (fun () -> "[cnormApxExp] Cofun ");
       let f = function (csp, e) -> (csp, cnormApxExp cD delta e (cD'', t)) in
         Apx.Comp.Cofun (loc, List.map f bs))


and cnormApxExp' cD delta i cDt = match i with
  | Apx.Comp.Var _x -> i
  | Apx.Comp.DataConst _c -> (dprint (fun () -> "[cnormApxExp'] Const " ^
				       (R.render_cid_comp_const _c));
      i)
  | Apx.Comp.DataDest _c -> (dprint (fun () -> "[cnormApxExp'] Dest " ^
				       (R.render_cid_comp_dest _c));
      i)
  | Apx.Comp.Const _c -> (dprint (fun () -> "[cnormApxExp'] Const " ^
				    R.render_cid_prog _c ); i)
  | Apx.Comp.PairVal (loc, i1, i2) ->
      let i1' = cnormApxExp' cD delta i1 cDt in
      let i2' = cnormApxExp' cD delta i2 cDt in
        Apx.Comp.PairVal (loc, i1', i2')
  | Apx.Comp.Apply (loc, i, e) ->
      let _ = dprint (fun () -> "[cnormApxExp'] Apply left arg ") in
      let i' = cnormApxExp' cD delta i cDt in
      let _ = dprint (fun () -> "[cnormApxExp'] Apply right arg ") in
      let e' = cnormApxExp cD delta e cDt in
        Apx.Comp.Apply (loc, i', e')
  | Apx.Comp.CtxApp (loc, i, psi) ->
        let i' = cnormApxExp' cD delta i cDt in
        let psi' = cnormApxDCtx loc cD delta psi cDt in
          Apx.Comp.CtxApp (loc, i', psi')

  | Apx.Comp.MApp (loc, i, Apx.Comp.MetaObj (loc', phat, m)) ->
      let _ = dprint (fun () -> "[cnormApxExp'] MApp left arg") in
      let i' = cnormApxExp' cD delta i cDt in
      let _ = dprint (fun () -> "[cnormApxExp'] MApp right arg") in
      let _ = dprint (fun () -> "[cnormApxExp'] phat = " ^
			P.dctxToString cD (Context.hatToDCtx phat)) in
      let (_cD', t) = cDt in
      let _ = dprint (fun () -> "[cnormApxExp'] _cD' = " ^ P.mctxToString _cD') in
      let _ = dprint (fun () -> "[cnormApxExp']    |- t = " ^ P.msubToString _cD' t) in
      let _ = dprint (fun () -> "[cnormApxExp']  : cD = " ^ P.mctxToString cD) in

      let cPsi = Context.hatToDCtx phat in
      let _ = dprint (fun () -> "[cnormApxExp'] MApp phat = " ^ P.dctxToString cD cPsi) in
      let l_delta = lengthApxMCtx delta in
      let _ = dprint (fun () -> "[cnormApxExp'] l_delta = " ^ string_of_int l_delta) in
      let phat' = Whnf.cnorm_psihat phat t in
      let _ = dprint (fun () -> "[cnormApxExp'] MApp = cnorm_psihat done") in
      let m' = cnormApxTerm cD delta m cDt in
        Apx.Comp.MApp (loc, i', Apx.Comp.MetaObj (loc', phat', m'))

  | Apx.Comp.MAnnApp (loc, i, (psi, m)) ->
      let _ = dprint (fun () -> "[cnormApxExp'] MAnnApp ") in
      let i' = cnormApxExp' cD delta i cDt in
      let _ = dprint (fun () -> "[cnormApxExp'] MAnnApp - cnormApxDCtx ") in
      let psi' = cnormApxDCtx loc cD delta psi cDt in
      let m' = cnormApxTerm cD delta m cDt in
        Apx.Comp.MAnnApp (loc, i', (psi', m'))

  | Apx.Comp.BoxVal (loc, psi, m) ->
      let _    = dprint (fun () -> "[cnormApxExp'] BoxVal ") in
      let psi' = cnormApxDCtx loc cD delta psi cDt in
      let m'   = cnormApxTerm cD delta m cDt in
        Apx.Comp.BoxVal (loc, psi', m')

(*  | Apx.Comp.Ann (e, tau) ->
      let e' = cnormApxExp e cDt in
      let tau' = cnormApxCTyp tau cDt in
        Apx.Comp.Ann (e', tau')

*)

  | Apx.Comp.Boolean (loc, b) -> Apx.Comp.Boolean(loc, b)
  | Apx.Comp.Equal (loc, i1, i2) ->
    let i1' = cnormApxExp' cD delta i1 cDt in
    let i2' = cnormApxExp' cD delta i2 cDt in
      Apx.Comp.Equal (loc, i1', i2')


and cnormApxBranches cD delta branches cDt = match branches with
  | [] -> []
  | b::bs -> (cnormApxBranch cD delta b cDt)::(cnormApxBranches cD delta bs cDt)

and cnormApxBranch cD delta b (cD'', t) =
  let rec mvar_dot_apx t delta = match delta with
    | Apx.LF.Empty -> t
    | Apx.LF.Dec(delta', _ ) ->
        mvar_dot_apx (Whnf.mvar_dot1 t) delta'

  and append delta1 delta2 = match delta2 with
    | Apx.LF.Empty -> delta1

    | Apx.LF.Dec (delta2', dec) ->
      let delta1' = append delta1 delta2' in
        Apx.LF.Dec (delta1', dec)

  and append_mctx cD'' delta' = match delta' with
  | Apx.LF.Empty -> cD''

  | Apx.LF.Dec (delta2', Apx.LF.MDecl (x, _, _ )) ->
      let cD1'' = append_mctx cD'' delta2' in
        Int.LF.Dec (cD1'', Int.LF.MDeclOpt x)

  | Apx.LF.Dec (delta2', Apx.LF.PDecl (x, _, _ )) ->
      let cD1 = append_mctx cD'' delta2' in
        Int.LF.Dec (cD1, Int.LF.PDeclOpt x)

  in
    match b with
      | Apx.Comp.Branch (loc, omega, delta', Apx.Comp.PatMetaObj (loc', mO), e) ->
      (*   16/12/11 -bp
        let cs' = match apxget_ctxvar_mobj mO with None -> cs
                      | Some _ -> Ctxsub.cdot1 cs in *)
	  let _ = dprint (fun () -> "[cnormApxExp] Branch PatMetaObj cD = "
			    ^ P.mctxToString cD) in
          let e' = cnormApxExp cD (append delta delta') e (append_mctx cD'' delta',
                                                           mvar_dot_apx t delta') in
	  let _ = dprint (fun () -> "[cnormApxExp] Branch PatMetaObj done " ) in
            Apx.Comp.Branch (loc, omega, delta', Apx.Comp.PatMetaObj (loc', mO), e')

      | Apx.Comp.Branch (loc, omega, delta', pat, e) ->
	  let _ = dprint (fun () -> "[cnormApxExp] Branch Pattern cD = "
			    ^ P.mctxToString cD) in
          let e' = cnormApxExp cD (append delta delta') e (append_mctx cD'' delta',
                                                           mvar_dot_apx t delta') in
	  let _ = dprint (fun () -> "[cnormApxExp] Branch Pattern done " ) in
            Apx.Comp.Branch (loc, omega, delta', pat, e')


      | Apx.Comp.EmptyBranch (loc, delta', Apx.Comp.PatEmpty _ ) -> b

      | Apx.Comp.BranchBox (loc, omega, delta', (psi1, Apx.Comp.NormalPattern (m, e), Some (a, psi))) ->
          (* |omega| = k  --> shift cs by k ERROR bp *)
(*   16/12/11 -bp
          let cs' = match apxget_ctxvar psi1 with None -> cs
                                                | Some _ -> Ctxsub.cdot1 cs in
*)
          let e' = cnormApxExp cD (append delta delta') e (append_mctx cD'' delta',
                                                              mvar_dot_apx t delta')
          in
            Apx.Comp.BranchBox (loc, omega, delta', (psi1, Apx.Comp.NormalPattern (m, e'), Some (a, psi)))

      | Apx.Comp.BranchBox (loc, omega, delta', (psi, Apx.Comp.NormalPattern (r, e), None)) ->
          (* |omega| = k  --> shift cs by k ERROR bp *)
(*            16/12/11 -bp
           let cs' = match apxget_ctxvar psi with None -> cs
                                               | Some _ -> Ctxsub.cdot1 cs in *)
          let e' = cnormApxExp cD (append delta delta') e (append_mctx cD'' delta',
                                                              mvar_dot_apx t delta')
          in
            Apx.Comp.BranchBox (loc, omega, delta', (psi, Apx.Comp.NormalPattern (r, e'), None))

      | Apx.Comp.BranchBox (loc, omega, delta', (psi1, Apx.Comp.EmptyPattern, typ)) ->
          (* |omega| = k  --> shift cs by k ERROR bp *)
            Apx.Comp.BranchBox (loc, omega, delta', (psi1, Apx.Comp.EmptyPattern, typ))


(* ******************************************************************* *)
(* Collect FMVars and FPVars in a given LF object                      *)

let rec collectApxTerm fMVs  m = match m with
  | Apx.LF.Lam (_loc, _x, m') ->  collectApxTerm fMVs  m'

   (* We only allow free meta-variables of atomic type *)
  | Apx.LF.Root (_loc, Apx.LF.FMVar (u, s), Apx.LF.Nil) ->
       collectApxSub (u::fMVs)  s

  | Apx.LF.Root (_loc, h, s) ->
      let fMVs' = collectApxHead fMVs  h in
        collectApxSpine fMVs'  s

  | Apx.LF.Tuple (_loc, tuple) ->
       collectApxTuple fMVs  tuple

and collectApxTuple fMVs tuple = match tuple with
  | Apx.LF.Last m -> collectApxTerm fMVs  m
  | Apx.LF.Cons (m, tuple) ->
      let fMVs' = collectApxTerm fMVs  m in
        collectApxTuple fMVs' tuple

and collectApxHead fMVs h = match h with
  | Apx.LF.FPVar (p, s) ->
      collectApxSub (p::fMVs) s

  | Apx.LF.MVar (Apx.LF.Offset _offset, s) ->
      collectApxSub fMVs s

  | Apx.LF.PVar (Apx.LF.Offset _offset, s) ->
      collectApxSub fMVs s

  | Apx.LF.Proj(Apx.LF.FPVar (p, s), _k) ->
      collectApxSub (p::fMVs) s

  | _ -> fMVs

and collectApxSub fMVs s = match s with
  | Apx.LF.EmptySub -> fMVs
  | Apx.LF.Id (Apx.LF.CtxName psi)  -> psi :: fMVs
  | Apx.LF.Id _ -> fMVs
  | Apx.LF.Dot (Apx.LF.Head h, s) ->
      let fMVs' = collectApxHead fMVs h in
        collectApxSub fMVs' s

  | Apx.LF.Dot (Apx.LF.Obj m, s) ->
      let fMVs' = collectApxTerm fMVs m in
        collectApxSub fMVs' s

and collectApxSpine fMVs s = match s with
  | Apx.LF.Nil -> fMVs
  | Apx.LF.App (m, s) ->
      let fMVs' = collectApxSpine fMVs s in
        collectApxTerm fMVs' m

and collectApxTyp fMVs a = match a with
  | Apx.LF.Atom (_ , _ , spine) -> collectApxSpine fMVs spine
  | Apx.LF.PiTyp ((tdecl, _ ) , a) ->
      let fMVs' = collectApxTypDecl fMVs tdecl in
        collectApxTyp fMVs' a
  | Apx.LF.Sigma t_rec -> collectApxTypRec fMVs t_rec

and collectApxTypRec fMVs t_rec = match t_rec with
  | Apx.LF.SigmaLast a -> collectApxTyp fMVs a
  | Apx.LF.SigmaElem (_, a, t_rec) ->
      let fMVs' = collectApxTyp fMVs a in
        collectApxTypRec fMVs' t_rec

and collectApxTypDecl fMVs (Apx.LF.TypDecl (_ , a))=
  collectApxTyp fMVs a

and collectApxDCtx fMVs c_psi = match c_psi with
  | Apx.LF.Null -> fMVs
  | Apx.LF.CtxVar (Apx.LF.CtxName psi) -> (psi :: fMVs)
  | Apx.LF.CtxVar (Apx.LF.CtxOffset _) -> fMVs
  | Apx.LF.DDec (c_psi', t_decl) ->
      let fMVs' = collectApxDCtx fMVs c_psi' in
        collectApxTypDecl fMVs' t_decl

and collectApxHat fMVs phat = match phat with
  | (None, _ ) -> fMVs
  | (Some (Int.LF.CtxName psi) , _ ) -> psi :: fMVs
  | (Some _ , _ ) -> fMVs


and collectApxMCtx fMVs c_mctx = match c_mctx with
  | Apx.LF.Empty -> fMVs
  | Apx.LF.Dec (c_mctx', ct_decl) ->
      let fMVs' = collectApxMCtx fMVs c_mctx' in
        collectApxCTypDecl fMVs' ct_decl

and collectApxCTypDecl fMVs ct_decl = match ct_decl with
  | Apx.LF.MDecl ( _, a, c_psi) ->
      let fMVs' = collectApxDCtx fMVs c_psi in
        collectApxTyp fMVs' a

  | Apx.LF.PDecl ( _, a, c_psi) ->
      let fMVs' = collectApxDCtx fMVs c_psi in
        collectApxTyp fMVs' a

and collectApxMetaObj fMVs mO = match mO with
  | Apx.Comp.MetaCtx (_loc, cPsi) ->
      collectApxDCtx fMVs cPsi
  | Apx.Comp.MetaObj (_loc, phat, tR) ->
      let fMVh = collectApxHat fMVs phat  in
      collectApxTerm fMVh tR
  | Apx.Comp.MetaObjAnn (_loc, cPsi, tR) ->
      let fMVd = collectApxDCtx fMVs cPsi in
        collectApxTerm fMVd tR

and collectApxMetaSpine fMVs mS = match mS with
  | Apx.Comp.MetaNil -> fMVs
  | Apx.Comp.MetaApp (mO, mS) ->
      let fMVs1 = collectApxMetaObj fMVs mO in
	collectApxMetaSpine fMVs1 mS

let rec collectApxTyp fMVd tA = match tA with
  | Apx.LF.Atom (loc, c, tS) ->
      collectApxSpine fMVd tS
  | Apx.LF.PiTyp ((Apx.LF.TypDecl (x, tA),_ ), tB) ->
      let fMVd1 = collectApxTyp fMVd tA in
	collectApxTyp fMVd1 tB
  | Apx.LF.Sigma trec ->
       collectApxTypRec fMVd trec

and collectApxTypRec fMVd trec = match trec with
  | Apx.LF.SigmaLast tA -> collectApxTyp fMVd tA
  | Apx.LF.SigmaElem (_, tA, trec) ->
      let fMVd1 = collectApxTyp fMVd tA in
	collectApxTypRec fMVd1 trec

let collectApxCDecl fMVd cdecl = match cdecl with
  | Apx.LF.MDecl (_, tA, cPsi) ->
      let fMVd1 = collectApxDCtx fMVd cPsi in
	collectApxTyp fMVd1 tA
  | Apx.LF.PDecl (_, tA, cPsi) ->
      let fMVd1 = collectApxDCtx fMVd cPsi in
	collectApxTyp fMVd1 tA
  | Apx.LF.CDecl (_, w) -> fMVd

let rec collectApxCompTyp fMVd tau = match tau with
  | Apx.Comp.TypArr (tau1, tau2) ->
      let fMVd1 = collectApxCompTyp fMVd tau1 in
	collectApxCompTyp fMVd1 tau2
  | Apx.Comp.TypCross (tau1, tau2) ->
      let fMVd1 = collectApxCompTyp fMVd tau1 in
	collectApxCompTyp fMVd1 tau2
  | Apx.Comp.TypCtxPi (_, tau) ->
      collectApxCompTyp fMVd tau
  | Apx.Comp.TypPiBox (cdecl, tau) ->
      let fMVd1 = collectApxCDecl fMVd cdecl in
	collectApxCompTyp fMVd1 tau
  | Apx.Comp.TypBox (loc, tA, cPsi) ->
      (let fMVd1 = collectApxTyp fMVd tA in
	 collectApxDCtx fMVd1 cPsi )
  | Apx.Comp.TypBool -> fMVd
  | Apx.Comp.TypBase (_loc, _c, mS) ->
      collectApxMetaSpine fMVd mS

let rec collectApxPattern fMVd pat = match pat with
  | Apx.Comp.PatEmpty (_ , cPsi) ->
      collectApxDCtx fMVd cPsi
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
  | Apx.Comp.PatTrue loc -> fMVd
  | Apx.Comp.PatFalse loc -> fMVd

and collectApxPatSpine fMVd pat_spine = match pat_spine with
  | Apx.Comp.PatNil _ -> fMVd
  | Apx.Comp.PatApp (loc, pat, pat_spine) ->
      let fMVs1 = collectApxPattern fMVd pat in
	collectApxPatSpine fMVs1 pat_spine

(* Replace FMVars with appropriate de Bruijn index
 * If a FMVar (of FPVar) occurs in fMVs do not replace it
 * since it is bound in some inner branch of a case-expression
 *
 *)
let rec fmvApxTerm fMVs cD ((l_cd1, l_delta, k) as d_param) m =   match m with
  | Apx.LF.Lam (loc, x, m') -> Apx.LF.Lam (loc, x, fmvApxTerm fMVs cD d_param  m')

   (* We only allow free meta-variables of atomic type *)
  | Apx.LF.Root (loc, Apx.LF.FMVar (u, s), Apx.LF.Nil) ->
      let s' = fmvApxSub fMVs cD d_param  s in
      if List.mem u fMVs then
          Apx.LF.Root (loc, Apx.LF.FMVar (u, s'), Apx.LF.Nil)
      else
        begin try
          let _ = dprint (fun () -> "[fmvApxTerm] Looking up position of " ^ R.render_name u ^ "\n") in
          let (offset, (_tP, _cPhi)) = Whnf.mctxMVarPos cD u in
	  let _ = dprint (fun () -> "[fmvApxTerm] " ^ R.render_name u
                               ^ " has  position " ^ R.render_offset (offset+k))  in
            Apx.LF.Root (loc, Apx.LF.MVar (Apx.LF.Offset (offset+k), s'), Apx.LF.Nil)
        with Whnf.Fmvar_not_found -> (dprint (fun () -> "[fmvApxTerm]  Error.UnboundName") ;
                                      raise (Index.Error (loc, Index.UnboundName u)))
        end

  | Apx.LF.Root (loc, h, s) ->
      let h' = fmvApxHead fMVs cD d_param  h in
      let s' = fmvApxSpine fMVs cD d_param  s in
        Apx.LF.Root (loc, h', s')

  | Apx.LF.Tuple (loc, tuple) ->
      Apx.LF.Tuple(loc, fmvApxTuple fMVs cD d_param  tuple)

  | Apx.LF.Ann (loc, m', a) ->
    Apx.LF.Ann (loc, fmvApxTerm fMVs cD d_param m', a)

and fmvApxTuple fMVs cD ((l_cd1, l_delta, k) as d_param)   tuple = match tuple with
  | Apx.LF.Last m -> Apx.LF.Last (fmvApxTerm fMVs cD d_param   m)
  | Apx.LF.Cons (m, tuple) ->
      Apx.LF.Cons (fmvApxTerm fMVs cD d_param   m,
                   fmvApxTuple fMVs cD d_param  tuple)

and fmvApxHead fMVs cD ((l_cd1, l_delta, k) as d_param)  h = match h with
  (* free meta-variables / parameter variables *)
  | Apx.LF.FPVar (p, s) ->
      let s' = fmvApxSub fMVs cD d_param  s in
      if List.mem p fMVs then
        Apx.LF.FPVar (p, s')
      else
        let (offset, (_tA, _cPhi)) = Whnf.mctxPVarPos cD p  in
          Apx.LF.PVar (Apx.LF.Offset (offset+k), s')

  | Apx.LF.FMVar (u, s) ->
      let s' = fmvApxSub fMVs cD d_param  s in
      if List.mem u fMVs then
        Apx.LF.FMVar (u, s')
      else
        let (offset, (_tA, _cPhi)) = Whnf.mctxMVarPos cD u  in
          Apx.LF.MVar (Apx.LF.Offset (offset+k), s')

  | Apx.LF.Proj (Apx.LF.FPVar (p,s), j) ->
      let s' = fmvApxSub fMVs cD d_param  s in
        if List.mem p fMVs then
          Apx.LF.Proj (Apx.LF.FPVar (p, s'), j)
        else
          let (offset, (_tA, _cPhi)) = Whnf.mctxPVarPos cD p  in
            Apx.LF.Proj(Apx.LF.PVar (Apx.LF.Offset (offset + k), s'), j)


  (* bound meta-variables / parameters *)
  | Apx.LF.MVar (Apx.LF.Offset offset, s) ->
      let s' = fmvApxSub fMVs cD d_param  s in
        if offset > (l_delta+k) then
          Apx.LF.MVar (Apx.LF.Offset (offset+ l_cd1), s')
        else
          Apx.LF.MVar (Apx.LF.Offset offset, s')

  | Apx.LF.PVar (Apx.LF.Offset offset, s) ->
      let s' = fmvApxSub fMVs cD d_param  s in
        if offset > (l_delta+k) then
          Apx.LF.PVar (Apx.LF.Offset (offset + l_cd1), s')
        else
          Apx.LF.PVar (Apx.LF.Offset offset, s')

  | Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset,s), j) ->
      let s' = fmvApxSub fMVs cD d_param  s in
        if offset > (l_delta+k) then
          Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset (offset + l_cd1), s'), j)
        else
          Apx.LF.Proj (Apx.LF.PVar (Apx.LF.Offset offset, s'), j)


  (* approx. terms may already contain valid LF objects due to
     applying the refinement substitution eagerly to the body of
     case-expressions
     Mon Sep  7 14:08:00 2009 -bp
  *)

  | Apx.LF.MVar (Apx.LF.MInst (tM, tP, cPhi), s) ->
      let s' = fmvApxSub fMVs cD d_param  s in
        (* mvar_dot t cD = t'

           if cD1 |- t <= .
           then cD1, cD |- t' <=  cD
        *)
      let rec mvar_dot t l_delta = match l_delta with
        | 0 -> t
        | l_delta' ->
            mvar_dot (Whnf.mvar_dot1 t) (l_delta' - 1)
      in
      (* cD',cD0 ; cPhi |- tM <= tP   where cD',cD0 = cD
             cD1, cD0   |- mvar_dot (MShift l_cd1) cD0 <= cD0
         cD',cD1,cD0    |- mvar_dot (MShift l_cd1) cD0 <= cD', cD0
       *)
      let r      = mvar_dot (Int.LF.MShift l_cd1) (l_delta+k) in
      let (tM',tP',cPhi') = (Whnf.cnorm (tM, r), Whnf.cnormTyp(tP, r), Whnf.cnormDCtx (cPhi, r)) in
        Apx.LF.MVar (Apx.LF.MInst (tM',tP',cPhi') , s')

  | Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s) ->
      let s' = fmvApxSub fMVs cD d_param  s in
      let rec mvar_dot t l_delta = match l_delta with
        | 0 -> t
        | l_delta' ->
            mvar_dot (Whnf.mvar_dot1 t) (l_delta' - 1)
      in
      (* cD',cD0 ; cPhi |- h => tA   where cD',cD0 = cD
             cD1, cD0   |- mvar_dot (MShift l_cd1) cD0 <= cD0
         cD',cD1,cD0    |- mvar_dot (MShift l_cd1) cD0 <= cD', cD0
       *)
      let r      = mvar_dot (Int.LF.MShift l_cd1) (l_delta + k) in
      let h'     = begin match h with
                   | Int.LF.BVar _k -> h
                   | Int.LF.PVar (Int.LF.Offset k ,s1) ->
                       let s1' =  Whnf.cnormSub (s1, r) in
                         begin match Substitution.LF.applyMSub k r with
                           | Int.LF.MV k' -> Int.LF.PVar (Int.LF.Offset k' ,s1')
                               (* other cases are impossible *)
                         end
                   end in
        Apx.LF.PVar (Apx.LF.PInst (h', Whnf.cnormTyp (tA,r), Whnf.cnormDCtx (cPhi,r)), s')

  | Apx.LF.Proj (Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s), j) ->
      (* let _ = Printf.printf "fmvApx PVar MInst ?\n" in  *)
      let s' = fmvApxSub fMVs cD d_param  s in
      let rec mvar_dot t l_delta = match l_delta with
        | 0 -> t
        | l_delta' ->
            mvar_dot (Whnf.mvar_dot1 t) (l_delta' - 1)
      in
      (* cD',cD0 ; cPhi |- h => tA   where cD',cD0 = cD
             cD1, cD0   |- mvar_dot (MShift l_cd1) cD0 <= cD0
         cD',cD1,cD0    |- mvar_dot (MShift l_cd1) cD0 <= cD', cD0
       *)
      let r      = mvar_dot (Int.LF.MShift l_cd1) (l_delta + k) in
      let h'     = begin match h with
                   | Int.LF.BVar _k -> h
                   | Int.LF.PVar (Int.LF.Offset k ,s1) ->
                       let s1' =  Whnf.cnormSub (s1, r) in
                         begin match Substitution.LF.applyMSub k r with
                           | Int.LF.MV k' -> Int.LF.PVar (Int.LF.Offset k' ,s1')
                               (* other cases are impossible *)
                         end
                   (* | Int.LF.PVar (Int.LF.PInst (_, {contents = Some h1} , _cPsi, _tA, _ ), s1) ->
                       Int.LF.PVar (h1, Whnf.cnormMSub (s1, r)) *)

                   | Int.LF.PVar (Int.LF.PInst (_, {contents = _ }, _cPsi, _tA, _ ) as p ,s1) ->
                       Int.LF.PVar (p, Whnf.cnormSub (s1, r))
                   end in
        Apx.LF.Proj (Apx.LF.PVar (Apx.LF.PInst (h', Whnf.cnormTyp (tA,r), Whnf.cnormDCtx (cPhi,r)), s'), j)

  | _ ->  h

and fmvApxSub fMVs cD ((l_cd1, l_delta, k) as d_param)  s = match s with
  | Apx.LF.EmptySub -> s
  | Apx.LF.Id (Apx.LF.CtxOffset offset) ->
      if offset > (l_delta + k) then
        Apx.LF.Id(Apx.LF.CtxOffset (offset + l_cd1))
      else s
  | Apx.LF.Id ctx_var -> s

  | Apx.LF.Dot (Apx.LF.Head h, s) ->
      let h' = fmvApxHead fMVs cD d_param  h in
      let s' = fmvApxSub fMVs cD d_param  s in
        Apx.LF.Dot (Apx.LF.Head h', s')
  | Apx.LF.Dot (Apx.LF.Obj m, s) ->
      let m' = fmvApxTerm fMVs cD d_param  m in
      let s' = fmvApxSub fMVs cD d_param  s in
        Apx.LF.Dot (Apx.LF.Obj m', s')
(*  | Apx.LF.SVar (u, s) -> *)


and fmvApxSpine fMVs cD ((l_cd1, l_delta, k) as d_param)  s = match s with
  | Apx.LF.Nil -> s
  | Apx.LF.App (m, s) ->
      let s' = fmvApxSpine fMVs cD d_param  s in
      let m' = fmvApxTerm fMVs cD d_param  m in
        Apx.LF.App (m' , s')

let rec fmvApxTyp fMVs cD ((l_cd1, l_delta, k) as d_param)  a = match a with
  | Apx.LF.Atom (loc, c, spine) ->
      Apx.LF.Atom (loc, c, fmvApxSpine fMVs cD d_param  spine)

  | Apx.LF.PiTyp ((t_decl, dep), a) ->
      let t_decl' = fmvApxTypDecl fMVs cD d_param  t_decl in
      let a' = fmvApxTyp fMVs cD d_param  a in
        Apx.LF.PiTyp ((t_decl', dep), a')

  | Apx.LF.Sigma typ_rec ->
      let typ_rec' = fmvApxTypRec fMVs cD d_param  typ_rec in
        Apx.LF.Sigma typ_rec'

and fmvApxTypDecl fMVs cD ((l_cd1, l_delta, k) as d_param)  t_decl = match t_decl with
  | Apx.LF.TypDecl (x, a) ->
      Apx.LF.TypDecl(x, fmvApxTyp fMVs cD d_param  a)

and fmvApxTypRec fMVs cD ((l_cd1, l_delta, k) as d_param)  t_rec = match t_rec with
  | Apx.LF.SigmaLast a -> Apx.LF.SigmaLast (fmvApxTyp fMVs cD d_param  a)
  | Apx.LF.SigmaElem (x, a, t_rec) ->
      let a' = fmvApxTyp fMVs cD d_param  a in
      let t_rec' = fmvApxTypRec fMVs cD d_param  t_rec in
        Apx.LF.SigmaElem (x, a', t_rec')

let rec fmvApxDCtx loc fMVs cD ((l_cd1, l_delta, k) as d_param) psi = match psi with
  | Apx.LF.Null -> psi
  | Apx.LF.CtxVar (Apx.LF.CtxOffset offset) ->
      let _ = dprint (fun () -> "[fmvApxDCtx] CtxOffset " ^ R.render_offset offset) in
      if offset > (l_delta + k) then
	let _ = dprint (fun () -> "[fmvApxDCtx] New CtxOffset " ^
			  R.render_offset (offset + l_cd1)) in
        Apx.LF.CtxVar(Apx.LF.CtxOffset (offset + l_cd1))
      else psi

  | Apx.LF.CtxVar (Apx.LF.CtxName x) ->
      if List.mem x fMVs then
	psi
      else
	begin try
	  let (offset, _w) = Whnf.mctxCVarPos cD x  in
	  let _ = dprint (fun () -> "[fmvApxDCtx] CtxName " ^ R.render_name x ^
			    " with CtxOffset " ^ R.render_offset offset) in
(*	  let _ = dprint (fun () -> "[fmvApxDCtx] in cD " ^ P.mctxToString cD) in
	  let _ = dprint (fun () -> "[fmvApxDCtx] l_cd1 " ^ string_of_int l_cd1) in
	  let _ = dprint (fun () -> "[fmvApxDCtx] l_delta " ^ string_of_int l_delta) in
	  let _ = dprint (fun () -> "[fmvApxDCtx] k " ^ string_of_int k) in *)
	    Apx.LF.CtxVar (Apx.LF.CtxOffset (offset + k))
	with Whnf.Fmvar_not_found ->
	  raise (Index.Error (loc, Index.UnboundCtxName x))
	end

  | Apx.LF.DDec (psi, t_decl) ->
      let psi' = fmvApxDCtx loc fMVs cD d_param  psi in
      let t_decl' = fmvApxTypDecl fMVs cD d_param  t_decl in
        Apx.LF.DDec (psi', t_decl')

let fmvApxHat loc fMVs cD (l_cd1, l_delta, k) phat =
  begin match phat with
    | (Some (Int.LF.CtxOffset offset), d) ->
        if offset > (l_delta + k) then
         (Some (Int.LF.CtxOffset (offset + l_cd1)), d)
        else phat
    | (Some (Int.LF.CtxName psi), d) ->
	if List.mem psi fMVs then
	  phat
	else
	  begin try
            let (offset, _) = Whnf.mctxCVarPos cD psi in
	    let _ = dprint (fun () -> "[fmvApxHat] CtxName " ^ R.render_name psi ^
			      " with " ^ R.render_offset offset ) in
              (Some (Int.LF.CtxOffset (offset + k)), d)
	  with Whnf.Fmvar_not_found ->
	    (Printf.printf "Unbound context variable %s"  (R.render_name psi);
	    raise (Index.Error (loc, Index.UnboundCtxName psi)))
	  end

    | _ -> phat
  end

let rec fmvApxExp fMVs cD ((l_cd1, l_delta, k) as d_param) e = match e with
  | Apx.Comp.Syn (loc, i)       -> Apx.Comp.Syn (loc, fmvApxExp' fMVs cD d_param  i)
  | Apx.Comp.Fun (loc, f, e)    ->
      Apx.Comp.Fun (loc, f, fmvApxExp fMVs cD d_param  e)
  | Apx.Comp.CtxFun (loc, g, e) ->
      Apx.Comp.CtxFun (loc, g, fmvApxExp fMVs cD (l_cd1, l_delta, (k+1)) e)
  | Apx.Comp.MLam (loc, u, e)   ->
      Apx.Comp.MLam (loc, u, fmvApxExp fMVs cD (l_cd1, l_delta, (k+1))  e)
  | Apx.Comp.Pair (loc, e1, e2) ->
      let e1' = fmvApxExp fMVs cD d_param  e1 in
      let e2' = fmvApxExp fMVs cD d_param  e2 in
        Apx.Comp.Pair (loc, e1', e2')
  | Apx.Comp.LetPair (loc, i, (x,y, e)) ->
      let i' = fmvApxExp' fMVs cD d_param  i in
      let e' = fmvApxExp  fMVs cD d_param  e in
        Apx.Comp.LetPair (loc, i', (x,y, e'))
  | Apx.Comp.Let (loc, i, (x, e)) ->
      let i' = fmvApxExp' fMVs cD d_param  i in
      let e' = fmvApxExp  fMVs cD d_param  e in
        Apx.Comp.Let (loc, i', (x, e'))

  | Apx.Comp.Box(loc, phat, m) ->
      Apx.Comp.Box (loc, fmvApxHat loc fMVs cD d_param phat, fmvApxTerm fMVs cD d_param  m)

  | Apx.Comp.SBox(loc, phat, s) ->
      Apx.Comp.SBox (loc, fmvApxHat loc fMVs cD d_param  phat, fmvApxSub fMVs cD d_param  s)

  | Apx.Comp.Case (loc, prag, i, branch) ->
      Apx.Comp.Case (loc, prag, fmvApxExp' fMVs cD d_param  i,
                          fmvApxBranches fMVs cD d_param  branch)
  | Apx.Comp.If (loc, i, e1, e2) ->
      let i' = fmvApxExp' fMVs cD d_param  i in
      let e1' = fmvApxExp  fMVs cD d_param  e1 in
      let e2' = fmvApxExp  fMVs cD d_param  e2 in
        Apx.Comp.If (loc, i', e1', e2')

  | Apx.Comp.Hole (loc) -> Apx.Comp.Hole (loc)

  | Apx.Comp.Cofun (loc, bs) ->
      let f = function (csp, e) -> (csp, fmvApxExp fMVs cD d_param e) in
        Apx.Comp.Cofun (loc, List.map f bs)
          (*Might be needed to get metaobjs from csp before call fmvApxExp on e *)


and fmvApxExp' fMVs cD ((l_cd1, l_delta, k) as d_param)  i = match i with
  | Apx.Comp.Var _x -> i
  | Apx.Comp.DataConst _c -> i
  | Apx.Comp.DataDest _c -> i
  | Apx.Comp.Const _c -> i
  | Apx.Comp.Apply (loc, i, e) ->
      let i' = fmvApxExp' fMVs cD d_param  i in
      let e' = fmvApxExp fMVs cD d_param  e in
        Apx.Comp.Apply (loc, i', e')
  | Apx.Comp.CtxApp (loc, i, psi) ->
      let i' = fmvApxExp' fMVs cD d_param  i in
      let psi' = fmvApxDCtx loc fMVs cD  d_param  psi  in
        Apx.Comp.CtxApp (loc, i', psi')

  | Apx.Comp.MApp (loc, i, Apx.Comp.MetaObj (loc', phat, m)) ->
      let i' = fmvApxExp' fMVs cD d_param  i in
      let m' = fmvApxTerm fMVs cD d_param  m in
        Apx.Comp.MApp (loc, i', Apx.Comp.MetaObj (loc', (fmvApxHat loc' fMVs cD d_param phat), m'))

  | Apx.Comp.MAnnApp (loc, i, (psi, m)) ->
      let i' = fmvApxExp' fMVs cD d_param  i in
      let psi' = fmvApxDCtx loc fMVs cD d_param  psi in
      let m' = fmvApxTerm fMVs cD d_param  m in
        Apx.Comp.MAnnApp (loc, i', (psi', m'))

  | Apx.Comp.BoxVal (loc, psi, m) ->
      let psi' = fmvApxDCtx loc fMVs cD d_param  psi in
      let m'   = fmvApxTerm fMVs cD d_param  m in
        Apx.Comp.BoxVal (loc, psi', m')

  | Apx.Comp.PairVal (loc, i1, i2) ->
      let i1' = fmvApxExp' fMVs cD d_param  i1 in
      let i2' = fmvApxExp' fMVs cD d_param  i2 in
        Apx.Comp.PairVal (loc, i1', i2')

(*  | Apx.Comp.Ann (e, tau) ->
      let e' = fmvApxExp e t in
      let tau' = fmvApxCTyp tau t in
        Apx.Comp.Ann (e', tau')

*)

  | Apx.Comp.Boolean (loc, b) -> Apx.Comp.Boolean (loc, b)
  | Apx.Comp.Equal (loc, i1, i2) ->
      let i1' = fmvApxExp' fMVs cD d_param  i1 in
      let i2' = fmvApxExp' fMVs cD d_param  i2 in
        Apx.Comp.Equal (loc, i1', i2')




and fmvApxBranches fMVs cD ((l_cd1, l_delta, k) as d_param)  branches = match branches with
  | [] -> []
  | b::bs -> (fmvApxBranch fMVs cD d_param  b)::(fmvApxBranches fMVs cD d_param  bs)

and fmvApxBranch fMVs cD (l_cd1, l_delta, k)  b =
   match b with
     | Apx.Comp.EmptyBranch (loc, delta, Apx.Comp.PatEmpty _ ) -> b
     | Apx.Comp.Branch (loc, omega, delta, Apx.Comp.PatMetaObj (loc', mO), e) ->
          let fMVd  = collectApxMCtx [] delta in
          let fMVb = collectApxMetaObj fMVd mO in
          let l    = lengthApxMCtx delta in
          let pat =  Apx.Comp.PatMetaObj (loc', mO) in
          let e' = fmvApxExp (fMVs@fMVb) cD (l_cd1, l_delta, (k+l))  e in
            Apx.Comp.Branch (loc, omega, delta, pat, e')

     | Apx.Comp.Branch (loc, omega, delta, pat, e) ->
          let fMVd  = collectApxMCtx [] delta in
          let fMVb  = collectApxPattern fMVd pat in
          let l    = lengthApxMCtx delta in
          let e' = fmvApxExp (fMVs@fMVb) cD (l_cd1, l_delta, (k+l))  e in
            Apx.Comp.Branch (loc, omega, delta, pat, e')

     | Apx.Comp.BranchBox (loc, omega, delta, (psi1, Apx.Comp.EmptyPattern, Some (a, psi))) ->
          let fMVd  = collectApxMCtx [] delta in
          let fMVb' = fMVd in
          let fMVb1  = collectApxDCtx fMVb' psi in
          let _fMVb  = collectApxTyp fMVb1 a in
            Apx.Comp.BranchBox (loc, omega, delta, (psi1, Apx.Comp.EmptyPattern, Some (a, psi)))

      | Apx.Comp.BranchBox (loc, omega, delta, (psi, Apx.Comp.EmptyPattern, None))  ->
          let fMVd  = collectApxMCtx [] delta in
          let fMVb' = fMVd in
          let _fMVb  = collectApxDCtx fMVb' psi in
            Apx.Comp.BranchBox (loc, omega, delta, (psi, Apx.Comp.EmptyPattern, None))

      | Apx.Comp.BranchBox (loc, omega, delta, (psi1, Apx.Comp.NormalPattern (m, e), Some (a, psi))) ->
          let fMVd  = collectApxMCtx [] delta in
          let fMVb' = collectApxTerm fMVd m in
          let fMVb1  = collectApxDCtx fMVb' psi in
          let fMVb  = collectApxTyp fMVb1 a in
          let l    = lengthApxMCtx delta in
          let e' = fmvApxExp (fMVs@fMVb) cD (l_cd1, l_delta, (k+l)) e in
            Apx.Comp.BranchBox (loc, omega, delta, (psi1, Apx.Comp.NormalPattern (m, e'), Some (a, psi)))

      | Apx.Comp.BranchBox (loc, omega, delta, (psi, Apx.Comp.NormalPattern (r, e), None))  ->
          let fMVd  = collectApxMCtx [] delta in
          let fMVb' = collectApxTerm fMVd r in
          let fMVb  = collectApxDCtx fMVb' psi in
          let l    = lengthApxMCtx delta in
          let e' = fmvApxExp (fMVs@fMVb) cD (l_cd1, l_delta, (k+l)) e in
            Apx.Comp.BranchBox (loc, omega, delta, (psi, Apx.Comp.NormalPattern (r, e'), None))
