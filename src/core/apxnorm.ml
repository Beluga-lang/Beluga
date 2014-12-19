
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

  | Apx.LF.LFHole loc ->
    m

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
               | Int.LF.PVar (q, s1) ->
                   begin match Substitution.LF.applyMSub q t with
                     | Int.LF.MV q' ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (q', s1')
                     | Int.LF.PObj (_hat, Int.LF.PVar (q', s2)) ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (q', Substitution.LF.comp s1' s2)
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
               | Int.LF.PVar (q, s1) ->
                   begin match Substitution.LF.applyMSub q t with
                     | Int.LF.MV q' ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (q', s1')
                     | Int.LF.PObj (_phat, Int.LF.PVar (p,s')) ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (p, s1')
                   end
               end in
        Apx.LF.Proj(Apx.LF.PVar (Apx.LF.PInst (h', tA', cPhi'), s'), j)

    | Apx.LF.NamedProj (Apx.LF.PVar (Apx.LF.Offset offset, s), j) ->
      let l_delta = lengthApxMCtx delta in
      let offset' = (offset - l_delta)  in
      let _ = dprint (fun () -> "[cnormApxTerm] Proj (PVar _ ) . " ^ j.Id.string_of_name ^ " : offset = " ^ string_of_int offset ) in
      let _ = dprint (fun () -> "[cnormApxTerm] Proj (PVar _ ) . " ^ j.Id.string_of_name ^ " : offset' = " ^ string_of_int offset' ) in
      let _ = dprint (fun () -> "[cnormApxTerm] l_delta = " ^ string_of_int l_delta ) in
      let _ = dprint (fun () -> "[cnormApxTerm] t = " ^ P.msubToString cD'' t ^ "\n") in
      let _ = dprint (fun () -> "[cnormApxTerm] (original) cD = " ^ P.mctxToString cD ^ "\n") in
        if offset > l_delta then
          begin match Substitution.LF.applyMSub offset t with
            | Int.LF.MV offset' ->
                Apx.LF.NamedProj(Apx.LF.PVar (Apx.LF.Offset offset',
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
                  Apx.LF.NamedProj(Apx.LF.PVar (Apx.LF.PInst (h, Whnf.cnormTyp (tP,t'), Whnf.cnormDCtx (cPhi,t')),
                                           cnormApxSub cD delta s (cD'', t)),
                              j)

            | Int.LF.MObj (phat, tM) ->
                (dprint (fun () -> "[cnormApxTerm] MObj :" ^
                           P.normalToString cD (Context.hatToDCtx phat) (tM, Substitution.LF.id) ^ "\n") ;
                 raise (Error.Violation "MObj found -- expected PObj"))
          end
        else
          Apx.LF.NamedProj (Apx.LF.PVar (Apx.LF.Offset offset, cnormApxSub cD delta s (cD'', t)), j)

  | Apx.LF.NamedProj(Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s), j) ->
      let (tA', cPhi')  = (Whnf.cnormTyp (tA, t), Whnf.cnormDCtx (cPhi, t)) in
      let s' = cnormApxSub cD delta s (cD'', t) in
      let h' = begin match h with
               | Int.LF.BVar _ -> h
               | Int.LF.PVar (q, s1) ->
                   begin match Substitution.LF.applyMSub q t with
                     | Int.LF.MV q' ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (q', s1')
                     | Int.LF.PObj (_phat, Int.LF.PVar (p,s')) ->
                         let s1' = Whnf.cnormSub (s1, t) in
                           Int.LF.PVar (p, s1')
                   end
               end in
        Apx.LF.NamedProj(Apx.LF.PVar (Apx.LF.PInst (h', tA', cPhi'), s'), j)

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

  | Apx.LF.SVar (Apx.LF.Offset offset , sigma) ->
      let sigma' = cnormApxSub cD delta sigma (cD'', t) in
      let l_delta = lengthApxMCtx delta in
      let offset' = (offset - l_delta)  in
        if offset > l_delta then
          begin match Substitution.LF.applyMSub offset  t with
            | Int.LF.MV u ->
                Apx.LF.SVar (Apx.LF.Offset u, sigma')
            | Int.LF.SObj (_phat, s) ->
                let (_s, cPsi, cPhi) = Whnf.mctxSDec cD offset' in
                let rec drop t l_delta = match (l_delta, t) with
                  | (0, t) -> t
                  | (k, Int.LF.MDot(_ , t') ) -> drop t' (k-1) in

                let t' = drop t l_delta in
		let _  = dprint (fun () -> "[cnormApxSub] cPsi = " ^
                                   P.dctxToString cD cPsi) in
		let _  = dprint (fun () -> "[cnormApxSub] cPhi = " ^
                                   P.dctxToString cD cPhi) in
                let (cPsi', cPhi')  = (Whnf.cnormDCtx (cPsi, t'), Whnf.cnormDCtx
		(cPhi, t')) in
		let _  = dprint (fun () -> "[cnormApxSub] cPsi' = " ^
                                   P.dctxToString cD'' cPsi') in
		let _  = dprint (fun () -> "[cnormApxSub] cPhi' = " ^
                                   P.dctxToString cD'' cPhi') in
		let _ = dprint (fun () -> "[cnormApxSub - SVar] done") in
                  Apx.LF.SVar (Apx.LF.SInst (s, cPsi', cPhi'), sigma')
          end
        else
	  let _ = dprint (fun () -> "[cnormApxSub] SVar offset = " ^
                  R.render_offset offset ) in
          Apx.LF.SVar (Apx.LF.Offset offset, sigma')

  | Apx.LF.SVar (Apx.LF.SInst (s, cPsi, cPhi), sigma) ->
      let s' = Whnf.cnormSub (s, t) in
      let (cPsi', cPhi') = (Whnf.cnormDCtx (cPsi, t) , Whnf.cnormDCtx (cPhi, t)) in
      let sigma' = cnormApxSub cD delta sigma (cD'', t) in
        Apx.LF.SVar (Apx.LF.SInst (s', cPsi', cPhi'), sigma')

  | Apx.LF.FSVar (s, sigma) ->
      let sigma' = cnormApxSub cD delta sigma (cD'', t) in
        Apx.LF.FSVar (s, sigma')

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
  | Apx.LF.SigmaLast(n, a) -> Apx.LF.SigmaLast (n, cnormApxTyp cD delta a (cD'', t))
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
(*  | Apx.Comp.CtxFun (loc, g, e) ->
      (dprint (fun () -> "cnormApxExp -- CtxFun ") ;
      Apx.Comp.CtxFun (loc, g, cnormApxExp cD (Apx.LF.Dec(delta, Apx.LF.CDeclOpt g)) e
                         (Int.LF.Dec (cD'', Int.LF.CDeclOpt g), Whnf.mvar_dot1 t))
      )*)
  | Apx.Comp.MLam (loc, u, e)   ->
      (dprint (fun () -> "cnormApxExp -- MLam (or could be PLam)") ;
      Apx.Comp.MLam (loc, u, cnormApxExp cD (Apx.LF.Dec(delta, Apx.LF.DeclOpt u)) e
                       (Int.LF.Dec (cD'', Int.LF.DeclOpt u), Whnf.mvar_dot1 t)))

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

  | Apx.Comp.Box(loc,  m) ->
      let _ = dprint (fun () -> "[cnormApxExp] BOX") in
      let m'     = cnormApxMetaObj cD delta m (cD'', t) in
      Apx.Comp.Box (loc, m')

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
  | Apx.Comp.Var (_, _x) -> i
  | Apx.Comp.DataConst (_, _c) -> i
  | Apx.Comp.DataDest (_, _c) ->  i
  | Apx.Comp.Const (_, _c) ->  i
  | Apx.Comp.PairVal (loc, i1, i2) ->
      let i1' = cnormApxExp' cD delta i1 cDt in
      let i2' = cnormApxExp' cD delta i2 cDt in
        Apx.Comp.PairVal (loc, i1', i2')

  | Apx.Comp.Apply (loc, i, e) ->
      let i' = cnormApxExp' cD delta i cDt in
      let e' = cnormApxExp cD delta e cDt in
        Apx.Comp.Apply (loc, i', e')

  | Apx.Comp.BoxVal (loc, mobj) ->
      let mobj'     = cnormApxMetaObj cD delta mobj cDt in
        Apx.Comp.BoxVal (loc, mobj')

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

and cnormApxMetaObj cD delta mobj cDt = let (_cD', t) = cDt in
  match mobj with
    | Apx.Comp.MetaObj (loc', phat, m) ->
        let phat'     = Whnf.cnorm_psihat phat t in
        let m'        = cnormApxTerm cD delta m cDt in
          Apx.Comp.MetaObj (loc', phat', m')

    | Apx.Comp.MetaCtx (loc', psi) ->
        let psi' = cnormApxDCtx loc' cD delta psi cDt in
          Apx.Comp.MetaCtx (loc', psi')

    | Apx.Comp.MetaObjAnn (loc', psi, m) ->
        let psi' = cnormApxDCtx loc' cD delta psi cDt in
        let m'   = cnormApxTerm cD delta m cDt in
          Apx.Comp.MetaObjAnn (loc', psi', m')

    | Apx.Comp.MetaSub (loc, phat, sigma) ->
      let phat'  = Whnf.cnorm_psihat phat t in
      let sigma' = cnormApxSub cD delta sigma cDt in
        Apx.Comp.MetaSub (loc, phat', sigma')

    | Apx.Comp.MetaSubAnn (loc, psi, sigma) ->
      let psi'   = cnormApxDCtx loc cD delta psi cDt in
      let sigma' = cnormApxSub cD delta sigma cDt in
        Apx.Comp.MetaSubAnn (loc, psi', sigma')



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

  | Apx.LF.Dec (delta2', Apx.LF.Decl(x, _,_)) ->
      let cD1'' = append_mctx cD'' delta2' in
        Int.LF.Dec (cD1'', Int.LF.DeclOpt x)

  in
    match b with
      | Apx.Comp.Branch (loc, omega, delta', Apx.Comp.PatMetaObj (loc', mO), e) ->
          let e' = cnormApxExp cD (append delta delta') e (append_mctx cD'' delta',
                                                           mvar_dot_apx t delta') in
            Apx.Comp.Branch (loc, omega, delta', Apx.Comp.PatMetaObj (loc', mO), e')

      | Apx.Comp.Branch (loc, omega, delta', pat, e) ->
          let e' = cnormApxExp cD (append delta delta') e (append_mctx cD'' delta',
                                                           mvar_dot_apx t delta') in
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

  | Apx.LF.LFHole _loc -> fMVs

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

  | Apx.LF.NamedProj(Apx.LF.FPVar (p, s), _k) ->
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
  | Apx.LF.SVar (i,s) ->
      collectApxSub fMVs s
  | Apx.LF.FSVar (n,s) ->
      collectApxSub (n::fMVs) s

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
  | Apx.LF.SigmaLast(_, a) -> collectApxTyp fMVs a
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
  | Apx.LF.Decl(_, Apx.LF.MTyp(a, c_psi), _)
  | Apx.LF.Decl(_, Apx.LF.PTyp(a, c_psi), _) ->
    let fMVs' = collectApxDCtx fMVs c_psi in
        collectApxTyp fMVs' a
  | Apx.LF.Decl(_, Apx.LF.STyp(c_phi, c_psi), _) ->
    let fMVs' = collectApxDCtx fMVs c_psi in
      collectApxDCtx fMVs' c_phi
  | Apx.LF.Decl(_, Apx.LF.CTyp _, _) ->  fMVs

and collectApxMetaObj fMVs mO = match mO with
  | Apx.Comp.MetaCtx (_loc, cPsi) ->
      collectApxDCtx fMVs cPsi
  | Apx.Comp.MetaObj (_loc, phat, tR) ->
      let fMVh = collectApxHat fMVs phat  in
      collectApxTerm fMVh tR
  | Apx.Comp.MetaObjAnn (_loc, cPsi, tR) ->
      let fMVd = collectApxDCtx fMVs cPsi in
        collectApxTerm fMVd tR
  | Apx.Comp.MetaSub (_loc, phat, s) ->
      let fMVh = collectApxHat fMVs phat  in
      collectApxSub fMVh s
  | Apx.Comp.MetaSubAnn (_loc, cPsi, s) ->
      let fMVd = collectApxDCtx fMVs cPsi in
        collectApxSub fMVd s

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
  | Apx.LF.SigmaLast(n, tA) -> collectApxTyp fMVd tA
  | Apx.LF.SigmaElem (_, tA, trec) ->
      let fMVd1 = collectApxTyp fMVd tA in
	collectApxTypRec fMVd1 trec

let collectApxCDecl fMVd cdecl = match cdecl with
  | Apx.LF.Decl(_, Apx.LF.MTyp(tA, cPsi), _)
  | Apx.LF.Decl(_, Apx.LF.PTyp(tA, cPsi), _) ->
    let fMVd1 = collectApxDCtx fMVd cPsi in
	    collectApxTyp fMVd1 tA
  | Apx.LF.Decl (_,Apx.LF.CTyp _,_) -> fMVd

let rec collectApxCompTyp fMVd tau = match tau with
  | Apx.Comp.TypArr (tau1, tau2) ->
      let fMVd1 = collectApxCompTyp fMVd tau1 in
	collectApxCompTyp fMVd1 tau2
  | Apx.Comp.TypCross (tau1, tau2) ->
      let fMVd1 = collectApxCompTyp fMVd tau1 in
	collectApxCompTyp fMVd1 tau2
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
          let (offset, _) = Whnf.mctxMVarPos cD u in
(*	  let _ = dprint (fun () -> "[fmvApxTerm] " ^ R.render_name u
                               ^ " has  position " ^ R.render_offset (offset+k))  in*)
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

  | Apx.LF.LFHole _ -> m

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
        let (offset, _) = Whnf.mctxMVarPos cD p  in
          Apx.LF.PVar (Apx.LF.Offset (offset+k), s')

  | Apx.LF.FMVar (u, s) ->
      let s' = fmvApxSub fMVs cD d_param  s in
      if List.mem u fMVs then
        Apx.LF.FMVar (u, s')
      else
        let (offset, _) = Whnf.mctxMVarPos cD u  in
          Apx.LF.MVar (Apx.LF.Offset (offset+k), s')

  | Apx.LF.Proj (Apx.LF.FPVar (p,s), j) ->
      let s' = fmvApxSub fMVs cD d_param  s in
        if List.mem p fMVs then
          Apx.LF.Proj (Apx.LF.FPVar (p, s'), j)
        else
          let (offset, _) = Whnf.mctxMVarPos cD p  in
            Apx.LF.Proj(Apx.LF.PVar (Apx.LF.Offset (offset + k), s'), j)

  | Apx.LF.NamedProj (Apx.LF.FPVar (p,s), j) ->
      let s' = fmvApxSub fMVs cD d_param  s in
        if List.mem p fMVs then
          Apx.LF.NamedProj (Apx.LF.FPVar (p, s'), j)
        else
          let (offset, _) = Whnf.mctxMVarPos cD p  in
            Apx.LF.NamedProj(Apx.LF.PVar (Apx.LF.Offset (offset + k), s'), j)

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

  | Apx.LF.NamedProj (Apx.LF.PVar (Apx.LF.Offset offset,s), j) ->
      let s' = fmvApxSub fMVs cD d_param  s in
        if offset > (l_delta+k) then
          Apx.LF.NamedProj (Apx.LF.PVar (Apx.LF.Offset (offset + l_cd1), s'), j)
        else
          Apx.LF.NamedProj (Apx.LF.PVar (Apx.LF.Offset offset, s'), j)

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
                   | Int.LF.PVar (k ,s1) ->
                       let s1' =  Whnf.cnormSub (s1, r) in
                         begin match Substitution.LF.applyMSub k r with
                           | Int.LF.MV k' -> Int.LF.PVar (k' ,s1')
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
                   | Int.LF.PVar (k ,s1) ->
                       let s1' =  Whnf.cnormSub (s1, r) in
                         begin match Substitution.LF.applyMSub k r with
                           | Int.LF.MV k' -> Int.LF.PVar (k' ,s1')
                               (* other cases are impossible *)
                         end
                   end in
        Apx.LF.Proj (Apx.LF.PVar (Apx.LF.PInst (h', Whnf.cnormTyp (tA,r), Whnf.cnormDCtx (cPhi,r)), s'), j)

  | Apx.LF.NamedProj (Apx.LF.PVar (Apx.LF.PInst (h, tA, cPhi), s), j) ->
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
                   | Int.LF.PVar (k ,s1) ->
                       let s1' =  Whnf.cnormSub (s1, r) in
                         begin match Substitution.LF.applyMSub k r with
                           | Int.LF.MV k' -> Int.LF.PVar (k' ,s1')
                               (* other cases are impossible *)
                         end
                   (* | Int.LF.PVar (Int.LF.PInst (_, {contents = Some h1} , _cPsi, _tA, _ ), s1) ->
                       Int.LF.PVar (h1, Whnf.cnormMSub (s1, r)) *)
                   end in
        Apx.LF.NamedProj (Apx.LF.PVar (Apx.LF.PInst (h', Whnf.cnormTyp (tA,r), Whnf.cnormDCtx (cPhi,r)), s'), j)

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

  | Apx.LF.FSVar (u, sigma) ->
    let sigma' = fmvApxSub fMVs cD d_param  sigma in
      if List.mem u fMVs then
        Apx.LF.FSVar (u, sigma')
      else
        let (offset, _) = Whnf.mctxMVarPos cD u  in
          (*  cPsi |- s : cPhi  *)
          Apx.LF.SVar (Apx.LF.Offset (offset+k), sigma')

  | Apx.LF.SVar (Apx.LF.SInst (s, cPsi, cPhi), sigma) ->
      let sigma' = fmvApxSub fMVs cD d_param  sigma in
        (* mvar_dot t cD = t'

           if cD1 |- t <= .
           then cD1, cD |- t' <=  cD
        *)
      let rec mvar_dot t l_delta = match l_delta with
        | 0 -> t
        | l_delta' ->
            mvar_dot (Whnf.mvar_dot1 t) (l_delta' - 1)
      in
      (* cD',cD0 ; cPhi |- s <= tPsi   where cD',cD0 = cD
             cD1, cD0   |- mvar_dot (MShift l_cd1) cD0 <= cD0
         cD',cD1,cD0    |- mvar_dot (MShift l_cd1) cD0 <= cD', cD0
       *)
      let r      = mvar_dot (Int.LF.MShift l_cd1) (l_delta+k) in
      let (s',cPsi',cPhi') = (Whnf.cnormSub (s, r), Whnf.cnormDCtx(cPsi, r), Whnf.cnormDCtx (cPhi, r)) in
        Apx.LF.SVar (Apx.LF.SInst (s',cPsi',cPhi') , sigma')


  | Apx.LF.SVar (Apx.LF.Offset offset, sigma) ->
    let sigma' = fmvApxSub fMVs cD d_param  sigma in
    let (l_cd1, l_delta, k) = d_param in
    if offset > (l_delta+k) then
      Apx.LF.SVar (Apx.LF.Offset (offset + l_cd1), sigma')
    else
      Apx.LF.SVar (Apx.LF.Offset offset, sigma')


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
  | Apx.LF.SigmaLast (n, a) -> Apx.LF.SigmaLast (n, fmvApxTyp fMVs cD d_param  a)
  | Apx.LF.SigmaElem (x, a, t_rec) ->
      let a' = fmvApxTyp fMVs cD d_param  a in
      let t_rec' = fmvApxTypRec fMVs cD d_param  t_rec in
        Apx.LF.SigmaElem (x, a', t_rec')

let rec fmvApxDCtx loc fMVs cD ((l_cd1, l_delta, k) as d_param) psi = match psi with
  | Apx.LF.Null -> psi
  | Apx.LF.CtxVar (Apx.LF.CtxOffset offset) ->
      if offset > (l_delta + k) then
        Apx.LF.CtxVar(Apx.LF.CtxOffset (offset + l_cd1))
      else psi

  | Apx.LF.CtxVar (Apx.LF.CtxName x) ->
      if List.mem x fMVs then
	psi
      else
	begin try
	  let (offset, _w) = Whnf.mctxMVarPos cD x  in
(*	  let _ = dprint (fun () -> "[fmvApxDCtx] CtxName " ^ R.render_name x ^
			    " with CtxOffset " ^ R.render_offset offset) in
	  let _ = dprint (fun () -> "[fmvApxDCtx] in cD " ^ P.mctxToString cD) in
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
            let (offset, _) = Whnf.mctxMVarPos cD psi in
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

  | Apx.Comp.Box(loc, m) ->
      let m' = fmvApxMetaObj fMVs cD d_param  m in
      Apx.Comp.Box (loc, m')

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
  | Apx.Comp.Var (_, _x) -> i
  | Apx.Comp.DataConst (_, _c) -> i
  | Apx.Comp.DataDest (_, _c) -> i
  | Apx.Comp.Const (_, _c) -> i
  | Apx.Comp.Apply (loc, i, e) ->
      let i' = fmvApxExp' fMVs cD d_param  i in
      let e' = fmvApxExp fMVs cD d_param  e in
        Apx.Comp.Apply (loc, i', e')

  | Apx.Comp.BoxVal (loc, mobj) ->
      let mobj' = fmvApxMetaObj fMVs cD d_param  mobj in
        Apx.Comp.BoxVal (loc, mobj')

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

and fmvApxMetaObj fMVs cD ((l_cd1, l_delta, k) as d_param) mobj = match mobj with
  | Apx.Comp.MetaObj (loc', phat, m) ->
      let phat' = fmvApxHat loc' fMVs cD d_param phat in
      let m'    = fmvApxTerm fMVs cD d_param  m in
        Apx.Comp.MetaObj (loc', phat', m')

  | Apx.Comp.MetaCtx (loc, psi) ->
      let psi' = fmvApxDCtx loc fMVs cD  d_param  psi  in
        Apx.Comp.MetaCtx (loc, psi')

  | Apx.Comp.MetaObjAnn (loc, psi, m) ->
      let psi' = fmvApxDCtx loc fMVs cD d_param  psi in
      let m' = fmvApxTerm fMVs cD d_param  m in
        Apx.Comp.MetaObjAnn (loc, psi', m')

  | Apx.Comp.MetaSub (loc, phat, sigma) ->
      let phat' = fmvApxHat loc fMVs cD d_param phat in
      let sigma' = fmvApxSub fMVs cD d_param  sigma in
        Apx.Comp.MetaSub (loc, phat', sigma')

  | Apx.Comp.MetaSubAnn (loc, psi, sigma) ->
      let psi' = fmvApxDCtx loc fMVs cD d_param  psi in
      let sigma' = fmvApxSub fMVs cD d_param  sigma in
        Apx.Comp.MetaSubAnn (loc, psi', sigma')




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
