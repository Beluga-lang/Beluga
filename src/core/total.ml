(* Checking termination of a function *)

open Syntax.Int
module Unify = Unify.StdTrail
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])

type dec =
{name : Id.name ;
 typ  : Comp.typ ;
 order: Order.order
}


let mutual_decs : (dec list) ref = ref []

let clear () = (mutual_decs :=  [])

let make_dec f tau order =
  { name = f;
    typ  = tau;
    order = order
  }

let extend_dec l =
mutual_decs := l::!mutual_decs

let rec args_to_string cD args = match args with
  | [] -> ""
  | (Comp.M cM)::args ->
      P.metaObjToString cD cM ^ " " ^
        args_to_string cD args

let calls_to_string cD (f, args, tau) =
(*   (R.render_cid_prog f) ^ " " ^ *)
  (R.render_name f) ^ " " ^
    args_to_string cD args ^ " : "  ^
    P.compTypToString cD tau

let get_order () =
  let [dec] = !mutual_decs in
  let tau = dec.typ in
(*  let _ = dprint (fun () -> "[get_order] " ^ (R.render_cid_prog dec.name) ^
" : " ^     P.compTypToString (LF.Empty) dec.typ) in *)
  let Order.Arg x = dec.order in
    (dec.name, x, (tau, Whnf.m_id))

(* let check (f,e) tau =
  match (Comp.get f).Comp.order with
    | None -> ()
    | Some (Order.Dec (order, Order.Empty)) -> ()
    | Some ( _ ) -> ()

*)

(* Given C:U, f, order Arg i, and type T of f where
   T = Pi X1:U1, ... X:i:Un. T, generate
   meta-variables for all argument up to i, i.e. theta,
   [theta]Un = U

   and return [theta](f X1 ... X(i-1)) C : [theta]T

   check: recursive call and its corresponding type are closed .



*)
exception Not_compatible

let gen_var loc cD cdecl = match cdecl with
  | LF.MDecl (n, tA, cPsi) ->
      let psihat  = Context.dctxToHat cPsi in
      let tM = Whnf.etaExpandMMV loc cD cPsi (tA, Substitution.LF.id) n Substitution.LF.id in
        ( Comp.MetaObj (loc, psihat, tM) ,
          LF.MObj (psihat, tM) )
  | LF.PDecl (p, tA, cPsi) ->
      let psihat  = Context.dctxToHat cPsi in
      let p     = Whnf.newMPVar (Some p) (cD, cPsi, tA) in
      let h     = LF.MPVar (p, (Whnf.m_id, Substitution.LF.id)) in
        (Comp.MetaParam (loc, psihat, h) ,
         LF.PObj (psihat, h) )

  | LF.SDecl (s, cPhi, cPsi) ->
      let psihat  = Context.dctxToHat cPsi in
      let s     =  Whnf.newMSVar (Some s) (cD, cPsi, cPhi) in
      let sigma = LF.MSVar (s, (LF.NoCtxShift, 0), (Whnf.m_id, Substitution.LF.id)) in
        (Comp.MetaSObj (loc, psihat, sigma) ,
         LF.SObj (psihat, sigma) )

  | LF.CDecl(psi_name, schema_cid, _) ->
      let cPsi = LF.CtxVar (LF.CInst (psi_name, ref None, schema_cid, cD, Whnf.m_id)) in
        (Comp.MetaCtx (loc, cPsi) , LF.CObj (cPsi) )

(* Given i and tau, compute vector V
  s.t. for all k < i

  if k-th position in V = 0 then
     type at i-th position in tau does NOT depend on it

     k-th position in V = 1 then
     type at i-th position in tau does depend on it


  We then generate a spine of arguments using V; any position
  marked with 0 in V, will generate DC; positions marked with 1
  will generate a term M.
*)


let rec rec_spine cD (cM, cU)  (i, ttau) = match (i, ttau) with
  | (1 , (Comp.TypPiBox ((cdecl, _ ) , tau) , theta) ) ->
      begin try
        Unify.unifyCDecl cD (cU, Whnf.m_id) (cdecl, theta);
        ([Comp.M cM] , Whnf.cnormCTyp (tau, theta))
      with
          _ -> raise Not_compatible
      end

  | (1, (Comp.TypArr (Comp.TypBox (loc, tA, cPsi), tau), theta)) ->
      let u = Id.mk_name (Id.MVarName None) in
      let cdec = LF.MDecl(u, tA, cPsi) in
        begin try
          Unify.unifyCDecl cD (cU, Whnf.m_id) (cdec, theta);
          ([Comp.M cM] , Whnf.cnormCTyp (tau, theta))
        with
            _ -> raise Not_compatible
        end
  | (n ,  (Comp.TypPiBox ((cdecl, _ ) , tau) , theta) ) ->
      let (cN, ft)        = gen_var (Syntax.Loc.ghost) cD (Whnf.cnormCDecl (cdecl, theta)) in
      let (spine, tau_r)  = rec_spine cD (cM, cU) (n-1, (tau, LF.MDot (ft, theta))) in
        (Comp.M cN :: spine, tau_r)

  | (n, (Comp.TypArr (_, tau2), theta) ) ->
      let (spine, tau_r) = rec_spine cD (cM, cU) (n-1, (tau2, theta)) in
        (Comp.DC :: spine, tau_r)


let gen_meta_obj (cdecl, theta) k = match cdecl with
  | LF.CDecl (psi_name, schema_cid, _ ) ->
      Comp.MetaCtx (Syntax.Loc.ghost, LF.CtxVar (LF.CtxOffset (k+1) ))
(*  | LF.SDecl (s,cPhi, cPsi) -> todo *)
  | LF.MDecl (u, tA, cPsi) ->
      let phat  = Context.dctxToHat cPsi in
      let psihat' = Whnf.cnorm_psihat phat theta in
      let mv = LF.MVar (LF.Offset k, Substitution.LF.id) in
      let tM = LF.Root (Syntax.Loc.ghost, mv, LF.Nil) in
        Comp.MetaObj (Syntax.Loc.ghost, psihat', tM)

  | LF.PDecl (p, tA, cPsi) ->
      let phat  = Context.dctxToHat cPsi in
      let psihat' = Whnf.cnorm_psihat phat theta in
      let pv = LF.PVar (LF.Offset k, Substitution.LF.id) in
        Comp.MetaParam (Syntax.Loc.ghost, psihat', pv)

let rec gen_rec_calls cD cG (cD', k) = match cD' with
  | LF.Empty -> cG
  | LF.Dec (cD', cdecl) ->
      begin try
        let cM   = gen_meta_obj (cdecl, LF.MShift k) k in
        let _ = dprint (fun () -> "[gen_rec_calls] cM = " ^ P.metaObjToString cD cM) in
        let (f, x, ttau) = get_order () in
        let _ = dprint (fun () -> "[gen_rec_calls] f = " ^ P.compTypToString cD (Whnf.cnormCTyp ttau)) in
        let (args, tau) = rec_spine cD (cM, cdecl) (x,ttau) in
        let d = Comp.WfRec (f, args, tau) in
        let _ = print_string ("Recursive call : " ^ calls_to_string cD (f, args, tau) ^ "\n") in
          gen_rec_calls cD (LF.Dec(cG, d)) (cD', k+1)
      with
          _ -> gen_rec_calls cD cG (cD', k+1)
      end

let wf_rec_calls cD  =
  gen_rec_calls cD (LF.Empty) (cD, 1)



let rec filter cIH e2 = match e2, cIH with
  | _ , LF.Empty -> LF.Empty
  | Comp.M cM' , LF.Dec (cIH, Comp.WfRec (f , Comp.M cM :: args, Comp.TypPiBox ((_cdecl, _ ),tau'))) ->
      let cIH' = filter cIH e2 in
        if Whnf.convMetaObj cM' cM then
          LF.Dec (cIH', Comp.WfRec (f, args, tau'))
            (* Note: tau' is understood as the approximate type *)
        else
          cIH'

  | Comp.V y , LF.Dec (cIH,Comp.WfRec (f , Comp.V x :: args, Comp.TypArr (_tau, tau') )) ->
      let cIH' = filter cIH e2 in
        if x = y then
          LF.Dec (cIH', Comp.WfRec (f, args, tau'))
            (* Note: tau' is understood as the approximate type *)
        else
          cIH'
(* other cases are invalid /not valid recursive calls *)




(* check a recursive call in the program is wf

  f = recursive call in the initial state
  check for conversion between arguments applied to f in the "programm"
  and arguments in generated wf-call.

*)
