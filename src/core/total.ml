(* Checking termination of a function *)

open Syntax.Int
module Unify = Unify.StdTrail
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

type error =
  | NoPositiveCheck of string 
  | NoStratifyCheck of string 
  | WrongArgNum  of int

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) -> 
    Error.print_with_location loc (fun ppf ->
      match err with 
	| NoPositiveCheck n -> 

  	  Format.fprintf ppf "Datatype %s hasn't done positivity checking."  n (* (R.render_name n) *)
	| NoStratifyCheck n -> 
  	  Format.fprintf ppf "Datatype %s hasn't done stratification checking."  n (* (R.render_name n) *)
	| WrongArgNum n -> 
  	  Format.fprintf ppf "The argument number %d wrong."  n (* (R.render_name n) *)

    )
  )

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])

exception Not_compatible
exception CtxNot_compatible

let enabled = ref false

type rec_arg = M of Comp.meta_obj | V of Comp.exp_syn


let smaller_meta_obj cM = match  cM with
  | Comp.MetaCtx (_ , LF.DDec (_ , _ )) -> true
  | Comp.MetaObj (_, phat, LF.Root (_, h, _spine)) ->
      (match h with
        | LF.Const _ -> true
        | LF.BVar _ -> true
        | _ -> false)
  | Comp.MetaObjAnn (_, _cPsi, LF.Root (_, h, _spine)) ->
      (match h with
        | LF.Const _ -> true
        | LF.BVar _ -> true
        | _ -> false)
  | Comp.MetaParam (_, (Some _ , n), h ) ->
      if n > 0 then
        match h with LF.PVar (_, s) -> Whnf.convSub s (Substitution.LF.id)
          | _ -> false
      else
        false
  | _ -> false
(*  | Comp.MetaSObj (_, phat, s ) -> LF.SObj (phat, s)
  | Comp.MetaSObjAnn (_, cPsi, s ) -> LF.SObj (Context.dctxToHat cPsi, s)
*)


let rec struct_smaller patt = match patt with
  | Comp.PatMetaObj (loc', mO) -> smaller_meta_obj mO
  | Comp.PatConst (_, _, _ ) -> true
  | Comp.PatVar (_, _ ) -> false
  | Comp.PatPair (_, pat1, pat2 ) ->
      (* This is quite naive - possibly one of them being smaller is enough *)
      struct_smaller pat1 && struct_smaller pat2
  | Comp.PatAnn (_, pat, _) -> struct_smaller pat
  | _ -> false

type dec =
{name : Id.name ;
 args : (Id.name option) list;
 typ  : Comp.typ ;
 order: Order.order
}

let mutual_decs : (dec list) ref = ref []

let clear () = (mutual_decs :=  [])

let make_dec f tau (order,args) =
  { name = f;
    args = args;
    typ  = tau;
    order = order
  }

let extend_dec l =
mutual_decs := l::!mutual_decs

let mobjToFront cM = match cM with
  | Comp.MetaCtx (_ , cPsi) -> LF.CObj cPsi
  | Comp.MetaObj (_, phat, tM ) -> LF.MObj (phat, tM)
  | Comp.MetaObjAnn (_, cPsi, tM ) -> LF.MObj (Context.dctxToHat cPsi, tM)
  | Comp.MetaParam (_, phat, h ) -> LF.PObj (phat, h)
  | Comp.MetaSObj (_, phat, s ) -> LF.SObj (phat, s)
  | Comp.MetaSObjAnn (_, cPsi, s ) -> LF.SObj (Context.dctxToHat cPsi, s)

let rec args_to_string cD args = match args with
  | [] -> ""
  | (Comp.M cM)::args ->
      P.metaObjToString cD cM ^ " " ^
        args_to_string cD args
  | Comp.DC ::args ->
     " _ " ^
        args_to_string cD args
  | Comp.V _ ::args ->
     " (V _) " ^
        args_to_string cD args



let calls_to_string cD (f, args, tau) =
(*   (R.render_cid_prog f) ^ " " ^ *)
  (R.render_name f) ^ " " ^
    args_to_string cD args ^ " : "  ^
    P.compTypToString cD tau

let rec ih_to_string cD cIH = match cIH with
  | LF.Empty -> "\n"
  | LF.Dec(cIH, Comp.WfRec (f, args, tau) ) ->
   "IH: " ^  calls_to_string cD (f, args, tau) ^ "\n"
     ^ ih_to_string cD cIH


let get_order () =
  List.map (function dec ->
              let tau = dec.typ in
                (*  let _ = dprint (fun () -> "[get_order] " ^ (R.render_cid_prog dec.name) ^
                    " : " ^     P.compTypToString (LF.Empty) dec.typ) in *)
              let Order.Arg x = dec.order in
              let k = List.length (dec.args) in
                (dec.name, x, k, (tau, Whnf.m_id)))
    !mutual_decs


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


let rec rec_spine cD (cM, cU)  (i, k, ttau) =
  if i = 0 then
    match (k, ttau) with
      | (0, _ ) -> ([], Whnf.cnormCTyp ttau)
      | (n, (Comp.TypPiBox ( _ , tau), theta)) ->
          let (spine, tau_r) = rec_spine cD (cM,cU) (i, k-1, (tau,theta)) in
            (Comp.DC :: spine, tau_r)
      | (n, (Comp.TypArr (_, tau), theta)) ->
          let (spine, tau_r) = rec_spine cD (cM,cU) (i, k-1, (tau,theta)) in
            (Comp.DC :: spine, tau_r)
  else
    match (i, ttau) with
      | (1 , (Comp.TypPiBox ((cdecl, _ ) , tau) , theta) ) ->
          begin try
            Unify.unifyCDecl cD (cU, Whnf.m_id) (cdecl, theta);
            let ft = mobjToFront cM in
            let (spine, tau_r)  = rec_spine cD (cM, cU) (0, k-1, (tau, LF.MDot (ft, theta))) in
              (Comp.M cM::spine, tau_r )
          with
              _ -> raise Not_compatible
          end

  | (1, (Comp.TypArr (Comp.TypBox (loc, Comp.MetaTyp(tA, cPsi)), tau), theta)) ->
      let u = Id.mk_name (Id.MVarName None) in
      let cdec = LF.MDecl(u, tA, cPsi) in
        begin try
          Unify.unifyCDecl cD (cU, Whnf.m_id) (cdec, theta);
          let (spine, tau_r)  = rec_spine cD (cM, cU) (0, k-1,(tau, theta)) in
            (Comp.M cM::spine, tau_r )
        with
            _ -> raise Not_compatible
        end
  | (n ,  (Comp.TypPiBox ((cdecl, _ ) , tau) , theta) ) ->
      let (cN, ft)        = gen_var (Syntax.Loc.ghost) cD (Whnf.cnormCDecl (cdecl, theta)) in
      let (spine, tau_r)  = rec_spine cD (cM, cU) (n-1, k-1, (tau, LF.MDot (ft, theta))) in
        (Comp.M cN :: spine, tau_r)

  | (n, (Comp.TypArr (_, tau2), theta) ) ->
      let (spine, tau_r) = rec_spine cD (cM, cU) (n-1, k-1, (tau2, theta)) in
        (Comp.DC :: spine, tau_r)


let gen_meta_obj (cdecl, theta) k = match cdecl with
  | LF.CDecl (psi_name, schema_cid, _ ) ->
      Comp.MetaCtx (Syntax.Loc.ghost, LF.CtxVar (LF.CtxOffset k))
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

let uninstantiated_arg cM = match Whnf.cnormMetaObj (cM, Whnf.m_id) with
  | Comp.MetaCtx (_ , LF.CtxVar (LF.CInst _)) -> true
  | Comp.MetaObj (_, phat, LF.Root (_, h, _spine)) ->
      (match h with
        | LF.MMVar (_ , _ ) -> true
        | _ -> false)
  | Comp.MetaObjAnn (_, _cPsi, LF.Root (_, h, _spine)) ->
      (match h with
        | LF.MMVar (_ , _ ) -> true
        | _ -> false)
  | Comp.MetaParam (_, (Some _ , n), h ) ->
      if n > 0 then
        match h with LF.MPVar (_, _) -> true
          | _ -> false
      else
        false
  | Comp.MetaSObj (_, _phat, LF.MSVar (_, _ , _ )) -> true
  | Comp.MetaSObjAnn (_, _cPsi, LF.MSVar (_, _ , _ )) -> true
  | _ -> false

let rec generalize args = match args with
  | [] -> []
  | Comp.M cM :: args ->
      if uninstantiated_arg cM then
        Comp.DC :: generalize args
      else
        Comp.M cM :: generalize args
  | Comp.V x :: args ->
      Comp.V x:: generalize args
  | Comp.DC :: args ->
      Comp.DC :: generalize args

let rec gen_rec_calls cD cG (cD', j) = match cD' with
  | LF.Empty -> cG
  | LF.Dec (cD', cdecl) ->
      begin try
        let cM  = gen_meta_obj (cdecl, LF.MShift (j+1)) (j+1) in
        let cU  = Whnf.cnormCDecl (cdecl, LF.MShift (j+1)) in
        let _   = print_string ("[gen_rec_calls] cD = " ^ P.mctxToString cD
                                ^" -- j = " ^ string_of_int j ^ "\n\n") in
        let _   = print_string ("[gen_rec_calls] cM = " ^ P.metaObjToString cD cM
                                ^ " : " ^ P.cdeclToString cD cU
                                ^ "\n\n") in
        let mf_list = get_order () in
        let _ = List.iter (function (f,x,k,ttau) ->
                             print_string ( "[gen_rec_calls] for f = " ^
                                              P.compTypToString cD
                                              (Whnf.cnormCTyp ttau)
                                          ^ "\n\n"))
          mf_list
        in
        let mk_wfrec (f,x,k,ttau) =
          let (args, tau) = rec_spine cD (cM, cU) (x,k,ttau) in
          let args = generalize args in
          let d = Comp.WfRec (f, args, tau) in
          let _ = print_string ("\nRecursive call : " ^
                                  calls_to_string cD (f, args, tau)
                                ^ "\n") in
            d
        in
        let rec mk_all (cG,j) mf_list = match mf_list with
          | [] -> (cG, j)
          | (f,x,k,ttau)::mf_list ->
              let d = mk_wfrec (f,x,k,ttau) in
	      (* Check that generated call is valid - 
		 mostly this prevents cases where we have contexts not matching
		 a given schema *)
                mk_all (LF.Dec(cG, d), j+1) mf_list
        in
        let (cG',j') = mk_all (cG, j) mf_list in
          gen_rec_calls cD cG'  (cD', j')
      with
          Not_compatible ->
            gen_rec_calls cD cG (cD', j+1)
      end

let gen_rec_calls' cD cG cIH (cG, j) = match cG with
  | LF.Empty -> cIH
(*  | LF.Dec(cG',CTypDecl (_x, tau)) ->
      let x = Comp.Var (j+1) in
      let mf_list = get_order () in

*)

let wf_rec_calls cD cG  =
  if !enabled then
    let cIH = gen_rec_calls cD (LF.Empty) (cD, 0) in
      gen_rec_calls' cD cG cIH (cG, 0)
  else
    LF.Empty


(*  ------------------------------------------------------------------------ *) 
(* wkSub cPsi cPsi' = s 

   iff cPsi' is a prefix of cPsi and 
       cPsi |- s : cPsi'

*)
exception WkViolation 

let rec wkSub cPsi cPsi' = 
  if Whnf.convDCtx cPsi cPsi' then 
   Substitution.LF.id 
  else 
    (match cPsi with 
       | LF.DDec (cPsi0, _ ) -> 
	   Substitution.LF.comp  (wkSub cPsi0 cPsi') (Substitution.LF.shift)
       | _ -> raise (WkViolation)
    )

(* convDCtxMod cPsi cPsi' = sigma 
  
   iff
   
    cD |- cPsi ctx,  cD |- cPsi' ctx 
   and there exists a  variable substitution sigma s.t. 

   cPsi' |- sigma : cPsi   

   Note: this could be generalized to allow for subordination

*)
let convDCtxMod cD cPsi cPhi = 
  let cPhi', conv_list = ConvSigma.flattenDCtx cD cPhi in 
  let s_proj = ConvSigma.gen_conv_sub conv_list in 
    (*  cPhi |- s_proj : cPhi' *)
    begin try 
      let wk_sub = wkSub cPhi' cPsi in 
	(* cPhi' |- wk_sub cPsi *)
	  Some (Substitution.LF.comp wk_sub s_proj)
    with _ -> None
    end


let shiftMetaObj cM (cPsi', s_proj, cPsi) = 
  let phat  = Context.dctxToHat cPsi in 
  let phat0 = Context.dctxToHat cPsi in 
    match cM with 
      | Comp.MetaCtx (l, cPhi) -> 
	  if Whnf.convDCtx cPsi cPhi then 
	    Comp.MetaCtx (l, cPsi')
	  else 
	    cM
      | Comp.MetaObj (l , phat', tM) -> 
	  if Whnf.conv_hat_ctx phat phat' then 
	    Comp.MetaObj (l, phat0, Whnf.norm (tM, s_proj))
	  else 
	    cM
      | Comp.MetaParam (l, phat', tH) -> 
	  if Whnf.conv_hat_ctx phat phat' then 
	    let LF.Root (_, tH', _ ) = Whnf.norm (LF.Root (l, tH, LF.Nil), s_proj)  in 
	      Comp.MetaParam (l, phat0, tH')
	  else 
	    cM
      | Comp.MetaSObj (l, phat', s) -> 
	  if Whnf.conv_hat_ctx phat phat' then 
	    Comp.MetaSObj (l, phat0, Substitution.LF.comp s s_proj) 
	  else 
	    cM

let rec shiftArgs args (cPsi', s_proj, cPsi) = match args with 
  | [] -> []
  | Comp.DC :: args -> Comp.DC :: shiftArgs args (cPsi', s_proj, cPsi)
  | Comp.V x :: args ->  Comp.V x :: shiftArgs args (cPsi', s_proj, cPsi)
  | Comp.M cM :: args -> 
      let cM' = shiftMetaObj cM (cPsi', s_proj, cPsi) in 
	Comp.M cM' :: shiftArgs args (cPsi', s_proj, cPsi)

(*  ------------------------------------------------------------------------ *) 


(* filter cD cG cIH e2 = cIH' 

   if  cD      |- cIH  
       cD ; cG |- e2 

       and f e2' args in cIH 
       and e2' ~ e2  (size-equivalent)
  then 
       f args in cIH'

*)

let rec filter cD cG cIH e2 = match e2, cIH with
  | _ , LF.Empty -> LF.Empty
  (* We are treating contexts in the list of arguments supplied to the IH
     special to allow for context transformations which preserve the size
    *)
  | Comp.M (Comp.MetaCtx (_, cPsi)) , 
    LF.Dec (cIH, Comp.WfRec (f , Comp.M (Comp.MetaCtx (_,cPhi)) :: args, tau )) ->
    let cIH' = filter cD cG cIH e2 in
    let cPsi = Whnf.cnormDCtx (cPsi, Whnf.m_id) in 
    let cPhi = Whnf.cnormDCtx (cPhi, Whnf.m_id) in 
      if Whnf.convDCtx cPsi cPhi then 
	LF.Dec (cIH', Comp.WfRec (f, args, tau))
      else 
	(match convDCtxMod cD cPhi cPsi with
	  | Some s_proj ->  (*  cPsi |- s_proj : cPhi *)
	      let args' = shiftArgs args (cPsi, s_proj, cPhi) in 
	      (* let tau' = shiftCompTyp tau (cPsi, s_proj, cPhi) in  *)
		LF.Dec (cIH', Comp.WfRec (f, args', tau))
	  | None -> cIH'
	)

  | Comp.M cM' , LF.Dec (cIH, Comp.WfRec (f , Comp.M cM :: args, tau )) ->
    let cIH' = filter cD cG cIH e2 in
    if Whnf.convMetaObj cM' cM then
      (print_string  ("IH and recursive call agree on : "
                      ^ P.metaObjToString cD cM' ^ " == " ^
                      P.metaObjToString cD cM ^ "\n");
      LF.Dec (cIH', Comp.WfRec (f, args, tau)))
      (* Note: tau' is understood as the approximate type *)
    else
      (dprint (fun () -> ("IH and recursive call do NOT agree : "
        ^ P.metaObjToString cD cM' ^ " == " ^
          P.metaObjToString cD cM));
      cIH')

  | Comp.V y , LF.Dec (cIH,Comp.WfRec (f , Comp.V x :: args, tau )) ->
    let cIH' = filter cD cG cIH e2 in
    if x = y then
      LF.Dec (cIH', Comp.WfRec (f, args, tau))
      (* Note: tau is the overall return type of ih type
         and it is not the type of f args : tau *)
    else
      cIH'
  | _ , LF.Dec (cIH,Comp.WfRec (f , Comp.DC :: args, tau )) ->
    let cIH' = filter cD cG cIH e2 in
      LF.Dec (cIH', Comp.WfRec (f, args, tau))

(* other cases are invalid /not valid recursive calls *)




(* check a recursive call in the program is wf

  f = recursive call in the initial state
  check for conversion between arguments applied to f in the "programm"
  and arguments in generated wf-call.

*)



(* positivity checking *)
exception Unimplemented 
let rec no_occurs a tau =
  match tau with
    | Comp.TypBase (loc, c , _) ->
      not (a = c) &&
	( match (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity with 
	  | Sgn.Positivity -> true
	  | _ ->  let n =  R.render_cid_comp_typ c in
		  raise (Error (loc, (NoPositiveCheck n)))
	)
	(* ((Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity *)
	(*  || let n =  R.render_cid_comp_typ c in *)
        (*     raise (Error (loc, (NoPositiveCheck n))) *)
	(* ) *)
    | Comp.TypCobase _ ->  raise Unimplemented
    | Comp.TypDef  _  ->  raise Unimplemented
    | Comp.TypBox  _ -> true 
    | Comp.TypArr (tau1, tau2)   -> (no_occurs a tau1) && (no_occurs a tau2) 
    | Comp.TypCross (tau1, tau2) -> (no_occurs a tau1) && (no_occurs a tau2)
    | Comp.TypPiBox (_, tau')    ->  no_occurs a tau' 
    | Comp.TypClo   _            ->  raise Unimplemented
    | Comp.TypBool               -> true 

let rec check_positive a tau =
  match tau with
    | Comp.TypBase (loc, c , _) -> 
      (a = c) ||
      ( match (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity with 
	 | Sgn.Positivity -> true
	 | _ -> let n =  R.render_cid_comp_typ c in
		raise (Error (loc, (NoPositiveCheck n)))
      )
      (* (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity *)
      (* || let n =  R.render_cid_comp_typ c in *)
      (*    raise (Error (loc, (NoPositiveCheck n))) *)
    | Comp.TypCobase _  ->  raise Unimplemented
    | Comp.TypDef  _  -> raise Unimplemented
    | Comp.TypBox  _ -> true 
    | Comp.TypArr (tau1, tau2)   -> (no_occurs a tau1) && (check_positive a tau2) 
    | Comp.TypCross (tau1, tau2) -> (check_positive a tau1) && (check_positive a tau2)
    | Comp.TypPiBox (_, tau')    -> check_positive a tau' 
    | Comp.TypClo   _            ->  raise Unimplemented
    | Comp.TypBool               -> true 


let rec positive a tau =
  match tau with 
    | Comp.TypBase _  -> true
    | Comp.TypCobase _ -> true
    | Comp.TypDef  _  -> raise Unimplemented
    | Comp.TypBox _   -> true
    | Comp.TypArr (tau1, tau2)   -> (check_positive a tau1) && (positive a tau2) 
    | Comp.TypCross (tau1, tau2) -> (positive a tau1) && (positive a tau2)
    | Comp.TypPiBox (_, tau')    -> positive a tau' 
    | Comp.TypClo   _            ->  raise Unimplemented
    | Comp.TypBool               -> true 



(* stratification  *)


(*should compare *)

let rec less_dctx cPsi1 cPsi2 = 
  (* print_string ("let's start\n"); *)
  match cPsi1, cPsi2 with
    | LF.Null, LF.Null -> false  
    | LF.Null, _       -> true 
    | _ , LF.DDec (cPsi', _ )  -> Whnf.convDCtx cPsi1 cPsi' || less_dctx cPsi1 cPsi' 
    | _ , _    -> false
 
let rec less_phat phat1 phat2 = 
  (* print_string ("let's start2\n"); *)
  match phat1, phat2 with
    | (Some cv1, offset1), (Some cv2, offset2) -> cv1 = cv2 && offset1 < offset2
    | (None, offset1)    , (None, offset2)     -> offset1 < offset2
    | _ , _  -> false

let equal_meta_obj = Whnf.convMetaObj  
  (* match cM1, cM2 with *)
  (*   | Comp.MetaCtx (_, cPsi1),     Comp.MetaCtx (_, cPsi2) -> true *)
  (*   | Comp.MetaObj (_, phat1, n1), Comp.MetaObj (_, phat2, n2) -> true  *)
  (*   | _, _  -> false  *)


let rec less_meta_obj mObj1 mObj2 = 
  match mObj1, mObj2 with
    | Comp.MetaCtx (_, cPsi1), Comp.MetaCtx(_, cPsi2) -> less_dctx cPsi1 cPsi2

    | Comp.MetaObj (_, phat1, n1), Comp.MetaObj (loc2, phat2, n2) ->
      (match n2 with 
	| LF.Root(_, h , sp)  ->  
	  let rec leq_some_hat = fun spine -> 
	    ( match spine with 
	      | LF.App (n', spine') -> 
		leq_meta_obj mObj1 (Comp.MetaObj (loc2, phat2 , n')) || leq_some_hat spine'
	      | _ -> false
	    ) in  leq_some_hat sp
	| _  -> false
      ) 
      || ((less_phat phat1 phat2)   && (Whnf.conv (n1, Substitution.LF.id) (n2, Substitution.LF.id)) )  
      

    | Comp.MetaObjAnn (_, cPsi1, n1), Comp.MetaObjAnn ( loc2,  cPsi2, n2) -> 
      (match n2 with 
	| LF.Root(_, h , sp)  -> 
	  let rec leq_some_dctx = fun spine -> 
	    ( match spine with 
	      | LF.App (n', spine') -> 
		leq_meta_obj mObj1 (Comp.MetaObjAnn (loc2,  cPsi2 , n')) || leq_some_dctx spine'
	      | _ -> false
	    ) in  leq_some_dctx sp
	| _  -> false
      ) 
      || ((less_dctx  cPsi1  cPsi2)   && (Whnf.conv (n1, Substitution.LF.id) (n2, Substitution.LF.id)) )  

    | _ , _  -> false
  

and leq_meta_obj mObj1 mObj2 =
  equal_meta_obj mObj1 mObj2 || less_meta_obj mObj1 mObj2 
  || (match mObj2 with 
    | Comp.MetaObj    (loc , (cv , offset ), LF.Lam(_, x, n)) -> 
      leq_meta_obj mObj1 (Comp.MetaObj (loc,  (cv , offset + 1 ), n))
    | Comp.MetaObjAnn (loc , cPsi , LF.Lam(_, x, n)) -> 
      leq_meta_obj mObj1 (Comp.MetaObjAnn(loc, LF.DDec (cPsi, LF.TypDeclOpt x ) , n))
    | _ -> false
  ) 
  || (match mObj1 with 
    | Comp.MetaObj    (loc , (cv , offset ), LF.Lam(_, x, n)) -> 
      leq_meta_obj (Comp.MetaObj (loc,  (cv , offset + 1 ), n)) mObj2
    | Comp.MetaObjAnn (loc , cPsi , LF.Lam(_, x, n)) -> 
      leq_meta_obj (Comp.MetaObjAnn(loc, LF.DDec (cPsi, LF.TypDeclOpt x ) , n)) mObj2
    | _ -> false
  ) 


(*find the meta obj need to be compared*)
let rec find_meta_obj mspine  n =
  match (mspine, n) with
    | (Comp.MetaApp (obj, _), 0 ) -> print_string ((P.metaObjToString LF.Empty  obj)^"\n" ); obj
    | (Comp.MetaApp (obj, sp), _ ) -> find_meta_obj sp (n-1)
    | (Comp.MetaNil , _)  -> raise Not_compatible (* raise (Error (loc, (WrongArgNum n))) *)

let rec get_typfamily tau =
  match tau with
    | Comp.TypBase (_, _, mspine)  ->  mspine
    | Comp.TypArr (tau1, tau2)     ->  get_typfamily tau2
    | Comp.TypPiBox (_, tau')      ->  get_typfamily (Whnf.cnormCTyp (tau', LF.MShift (-1)) )
    | _   -> raise Not_compatible

let rec compare a tau n m =
  (* let  n1 = R.render_cid_comp_typ a in *)
  (* print_string (n1 ^ " = " ^ (string_of_int a)^"\n"); *)
  match  tau with
    | Comp.TypBase  (loc, c, mspine) ->
      (* print_string ("let's start3\n"); *)
      (* let  n2 = R.render_cid_comp_typ c in *)
      (* print_string (n2 ^ " = "^(string_of_int c)^" in\n"); *)
      not (a = c) ||
      less_meta_obj (find_meta_obj  mspine n)  m
    | Comp.TypArr   (tau1, tau2)  ->(compare a tau1 n m) && (compare a tau2 n m)
    | Comp.TypCross (tau1, tau2)  -> (compare a tau1 n m) && (compare a tau2 n m)
    | Comp.TypPiBox (_, tau')     -> (* print_string ("PiBox \n"); *)  compare a tau' n (Whnf.cnormMetaObj (m, LF.MShift 1) )
    | Comp.TypBox _    -> true
    | Comp.TypClo _    -> true
    | Comp.TypBool     -> true
    | Comp.TypCobase _ -> true
    | Comp.TypDef _    -> true
 

let rec stratify a tau n =
  let mspine = get_typfamily tau in
  let m = find_meta_obj mspine n  in
  match tau with
    | Comp.TypBase _   -> true
    | Comp.TypCobase _ -> true
    | Comp.TypDef  _   -> raise Unimplemented
    | Comp.TypBox  _   -> true
    | Comp.TypArr (tau1, tau2)   -> (compare a tau1 n m) && (stratify a tau2 n)
    | Comp.TypCross (tau1, tau2) -> (compare a tau1 n m) && (compare  a tau2 n m)
    | Comp.TypPiBox (_, tau')    -> stratify a tau' n
    | Comp.TypClo  _            -> raise Unimplemented
    | Comp.TypBool               -> true

 
