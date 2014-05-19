(* Checking termination of a function *)

open Syntax.Int
module Unify = Unify.StdTrail
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer


type error =
  | NoPositiveCheck of string 
  | RecCallIncompatible of LF.mctx * Comp.args * Comp.ctyp_decl

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) -> 
    Error.print_with_location loc (fun ppf ->
      match err with 
	| RecCallIncompatible (cD, x, Comp.WfRec (f, args, _tau)) -> 
	    (match x , args with 
	       | _ , [] -> 
		   Format.fprintf ppf "Recursive call is incompatible with valid automatically generated recursive calls. \n Report as a bug."
	       | Comp.M cM  , (Comp.M cM' :: _ ) -> 
		   Format.fprintf ppf "Recursive call is incompatible with valid automatically generated recursive calls. \nBeluga cannot establish that the given recursive call is a size-preserving variant of it.\nArgument found: %a@\nArgument expected: %a@"
		     (P.fmt_ppr_meta_obj cD Pretty.std_lvl) cM
		     (P.fmt_ppr_meta_obj cD Pretty.std_lvl) cM'

	       | Comp.M cM  , (Comp.V _ :: _ ) -> 
		   Format.fprintf ppf "Recursive call is incompatible with valid automatically generated recursive calls. \n\nArgument found: %a@\nExpected computation-level variable.\n\nCheck specified totality declaration. "
		     (P.fmt_ppr_meta_obj cD Pretty.std_lvl) cM

	       | Comp.V _ , _ -> 
		   Format.fprintf ppf "Recursive call is incompatible with valid automatically generated recursive calls. \n\n Found computation-level variable while generated recursive call expected a meta-object.\n\nCheck specified totality declaration."
	    )
	| NoPositiveCheck n -> 
  	  Format.fprintf ppf "Datatype %s has not been checked for positivity."  n (* (R.render_name n) *)
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
 order: Order.order option
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
		match dec.order with
		  | Some (Order.Arg x) -> 
		      let k = List.length (dec.args) in
			(dec.name, Some x, k, (tau, Whnf.m_id))
		  | None -> (dec.name, None, 0, (tau, Whnf.m_id))
	   )
    !mutual_decs


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



let rec rec_spine' cD (x, tau)  (i, k, ttau) =
  if i = 0 then
    match (k, ttau) with
      | (0, _ ) -> ([], Whnf.cnormCTyp ttau)
      | (n, (Comp.TypPiBox ( _ , tau), theta)) ->
          let (spine, tau_r) = rec_spine' cD (x,tau) (i, k-1, (tau,theta)) in
            (Comp.DC :: spine, tau_r)
      | (n, (Comp.TypArr (_, tau), theta)) ->
          let (spine, tau_r) = rec_spine' cD (x,tau) (i, k-1, (tau,theta)) in
            (Comp.DC :: spine, tau_r)
  else
    match (i, ttau) with
      | (1 , (Comp.TypPiBox ((cdecl, _ ) , tau) , theta) ) ->
	  raise Not_compatible (* Error *)

  | (1, (Comp.TypArr (tau1, tau2), theta)) -> 
        begin try
          Unify.unifyCompTyp cD (tau, Whnf.m_id) (tau1, theta);
          let (spine, tau_r)  = rec_spine' cD (x, tau) (0, k-1,(tau2, theta)) in
            (Comp.V x::spine, tau_r )
        with
            _ -> raise Not_compatible
        end
  | (n ,  (Comp.TypPiBox ((cdecl, _ ) , tau) , theta) ) ->
      let (cN, ft)        = gen_var (Syntax.Loc.ghost) cD (Whnf.cnormCDecl (cdecl, theta)) in
      let (spine, tau_r)  = rec_spine' cD (x,tau) (n-1, k-1, (tau, LF.MDot (ft, theta))) in
        (Comp.M cN :: spine, tau_r)

  | (n, (Comp.TypArr (_, tau2), theta) ) ->
      let (spine, tau_r) = rec_spine' cD (x,tau) (n-1, k-1, (tau2, theta)) in
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

let rec gen_rec_calls cD cIH (cD', j) = match cD' with
  | LF.Empty -> cIH
  | LF.Dec (cD', cdecl) ->
      begin try
        let cM  = gen_meta_obj (cdecl, LF.MShift (j+1)) (j+1) in
        let cU  = Whnf.cnormCDecl (cdecl, LF.MShift (j+1)) in
        let mf_list = get_order () in
        let mk_wfrec (f,x,k,ttau) =
          let (args, tau) = rec_spine cD (cM, cU) (x,k,ttau) in
          let args = generalize args in
          let d = Comp.WfRec (f, args, tau) in
          let _ = print_string ("\nRecursive call : " ^
                                  calls_to_string cD (f, args, tau)
                                ^ "\n\n") in
            d
        in
        let rec mk_all (cIH,j) mf_list = match mf_list with
          | [] -> (cIH, j)
	  | (f, None, _ , _ttau)::mf_list ->  mk_all (cIH, j) mf_list
          | (f, Some x, k, ttau)::mf_list ->
              let d = mk_wfrec (f,x,k,ttau) in
	      (* Check that generated call is valid - 
		 mostly this prevents cases where we have contexts not matching
		 a given schema *)
                mk_all (LF.Dec(cIH, d), j+1) mf_list (* ? why j + 1 ? *)
        in
        let (cIH',j') = mk_all (cIH, j) mf_list in
          gen_rec_calls cD cIH'  (cD', j')
      with
          Not_compatible ->
            gen_rec_calls cD cIH (cD', j+1)
      end

let rec gen_rec_calls' cD cIH (cG0, j) = match cG0 with
  | LF.Empty -> cIH
  | LF.Dec(cG', Comp.CTypDecl (_x, tau)) ->
      begin try 
	let y = j+1 in
	let mf_list = get_order () in
	let mk_wfrec (f,x,k, ttau) = 
	  let (args, tau) = rec_spine' cD (y, tau) (x,k,ttau) in 
	  let args = generalize args in 
	  let d = Comp.WfRec (f, args, tau) in 
          let _ = print_string ("\nRecursive call : " ^
                                  calls_to_string cD (f, args, tau)
                                ^ "\n\n") in
	    d 
	in 
	let rec mk_all cIH mf_list = match mf_list with
          | [] -> cIH
	  | (f, None, _ , _ttau)::mf_list ->  mk_all cIH mf_list
          | (f, Some x, k, ttau)::mf_list ->
              let d = mk_wfrec (f,x,k,ttau) in
		(* Check that generated call is valid - 
		   mostly this prevents cases where we have contexts not matching
		   a given schema *)
		mk_all (LF.Dec(cIH, d)) mf_list 
	in
	let cIH' = mk_all cIH mf_list in
          gen_rec_calls' cD cIH' (cG', j+1)
      with
          Not_compatible ->
            gen_rec_calls' cD cIH (cG', j+1)
      end
	


let wf_rec_calls cD cG  =
  if !enabled then
    let cIH = gen_rec_calls cD (LF.Empty) (cD, 0) in
      gen_rec_calls' cD cIH (cG, 0)
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


(* weakSub cPsi cPsi' = s 

   iff cPsi' is a subset of cPsi and 
       cPsi |- s : cPsi'
 
*)
(* pos cPsi tA k = k' 
  
   if cPsi0 = cPsi, x1:tB1, .., xk:tBk 
    and k' is the position of the declaration (y:tA) in cPsi0


   i.e.  (k'-k) is the position of (y:tA) in cPsi

   NOTE: there might be more than one declaration in cPsi with type tA;
   this will return the rightmost position. We do not compute all possible
   positions.
*)
let rec pos cPsi tA k = match cPsi with 
  (* cPsi |- tA *)
  | LF.Null     -> None
  | LF.CtxVar _ -> None
  | LF.DDec (cPsi, LF.TypDecl (_x, tB)) -> 
      if Whnf.convTyp (tA, Substitution.LF.invShift) (tB, Substitution.LF.id) then
	Some (k)
      else 
	pos cPsi (Whnf.normTyp (tA, Substitution.LF.invShift)) (k+1)

let rec weakSub cD cPsi cPsi' = 
  if Whnf.convDCtx cPsi cPsi' then 
   Substitution.LF.id 
  else 
    (match cPsi' with 
       | LF.DDec (cPsi', LF.TypDecl (x, tA)) -> 
	   let s = weakSub cD cPsi cPsi' in (*  cPsi |- s : cPsi' *)
	   let _ = print_string ("Is " ^ P.typToString cD cPsi' (tA, Substitution.LF.id)
	     ^ "\n in " ^ P.dctxToString cD cPsi ^ " ? \n") in
	   (match pos cPsi (Whnf.normTyp (tA,s)) 1 with 
	      | Some k ->  
		  (print_string (" Found at " ^ string_of_int k ^ "\n");
		  LF.Dot( LF.Head (LF.BVar k), s))
	      | None -> print_string (" Not Found.\n") ; raise WkViolation)
       | _ -> LF.Shift (LF.NoCtxShift, Context.dctxLength cPsi))

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
    with _ -> 
      try 
	let _ = (print_string "[convDCtxMod] compute possible weakening substitution which allows for permutations : \n" ;
		 print_string (" cPsi = " ^ P.dctxToString cD cPsi ^ "\n");
		 print_string (" cPhi' = " ^ P.dctxToString cD cPhi' ^ "\n") ) in
      let wk_sub = weakSub cD cPhi' cPsi in 
	  Some (Substitution.LF.comp wk_sub s_proj)
      with _ -> None
    end


let prefix_hat phat phat' = match phat, phat' with
  | (None, k) , (None, k') -> Some (k' - k )
  | (Some (LF.CtxOffset g), k) , (Some (LF.CtxOffset g'), k') -> 
      if g = g' then Some (k' - k )
      else None
  | _, _ -> None


let rec dot_k s k = if k = 0 then s
else dot_k (Substitution.LF.dot1 s) (k-1)


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
	  (match prefix_hat (Whnf.cnorm_psihat phat Whnf.m_id) 
 	                    (Whnf.cnorm_psihat phat' Whnf.m_id)  with 
	    | None -> cM 
	    | Some k -> 
		Comp.MetaObj (l, phat0, Whnf.norm (tM, dot_k s_proj k)))
	  (* phat' >= phat, i.e.  phat is a prefix of phat' possibly *)
(*	  if Whnf.conv_hat_ctx phat phat' then 
	    Comp.MetaObj (l, phat0, Whnf.norm (tM, s_proj))
	  else 
	    cM *)
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

let rec filter cD cG cIH (loc, e2) = match e2, cIH with
  | _ , LF.Empty -> LF.Empty
  (* We are treating contexts in the list of arguments supplied to the IH
     special to allow for context transformations which preserve the size
    *)
  | Comp.M (Comp.MetaCtx (_, cPsi)) , 
    LF.Dec (cIH, Comp.WfRec (f , Comp.M (Comp.MetaCtx (_,cPhi)) :: args, tau )) ->
    let cIH' = filter cD cG cIH (loc, e2) in
    let cPsi = Whnf.cnormDCtx (cPsi, Whnf.m_id) in 
    let cPhi = Whnf.cnormDCtx (cPhi, Whnf.m_id) in 
    let _ = print_string ("MetaCtx : FOUND " ^ P.dctxToString cD cPhi ^
			    "\n           EXPECTED " ^ P.dctxToString cD cPsi ^ "\n\n") in
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
    let cIH' = filter cD cG cIH (loc, e2) in
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
    let cIH' = filter cD cG cIH (loc, e2) in
    if x = y then
      LF.Dec (cIH', Comp.WfRec (f, args, tau))
      (* Note: tau is the overall return type of ih type
         and it is not the type of f args : tau *)
    else
      cIH'
  | _ , LF.Dec (cIH,Comp.WfRec (f , Comp.DC :: args, tau )) ->
    let cIH' = filter cD cG cIH (loc, e2) in
      LF.Dec (cIH', Comp.WfRec (f, args, tau))

  | x, LF.Dec (cIH, wf) -> 
      raise (Error (loc, RecCallIncompatible (cD, x, wf)))
(* other cases are invalid /not valid recursive calls *)




(* check a recursive call in the program is wf

  f = recursive call in the initial state
  check for conversion between arguments applied to f in the "programm"
  and arguments in generated wf-call.

*)

(*  ------------------------------------------------------------------------ *) 

(* positivity checking *)

exception Unimplemented 

let rec no_occurs a tau =
  match tau with
    | Comp.TypBase (loc, c , _) ->
      not (a = c) &&
	((Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity
	 || let n =  R.render_cid_comp_typ c in
            raise (Error (loc, (NoPositiveCheck n)))
	)
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
      (a = c) 
      || (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity
      || let n =  R.render_cid_comp_typ c in
         raise (Error (loc, (NoPositiveCheck n)))
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

