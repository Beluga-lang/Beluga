(* Checking termination of a function *)

open Syntax.Int
module Unify = Unify.StdTrail
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

type error =
  | NoPositiveCheck of string 
  | NoStratifyCheck of string 
  | WrongArgNum  of int
  | RecCallIncompatible of LF.mctx * Comp.args * Comp.ctyp_decl
  | NotImplemented of string

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
  	  Format.fprintf ppf "Datatype %s hasn't done positivity checking."  n (* (R.render_name n) *)
	| NoStratifyCheck n -> 
  	  Format.fprintf ppf "Datatype %s hasn't done stratification checking."  n (* (R.render_name n) *)
	| WrongArgNum n -> 
  	  Format.fprintf ppf "The argument number %d is wrong."  n (* (R.render_name n) *)
	| NotImplemented n      -> 
  	  Format.fprintf ppf "The case %s is not implemented yet."  n

    )
  )

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])

exception Not_compatible
exception CtxNot_compatible

let enabled = ref false

type rec_arg = M of Comp.meta_obj | V of Comp.exp_syn

let sub_smaller phat s = match phat , s with 
  | (_ , n) , LF.Shift (_, n') -> 
      (n-n') < n'
  | _ -> false

let rec smaller_meta_obj cM = match  cM with
  | Comp.MetaCtx (_ , LF.DDec (_ , _ )) -> true
  | Comp.MetaObj (l, phat, LF.Root (l', h, spine)) ->
      (match h with
        | LF.Const _ -> true
        | LF.BVar _ -> true
	| LF.PVar (_, s) -> 
	    (print_string "Checking whether pvar is smaller (0)\n";
	     match spine with 
	       | LF.Nil -> sub_smaller phat s
	       | _ -> true)
	| LF.Proj (h, _ ) -> 
	    (print_string "Checking whether proj is smaller (1)\n";
	    smaller_meta_obj (Comp.MetaObj (l, phat, LF.Root(l', h, spine))))
	| LF.MVar (_, s) -> sub_smaller phat  s
        | _ -> false)
  | Comp.MetaObjAnn (l, cPsi, LF.Root (l', h, spine)) ->
      (match h with
        | LF.Const _ -> true
        | LF.BVar _ -> true
	| LF.PVar (_, s) -> 
	    (print_string "Checking whether pvar is smaller (1)\n";
	     match spine with 
	       | LF.Nil -> sub_smaller (Context.dctxToHat cPsi) s
	       | _ -> true)
	| LF.Proj (h, _ ) -> 
	    (print_string "Checking whether proj is smaller (1)\n";
	    smaller_meta_obj (Comp.MetaObjAnn (l, cPsi, LF.Root(l', h, spine))))
	| LF.MVar (_, s) -> sub_smaller (Context.dctxToHat cPsi) s
	| _ -> false
      )
  | Comp.MetaParam (_, phat, h ) ->
      match h with 
	| LF.PVar (_, s) -> sub_smaller phat s
	| _ -> false
(*  | Comp.MetaSObj (_, phat, s ) -> LF.SObj (phat, s)
  | Comp.MetaSObjAnn (_, cPsi, s ) -> LF.SObj (Context.dctxToHat cPsi, s)
*)


let rec struct_smaller patt = match patt with
  | Comp.PatMetaObj (loc', mO) -> 
      smaller_meta_obj mO
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

let order_to_string order = match order with 
  | None -> " _ " 
  | Some (Order.Arg x) -> string_of_int x

let make_dec f tau (order,args) =
((* print_string ("Total declaration for " ^ 
R.render_name f ^ " : " ^ "total in position " ^ order_to_string order ^ 
" in total number of args " ^ string_of_int (List.length args) ^ "\n");*)
  { name = f;
    args = args;
    typ  = tau;
    order = order
  })

let extend_dec l =
mutual_decs := l::!mutual_decs


let exists_total_decl f = 
  let rec exists decs = match decs with 
    | [] -> false
    | l :: decs -> l.name = f || exists decs
  in 
    exists (!mutual_decs)


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
	    print_string ("rec_spine: Unify " ^ P.cdeclToString cD cU ^ 
			    "  with " ^ P.cdeclToString cD (Whnf.cnormCDecl (cdecl, theta)) ^ "\n");
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
        let cM  = gen_meta_obj (cdecl, LF.MShift (j+1)) (j+1) in
        let cU  = Whnf.cnormCDecl (cdecl, LF.MShift (j+1)) in
        let mf_list = get_order () in
	(* let _ = print_string ("Considering a total of " ^ 
				string_of_int (List.length mf_list)  ^ 
				" rec. functions\n") in *)
        let mk_wfrec (f,x,k,ttau) =
	  (* let _ = print_string ("mk_wf_rec ...for " ^ P.cdeclToString cD cU ^ 
				  " ") in 
	  let _ = print_string ("for position " ^ string_of_int x ^ 
				  " considering in total " ^ string_of_int k ^
				  "\n") in *)
          let (args, tau) = rec_spine cD (cM, cU) (x,k,ttau) in
          let args = generalize args in
          let d = Comp.WfRec (f, args, tau) in
          let _ = print_string ("\nRecursive call : " ^
                                  calls_to_string cD (f, args, tau)
                                ^ "\n\n") in
            d
        in
        let rec mk_all (cIH,j) mf_list = match mf_list with
          | [] -> cIH
	  | (f, None, _ , _ttau)::mf_list ->  mk_all (cIH, j) mf_list
          | (f, Some x, k, ttau)::mf_list ->
	      begin try 
		let d = mk_wfrec (f,x,k,ttau) in
		  (* Check that generated call is valid - 
		     mostly this prevents cases where we have contexts not matching
		     a given schema *)
                mk_all (LF.Dec(cIH, d),j) mf_list 
	      with 
		  Not_compatible -> mk_all (cIH,j) mf_list 
	      end
        in
        let cIH' = mk_all (cIH,j)  mf_list in
          gen_rec_calls cD cIH'  (cD', j+1)


let rec gen_rec_calls' cD cIH (cG0, j) = match cG0 with
  | LF.Empty -> cIH
  | LF.Dec(cG', Comp.CTypDecl (_x, tau)) ->
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
	      begin try 
		let d = mk_wfrec (f,x,k,ttau) in
		  (* Check that generated call is valid - 
		     mostly this prevents cases where we have contexts not matching
		     a given schema *)
		  mk_all (LF.Dec(cIH, d)) mf_list 
	      with
		  Not_compatible ->
		    mk_all cIH mf_list
	      end 
	in
	let cIH' = mk_all cIH mf_list in
          gen_rec_calls' cD cIH' (cG', j+1)

	


let wf_rec_calls cD cG  =
  if !enabled then
    ( (*print_string ("Generate recursive calls from \n" 
		     ^ "cD = " ^ P.mctxToString cD 
		     ^ "\ncG = " ^ P.gctxToString cD cG ^ "\n\n");*)
    let cIH = gen_rec_calls cD (LF.Empty) (cD, 0) in
      gen_rec_calls' cD cIH (cG, 0)) 
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
  match cPsi1, cPsi2 with
    | LF.Null, LF.Null -> false  
    | LF.Null, _       -> true 
    | _ , LF.DDec (cPsi', _ )  -> Whnf.convDCtx cPsi1 cPsi' || less_dctx cPsi1 cPsi' 
    | _ , _    -> false
 
(* let rec less_phat phat1 phat2 =  *)
(*   (\* print_string ("let's start2\n"); *\) *)
(*   let psi = Whnf.cnorm_psihat phat1 Whnf.m_id in *)
(*   let phi = Whnf.cnorm_psihat phat2 Whnf.m_id in  *)
(*   match psi, phi with *)
(*     | (Some cv1, offset1), (Some cv2, offset2) -> cv1 = cv2 && offset1 < offset2 *)
(*     | (None, offset1)    , (None, offset2)     -> offset1 < offset2 *)
(*     | _ , _  -> false *)

let  less_phat phat1 phat2 =
  match prefix_hat phat1 phat2 with
    | Some k -> k > 0
    | _ -> false 


let equal_meta_obj = Whnf.convMetaObj  
  (* match cM1, cM2 with *)
  (*   | Comp.MetaCtx (_, cPsi1),     Comp.MetaCtx (_, cPsi2) -> true *)
  (*   | Comp.MetaObj (_, phat1, tM1), Comp.MetaObj (_, phat2, tM2) -> true  *)
  (*   | _, _  -> false  *)


let rec less_meta_obj mC1 mC2 = 
  match mC1, mC2 with
    | Comp.MetaCtx (_, cPsi1), Comp.MetaCtx(_, cPsi2) -> less_dctx cPsi1 cPsi2

    | Comp.MetaObj (_, phat1, tM1), Comp.MetaObj (loc2, phat2, tM2) ->
      (match tM2 with
  	| LF.Root(_, h , tS)  ->
  	  let rec leq_some_hat = fun spine ->
  	    ( match spine with
  	      | LF.App (n', spine') ->
  		leq_meta_obj mC1 (Comp.MetaObj (loc2, phat2 , n')) || leq_some_hat spine'
  	      | _ -> false
  	    ) in  leq_some_hat tS
  	| _  -> false
      )
      || ((less_phat phat1 phat2)   && (Whnf.conv (tM1, Substitution.LF.id) (tM2, Substitution.LF.id)) )
      

    | Comp.MetaObjAnn (_, cPsi1, tM1), Comp.MetaObjAnn ( loc2,  cPsi2, tM2) ->
      (match tM2 with
  	| LF.Root(_, h , tS)  ->
  	  let rec leq_some_dctx = fun spine ->
  	    ( match spine with
  	      | LF.App (n', spine') ->
  		leq_meta_obj mC1 (Comp.MetaObjAnn (loc2,  cPsi2 , n')) || leq_some_dctx spine'
  	      | _ -> false
  	    ) in  leq_some_dctx tS
  	| _  -> false
      )
      || ((less_dctx  cPsi1  cPsi2)   && (Whnf.conv (tM1, Substitution.LF.id) (tM2, Substitution.LF.id)) )

  
    | Comp.MetaParam (_, phat1, tH1) , Comp. MetaParam (_, phat2, tH2) -> 
      (less_phat  phat1 phat2)   && (Whnf.convHead (tH1, Substitution.LF.id) (tH2, Substitution.LF.id)) 
    (* is the first rule still applied in this case?  *)

    | Comp.MetaSObj (loc1, _, _ ), Comp.MetaSObj (_, _ , _) -> raise (Error (loc1, NotImplemented "Comp.MetaSObj"))

    | Comp.MetaSObjAnn (loc1, _, _ ), Comp.MetaSObjAnn (_, _ , _) ->  raise (Error (loc1, NotImplemented "Comp.MetaSObjAnn"))

    | _ , _  -> false
  

and leq_meta_obj mC1 mC2 =
  equal_meta_obj mC1 mC2 || less_meta_obj mC1 mC2
  || (match mC2 with
    | Comp.MetaObj    (loc , (cv , offset ), LF.Lam(_, x, n)) ->
      leq_meta_obj mC1 (Comp.MetaObj (loc,  (cv , offset + 1 ), n))
    | Comp.MetaObjAnn (loc , cPsi , LF.Lam(_, x, n)) ->
      leq_meta_obj mC1 (Comp.MetaObjAnn(loc, LF.DDec (cPsi, LF.TypDeclOpt x ) , n))
    | _ -> false
  )
  || (match mC1 with
    | Comp.MetaObj    (loc , (cv , offset ), LF.Lam(_, x, n)) ->
      leq_meta_obj (Comp.MetaObj (loc,  (cv , offset + 1 ), n)) mC2
    | Comp.MetaObjAnn (loc , cPsi , LF.Lam(_, x, n)) ->
      leq_meta_obj (Comp.MetaObjAnn(loc, LF.DDec (cPsi, LF.TypDeclOpt x ) , n)) mC2
    | _ -> false
  )


(*find the meta obj needs to be compared*)
let rec find_meta_obj cD mS n =
  match mS, n with
    | Comp.MetaApp (mC, _)  , 1   -> (cD, mC) (* print_string ((P.metaObjToString LF.Empty  obj)^"\n" ); *) 
    | Comp.MetaApp (mC, mS'), _   -> find_meta_obj cD mS' (n-1)
    | Comp.MetaNil          , _   -> raise Not_compatible (* raise (Error (loc, (WrongArgNum n))) *)

let rec get_typbase cD tau =
  match tau with
    | Comp.TypBase (_, _, mS)      -> (* print_string ((P.mctxToString cD)^"\n" ); *)(cD,  mS)
    | Comp.TypArr (tau1, tau2)     ->   get_typbase cD tau2
    | Comp.TypPiBox ((dec,_), tau')    ->   get_typbase (LF.Dec (cD, dec)) tau'
    | _   -> raise Not_compatible



let rec ctxlength cD = 
  match cD with
    | LF. Empty -> 0
    | LF. Dec (cD', _) -> ctxlength cD' + 1

(* compare a (cD1', tau1) n (cD2, mC2) cD0 = bool 
if type_family(tau1) = a 
   cD  |- tau : ctype 
   cD0 |- mC

*)

let rec compare a (cD1',tau1) n (cD2, mC2) cD0= 
  match  tau1 with
    | Comp.TypBase  (loc, c, mS) ->
      not (a = c) ||     
	(*  cD1  = cD0, cDa *)
	(*  cD2  = cD0, cDb *)
	(* k0 = | cD0 | *)
	(* k1 = | cD1 | *)
	(* k2 = | cD2 | *)
	let (cD1, mC1) =  find_meta_obj cD1' mS n in

	let k0  = ctxlength cD0  in
	let k1  = ctxlength cD1  in
	let k2  = ctxlength cD2  in	
	
	let _ = dprint (fun () -> ("cD1 : " ^ (P.mctxToString  cD1) ^ "\n" ) ^
	  ("cD2 : " ^ (P.mctxToString  cD2) ^ "\n" ) ^
	  ("cD0 : " ^ (P.mctxToString  cD0) ^ "\n" ) ^
	  ((P.metaObjToString cD1  mC1 )^"  shift offset:"^(string_of_int (k1-k0))^"\n" )^ 
	  ((P.metaObjToString cD2  mC2) ^"  shift offset:"^(string_of_int (k2-k0))^"\n" ) )in

	
	let mC1 = Whnf.cnormMetaObj   (mC1 , LF.MShift  (k0-k1)) in
	let mC2 = Whnf.cnormMetaObj   (mC2 , LF.MShift  (k0-k2)) in
	

	let _ = dprint (fun () -> 
	  ("mC1: " ^  (P.metaObjToString cD0  mC1)^"\n" ) ^
	  ("mC2: " ^  (P.metaObjToString cD0  mC2)^"\n" ) ) in
	let _ = dprint (fun () -> 
	  ("meta mC1: " ^  (P.metaObjToString LF.Empty  mC1)^"\n" ) ^
	  ("meta mC2: " ^  (P.metaObjToString LF.Empty  mC2)^"\n" ) ) in

	
	less_meta_obj mC1 mC2

    | Comp.TypArr   (tau, tau')  -> (compare a (cD1', tau) n (cD2, mC2) cD0) && (compare a (cD1', tau') n (cD2, mC2) cD0)
    | Comp.TypCross (tau, tau')  -> (compare a (cD1', tau) n (cD2, mC2) cD0) && (compare a (cD1', tau') n (cD2, mC2) cD0)
    | Comp.TypPiBox ((dec,_), tau)   -> compare a (LF.Dec (cD1', dec), tau)  n  (cD2, mC2) cD0
    | Comp.TypBox _    -> true
    | Comp.TypClo _    -> true
    | Comp.TypBool     -> true
    | Comp.TypCobase _ -> true
    | Comp.TypDef _    -> true
 

(* stratify a tau n = bool 

Preconditions:
    |- tau : ctype
    type_family (tau) = a, i.e. the target type of tau has type family a
    n is the position of an argument given to the type family s
   
if  all occurrence of the type family a in tau are stratified in n
then return true
false otherwise

*)
let stratify a tau n =
  let (cD, mS) = get_typbase LF.Empty tau in
  let cD_mC = find_meta_obj cD mS n  in
  let rec strat cD0 tau0 = 
    match tau0 with
      | Comp.TypBase _   -> true
      | Comp.TypCobase _ -> true
      | Comp.TypDef  _   -> raise Unimplemented
      | Comp.TypBox  _   -> true
      | Comp.TypArr   (tau1, tau2)   -> (compare a (cD0,tau1) n cD_mC cD0) && (strat cD0 tau2)
      | Comp.TypCross (tau1, tau2)   -> (compare a (cD0,tau1) n cD_mC cD0) && (compare a (cD0,tau2) n cD_mC cD0)
      | Comp.TypPiBox ((dec,_), tau')    ->  strat (LF.Dec (cD0, dec)) tau'
      | Comp.TypClo  _            -> raise Unimplemented
      | Comp.TypBool               -> true
  in 
  strat LF.Empty tau

let rec mS_size mS = 
  match mS with
    | Comp.MetaApp (mC, mS')   -> mS_size mS' + 1
    | Comp.MetaNil             -> 0


  

let stratifyAll a tau =
  let (cD, mS) = get_typbase LF.Empty tau in
  let mSize = mS_size mS in
  let rec stratAll n =
     (n>=1) &&  ((stratify a tau n) || stratAll (n-1))
  in stratAll mSize
