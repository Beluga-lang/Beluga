open Id

open Store
open Store.Cid
open Syntax

module C = Whnf
module S = Substitution
module Unify = Unify.StdTrail

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer
module RR = Store.Cid.NamedRenderer

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [11])

type error =
  | UnexpectedSucess
  | IllegalOptsPrag

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
	| UnexpectedSucess ->
	  Format.fprintf ppf "Unexpected success: expected failure of type reconstruction for %%not'ed declaration."
        | IllegalOptsPrag ->
          Format.fprintf ppf "%%opts pragma can only appear before any declarations."))

let rec lookupFun cG f = match cG with
  | Int.LF.Dec (cG', Int.Comp.CTypDecl (f',  tau)) ->
      if f = f' then tau else
      lookupFun cG' f

let rec get_target_cid_comptyp tau = match tau with
  | Int.Comp.TypBase (_, a, _ ) -> a
  | Int.Comp.TypArr (_ , tau) -> get_target_cid_comptyp tau
  | Int.Comp.TypPiBox (_, tau) -> get_target_cid_comptyp tau

let rec get_target_cid_compcotyp tau = match tau with
  | Int.Comp.TypCobase (_, a, _ ) -> a
  | Int.Comp.TypArr (tau , _) -> get_target_cid_compcotyp tau
  | Int.Comp.TypPiBox (_, tau) -> get_target_cid_compcotyp tau

let freeze_from_name tau = match tau with
  |Ext.Sgn.Typ ( _, n, _) ->  let a = Typ.index_of_name n in
                               Typ.freeze a;
                               ()
  |Ext.Sgn.CompTyp (_, n, _) -> let a =   CompTyp.index_of_name n in
                               CompTyp.freeze a;
                               ()
   |Ext.Sgn.CompCotyp (_, n, _) -> let a =   CompCotyp.index_of_name n in
                               CompCotyp.freeze a;
                                ()


let rec recSgnDecls = function
  | [] -> ()

  | Ext.Sgn.Pragma(loc, Ext.Sgn.NotPrag) :: not'd_decl :: rest ->
    let not'd_decl_succeeds =
      begin
	try
	  recSgnDecl not'd_decl; true
	with _ ->
	  if !Debug.chatter != 0 then
	    print_string ("Reconstruction fails for %not'd declaration\n");
          false
      end in
    if not'd_decl_succeeds
    then raise (Error (loc, UnexpectedSucess))
    else recSgnDecls rest

  (* %not declaration with nothing following *)
  | [Ext.Sgn.Pragma(_, Ext.Sgn.NotPrag)] -> ()

  | Ext.Sgn.Pragma(loc, Ext.Sgn.OptsPrag _) :: rest ->
    raise (Error (loc, IllegalOptsPrag))

  | decl :: rest ->
    recSgnDecl decl;
    recSgnDecls rest

and recSgnDecl d =
    Reconstruct.reset_fvarCnstr ();  FCVar.clear ();
    match d with
    | Ext.Sgn.CompTypAbbrev (loc, a, cK, cT) ->
        let _ = dprint (fun () -> "\nIndexing computation-level data-type constant " ^ a.string_of_name) in
        (* index cT  in a context which contains arguments to cK *)
        let (apx_tau, apxK) = Index.comptypdef  (cT, cK) in

        let ((cD,tau), i, cK) = Reconstruct.comptypdef loc a (apx_tau, apxK) in
	let _         = dprint (fun () ->  "typedef " ^ a.string_of_name ^ " : " ^
                                  (P.compKindToString Int.LF.Empty cK) ^ " = " ^
				   (P.compTypToString cD tau)) in
	let _         = (Monitor.timer ("Type abbrev. : Kind Check",
					fun () -> Check.Comp.checkKind Int.LF.Empty cK)) in
	let _         = (Monitor.timer ("Type abbrev. : Type Check",
					fun () -> Check.Comp.checkTyp cD tau)) in
        let _a = CompTypDef.add (CompTypDef.mk_entry a i (cD,tau) cK) in ()

    | Ext.Sgn.CompTyp (_ , a, extK) ->
        let _ = dprint (fun () -> "\nIndexing computation-level data-type constant " ^ a.string_of_name) in
        let apxK = Index.compkind extK in
        let _ = FVar.clear () in
        let _ = dprint (fun () -> "\nElaborating data-type declaration " ^ a.string_of_name) in
        let cK = Monitor.timer ("CType Elaboration" ,
                               (fun () -> let cK = Reconstruct.compkind apxK in
                                  Reconstruct.solve_fvarCnstr Lfrecon.Pibox; cK
                               )) in
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let (cK', i) = Monitor.timer ("Type Abstraction",
                                      fun () -> Abstract.compkind cK) in

        let _        = (Reconstruct.reset_fvarCnstr ();
			Unify.resetGlobalCnstrs ();
			dprint (fun () ->  a.string_of_name ^
				  " : " ^  (P.compKindToString Int.LF.Empty cK'))) in
	  Monitor.timer ("Type Check",
            fun () -> Check.Comp.checkKind  Int.LF.Empty cK');
	    dprint (fun () ->  "\nDOUBLE CHECK for data type constant " ^a.string_of_name ^
            " successful!");
        let _a = CompTyp.add (CompTyp.mk_entry a cK' i) in
          (if (!Debug.chatter) == 0 then ()
          else (Format.printf "\ndatatype %s : @[%a@] = \n"
                 (a.string_of_name)
                 (P.fmt_ppr_cmp_kind Int.LF.Empty Pretty.std_lvl) cK'))


  | Ext.Sgn.CompCotyp (_ , a, extK) ->
        let _ = dprint (fun () -> "\nIndexing computation-level codata-type constant " ^ a.string_of_name) in
        let apxK = Index.compkind extK in
        let _ = FVar.clear () in
        let _ = dprint (fun () -> "\nElaborating codata-type declaration " ^ a.string_of_name) in
        let cK = Monitor.timer ("CType Elaboration" ,
                               (fun () -> let cK = Reconstruct.compkind apxK in
                                  Reconstruct.solve_fvarCnstr Lfrecon.Pibox; cK
       )) in
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let (cK', i) = Monitor.timer ("Type Abstraction",
                                      fun () -> Abstract.compkind cK) in

        let _        = (Reconstruct.reset_fvarCnstr ();
                        Unify.resetGlobalCnstrs ();
                        dprint (fun () ->  a.string_of_name ^
                                  " : " ^  (P.compKindToString Int.LF.Empty cK'))) in
          Monitor.timer ("Type Check",
            fun () -> Check.Comp.checkKind  Int.LF.Empty cK');
            dprint (fun () ->  "\nDOUBLE CHECK for codata type constant " ^a.string_of_name ^
            " successful!");
        let _a = CompCotyp.add (CompCotyp.mk_entry a cK' i) in ()


    | Ext.Sgn.CompConst (_ , c, tau) ->
        let _         = dprint (fun () -> "\nIndexing computation-level data-type constructor " ^ c.string_of_name) in
        let apx_tau   = Index.comptyp tau in
        let cD        = Int.LF.Empty in
        let _         = dprint (fun () -> "\nElaborating data-type constructor " ^ c.string_of_name) in
        let tau'      = Monitor.timer ("Data-type Constant: Type Elaboration",
				       fun () -> Reconstruct.comptyp apx_tau)  in
        let _         = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
	let _         = dprint (fun () -> "Abstracting over comp. type") in
        let (tau', i) = Monitor.timer ("Data-type Constant: Type Abstraction",
				       fun () -> Abstract.comptyp tau') in
	let _         = dprint (fun () -> "Abstracting over comp. type: done") in
	let _         = dprint (fun () ->  c.string_of_name ^ " : " ^
				   (P.compTypToString cD tau')) in
	let _         = (Monitor.timer ("Data-type Constant: Type Check",
					fun () -> Check.Comp.checkTyp cD tau'))
        in	let cid_ctypfamily = get_target_cid_comptyp tau' in
        let _c        = CompConst.add cid_ctypfamily (CompConst.mk_entry c tau' i) in
          (if (!Debug.chatter) == 0 then ()
           else (Format.printf " | %s : @[%a@] \n"
                   (c.string_of_name)
                   (P.fmt_ppr_cmp_typ Int.LF.Empty Pretty.std_lvl) tau'))



   | Ext.Sgn.CompDest (_ , c, tau) ->
        let _         = dprint (fun () -> "\nIndexing computation-level codata-type destructor " ^ c.string_of_name) in
        let apx_tau   = Index.comptyp tau in
        let cD        = Int.LF.Empty in
        let _         = dprint (fun () -> "\nElaborating codata-type destructor " ^ c.string_of_name) in
        let tau'      = Monitor.timer ("Codata-type Constant: Type Elaboration",
                                       fun () -> Reconstruct.comptyp apx_tau)  in
        let _         = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let _         = dprint (fun () -> "Abstracting over comp. type") in
        let (tau', i) = Monitor.timer ("Codata-type Constant: Type Abstraction",
                                       fun () -> Abstract.comptyp tau') in
        let _         = dprint (fun () -> "Abstracting over comp. type: done") in
        let _         = dprint (fun () ->  c.string_of_name ^ " : " ^
                                   (P.compTypToString cD tau')) in
        let _         = (Monitor.timer ("Codata-type Constant: Type Check",
                                        fun () -> Check.Comp.checkTyp cD tau'))
        in      let cid_ctypfamily = get_target_cid_compcotyp tau' in
        let _c        = CompDest.add cid_ctypfamily (CompDest.mk_entry c tau' i) in ()


    | Ext.Sgn.Typ (_, a, extK)   ->
        let _        = dprint (fun () -> "\nIndexing type constant " ^ a.string_of_name) in
        let (apxK, _ ) = Index.kind extK in
        let _        = FVar.clear () in

        let _        = dprint (fun () -> "\nElaborating type constant " ^ a.string_of_name) in

        let tK       = Monitor.timer ("Type Elaboration",
                                      fun () -> (let tK = Reconstruct.kind apxK in
                                                   Reconstruct.solve_fvarCnstr Lfrecon.Pi; tK )) in

        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in

        let (tK', i) = Monitor.timer ("Type Abstraction",
                                      fun () -> Abstract.kind tK) in
        let _        = (Reconstruct.reset_fvarCnstr ();
			Unify.resetGlobalCnstrs ();
			dprint (fun () ->  a.string_of_name ^ " : " ^  (P.kindToString Int.LF.Null (tK', S.LF.id)));
			Monitor.timer ("Type Check",
				       fun () -> Check.LF.checkKind Int.LF.Empty Int.LF.Null tK');
			dprint (fun () ->  "\nDOUBLE CHECK for type constant " ^a.string_of_name ^
				  " successful!")) in
        let _a = Typ.add (Typ.mk_entry a tK' i) in ()


    | Ext.Sgn.Const (loc, c, extT) ->
        let (apxT, _ ) = Index.typ extT in
        let rec get_type_family = function
                           | Apx.LF.Atom(_loc, a, _spine) -> a
                           | Apx.LF.PiTyp ((_, _), t) -> get_type_family t in
        let constructedType = get_type_family apxT in
        let _          = dprint (fun () -> "Reconstructing term constant " ^ c.string_of_name) in

        let _        = FVar.clear () in
        let tA       = Monitor.timer ("Constant Elaboration",
                                      fun () -> (let tA = Reconstruct.typ Lfrecon.Pi  apxT in
                                                   Reconstruct.solve_fvarCnstr Lfrecon.Pi; tA)) in
        let cD       = Int.LF.Empty in

        let _        = dprint (fun () -> "\nElaboration of constant " ^ c.string_of_name ^ " : " ^
                                         P.typToString cD Int.LF.Null (tA, S.LF.id)) in

        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let (tA', i) = Monitor.timer ("Constant Abstraction",
                                      fun () -> Abstract.typ tA) in
	let _        = ( Reconstruct.reset_fvarCnstr ();
			 Unify.resetGlobalCnstrs ();
        		 dprint (fun () -> "\nReconstruction (with abstraction) of constant: " ^
				   c.string_of_name ^ " : " ^
				   (P.typToString cD Int.LF.Null (tA', S.LF.id)) ^ "\n\n");
			 Monitor.timer ("Constant Check",
					fun () -> Check.LF.checkTyp Int.LF.Empty Int.LF.Null (tA', S.LF.id))) in
	let _c = Term.add loc constructedType (Term.mk_entry c tA' i) in ()


    | Ext.Sgn.Schema (_, g, schema) ->
        let apx_schema = Index.schema schema in
        let _        = dprint (fun () -> "\nReconstructing schema " ^ g.string_of_name ^ "\n") in
        let _        = FVar.clear () in
        let sW       = Reconstruct.schema apx_schema in
        let _        = (dprint (fun () -> "\nElaborating schema " ^ g.string_of_name );
			Reconstruct.solve_fvarCnstr Lfrecon.Pi;
			Unify.forceGlobalCnstr (!Unify.globalCnstrs);
			Reconstruct.reset_fvarCnstr ();
			Unify.resetGlobalCnstrs ()) in

        let sW'      = Abstract.schema sW in
        (Check.LF.checkSchemaWf sW' ;
	 dprint (fun () -> "\nTYPE CHECK for schema " ^ g.string_of_name ^ " successful" );
         let _s = Schema.add (Schema.mk_entry g sW') in ();
         if (!Debug.chatter) == 0 then ()
         else (Format.printf "\nschema %s = @[%a@];@."
                 (g.string_of_name)
                 (P.fmt_ppr_lf_schema Pretty.std_lvl) sW'))


    | Ext.Sgn.Val (loc, x, None, i) ->
          let apx_i              = Index.exp' (Var.create ()) i in
	  let (cD, cG)       = (Int.LF.Empty, Int.LF.Empty) in
          let (i', (tau, theta)) = Monitor.timer ("Function Elaboration", fun () -> Reconstruct.exp' cG apx_i) in
          let _                  = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
          let tau'               = Whnf.cnormCTyp (tau, theta) in
          let i'                 = Whnf.cnormExp' (i', Whnf.m_id) in
          let _                  = dprint (fun () ->  "\n [AFTER Reconstruction Val] let " ^ x.string_of_name ^
					     "\n   : " ^ P.compTypToString cD tau' ^
					     "\n  =  " ^
                                P.expSynToString cD cG i' ^ "\n") in
          let i''                = Monitor.timer ("Function Abstraction", fun () ->
						    Abstract.exp (Int.Comp.Syn (loc, i'))) in
          let _                  = Monitor.timer ("Function Check", fun () ->
						    Check.Comp.check cD  cG i'' (tau', C.m_id)) in

	  if Holes.none () then begin
            let v = Opsem.eval i'' in
            let _x = Comp.add (fun _ -> Comp.mk_entry x tau' 0 v []) in
            if (!Debug.chatter) <> 0 then
              Printf.printf  "\n\nlet %s : %s = %s  \n ===>  %s \n"
                (R.render_name x)
                (P.compTypToString cD tau')
                (P.expChkToString cD cG i'')
                (P.valueToString v)
	  end

    | Ext.Sgn.Val (loc, x, Some tau, i) ->
          let apx_tau = Index.comptyp tau in
	  let (cD, cG)       = (Int.LF.Empty, Int.LF.Empty) in
          let tau'    = Monitor.timer ("Function Type Elaboration", fun () -> Reconstruct.comptyp apx_tau)  in
          let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
          let (tau', _imp) = Monitor.timer ("Function Type Abstraction", fun ()
					      -> Abstract.comptyp tau') in
	  let _       = dprint (fun () -> "[checkTyp] ") in
          let  _      = Monitor.timer ("Function Type Check", fun () -> Check.Comp.checkTyp cD tau') in

          let apx_i   = Index.exp' (Var.create ()) i in

          let i'      = Monitor.timer ("Function Elaboration",
                                       fun () ->
                                         Reconstruct.exp cG (Apx.Comp.Syn(loc, apx_i)) (tau', C.m_id)) in
          let i'      = Whnf.cnormExp (i', Whnf.m_id) in
          let _       = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
          let tau'    = Whnf.cnormCTyp (tau', C.m_id) in
          let _       = dprint (fun () ->  "\n [AFTER Reconstruction Val - 2] let " ^ x.string_of_name ^
                               "\n   : " ^ P.compTypToString cD tau' ^
                                "\n  =  " ^
                                P.expChkToString cD cG i' ^ "\n") in

          let i''     = Monitor.timer ("Function Abstraction", fun () -> Abstract.exp i') in
          let _       = Monitor.timer ("Function Check", fun () -> Check.Comp.check cD  cG i'' (tau', C.m_id)) in
	  if Holes.none () then begin
            let v = Opsem.eval i'' in
            let _x = Comp.add (fun _ -> Comp.mk_entry x tau' 0 v []) in
            if (!Debug.chatter) <> 0 then
	      Printf.printf "\nlet %s : %s = %s\n===>  %s\n"
		(R.render_name x)
		(P.compTypToString cD tau')
		(P.expChkToString cD cG i'')
		(P.valueToString v)
  	  end

    | Ext.Sgn.MRecTyp (_, recDats) ->
          let recTyps = List.map List.hd recDats in
          let   _   =  recSgnDecls recTyps in
          let recConts = List.map List.tl recDats in
          let recConts' = List.flatten recConts in
          let   _   = recSgnDecls recConts' in
          let  _  = List.map freeze_from_name recTyps in
               ()
    | Ext.Sgn.Rec (_, recFuns) ->
        (* let _       = Printf.printf "\n Indexing function : %s  \n" f.string_of_name  in   *)
        let (cO, cD)   = (Int.LF.Empty, Int.LF.Empty) in

        let rec preprocess l = match l with
          | [] -> (Int.LF.Empty, Var.create (), [])
          | Ext.Comp.RecFun (f, tau, _e) :: lf ->
          let apx_tau = Index.comptyp  tau in
          let _       = dprint (fun () ->  "Reconstructing function " ^  f.string_of_name ^ " \n") in
          let tau'    = Monitor.timer ("Function Type Elaboration", fun () -> Reconstruct.comptyp apx_tau)  in
          let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
          (* Are some FMVars delayed since we can't infer their type? - Not associated with pattsub *)
          let _        = dprint (fun () ->  "Elaboration of function type " ^ f.string_of_name ^
                                   " \n : " ^  (P.compTypToString cD tau') ^ " \n\n" )   in

          (* let _       = Monitor.timer ("Function Type Reconstruction", fun () -> recCompTyp cO cD tau') in *)
          let (tau', _i) = Monitor.timer ("Function Type Abstraction", fun () -> Abstract.comptyp tau') in
          let _ = dprint (fun () ->  "Abstracted elaborated function type " ^ f.string_of_name ^
                                   " \n : " ^  (P.compTypToString cD tau') ^ " \n\n" )   in

          let  _      = Monitor.timer ("Function Type Check", fun () -> Check.Comp.checkTyp cD tau') in
          let _       = dprint (fun () -> "Checked computation type " ^ (P.compTypToString cD tau') ^ " successfully\n\n")  in
          let _       = FCVar.clear () in

          let (cG, vars, n_list) = preprocess lf in
            (* check that names are unique ? *)
            (Int.LF.Dec(cG, Int.Comp.CTypDecl (f, tau')) , Var.extend  vars (Var.mk_entry f), f::n_list )

        in

        let (cG , vars', n_list ) = preprocess recFuns in

        let reconFun f e =
          let apx_e   = Index.exp vars' e in
          let _       = dprint (fun () -> "\n  Indexing  expression done \n") in
          let tau'    = lookupFun cG f in
          let e'      = Monitor.timer ("Function Elaboration", fun () -> Reconstruct.exp cG apx_e (tau', C.m_id)) in

          let _       = dprint (fun () ->  "\n Elaboration of function " ^ f.string_of_name ^
                                  "\n   type: " ^ P.compTypToString cD tau' ^
                                  "\n   result:  " ^
                                  P.expChkToString cD cG e' ^ "\n") in

          let _        = begin try
                           Unify.forceGlobalCnstr (!Unify.globalCnstrs)
                        with Unify.GlobalCnstrFailure (loc,cnstr) ->
                          raise (Check.Comp.Error  (loc, Check.Comp.UnsolvableConstraints (f, cnstr)))
                        end
          in
          let _        = Unify.resetGlobalCnstrs () in

          (* let e_r     = Monitor.timer ("Function Reconstruction", fun () -> check  cO cD cG e' (tau', C.m_id)) in  *)

          let _       = dprint (fun () ->  "\n [AFTER reconstruction] Function " ^ f.string_of_name ^
                               "\n   type: " ^ P.compTypToString cD tau' ^
                                "\n   result:  " ^
                                P.expChkToString cD cG e' ^ "\n") in

          let e'' = Whnf.cnormExp (e', Whnf.m_id) in
          let e_r'    = Monitor.timer ("Function Abstraction", fun () -> Abstract.exp e'' ) in

          let e_r'    = Whnf.cnormExp (e_r', Whnf.m_id) in

          let _       = Monitor.timer ("Function Check", fun () ->
                                         Check.Comp.check cD  cG e_r' (tau', C.m_id)
                                      ) in
             (e_r' , tau')
        in

        let rec reconRecFun recFuns = match recFuns with
          | [] -> ()
          | Ext.Comp.RecFun (f, _tau, e) :: lf ->
            let (e_r' , tau') = reconFun f e in
            if !Debug.chatter <> 0 then
              Printf.printf  "and %s : %s =\n %s\n"
                (R.render_name f)
                (P.compTypToString cD tau')
                (P.expChkToString cD cG e_r');
            if !Coverage.enableCoverage then
              Printf.printf "\n## Coverage checking done: %s  ##\n"
                (R.render_name f);
            dprint (fun () -> "DOUBLE CHECK of function " ^ f.string_of_name ^ " successful!\n\n");
            let _x = Comp.add
              (fun cid ->
                Comp.mk_entry f tau' 0
                  (Int.Comp.RecValue (cid, e_r', Int.LF.MShift 0, Int.Comp.Empty))
                  n_list) in
            reconRecFun lf in
        begin match recFuns with
          | Ext.Comp.RecFun (f, _tau, e) :: lf ->
            let (e_r' , tau') = reconFun f e in
            if !Debug.chatter <> 0 then
              Format.printf "\nrec %s :@[<2>@ %a@] = @.@[<2>%a@]@.\n"
                (R.render_name f)
                (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.normCTyp tau')
                (P.fmt_ppr_cmp_exp_chk cD cG Pretty.std_lvl)
                (Whnf.cnormExp (e_r', Whnf.m_id));
            if !Coverage.enableCoverage then
              Printf.printf "\n## Coverage checking done: %s  ##\n"
                (R.render_name f);
            dprint (fun () -> "DOUBLE CHECK of function " ^ f.string_of_name ^ " successful!\n");

            let _x = Comp.add
              (fun cid ->
                Comp.mk_entry f tau' 0
                  (Int.Comp.RecValue (cid, e_r', Int.LF.MShift 0, Int.Comp.Empty))
                  n_list) in
            reconRecFun lf

          | _ -> raise (Error.Violation "No recursive function defined")
        end


    | Ext.Sgn.Query (loc, name, extT, expected, tries) ->
      let (apxT, _ ) = Index.typ extT in
      let _          = dprint (fun () -> "Reconstructing query.") in

      let _        = FVar.clear () in
      let tA       = Monitor.timer ("Constant Elaboration",
                                    fun () -> (let tA = Reconstruct.typ Lfrecon.Pi apxT in
                                               Reconstruct.solve_fvarCnstr Lfrecon.Pi;
                                               tA)) in
      let cD       = Int.LF.Empty in


      let _        = dprint (fun () -> "\nElaboration of query : " ^
        P.typToString cD Int.LF.Null (tA, S.LF.id)) in

      let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in

      let (tA', i) = Monitor.timer ("Constant Abstraction",
                                    fun () -> Abstract.typ tA) in

      let _        = Reconstruct.reset_fvarCnstr () in
      let _        = Unify.resetGlobalCnstrs () in
      let _        = dprint (fun () -> "\nReconstruction (with abstraction) of query: " ^
        (P.typToString cD Int.LF.Null (tA', S.LF.id)) ^ "\n\n") in

      let _        = Monitor.timer ("Constant Check",
                                    fun () -> Check.LF.checkTyp Int.LF.Empty Int.LF.Null (tA', S.LF.id)) in
      let _c'       = Logic.storeQuery name (tA', i) expected tries in
      ()

    | Ext.Sgn.Pragma (loc, Ext.Sgn.NamePrag (typ_name, m_name, v_name)) ->
        begin try
          begin match v_name with
            | None ->
                let _cid_tp = Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name)) None in
                  (* Int.Sgn.Pragma(Int.LF.NamePrag(cid_tp)) *) ()
            | Some x ->
                let _cid_tp = Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name))
                  (Some (Gensym.VarData.name_gensym x)) in
                  (* Int.Sgn.Pragma(Int.LF.NamePrag(cid_tp)) *) ()
          end
        with _ -> raise (Index.Error (loc, Index.UnboundName typ_name))
        end

    | Ext.Sgn.Pragma (loc, Ext.Sgn.Total (order, c, args)) ->
        begin try
          let rec pos x args k = match args with
            | [] -> raise (Index.Error (loc, Index.UnboundName x))
            | (Some y)::ys -> if x = y then k else pos x ys (k+1)
            | None::ys -> pos x ys (k+1)
          in
            match order with
              | Ext.Sgn.Arg x ->
                  let p = pos x args 1 in
                    (Printf.printf "\n## Totality declaration: %s terminates in position %s ##\n"
                      (R.render_name c) (string_of_int p);
                    Comp.add_total c (Order.Dec (Order.Arg p, Order.Empty)))
              | _ -> ()
        with
            _ -> raise (Index.Error (loc, Index.UnboundName c))
        end

