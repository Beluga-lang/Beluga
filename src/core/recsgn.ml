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
  | InvalidOpenPrag of string

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
      | InvalidOpenPrag s ->
        Format.fprintf ppf "Invalid module in pragma '#open %s'" s
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
  | [] -> []

  | Ext.Sgn.Pragma(loc, Ext.Sgn.NotPrag) :: not'd_decl :: rest ->
    let not'd_decl_succeeds =
      begin
    try
      let _ = recSgnDecl not'd_decl in true
    with _ ->
      if !Debug.chatter != 0 then
        print_string ("Reconstruction fails for %not'd declaration\n");
            false
        end in
    if not'd_decl_succeeds
    then raise (Error (loc, UnexpectedSucess))
    else recSgnDecls rest

  (* %not declaration with nothing following *)
  | [Ext.Sgn.Pragma(_, Ext.Sgn.NotPrag)] -> []

  | Ext.Sgn.Pragma(loc, Ext.Sgn.OptsPrag _) :: rest ->
    raise (Error (loc, IllegalOptsPrag))

  | decl :: rest ->
    let decl' = recSgnDecl decl in
    let rest' = recSgnDecls rest in
    decl'::rest'

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
        let _a = CompTypDef.add (CompTypDef.mk_entry a i (cD,tau) cK) in 
        let sgn = Int.Sgn.CompTypAbbrev(loc, a, cK, tau) in
        Store.Modules.addSgnToCurrent sgn;
        sgn        

    | Ext.Sgn.CompTyp (loc , a, extK) ->
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
        let sgn = Int.Sgn.CompTyp(loc, a, cK') in
        Store.Modules.addSgnToCurrent sgn;
        sgn

  | Ext.Sgn.CompCotyp (loc, a, extK) ->
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
        let _a = CompCotyp.add (CompCotyp.mk_entry a cK' i) in
        let sgn = Int.Sgn.CompCotyp(loc, a, cK') in
        Store.Modules.addSgnToCurrent sgn;
        sgn


    | Ext.Sgn.CompConst (loc , c, tau) ->
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
        let sgn = Int.Sgn.CompConst(loc, c, tau') in
        Store.Modules.addSgnToCurrent sgn;
        sgn


   | Ext.Sgn.CompDest (loc , c, tau) ->
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
        let _c        = CompDest.add cid_ctypfamily (CompDest.mk_entry c tau' i) in 
        let sgn = Int.Sgn.CompDest(loc, c, tau') in
        Store.Modules.addSgnToCurrent sgn;
        sgn


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
        let _a = Typ.add (Typ.mk_entry a tK' i) in
        let sgn = Int.Sgn.Typ(_a, tK') in
        Store.Modules.addSgnToCurrent sgn;
        sgn

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
	      let _c = Term.add loc constructedType (Term.mk_entry c tA' i) in
        let sgn = Int.Sgn.Const(_c, tA') in
        Store.Modules.addSgnToCurrent sgn;
        sgn

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
        let _ = Check.LF.checkSchemaWf sW' in
      	 dprint (fun () -> "\nTYPE CHECK for schema " ^ g.string_of_name ^ " successful" );
         let _s = Schema.add (Schema.mk_entry g sW') in 
         let sgn = Int.Sgn.Schema(_s, sW') in
         Store.Modules.addSgnToCurrent sgn;
         sgn



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

    let sgn = Int.Sgn.Val(loc, x, tau', i'') in
    let _ = Store.Modules.addSgnToCurrent sgn in
	  if Holes.none () then begin
            let v = Opsem.eval i'' in
            let _ = Comp.add (fun _ -> Comp.mk_entry x tau' 0 v []) in ()
	  end;
    sgn

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

    let sgn = Int.Sgn.Val(loc, x, tau', i'') in
    let _ = Store.Modules.addSgnToCurrent sgn in
    if Holes.none () then begin
            let v = Opsem.eval i'' in
            let _ = Comp.add (fun _ -> Comp.mk_entry x tau' 0 v []) in ()
    end;
    sgn

    | Ext.Sgn.MRecTyp (loc, recDats) ->
        let recTyps = List.map List.hd recDats in
        let   recTyps'   =  recSgnDecls recTyps in
        let recConts = List.map List.tl recDats in
        let   recConts'   = List.map recSgnDecls recConts in
        let  _  = List.map freeze_from_name recTyps in
        Int.Sgn.MRecTyp (loc, List.map2 (fun x y -> x::y) recTyps' recConts')

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
          let _       = dprint (fun () -> "\n  Indexing expression done \n") in
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
          | [] -> []
          | Ext.Comp.RecFun (f, _tau, e) :: lf ->
            let (e_r' , tau') = reconFun f e in
            if !Coverage.enableCoverage && !Debug.chatter <> 0 then
              Printf.printf "\n## Coverage checking done: %s  ##\n"
                (R.render_name f);
            dprint (fun () -> "DOUBLE CHECK of function " ^ f.string_of_name ^ " successful!\n\n");
            let _x = Comp.add
              (fun cid ->
                Comp.mk_entry f tau' 0
                  (Int.Comp.RecValue (cid, e_r', Int.LF.MShift 0, Int.Comp.Empty))
                  n_list) in
            (_x, tau', e_r')::(reconRecFun lf) in
        begin match recFuns with
          | Ext.Comp.RecFun (f, _tau, e) :: lf ->
            let (e_r' , tau') = reconFun f e in
            if !Coverage.enableCoverage&& !Debug.chatter <> 0 then
              Printf.printf "\n## Coverage checking done: %s  ##\n"
                (R.render_name f);
            dprint (fun () -> "DOUBLE CHECK of function " ^ f.string_of_name ^ " successful!\n");

            let _x = Comp.add
              (fun cid ->
                Comp.mk_entry f tau' 0
                  (Int.Comp.RecValue (cid, e_r', Int.LF.MShift 0, Int.Comp.Empty))
                  n_list) in
            let sgn = Int.Sgn.Rec((_x, tau', e_r')::(reconRecFun lf)) in
            Store.Modules.addSgnToCurrent sgn;
            sgn

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
      Int.Sgn.Query(loc, name, (tA', i), expected, tries)

    | Ext.Sgn.Pragma(loc, Ext.Sgn.NamePrag (typ_name, m_name, v_name)) ->
        begin try
          let cid =
          begin match v_name with
            | None ->
                Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name)) None
            | Some x ->
                Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name))
                  (Some (Gensym.VarData.name_gensym x))
          end in Store.Cid.NamedHoles.addNameConvention cid m_name v_name; Int.Sgn.Pragma(Int.LF.NamePrag cid)
        with _ -> raise (Index.Error (loc, Index.UnboundName typ_name))
        end

    | Ext.Sgn.Module(loc, name, None, decls) -> 
(*       let (signature, sig_opt') = begin match sig_opt with
        | Some (Ext.Sgn.Name n) -> 
            (Some !(Hashtbl.find Modules.signatures (!Modules.current @ [n])), Some(Int.Sgn.Name n))
        | Some (Ext.Sgn.Sig l) -> 

            let Int.Sgn.ModuleType(_, _, l') = recSgnDecl (Ext.Sgn.ModuleType(loc, name ^ "TYPE", l)) in 
            (Some l', Some (Int.Sgn.Sig l'))
        | None -> (None, None)
      end in *)
      let orig = !Store.Modules.current in 
      let opened = !Store.Modules.opened in
      let _ = Store.Modules.instantiateModule name in
      let decls' = List.map recSgnDecl decls in

      (* TODO: NEED TO CHECK AGAINST SIG *)
(*       let decls'' = begin match signature with
        | None -> decls'
        | Some signature -> 
          let checkDecl (dec : Int.Sgn.decl) (sgn : Int.Sgn.module_sig) : bool = 
            let module R = Store.Cid.NamedRenderer in
            let eqTyp a b = 
              try Unify.unifyTyp Int.LF.Empty Int.LF.Null (a, Int.LF.EmptySub) (b, Int.LF.EmptySub); true
              with | _ -> false  in

            begin match (dec, sgn) with
              | (Int.Sgn.Typ(n, k), Int.Sgn.TypSig(_, n', k')) ->
                  (R.render_cid_typ n) = n'.Id.string_of_name && k = k'
              | (Int.Sgn.Const(n, t), Int.Sgn.ConstSig(_, n', t')) ->
                  (R.render_cid_term n) = n'.string_of_name && (eqTyp t t')
              | (Int.Sgn.CompTyp(_, n, k), Int.Sgn.CompTypSig(_, n', k')) ->
                  n.Id.string_of_name = n'.Id.string_of_name && k = k'
              | (Int.Sgn.CompCotyp(_, n, k), Int.Sgn.CompCotypSig(_, n', k')) ->
                  n.Id.string_of_name = n'.Id.string_of_name && k = k'
              | (Int.Sgn.CompConst(_, n, t), Int.Sgn.CompConstSig(_, n', t')) ->
                  n.Id.string_of_name = n'.Id.string_of_name && t = t'
              | (Int.Sgn.CompDest(_, n, t), Int.Sgn.CompDestSig(_, n', t')) ->
                  n.Id.string_of_name = n'.Id.string_of_name && t = t'
              | (Int.Sgn.CompTypAbbrev(_, n, k, t), Int.Sgn.CompTypAbbrevSig(_, n', k', t')) ->
                  n.Id.string_of_name = n'.Id.string_of_name && k = k' && t = t'
              | (Int.Sgn.Schema(n, sw), Int.Sgn.SchemaSig(_, n', sw')) ->
                  (R.render_cid_schema n) = n'.Id.string_of_name && sw = sw'
              | (_, _) -> false
          end in
          let declExists (_sgn: Int.Sgn.module_sig) = () in
          List.iter declExists signature;
          List.filter (fun dec -> List.exists (checkDecl dec) signature) decls'
        end in *)
      let _ = Store.Modules.current := orig in
      let _ = Store.Modules.opened := opened in
      let sgn = Int.Sgn.Module(loc, name, None, decls') in
      Store.Modules.addSgnToCurrent sgn;
      sgn

    | Ext.Sgn.ModuleType(loc, name, sigs) ->
      let orig = !Store.Modules.current in
      let opened = !Store.Modules.opened in
      (* let _ = Store.Modules.opened := [] in *)
      let _ = Store.Modules.instantiateModuleType name in
      let sigs' = List.map recSgnSig sigs in
      let _ = Store.Modules.current := orig in
      let _ = Store.Modules.opened := opened in 
      let sgn = Int.Sgn.ModuleType(loc, name, sigs') in
      Store.Modules.addSgnToCurrent sgn;
      sgn

    | Ext.Sgn.Pragma(loc, Ext.Sgn.OpenPrag(n)) ->
      try 
        Modules.open_module n;
        Int.Sgn.Pragma(Int.LF.OpenPrag n)
      with Not_found -> raise (Error(loc, (InvalidOpenPrag (String.concat "." n))))

and recSgnSig = function
  | Ext.Sgn.SchemaSig (_loc, g, schema) ->
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
        Check.LF.checkSchemaWf sW' ;
        dprint (fun () -> "\nTYPE CHECK for schema " ^ g.string_of_name ^ " successful" );
         let _s = Schema.add (Schema.mk_entry g sW') in 
         let sgn = Int.Sgn.SchemaSig(_loc, g, sW') in
         let _ = Store.Modules.addSigToCurrent sgn in
         sgn
 
  | Ext.Sgn.ValSig (loc, x, tau) ->
    let apx_tau = Index.comptyp tau in
    let (cD, cG)       = (Int.LF.Empty, Int.LF.Empty) in
    let tau'    = Monitor.timer ("Function Type Elaboration", fun () -> Reconstruct.comptyp apx_tau)  in
    let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
    let (tau', _imp) = Monitor.timer ("Function Type Abstraction", fun ()
          -> Abstract.comptyp tau') in
    let _       = dprint (fun () -> "[checkTyp] ") in
    let  _      = Monitor.timer ("Function Type Check", fun () -> Check.Comp.checkTyp cD tau') in
    let sgn = Int.Sgn.ValSig(loc, x, tau') in
    let _ = Store.Modules.addSigToCurrent in
    sgn

  | Ext.Sgn.RecSig (loc, x, tau) ->
    let apx_tau = Index.comptyp tau in
    let (cD, cG)       = (Int.LF.Empty, Int.LF.Empty) in
    let tau'    = Monitor.timer ("Function Type Elaboration", fun () -> Reconstruct.comptyp apx_tau)  in
    let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
    let (tau', _imp) = Monitor.timer ("Function Type Abstraction", fun ()
          -> Abstract.comptyp tau') in
    let _       = dprint (fun () -> "[checkTyp] ") in
    let  _      = Monitor.timer ("Function Type Check", fun () -> Check.Comp.checkTyp cD tau') in
    let sgn = Int.Sgn.ValSig(loc, x, tau') in
    let _ = Store.Modules.addSigToCurrent in
    sgn
    

  | Ext.Sgn.ConstSig (loc, c, extT) ->
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
        let _c = Term.add loc constructedType (Term.mk_entry c tA' i) in
        let sgn = Int.Sgn.ConstSig(loc, c, tA') in
        Store.Modules.addSigToCurrent sgn;
        sgn

  | Ext.Sgn.TypSig (loc, a, extK) ->
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
        let _a = Typ.add (Typ.mk_entry a tK' i) in
        let sgn = Int.Sgn.TypSig(loc, a, tK') in
        Store.Modules.addSigToCurrent sgn;
        sgn

  | Ext.Sgn.CompTypSig (loc, a, extK) ->
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
    let sgn = Int.Sgn.CompTypSig(loc, a, cK') in
    Store.Modules.addSigToCurrent sgn;
    sgn



  | Ext.Sgn.CompCotypSig (loc, a, extK) ->
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
    let _a = CompCotyp.add (CompCotyp.mk_entry a cK' i) in
    let sgn = Int.Sgn.CompCotypSig(loc, a, cK') in
    Store.Modules.addSigToCurrent sgn;
    sgn


  | Ext.Sgn.CompConstSig (loc, c, tau) ->
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
        in  let cid_ctypfamily = get_target_cid_comptyp tau' in
        let _c        = CompConst.add cid_ctypfamily (CompConst.mk_entry c tau' i) in
        let sgn = Int.Sgn.CompConstSig(loc, c, tau') in
        Store.Modules.addSigToCurrent sgn;
        sgn

  | Ext.Sgn.CompDestSig (loc, c, tau) ->
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
      let _c        = CompDest.add cid_ctypfamily (CompDest.mk_entry c tau' i) in 
      let sgn = Int.Sgn.CompDestSig(loc, c, tau') in 
      Store.Modules.addSigToCurrent sgn;
      sgn


  | Ext.Sgn.CompTypAbbrevSig (loc, a, cK, cT) ->
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
      let _a = CompTypDef.add (CompTypDef.mk_entry a i (cD,tau) cK) in 
      let sgn = Int.Sgn.CompTypAbbrevSig(loc, a, cK, tau) in
      Store.Modules.addSigToCurrent sgn;
      sgn

  | Ext.Sgn.MRecTypSig (loc, sig_list) ->
        let recTyps  = List.map List.hd sig_list in
        let recTyps' = List.map recSgnSig recTyps in
        let recConts = List.map List.tl sig_list in
        let recConts'= List.map (fun x -> List.map recSgnSig x) recConts in
        let sgn = Int.Sgn.MRecTypSig (loc, List.map2 (fun x y -> x::y) recTyps' recConts') in
        Store.Modules.addSigToCurrent sgn;
        sgn