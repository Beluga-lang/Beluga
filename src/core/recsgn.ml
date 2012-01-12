open Id

open Store
open Store.Cid
open Syntax

module C     = Whnf
module S = Substitution
module Rec = Reconstruct
(* module Unify = Unify.EmptyTrail  *)
module Unify = Unify.StdTrail 

module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer
module RR = Pretty.Int.NamedRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [11])


(* ------------------------------------------------------------------- *)
let rec lookupFun cG f = match cG with
  | Int.LF.Dec (cG', Int.Comp.CTypDecl (f',  tau)) ->  
      if f = f' then tau else         
      lookupFun cG' f

let recSgnDecl d = 
    Rec.reset_fvarCnstr ();  FCVar.clear ();
    match d with
    | Ext.Sgn.CompTypAbbrev (_, a, _cK, _cT) -> print_string "Not implemented yet\n"
    | Ext.Sgn.CompTyp (_ , a, extK) -> 
        let _ = dprint (fun () -> "\nIndexing computation-level data-type constant " ^ a.string_of_name) in
        let apxK = Index.compkind extK in 
        let _ = FVar.clear () in 
        let _ = dprint (fun () -> "\nElaborating data-type declaration " ^ a.string_of_name) in 
        let cK = Monitor.timer ("CType Elaboration" , 
                               (fun () -> let cK = Rec.compkind apxK in 
                                  Rec.solve_fvarCnstr Lfrecon.Pibox; cK 
                               )) in 
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
        let (cK', i) = Monitor.timer ("Type Abstraction",  
                                      fun () -> Abstract.abstrCompKind cK) in

        let _        = (Rec.reset_fvarCnstr ();
			Unify.resetGlobalCnstrs ();
			dprint (fun () ->  a.string_of_name ^ 
				  " : " ^  (P.compKindToString Int.LF.Empty cK'))) in
	 (* Monitor.timer ("Type Check", 
            fun () -> Check.LF.checkCompKind Int.LF.Empty Int.LF.Empty cK');
	    dprint (fun () ->  "\nDOUBLE CHECK for data type constant " ^a.string_of_name ^
            " successful!"); *)
        let _a = CompTyp.add (CompTyp.mk_entry a cK' i) in ()


    | Ext.Sgn.CompConst (_ , c, tau) -> 
        let _         = dprint (fun () -> "\nIndexing computation-level data-type constructor " ^ c.string_of_name) in
        let apx_tau   = Index.comptyp tau in
        let cD        = Int.LF.Empty in
        let _         = dprint (fun () -> "\nElaborating data-type constructor " ^ c.string_of_name) in 
        let tau'      = Monitor.timer ("Data-type Constant: Type Elaboration", fun () -> Rec.comptyp apx_tau)  in
        let _         = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
        let _         = Unify.resetGlobalCnstrs () in 
	let _         = dprint (fun () -> "Abstracting over comp. type") in 
        let (tau', i) = Monitor.timer ("Data-type Constant: Type Abstraction",
        fun () -> Abstract.abstrCompTyp tau') in
	let _         = dprint (fun () -> "Abstracting over comp. type: done") in 
	let _         = dprint (fun () ->  c.string_of_name ^ " : " ^  
				   (P.compTypToString cD tau')) in 
	let _         = (Monitor.timer ("Data-type Constant: Type Check", 
					fun () -> Check.Comp.checkTyp cD tau')) in 
        let _c        = CompConst.add (CompConst.mk_entry c tau' i) in () 

    | Ext.Sgn.Typ (_, a, extK)   ->
        let _        = dprint (fun () -> "\nIndexing type constant " ^ a.string_of_name) in
        let (apxK, _ ) = Index.kind extK in
        let _        = FVar.clear () in

        let _        = dprint (fun () -> "\nElaborating type constant " ^ a.string_of_name) in

        let tK       = Monitor.timer ("Type Elaboration", 
                                      fun () -> (let tK = Rec.kind apxK in
                                                   Rec.solve_fvarCnstr Lfrecon.Pi; tK )) in

        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 

        let (tK', i) = Monitor.timer ("Type Abstraction",  
                                      fun () -> Abstract.abstrKind tK) in
        let _        = (Rec.reset_fvarCnstr ();
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
                                      fun () -> (let tA = Rec.typ Lfrecon.Pi  apxT in
                                                   Rec.solve_fvarCnstr Lfrecon.Pi; tA)) in
        let cD       = Int.LF.Empty in

        let _        = dprint (fun () -> "\nElaboration of constant " ^ c.string_of_name ^ " : " ^
                                         P.typToString cD Int.LF.Null (tA, S.LF.id)) in

        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
        let (tA', i) = Monitor.timer ("Constant Abstraction", 
                                      fun () -> Abstract.abstrTyp tA) in
	let _        = ( Rec.reset_fvarCnstr ();
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
        let sW       = Rec.schema apx_schema in
        let _        = (dprint (fun () -> "\nElaborating schema " ^ g.string_of_name );
			Rec.solve_fvarCnstr Lfrecon.Pi;
			Unify.forceGlobalCnstr (!Unify.globalCnstrs);
			Rec.reset_fvarCnstr ();
			Unify.resetGlobalCnstrs ()) in 

        let sW'      = Abstract.abstrSchema sW in 
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
          let (i', (tau, theta)) = Monitor.timer ("Function Elaboration", fun () -> Rec.exp' cG apx_i) in
          let _                  = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _                  = Unify.resetGlobalCnstrs () in 
          let tau'               = Whnf.cnormCTyp (tau, theta) in 
          let i'                 = Whnf.cnormExp' (i', Whnf.m_id) in 
          let _                  = dprint (fun () ->  "\n [AFTER Reconstruction] let " ^ x.string_of_name ^
					     "\n   : " ^ P.compTypToString cD tau' ^ 
					     "\n  =  " ^ 
                                P.expSynToString cD cG i' ^ "\n") in
          let i''                = Monitor.timer ("Function Abstraction", fun () -> 
						    Abstract.abstrExp (Int.Comp.Syn (loc, i'))) in
          let _                  = Monitor.timer ("Function Check", fun () -> 
						    Check.Comp.check cD  cG i'' (tau', C.m_id)) in

          let v                  =   Opsem.eval i''  in 
          let _x                 = Comp.add (Comp.mk_entry x tau' 0 v []) in 
            if (!Debug.chatter) == 0 then () 
            else (Printf.printf  "\n\nlet %s : %s = %s  \n ===>  %s \n"
                    (R.render_name x)
                    (P.compTypToString cD tau') 
                    (P.expChkToString cD cG i'') 
                    (P.expChkToString cD cG v))

    | Ext.Sgn.Val (loc, x, Some tau, i) -> 
          let apx_tau = Index.comptyp tau in
	  let (cD, cG)       = (Int.LF.Empty, Int.LF.Empty) in 
          let tau'    = Monitor.timer ("Function Type Elaboration", fun () -> Rec.comptyp apx_tau)  in
          let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _        = Unify.resetGlobalCnstrs () in 
          let (tau', _imp) = Monitor.timer ("Function Type Abstraction", fun ()
					      -> Abstract.abstrCompTyp tau') in
	  let _       = dprint (fun () -> "[checkTyp] ") in 
          let  _      = Monitor.timer ("Function Type Check", fun () -> Check.Comp.checkTyp cD tau') in

          let apx_i   = Index.exp' (Var.create ()) i in

          let i'      = Monitor.timer ("Function Elaboration", fun () -> Rec.exp cG (Apx.Comp.Syn(loc, apx_i)) (tau', C.m_id)) in
          let _       = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _       = Unify.resetGlobalCnstrs () in 

          let _       = dprint (fun () ->  "\n [AFTER Reconstruction] let " ^ x.string_of_name ^
                               "\n   : " ^ P.compTypToString cD tau' ^ 
                                "\n  =  " ^ 
                                P.expChkToString cD cG i' ^ "\n") in

          let i''     = Monitor.timer ("Function Abstraction", fun () -> Abstract.abstrExp i') in
          let _       = Monitor.timer ("Function Check", fun () -> Check.Comp.check cD  cG i'' (tau', C.m_id)) in

          let v  =   Opsem.eval i''  in
          let _       = if (!Debug.chatter) == 0 then () 
          else (Printf.printf  "\nlet %s : %s = %s\n===>  %s\n"
                                       (R.render_name x)
                                       (P.compTypToString cD tau') 
                                       (P.expChkToString cD cG i'') 
                                       (P.expChkToString cD cG v)) in 
          let _x = Comp.add (Comp.mk_entry x tau' 0 v []) in 
            ()


    | Ext.Sgn.Rec (_, recFuns) ->
        (* let _       = Printf.printf "\n Indexing function : %s  \n" f.string_of_name  in   *)
        let (cO, cD)   = (Int.LF.Empty, Int.LF.Empty) in

        let rec preprocess l = match l with 
          | [] -> (Int.LF.Empty, Var.create (), [])
          | Ext.Comp.RecFun (f, tau, _e) :: lf -> 
          let apx_tau = Index.comptyp  tau in
          let _       = dprint (fun () ->  "Reconstructing function " ^  f.string_of_name ^ " \n") in
          let tau'    = Monitor.timer ("Function Type Elaboration", fun () -> Rec.comptyp apx_tau)  in
          let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _        = Unify.resetGlobalCnstrs () in 
          (* Are some FMVars delayed since we can't infer their type? - Not associated with pattsub *)
          let _        = dprint (fun () ->  "Elaboration of function type " ^ f.string_of_name ^ 
                                   " \n : " ^  (P.compTypToString cD tau') ^ " \n\n" )   in   

          (* let _       = Monitor.timer ("Function Type Reconstruction", fun () -> recCompTyp cO cD tau') in *)
          let (tau', _i) = Monitor.timer ("Function Type Abstraction", fun () -> Abstract.abstrCompTyp tau') in
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
          let e'      = Monitor.timer ("Function Elaboration", fun () -> Rec.exp cG apx_e (tau', C.m_id)) in

          let _       = dprint (fun () ->  "\n Elaboration of function " ^ f.string_of_name ^
                                  "\n   type: " ^ P.compTypToString cD tau' ^ 
                                  "\n   result:  " ^ 
                                  P.expChkToString cD cG e' ^ "\n") in

          let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in 
          let _        = Unify.resetGlobalCnstrs () in 

          (* let e_r     = Monitor.timer ("Function Reconstruction", fun () -> check  cO cD cG e' (tau', C.m_id)) in  *)

          let _       = dprint (fun () ->  "\n [AFTER reconstruction] Function " ^ f.string_of_name ^
                               "\n   type: " ^ P.compTypToString cD tau' ^ 
                                "\n   result:  " ^ 
                                P.expChkToString cD cG e' ^ "\n") in

          let e_r'    = Monitor.timer ("Function Abstraction", fun () -> Abstract.abstrExp e' ) in

          let e_r'    = Whnf.cnormExp (e_r', Whnf.m_id) in  

          let _       = Monitor.timer ("Function Check", fun () -> 
                                         Check.Comp.check cD  cG e_r' (tau', C.m_id)                                   
                                      ) in
             (e_r' , tau')
        in 

        let rec reconRecFun recFuns = match recFuns with
          | [] -> ()
          | Ext.Comp.RecFun (f, _tau, e) :: lf -> 
              (let (e_r' , tau') = reconFun f e in 
                 (if (!Debug.chatter) == 0 then () 
                  else (Printf.printf  "and %s : %s =\n %s\n"
                          (R.render_name f)
                          (P.compTypToString cD tau') 
                          (P.expChkToString cD cG e_r')))
                    (* (P.expChkToString cD cG (Whnf.cnormExp (e_r', C.m_id)) ) *); 
                  
                 (if !Coverage.enableCoverage then 
                    Printf.printf "\n## Coverage checking done: %s  ##\n"  
                      (R.render_name f)
                  else ()) ; 
                 dprint (fun () ->  "DOUBLE CHECK of function " ^    
                           f.string_of_name ^  " successful!\n\n" ) ; 
                 
                 let _ = Comp.add (Comp.mk_entry f tau' 0  e_r' n_list) in 
                   reconRecFun lf 
              )
        in 
          begin match recFuns with
            | Ext.Comp.RecFun (f, _tau, e) :: lf -> 
                let (e_r' , tau') = reconFun f e in 
                (if (!Debug.chatter) == 0 then () 
                else Format.printf "\nrec %s :@[<2>@ %a@] = @.@[<2>%a@]@.\n"
                     (R.render_name f)
                     (P.fmt_ppr_cmp_typ cD Pretty.std_lvl) (Whnf.normCTyp tau')
                     (P.fmt_ppr_cmp_exp_chk cD cG Pretty.std_lvl) 
                     (Whnf.cnormExp (e_r', Whnf.m_id)); 
                  if !Coverage.enableCoverage then 
                    (if !Debug.chatter = 0 then () else
                      Printf.printf "\n## Coverage checking done: %s  ##\n"  
                        (R.render_name f))
                  else () ;                   
                  dprint (fun () ->  "DOUBLE CHECK of function " ^    
                            f.string_of_name ^  " successful!\n" )  ;

                  let _ = Comp.add (Comp.mk_entry f tau' 0  e_r' n_list) in

                reconRecFun lf 
                )
            | _ -> raise (Error.Violation "No recursive function defined")
          end


    | Ext.Sgn.Query (loc, name, extT, expected, tries) ->
      let (apxT, _ ) = Index.typ extT in
      let _          = dprint (fun () -> "Reconstructing query.") in

      let _        = FVar.clear () in
      let tA       = Monitor.timer ("Constant Elaboration",
                                    fun () -> (let tA = Rec.typ Lfrecon.Pi apxT in
                                               Rec.solve_fvarCnstr Lfrecon.Pi;
                                               tA)) in
      let cD       = Int.LF.Empty in


      let _        = dprint (fun () -> "\nElaboration of query : " ^
        P.typToString cD Int.LF.Null (tA, S.LF.id)) in

      let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in

      let (tA', i) = Monitor.timer ("Constant Abstraction",
                                    fun () -> Abstract.abstrTyp tA) in

      let _        = Rec.reset_fvarCnstr () in
      let _        = Unify.resetGlobalCnstrs () in
      let _        = dprint (fun () -> "\nReconstruction (with abstraction) of query: " ^
        (P.typToString cD Int.LF.Null (tA', S.LF.id)) ^ "\n\n") in

      let _        = Monitor.timer ("Constant Check",
                                    fun () -> Check.LF.checkTyp Int.LF.Empty Int.LF.Null (tA', S.LF.id)) in
      let _c'       = Logic.storeQuery name (tA', i) expected tries in
      ()


    | Ext.Sgn.Pragma(loc, Ext.LF.NamePrag (typ_name, m_name, v_name)) ->
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
        with _ -> raise (Error.Error (loc, Error.UnboundName typ_name)) 
        end 


let rec recSgnDecls = function

  | [] -> ()

  | Ext.Sgn.Pragma(_, Ext.LF.NotPrag) :: not'd_decl :: rest ->
      (*   let internal_syntax_pragma = Int.Sgn.Pragma(Int.LF.NotPrag) in *)
      let not'd_decl_succeeds = 
        begin try
          (let _ = recSgnDecl not'd_decl in
             true)
        with
            _ -> ((if (!Debug.chatter) == 0 then () 
                  else print_string ("Reconstruction fails for %not'd declaration\n"));
                  false)
        end
      in
        if not'd_decl_succeeds then
          raise (Error.Violation ("UNSOUND: reconstruction succeeded for %not'd declaration"))
        else recSgnDecls rest

  | [Ext.Sgn.Pragma(_, Ext.LF.NotPrag)] ->  (* %not declaration with nothing following *)
      ()

  | decl :: rest ->
      recSgnDecl decl;
      recSgnDecls rest
