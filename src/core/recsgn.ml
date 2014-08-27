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
  | IllegalOptsPrag of string
  | IllegalOperatorPrag of name * Ext.Sgn.fix * int
  | InvalidOpenPrag of string
  | InvalidAbbrev of string list * string

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
      	| UnexpectedSucess ->
      	  Format.fprintf ppf "Unexpected success: expected failure of type reconstruction for %%not'ed declaration."
        | IllegalOptsPrag s ->
          Format.fprintf ppf "\"%s\" pragma must appear before any declarations." s
        | IllegalOperatorPrag(n, f, actual) -> begin 
          let (fix, expected) = match f with Ext.Sgn.Infix -> ("infix", 2) | Ext.Sgn.Postfix -> ("postfix", 1) in
          Format.fprintf ppf 
            "Illegal %s operator %s. Operator declared with %d arguments, but only operators with %d args permitted" 
            (fix)
            (R.render_name n)
            (actual)
            (expected) end
      | InvalidOpenPrag s ->
        Format.fprintf ppf "Invalid module in pragma '%%open %s'" s
      | InvalidAbbrev (l, s) ->
        Format.fprintf ppf "Invalid module in pragma '%%abbrev %s %s'" (String.concat "." l) s))

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

let sgnDeclToHtml = function
  | Ext.Sgn.Comment (_, x) -> Html.appendAsComment x
  | d -> 
    let margin = Format.pp_get_margin Format.str_formatter () in
    let _ = Html.printingHtml := true in
    (* let _ = Format.set_margin 150 in *)
    let _ = Format.pp_set_margin Format.str_formatter 200 in
    let _ = Prettyext.Ext.DefaultPrinter.fmt_ppr_sgn_decl Prettyext.std_lvl Format.str_formatter d in
    let _ = Html.append (Format.flush_str_formatter ()) in
    let _ = Format.pp_set_margin (Format.str_formatter) margin in
    Html.printingHtml := false

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

  | Ext.Sgn.GlobalPragma(loc, Ext.Sgn.Coverage `Warn ) :: rest ->
    raise (Error (loc, IllegalOptsPrag "%warncoverage"))
  | Ext.Sgn.GlobalPragma(loc, Ext.Sgn.Coverage `Error ) :: rest ->
    raise (Error (loc, IllegalOptsPrag "%coverage"))
  | Ext.Sgn.GlobalPragma(loc, Ext.Sgn.NoStrengthen) :: rest ->
    raise (Error (loc, IllegalOptsPrag "%nostrengthen"))

  | decl :: rest ->
    let decl' = recSgnDecl decl in
    let rest' = recSgnDecls rest in
    decl'::rest'

and recSgnDecl ?(pauseHtml=false) d =
    Reconstruct.reset_fvarCnstr ();  FCVar.clear ();
    if !Html.genHtml && not pauseHtml then sgnDeclToHtml d;
    match d with
    | Ext.Sgn.Comment (l, s) -> Int.Sgn.Comment(l, s)
        
    | Ext.Sgn.Pragma(loc, Ext.Sgn.AbbrevPrag(orig, abbrev)) ->
      begin try Store.Modules.addAbbrev orig abbrev 
      with Not_found -> raise (Error(loc, InvalidAbbrev(orig, abbrev))) end;
      Int.Sgn.Pragma(Int.LF.AbbrevPrag(orig, abbrev))
    | Ext.Sgn.Pragma(loc, Ext.Sgn.DefaultAssocPrag a) -> OpPragmas.default := a; 
        let a' = match a with
        | Ext.Sgn.Left -> Int.LF.Left
        | Ext.Sgn.Right -> Int.LF.Right
        | Ext.Sgn.None -> Int.LF.NoAssoc in
        Int.Sgn.Pragma(Int.LF.DefaultAssocPrag a')
    | Ext.Sgn.Pragma(loc, Ext.Sgn.FixPrag (name, fix, precedence, assoc)) -> 
        let _ = dprint(fun () -> "Pragma found for " ^ (R.render_name name)) in
        
        if fix = Ext.Sgn.Prefix then 
          OpPragmas.addPragma name fix (Some precedence) assoc
        else begin
          let args_expected = match fix with
            | Ext.Sgn.Postfix -> 1
            | Ext.Sgn.Infix   -> 2 in
          
          let actual = 
            try Some (Typ.args_of_name name)
            with _ -> 
              try Some (Term.args_of_name name)
              with _ -> None in
          match actual with
          | None -> ()
          | Some actual -> 
            if args_expected = actual then 
              OpPragmas.addPragma name fix (Some precedence) assoc
            else raise (Error(loc, IllegalOperatorPrag(name, fix, actual)))
        end; 
        let assoc' = match assoc with
        | None -> None
        | Some x -> Some(match x with
          | Ext.Sgn.Left -> Int.LF.Left
          | Ext.Sgn.Right -> Int.LF.Right
          | Ext.Sgn.None -> Int.LF.NoAssoc) in
        let fix' = match fix with
          | Ext.Sgn.Postfix -> Int.LF.Postfix
          | Ext.Sgn.Prefix -> Int.LF.Prefix
          | Ext.Sgn.Infix -> Int.LF.Infix in
        Int.Sgn.Pragma(Int.LF.FixPrag(name, fix', precedence, assoc'))

    | Ext.Sgn.CompTypAbbrev (loc, a, cK, cT) ->
        dprint (fun () -> "[RecSgn Checking] CompTypAbbrev at: \n" ^ Syntax.Loc.to_string loc);
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
        dprint (fun () -> "[RecSgn Checking] CompTyp at: \n" ^ Syntax.Loc.to_string loc);
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


  | Ext.Sgn.CompCotyp (loc , a, extK) ->
        dprint (fun () -> "[RecSgn Checking] CompCotyp at: \n" ^ Syntax.Loc.to_string loc);
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
        dprint (fun () -> "[RecSgn Checking] CompConst at: \n" ^ Syntax.Loc.to_string loc);
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
        dprint (fun () -> "[RecSgn Checking] CompDest at: \n" ^ Syntax.Loc.to_string loc);
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


    | Ext.Sgn.Typ (loc, a, extK)   ->
        dprint (fun () -> "[RecSgn Checking] Typ at: \n" ^ Syntax.Loc.to_string loc);
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
        let _ = Typeinfo.Sgn.add loc (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Kind tK')) "" in
        let _a = Typ.add (Typ.mk_entry a tK' i) in
        let sgn = Int.Sgn.Typ(loc, _a, tK') in
        Store.Modules.addSgnToCurrent sgn;
        sgn

    | Ext.Sgn.Const (loc, c, extT) ->
        dprint (fun () -> "[RecSgn Checking] Const at: \n" ^ Syntax.Loc.to_string loc);
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
        let _ = Typeinfo.Sgn.add loc (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Typ tA')) "" in
	      let _c = Term.add loc constructedType (Term.mk_entry c tA' i) in
        let sgn = Int.Sgn.Const(loc, _c, tA') in
        Store.Modules.addSgnToCurrent sgn;
        sgn

    | Ext.Sgn.Schema (loc, g, schema) ->
        dprint (fun () -> "[RecSgn Checking] Schema at: \n" ^ Syntax.Loc.to_string loc);
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
          dprint (fun () -> "[RecSgn Checking] Val at: \n" ^ Syntax.Loc.to_string loc);
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

    let v = if Holes.none () then begin
            let v = Opsem.eval i'' in
            let _ = Comp.add loc (fun _ -> Comp.mk_entry x tau' 0 v []) in Some v
    end else None in
    let sgn = Int.Sgn.Val(loc, x, tau', i'', v) in
    let _ = Store.Modules.addSgnToCurrent sgn in
    sgn

    | Ext.Sgn.Val (loc, x, Some tau, i) ->
          dprint (fun () -> "[RecSgn Checking] Val at: \n" ^ Syntax.Loc.to_string loc);
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

    let v = if Holes.none () then begin
            let v = Opsem.eval i'' in
            let _ = Comp.add loc (fun _ -> Comp.mk_entry x tau' 0 v []) in Some v
    end else None in
    let sgn = Int.Sgn.Val(loc, x, tau', i'', v) in
    let _ = Store.Modules.addSgnToCurrent sgn in
    sgn

    | Ext.Sgn.MRecTyp (loc, recDats) ->
        let recTyps = List.map List.hd recDats in
        let   recTyps'   =  List.map (recSgnDecl ~pauseHtml:true) recTyps in
        let recConts = List.map List.tl recDats in
        let   recConts'   = List.map (List.map (recSgnDecl ~pauseHtml:true)) recConts in
        let  _  = List.map freeze_from_name recTyps in
        Int.Sgn.MRecTyp (loc, List.map2 (fun x y -> x::y) recTyps' recConts')

    | Ext.Sgn.Rec (loc, recFuns) ->
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

          let _       = Monitor.timer ("Function Check: ", fun () ->                                         
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
            let (loc_opt, cid) = Comp.add loc
              (fun cid ->
                Comp.mk_entry f tau' 0
                  (Int.Comp.RecValue (cid, e_r', Int.LF.MShift 0, Int.Comp.Empty))
                  n_list) in
            let _ = match loc_opt with
              | Some loc -> Holes.destroyHoles(loc)
              | None -> () in
            let _ = Holes.commitHoles() in
            (cid, tau', e_r')::(reconRecFun lf) in
        begin match recFuns with
          | Ext.Comp.RecFun (f, _tau, e) :: lf ->
            let (e_r' , tau') = reconFun f e in
            if !Coverage.enableCoverage&& !Debug.chatter <> 0 then
              Printf.printf "\n## Coverage checking done: %s  ##\n"
                (R.render_name f);
            dprint (fun () -> "DOUBLE CHECK of function " ^ f.string_of_name ^ " successful!\n");

            let (loc_opt, cid) = Comp.add loc
              (fun cid ->
                Comp.mk_entry f tau' 0
                  (Int.Comp.RecValue (cid, e_r', Int.LF.MShift 0, Int.Comp.Empty))
                  n_list) in
            let _ = match loc_opt with
              | Some loc -> Holes.destroyHoles(loc)
              | None -> () in
            let _ = Holes.commitHoles() in
            let sgn = Int.Sgn.Rec((cid, tau', e_r')::(reconRecFun lf)) in
            Store.Modules.addSgnToCurrent sgn;
            sgn

          | _ -> raise (Error.Violation "No recursive function defined")
        end


    | Ext.Sgn.Query (loc, name, extT, expected, tries) ->
      dprint (fun () -> "[RecSgn Checking] Query at: \n" ^ Syntax.Loc.to_string loc); 
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
        dprint (fun () -> "[RecSgn Checking] Pragma at: \n" ^ Syntax.Loc.to_string loc); 
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

    | Ext.Sgn.Module(loc, name, decls) -> 

      let state = Store.Modules.getState () in
      let _ = Store.Modules.instantiateModule name in
      let decls' = List.map recSgnDecl decls in

      let _ = Store.Modules.setState state in
      let sgn = Int.Sgn.Module(loc, name, decls') in
      Store.Modules.addSgnToCurrent sgn;
      sgn

    | Ext.Sgn.Pragma(loc, Ext.Sgn.OpenPrag(n)) ->
      try 
        let x = Modules.open_module n in
        let sgn = Int.Sgn.Pragma(Int.LF.OpenPrag x) in
        Store.Modules.addSgnToCurrent sgn;
        sgn
      with Not_found -> raise (Error(loc, (InvalidOpenPrag (String.concat "." n))))
