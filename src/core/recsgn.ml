open Id

open Store
open Store.Cid
open Syntax

module C = Whnf
module S = Substitution
module Unify = Unify.StdTrail

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprint, _) = Debug.makeFunctions (Debug.toFlags [11])

type leftoverVars = (Abstract.free_var Int.LF.ctx * Syntax.Loc.t) list

type error =
  | UnexpectedSucess
  | TotalDeclError of name * name
  | MutualTotalDecl of name
  | MutualTotalDeclAfter of name
  | NoPositive of string
  | NoStratify of string
  | NoStratifyOrPositive of string
  | TotalArgsError of name
  | IllegalOptsPrag of string
  | IllegalOperatorPrag of name * Ext.Sgn.fix * int
  | InvalidOpenPrag of string
  | InvalidAbbrev of string list * string

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
	| TotalDeclError (f, f') ->
	  Format.fprintf ppf "Expected totalilty declaration for %s \nFound totality declaration for %s\n"
	    (Id.render_name f) (Id.string_of_name f')
	| MutualTotalDecl f ->
	  Format.fprintf ppf "All functions in a mutual function declaration must be declared total.\nFunction %s does not have a totality declaration.\n" (Id.render_name f)
	| MutualTotalDeclAfter f ->
	  Format.fprintf ppf "Function %s has a totality declaration, but not all mutually recursive functions have a totality declaration.\n" (Id.render_name f)
   	| NoPositive n ->
	  Format.fprintf ppf "Positivity checking of constructor %s fails.\n" n
	| NoStratify n ->
	  Format.fprintf ppf "Stratification checking of constructor %s fails.\n" n

	| NoStratifyOrPositive n ->
	  Format.fprintf ppf "Stratification or positivity checking of datatype %s fails.\n" n
	| TotalArgsError f ->
	  Format.fprintf ppf "Totality declaration for %s takes too many arguments.\n" (Id.render_name f)

      	| UnexpectedSucess ->
      	  Format.fprintf ppf "Unexpected success: expected failure of type reconstruction for %%not'ed declaration."
        | IllegalOptsPrag s ->
          Format.fprintf ppf "\"%s\" pragma must appear before any declarations." s
        | IllegalOperatorPrag(n, f, actual) -> begin
          let (fix, expected) = match f with Ext.Sgn.Infix -> ("infix", 2) | Ext.Sgn.Postfix -> ("postfix", 1) in
          Format.fprintf ppf
            "Illegal %s operator %s. Operator declared with %d arguments, but only operators with %d args permitted"
            (fix)
            (Id.render_name n)
            (actual)
            (expected) end
      | InvalidOpenPrag s ->
        Format.fprintf ppf "Invalid module in pragma '%%open %s'" s
      | InvalidAbbrev (l, s) ->
        Format.fprintf ppf "Invalid module in pragma '%%abbrev %s %s'"
      	  (String.concat "." l) s
				  )
  )

let print_leftoverVars = function
  | [] -> ()
  | (_cQ, loc):: rest ->
    Format.fprintf Format.std_formatter "\n%s@." (Syntax.Loc.to_string loc) ;
    ()

let rec stripInd tau = match tau with
  | Int.Comp.TypArr (tau1, tau2) ->
      Int.Comp.TypArr (stripInd tau1, stripInd tau2)
  | Int.Comp.TypCross (tau1, tau2) ->
      Int.Comp.TypCross (stripInd tau1, stripInd tau2)
  | Int.Comp.TypInd tau ->
      stripInd tau
  | Int.Comp.TypPiBox (cdec, tau) ->
      Int.Comp.TypPiBox (cdec, stripInd tau)
  | tau -> tau

let rec lookupFun cG f = match cG with
  | Int.LF.Dec (cG', Int.Comp.CTypDecl (f',  tau, false)) ->
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
  |Ext.Sgn.CompTyp (_, n, _, _) -> let a =   CompTyp.index_of_name n in
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

let recSgnDecls decls =
  let leftoverVars : leftoverVars ref = ref [] in
  let is_empty = function
    | Int.LF.Empty -> true
    | _ -> false
  in
  let storeLeftoverVars (cQ : Abstract.free_var Int.LF.ctx) (loc : Syntax.Loc.t) : unit =
    match cQ with
      | Int.LF.Empty -> ();
      | _ -> leftoverVars := (cQ, loc) :: !leftoverVars ; ()
  in
  let rec recSgnDecls' = function
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
      else recSgnDecls' rest

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
      let rest' = recSgnDecls' rest in
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
        let _ = dprint(fun () -> "Pragma found for " ^ (Id.render_name name)) in

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
        (* index cT  in a context which contains arguments to cK *)
        let (apx_tau, apxK) = Index.comptypdef  (cT, cK) in

        let ((cD,tau), i, cK) = Reconstruct.comptypdef loc a (apx_tau, apxK) in
	let _         = dprint (fun () ->  "typedef " ^ (string_of_name a) ^ " : " ^
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

      | Ext.Sgn.CompTyp (loc , a, extK, pflag) ->
        let _ = dprint (fun () -> "\nIndexing computation-level data-type constant " ^ (string_of_name a)) in
        let apxK = Index.compkind extK in
        let _ = FVar.clear () in
        let _ = dprint (fun () -> "\nElaborating data-type declaration " ^ (string_of_name a)) in
        let cK = Monitor.timer ("CType Elaboration" ,
				(fun () -> let cK = Reconstruct.compkind apxK in
					   Reconstruct.solve_fvarCnstr Lfrecon.Pibox; cK
				)) in
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let (cK', i) = Monitor.timer ("Type Abstraction",
                                      fun () -> Abstract.compkind cK) in

        let _        = (Reconstruct.reset_fvarCnstr ();
			Unify.resetGlobalCnstrs ();
			dprint (fun () ->  (string_of_name a) ^
			  " : " ^  (P.compKindToString Int.LF.Empty cK'))) in
	Monitor.timer ("Type Check",
		       fun () -> Check.Comp.checkKind  Int.LF.Empty cK');
	dprint (fun () ->  "\nDOUBLE CHECK for data type constant " ^(string_of_name a) ^
          " successful!");
	(* let p = match pflag with  *)
	(*   | None -> Int.Sgn. Noflag  *)
	(*   | Some Ext. Sgn.Stratify  (_loc, x, Id.mk_name (Id.SomeString r), args)  *)
	(*         -> Int.Sgn.Stratify   (_loc, x, Id.mk_name (Id.SomeString r), args)  *)
	(*   | Some _ -> Int.Sgn.Positivity *)

	let p = (match pflag with
	  | Ext.Sgn.StratifiedDatatype -> Int.Sgn.StratifyAll loc
	  | Ext.Sgn.InductiveDatatype -> Int.Sgn.Positivity
        ) in
	Total.stratNum := -1 ;
        let _a = CompTyp.add (CompTyp.mk_entry a cK' i p) in
        let sgn = Int.Sgn.CompTyp(loc, a, cK', p) in
        Store.Modules.addSgnToCurrent sgn;
        sgn

      | Ext.Sgn.CompCotyp (loc , a, extK) ->
        dprint (fun () -> "[RecSgn Checking] CompCotyp at: \n" ^ Syntax.Loc.to_string loc);
        let _ = dprint (fun () -> "\nIndexing computation-level codata-type constant " ^ (string_of_name a)) in
        let apxK = Index.compkind extK in
        let _ = FVar.clear () in
        let _ = dprint (fun () -> "\nElaborating codata-type declaration " ^ (string_of_name a)) in
        let cK = Monitor.timer ("CType Elaboration" ,
				(fun () -> let cK = Reconstruct.compkind apxK in
					   Reconstruct.solve_fvarCnstr Lfrecon.Pibox; cK
				)) in
        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let (cK', i) = Monitor.timer ("Type Abstraction",
                                      fun () -> Abstract.compkind cK) in

        let _        = (Reconstruct.reset_fvarCnstr ();
                        Unify.resetGlobalCnstrs ();
                        dprint (fun () ->  (string_of_name a) ^
                          " : " ^  (P.compKindToString Int.LF.Empty cK'))) in
        Monitor.timer ("Type Check",
		       fun () -> Check.Comp.checkKind  Int.LF.Empty cK');
        dprint (fun () ->  "\nDOUBLE CHECK for codata type constant " ^(string_of_name a) ^
          " successful!");
        let _a = CompCotyp.add (CompCotyp.mk_entry a cK' i) in
        let sgn = Int.Sgn.CompCotyp(loc, a, cK') in
        Store.Modules.addSgnToCurrent sgn;
        sgn


      | Ext.Sgn.CompConst (loc , c, tau) ->
        dprint (fun () -> "[RecSgn Checking] CompConst at: \n" ^ Syntax.Loc.to_string loc);
        let _         = dprint (fun () -> "\nIndexing computation-level data-type constructor " ^ (string_of_name c)) in
        let apx_tau   = Index.comptyp tau in
        let cD        = Int.LF.Empty in
        let _         = dprint (fun () -> "\nElaborating data-type constructor " ^ (string_of_name c)) in
        let tau'      = Monitor.timer ("Data-type Constant: Type Elaboration",
				       fun () -> Reconstruct.comptyp apx_tau)  in
        let _         = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
	let _         = dprint (fun () -> "Abstracting over comp. type") in
        let (tau', i) = Monitor.timer ("Data-type Constant: Type Abstraction",
				       fun () -> Abstract.comptyp tau') in
	let _         = dprint (fun () -> "Abstracting over comp. type: done") in
	let _         = dprint (fun () ->  (string_of_name c) ^ " : " ^
				  (P.compTypToString cD tau')) in
	let _         = (Monitor.timer ("Data-type Constant: Type Check",
					fun () -> Check.Comp.checkTyp cD tau'))  in	
	let cid_ctypfamily = get_target_cid_comptyp tau' in

	let flag = (CompTyp.get cid_ctypfamily).CompTyp.positivity in

	  (match flag with
	     | Int.Sgn.Nocheck    -> ()
	     | Int.Sgn.Positivity ->  if Total.positive cid_ctypfamily tau' then ()
	       else raise (Error (loc, (NoPositive (string_of_name c))))
	     | Int.Sgn.Stratify (loc_s, n)   -> if Total.stratify cid_ctypfamily tau' n then ()
	       else raise (Error (loc, (NoStratify (string_of_name c))))
	     | Int.Sgn.StratifyAll loc_s   ->
		 let t =  Total.stratifyAll cid_ctypfamily tau' in
		 let t' = (t land (!Total.stratNum)) in
		   if t'<>0 then Total.stratNum := t'
		   else raise (Error (loc_s, (NoStratifyOrPositive  (R.render_cid_comp_typ cid_ctypfamily) )))
	);
	(* if true (\* Total.stratifyAll cid_ctypfamily tau'  *\)then () *)
	(* else raise (Error (loc, (NoStratify (string_of_name c)))) *)


	(* (if flag then if Total.positive cid_ctypfamily tau' then ()  *)
        (*                        else raise (Error (loc, (NoPositive (string_of_name c)))) *)
	(* else () ); *)
        let _c        = CompConst.add cid_ctypfamily (CompConst.mk_entry c tau' i) in
        let sgn = Int.Sgn.CompConst(loc, c, tau') in
        Store.Modules.addSgnToCurrent sgn;
        sgn



   | Ext.Sgn.CompDest (loc , c, cD, tau0, tau1) ->
        dprint (fun () -> "[RecSgn Checking] CompDest at: \n" ^ Syntax.Loc.to_string loc);
        let _         = dprint (fun () -> "\nIndexing computation-level codata-type destructor " ^ (string_of_name c)) in
        let cD = Index.mctx cD in
        let cD = Reconstruct.mctx cD in
        let apx_tau0  = Index.comptyp tau0 in
        let apx_tau1  = Index.comptyp tau1 in
        let _         = dprint (fun () -> "\nElaborating codata-type destructor " ^ (string_of_name c)) in
        let tau0'      = Monitor.timer ("Codata-type Constant: Type Elaboration",
                                        fun () -> Reconstruct.comptyp_cD cD apx_tau0)  in
        let tau1'      = Monitor.timer ("Codata-type Constant: Type Elaboration",
                                        fun () -> Reconstruct.comptyp_cD cD apx_tau1)  in
        let _         = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let _         = dprint (fun () -> "Abstracting over comp. type") in
        let (cD1, tau0', tau1', i) = Monitor.timer ("Codata-type Constant: Type Abstraction",
                                        fun () -> Abstract.codatatyp cD tau0' tau1') in
        let _ = dprint (fun () -> "cD1 = " ^ P.mctxToString cD1) in
        let _         = dprint (fun () -> "tau1' = " ^ P.compTypToString cD1 tau1') in
        let _         = dprint (fun () -> "Abstracting over comp. type: done") in
        let _         = dprint (fun () ->  (string_of_name c) ^ " : " ^
                                           (P.compTypToString cD1 tau0') ^ " :: " ^
                                           (P.compTypToString cD1 tau1')) in
        let _         = (Monitor.timer ("Codata-type Constant: Type Check",
                                        fun () -> Check.Comp.checkTyp cD1 tau0')) in
        let _         = (Monitor.timer ("Codata-type Constant: Type Check",
                                        fun () -> Check.Comp.checkTyp cD1 tau1')) in
        let cid_ctypfamily = get_target_cid_compcotyp tau0' in
        let _c        = CompDest.add cid_ctypfamily (CompDest.mk_entry c cD1 tau0' tau1' i) in
        let sgn = Int.Sgn.CompDest(loc, c, cD1, tau0', tau1') in
        Store.Modules.addSgnToCurrent sgn;
        sgn


    | Ext.Sgn.Typ (loc, a, extK)   ->
        dprint (fun () -> "[RecSgn Checking] Typ at: \n" ^ Syntax.Loc.to_string loc);
        let _        = dprint (fun () -> "\nIndexing type constant " ^ (string_of_name a)) in
        let (apxK, _ ) = Index.kind extK in
        let _        = FVar.clear () in

        let _        = dprint (fun () -> "\nElaborating type constant " ^ (string_of_name a)) in

        let tK       = Monitor.timer ("Type Elaboration",
                                      fun () -> (let tK = Reconstruct.kind apxK in
                                                   Reconstruct.solve_fvarCnstr Lfrecon.Pi; tK )) in

        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in

        let (tK', i) = Monitor.timer ("Type Abstraction",
                                      fun () -> Abstract.kind tK) in
        let _        = (Reconstruct.reset_fvarCnstr ();
			Unify.resetGlobalCnstrs ();
			dprint (fun () ->  (string_of_name a) ^ " : " ^  (P.kindToString Int.LF.Null (tK', S.LF.id)));
			Monitor.timer ("Type Check",
				       fun () -> Check.LF.checkKind Int.LF.Empty Int.LF.Null tK');
			dprint (fun () ->  "\nDOUBLE CHECK for type constant " ^(string_of_name a) ^
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
        let _          = dprint (fun () -> "Reconstructing term constant " ^ (string_of_name c)) in

        let _        = FVar.clear () in
        let tA       = Monitor.timer ("Constant Elaboration",
                                      fun () -> (let tA = Reconstruct.typ Lfrecon.Pi  apxT in
                                                   Reconstruct.solve_fvarCnstr Lfrecon.Pi; tA)) in
        let cD       = Int.LF.Empty in

        let _        = dprint (fun () -> "\nElaboration of constant " ^ (string_of_name c) ^ " : " ^
                                         P.typToString cD Int.LF.Null (tA, S.LF.id)) in

        let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
        let (tA', i) = Monitor.timer ("Constant Abstraction",
                                      fun () -> Abstract.typ tA) in
	let _        = ( Reconstruct.reset_fvarCnstr ();
			 Unify.resetGlobalCnstrs ();
        		 dprint (fun () -> "\nReconstruction (with abstraction) of constant: " ^
				   (string_of_name c) ^ " : " ^
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
        let _        = dprint (fun () -> "\nReconstructing schema " ^ (string_of_name g) ^ "\n") in
        let _        = FVar.clear () in
        let sW       = Reconstruct.schema apx_schema in
        let _        = (dprint (fun () -> "\nElaborated schema " ^ (string_of_name g) ^ " : " ^ P.schemaToString sW);
			Reconstruct.solve_fvarCnstr Lfrecon.Pi;
			Unify.forceGlobalCnstr (!Unify.globalCnstrs);
			Reconstruct.reset_fvarCnstr ();
			Unify.resetGlobalCnstrs ()) in

        let sW'      = Abstract.schema sW in
	let _        = dprint (fun () -> "\nSchema " ^  (string_of_name g) ^ " : " ^ P.schemaToString sW' ^ " after abstraction " ) in
        let _ = Check.LF.checkSchemaWf sW' in
      	 dprint (fun () -> "\nTYPE CHECK for schema " ^ (string_of_name g) ^ " successful" );
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

          let _                  = dprint (fun () ->  "\n [AFTER Reconstruction Val] let " ^ (string_of_name x) ^
					     "\n   : " ^ P.compTypToString cD tau' ^
					     "\n  =  " ^
                                P.expSynToString cD cG i' ^ "\n") in
          let cQ, i''             = Monitor.timer ("Function Abstraction", fun () ->
						    Abstract.exp (Int.Comp.Syn (loc, i'))) in
	  let _                  = storeLeftoverVars cQ loc in
          let _                  = Monitor.timer ("Function Check", fun () ->
						    Check.Comp.check cD  cG i'' (tau', C.m_id)) in

	  let v = if Holes.none () && is_empty cQ then
	    begin
              let v = Opsem.eval i'' in
              let _x = Comp.add loc (fun _ -> Comp.mk_entry x tau' 0 false v []) in
		Some v
	  end
	  else None in
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
          let _       = dprint (fun () ->  "\n [AFTER Reconstruction Val - 2] let " ^ (string_of_name x) ^
                               "\n   : " ^ P.compTypToString cD tau' ^
                                "\n  =  " ^
                                P.expChkToString cD cG i' ^ "\n") in

          let cQ, i''  = Monitor.timer ("Function Abstraction", fun () -> Abstract.exp i') in
	  let _       = storeLeftoverVars cQ loc in
          let _       = Monitor.timer ("Function Check", fun () -> Check.Comp.check cD  cG i'' (tau', C.m_id)) in

	  let v = if Holes.none () && is_empty cQ then begin
            let v = Opsem.eval i'' in
            let _ = Comp.add loc (fun _ -> Comp.mk_entry x tau' 0 false v []) in Some v
            end else None in
	  let sgn = Int.Sgn.Val(loc, x, tau', i'', v) in
	  let _ = Store.Modules.addSgnToCurrent sgn in
	    sgn

    | Ext.Sgn.MRecTyp (loc, recDats) ->
        let recTyps   = List.map (fun (k,_) -> k) recDats in
        let recTyps'  = List.map (recSgnDecl ~pauseHtml:true) recTyps in
        let recConts  = List.map (fun (_,cs) -> cs) recDats in
        let recConts' = List.map (List.map (recSgnDecl ~pauseHtml:true)) recConts in
        let  _  = List.map freeze_from_name recTyps in
        Int.Sgn.MRecTyp (loc, List.map2 (fun x y -> x::y) recTyps' recConts')

    | Ext.Sgn.Rec (loc, recFuns) ->
        (* let _       = Printf.printf "\n Indexing function : %s  \n" f.string_of_name  in   *)
        let (cO, cD)   = (Int.LF.Empty, Int.LF.Empty) in

        let rec pos loc x args k = match args with
          | [] -> raise (Index.Error (loc, Index.UnboundName x))
          | (Some y)::ys -> if x = y then k else pos loc x ys (k+1)
          | None::ys -> pos loc x ys (k+1)
        in
        let mk_total_decl f (Ext.Comp.Total (loc, order, f', args)) =
	  (* print_string ("args length: "^string_of_int (List.length args) ^"\n" ); *)
	  if f = f' then
            match order with
              | Some (Ext.Comp.Arg x) ->
                let p = pos loc x args 1 in  (Some (Order.Arg p) , args)
	      | None -> (None, [])
	  else
	    raise (Error (loc, TotalDeclError (f, f')))

        in
        let is_total total =
          match total with None -> false | Some _ -> true in

        let rec preprocess l m = match l with
          | [] -> (Int.LF.Empty, Var.create (), [])
          | Ext.Comp.RecFun (loc, f, total, tau, _e) :: lf ->
              let apx_tau = Index.comptyp  tau in
	      (* print_string ("Reconstructing function " ^  (string_of_name f) ^ " \n"); *)
              let _       = dprint (fun () ->  "Reconstructing function " ^  (string_of_name f) ^ " \n") in
              let tau'    = Monitor.timer ("Function Type Elaboration", fun () -> Reconstruct.comptyp apx_tau)  in
              let _       = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
                (* Are some FMVars delayed since we can't infer their type? - Not associated with pattsub *)
              let _        = dprint (fun () ->  "Elaboration of function type " ^ (string_of_name f) ^
                                       " \n : " ^  (P.compTypToString cD tau') ^ " \n\n" )   in

              let (tau', _i) = Monitor.timer ("Function Type Abstraction", fun () -> Abstract.comptyp tau') in
              let _ = dprint (fun () ->  "Abstracted elaborated function type " ^ (string_of_name f) ^
                            " \n : " ^  (P.compTypToString cD tau') ^ " \n\n" )   in


              (* print_string ( "Abstracted elaborated function type " ^ (string_of_name f) ^ *)
              (*               " \n : " ^  (P.compTypToString cD tau') ^ " \n\n" ) ; *)

              let  _      = Monitor.timer ("Function Type Check", fun () -> Check.Comp.checkTyp cD tau') in
              let _       = dprint (fun () -> "Checked computation type " ^ (P.compTypToString cD tau') ^ " successfully\n\n")  in
              let _       = FCVar.clear () in
                (* check that names are unique ? *)
                (begin match total with
                  | None ->
		    if !Total.enabled then
		      raise (Error (loc, MutualTotalDecl f))
		    else
		      ()
		  | Some (Ext.Comp.Trust _) -> ()
                  | Some t ->
		    if !Total.enabled then
		      ((*print_string ("Encountered total declaration for " ^ Id.render_name f ^ "\n"); *)
	   	      Total.extend_dec (Total.make_dec loc f tau' (mk_total_decl f t)))
		    else
		      (if m = 1 then
			  ( (*Coverage.enableCoverage := true; *)
			   Total.enabled := true;
			   (* print_string ("Encountered total declaration for " ^ Id.render_name f ^ "\n"); *)
			   Total.extend_dec (Total.make_dec loc f tau' (mk_total_decl f t)))
		       else
			  raise (Error (loc, MutualTotalDeclAfter f))
		      )
                end ;
		 let (cG, vars, n_list) = preprocess lf (m+1) in
                 (Int.LF.Dec(cG, Int.Comp.CTypDecl (f, stripInd tau',false)) , Var.extend  vars (Var.mk_entry f), f::n_list ))

        in

        let (cG , vars', n_list ) = preprocess recFuns 1 in

        let reconFun loc f  e =
          let apx_e   = Index.exp vars' e in
          let _       = dprint (fun () -> "\n  Indexing expression done \n") in
          let tau'    = lookupFun cG f in
          let e'      = Monitor.timer ("Function Elaboration", fun () ->
					 Reconstruct.exp cG apx_e (stripInd tau', C.m_id)) in

          let _       = dprint (fun () ->  "\n Elaboration of function " ^ (string_of_name f) ^
                                  "\n   type: " ^ P.compTypToString cD tau' ^
                                  "\n   result:  " ^
                                  P.expChkToString cD cG e' ^ "\n") in

          let _        = begin try
                           Unify.forceGlobalCnstr (!Unify.globalCnstrs)
                        with Unify.GlobalCnstrFailure (loc,cnstr) ->
                          raise (Check.Comp.Error  (loc, Check.Comp.UnsolvableConstraints (Some f, cnstr)))
                        end
          in
          let _        = Unify.resetGlobalCnstrs () in

          (* let e_r     = Monitor.timer ("Function Reconstruction", fun () -> check  cO cD cG e' (tau', C.m_id)) in  *)

          let _       = dprint (fun () ->  "\n [AFTER reconstruction] Function " ^ (string_of_name f) ^
                               "\n   type: " ^ P.compTypToString cD tau' ^
                                "\n   result:  " ^
                                P.expChkToString cD cG e' ^ "\n") in

          let e''     = Whnf.cnormExp (e', Whnf.m_id) in
          let cQ, e_r' = Monitor.timer ("Function Abstraction", fun () -> Abstract.exp e'' ) in
	  let _       = storeLeftoverVars cQ loc in
          let e_r'    = Whnf.cnormExp (e_r', Whnf.m_id) in

	  let tau_ann = if !Total.enabled then Total.annotate loc f tau'
 	                else tau' in
          let _       = Monitor.timer ("Function Check", fun () ->
					    Check.Comp.check
					      cD cG e_r' (tau_ann, C.m_id)
                                      ) in
             (e_r' , tau')
        in

        let rec reconRecFun recFuns = match recFuns with
          | [] ->   (Coverage.enableCoverage := !Coverage.enableCoverage ;
                     Total.enabled := false;
                     [])
          | Ext.Comp.RecFun (loc, f, total, _tau, e) :: lf ->
            let (e_r' , tau') = reconFun loc f  e in
              (* begin match total with
                | None -> ()
		| Some (Ext.Comp.Trust _) ->
		      Printf.printf "\n## Totality checking: %s is trusted. ##\n"
			    (Id.render_name f)
		| Some t ->
	          let x = get_rec_arg t in
		  (match x with
		    | Some x ->
		      Printf.printf "\n## Totality checking: %s terminates in position %s ##\n"
			(Id.render_name f) (Id.string_of_name x)
		    | None ->
		      Printf.printf "\n## Totality checking: %s terminates. ##\n"
			(Id.render_name f) )

              end ;*)
              dprint (fun () -> "DOUBLE CHECK of function " ^ (string_of_name f) ^ " successful!\n\n");
              let (loc_opt, cid) = Comp.add loc
		(fun cid ->
                  Comp.mk_entry f tau' 0 (is_total total)
                    (Int.Comp.RecValue (cid, e_r', Int.LF.MShift 0, Int.Comp.Empty))
                    n_list) in
	      let _ = match loc_opt with
                | Some loc -> Holes.destroyHoles(loc)
                | None -> () in
              let _ = Holes.commitHoles() in
		(cid, tau', e_r')::(reconRecFun lf) in
	  (* For checking totality of mutual recursive functions,
	     we should check all functions together by creating a variable
	     which collects all total declarations *)
          begin match recFuns with
            | Ext.Comp.RecFun (loc, f, total, _tau, e) :: lf ->
		let (e_r' , tau') = reconFun loc f e in
		  (* begin match total with
		    | None -> ()
		    | Some (Ext.Comp.Trust _ ) ->
			Printf.printf "\n## Totality checking: %s is trusted. ##\n"
			  (Id.render_name f)
		    | Some t -> let x = get_rec_arg t in
			Total.clear () ;
			(match x with
			   | Some x ->
			       Printf.printf "\n## Totality checking: %s terminates in position %s ##\n"
				 (Id.render_name f) (Id.string_of_name x)
			   | None ->
			       Printf.printf "\n## Totality checking: %s terminates ##\n"
				 (Id.render_name f))
		  end ;*)
		  dprint (fun () -> "DOUBLE CHECK of function " ^ (string_of_name f) ^ " successful!\n");
		  let (loc_opt, cid) = Comp.add loc
		    (fun cid ->
                       Comp.mk_entry  f tau' 0 (is_total total)
			 (Int.Comp.RecValue (cid, e_r', Int.LF.MShift 0, Int.Comp.Empty))
			 n_list) in
		  let _ = match loc_opt with
		    | Some loc -> Holes.destroyHoles(loc)
		    | None -> () in
		  let _ = Holes.commitHoles() in
		  let _ = Total.clear () in
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


      let _        = dprint (fun () -> "\nElaboration of query : " ^  P.typToString cD Int.LF.Null (tA, S.LF.id)) in

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

  in
  let decls' = recSgnDecls' decls in
  match !leftoverVars with
    | [] -> decls', None
    | _  -> decls', Some !leftoverVars
