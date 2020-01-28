open Support
open Id
open Store
open Store.Cid
open Syntax

module C = Whnf
module S = Substitution
module Unify = Unify.StdTrail

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprintf, dprint, _) = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

type leftover_vars = (Abstract.free_var Int.LF.ctx * Syntax.Loc.t) list

type error =
  | UnexpectedSucess
  | TotalDeclError of name * name
  | MutualTotalDecl
    of name list (* functions with total decls *)
       * name list (* functions without total decls *)
  | NoPositive of string
  | NoStratify of string
  | NoStratifyOrPositive of string
  | TotalArgsError of name
  | IllegalOptsPrag of string
  | IllegalOperatorPrag of name * Ext.Sgn.fix * int
  | InvalidOpenPrag of string
  | InvalidAbbrev of string list * string
  | UnboundArg of Id.name * Id.name option list
  | UnboundNamePragma of Id.name

exception Error of Syntax.Loc.t * error

let throw loc e = raise (Error (loc, e))

let _ =
  let open Format in
  Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc
      (fun ppf ->
        match err with
	      | TotalDeclError (f, f') ->
	         fprintf ppf "Expected totalilty declaration for %s \nFound totality declaration for %s\n"
	           (Id.render_name f) (Id.string_of_name f')
	      | MutualTotalDecl (haves, have_nots) ->
           fprintf ppf "@[<v>%a@,The functions@,  @[<hov>%a@]@,have totality declarations, \
                        but the functions@,  @[<hov>%a@]@,are missing totality declarations."
             pp_print_string
             "This mutual definition block does not have
              consistent totality declarations. Either all or none of
              functions must be declared total."
             (pp_print_list ~pp_sep: Fmt.comma Id.print) haves
             (pp_print_list ~pp_sep: Fmt.comma Id.print) have_nots
   	    | NoPositive n ->
	         fprintf ppf "Positivity checking of constructor %s fails.\n" n
	      | NoStratify n ->
	         fprintf ppf "Stratification checking of constructor %s fails.\n" n

	      | NoStratifyOrPositive n ->
	         fprintf ppf "Stratification or positivity checking of datatype %s fails.\n" n
	      | TotalArgsError f ->
	         fprintf ppf "Totality declaration for %s takes too many arguments.\n" (Id.render_name f)

      	| UnexpectedSucess ->
      	   fprintf ppf "Unexpected success: expected failure of type reconstruction for --not'ed declaration."
        | IllegalOptsPrag s ->
           fprintf ppf "\"%s\" pragma must appear before any declarations." s
        | IllegalOperatorPrag(n, f, actual) ->
            let (fix, expected) =
              match f with Ext.Sgn.Infix -> ("infix", 2) | Ext.Sgn.Postfix -> ("postfix", 1)
            in
            fprintf ppf
              "Illegal %s operator %s. Operator declared with %d arguments, but only operators with %d args permitted"
              (fix)
              (Id.render_name n)
              (actual)
              (expected)
        | InvalidOpenPrag s ->
           fprintf ppf "Invalid module in pragma '--open %s'" s
        | InvalidAbbrev (l, s) ->
           fprintf ppf "Invalid module in pragma '--abbrev %s %s'"
      	     (String.concat "." l) s
        | UnboundArg (a, args) ->
           fprintf ppf "Argument %a does not appear in argument list @[<h>%a@]."
             Id.print a
             (pp_print_list
                ~pp_sep: Fmt.comma
                (fun ppf ->
                  (Maybe.eliminate
                     (fun _ -> fprintf ppf "_")
                     (Id.print ppf))))
             args
        | UnboundNamePragma typ_name ->
           fprintf ppf "Name pragma refers to unbound type %a." Id.print typ_name
      )
  )

let fmt_ppr_leftover_vars ppf : leftover_vars -> unit =
  let open Format in
  fprintf ppf "@[<v>%a@]"
    (pp_print_list ~pp_sep: pp_print_cut
       begin fun ppf (cQ, loc) ->
       fprintf ppf "@[<2>@[%a@] |-@ @[%a@]@]"
         Abstract.fmt_ppr_collection cQ
         Syntax.Loc.print loc
       end)

let ppr_leftover_vars = fmt_ppr_leftover_vars Format.std_formatter

let rec get_target_cid_comptyp tau = match tau with
  | Int.Comp.TypBase (_, a, _ ) -> a
  | Int.Comp.TypArr (_, _, tau) -> get_target_cid_comptyp tau
  | Int.Comp.TypPiBox (_, _, tau) -> get_target_cid_comptyp tau
  | _ ->
     Error.violation
       "[get_target_cid_comptyp] no target comp typ"

let rec get_target_cid_compcotyp tau = match tau with
  | Int.Comp.TypCobase (_, a, _ ) -> a
  | Int.Comp.TypArr (_, tau , _) ->
     get_target_cid_compcotyp tau
     (* XXX it's strange that this walks backwards, but is called "get *target*".
        Perhaps for codatatypes this should be "source" ? -je *)
  | Int.Comp.TypPiBox (_, _, tau) -> get_target_cid_compcotyp tau
  | _ ->
     Error.violation
       "[get_target_cid_compcotyp] no target comp cotyp"

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
    let module P = Pretty.Ext.DefaultPrinter in
    let _ = P.fmt_ppr_sgn_decl Format.str_formatter d in
    let _ = Html.append (Format.flush_str_formatter ()) in
    let _ = Format.pp_set_margin (Format.str_formatter) margin in
    Html.printingHtml := false

let rec apply_global_pragmas =
  function
  | Synext.Sgn.GlobalPragma(_, Synext.Sgn.NoStrengthen) :: t ->
     Lfrecon.strengthen := false;
     apply_global_pragmas t
  | Synext.Sgn.GlobalPragma(_, Synext.Sgn.Coverage(opt))::t ->
     Coverage.enableCoverage := true;
     begin
       match opt with
       | `Warn -> Coverage.warningOnly := true
       | `Error -> ()
     end;
     apply_global_pragmas t
  | l -> l

let recSgnDecls decls =
  let leftoverVars : leftover_vars ref = ref [] in
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
	         with
           | _ ->
	            if !Debug.chatter != 0 then
                print_string ("Reconstruction fails for --not'd declaration\n");
              false
         end in
       if not'd_decl_succeeds
       then raise (Error (loc, UnexpectedSucess))
       else recSgnDecls' rest

    (* %not declaration with nothing following *)
    | [Ext.Sgn.Pragma(_, Ext.Sgn.NotPrag)] -> []

    | Ext.Sgn.GlobalPragma(loc, Ext.Sgn.Coverage `Warn ) :: rest ->
       raise (Error (loc, IllegalOptsPrag "--warncoverage"))
    | Ext.Sgn.GlobalPragma(loc, Ext.Sgn.Coverage `Error ) :: rest ->
       raise (Error (loc, IllegalOptsPrag "--coverage"))
    | Ext.Sgn.GlobalPragma(loc, Ext.Sgn.NoStrengthen) :: rest ->
       raise (Error (loc, IllegalOptsPrag "--nostrengthen"))

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
    | Ext.Sgn.Pragma(loc, Ext.Sgn.DefaultAssocPrag a) ->
       OpPragmas.default := a;
       let a' = match a with
         | Ext.Sgn.Left -> Int.LF.Left
         | Ext.Sgn.Right -> Int.LF.Right
         | Ext.Sgn.None -> Int.LF.NoAssoc in
       Int.Sgn.Pragma(Int.LF.DefaultAssocPrag a')
    | Ext.Sgn.Pragma(loc, Ext.Sgn.FixPrag (name, fix, precedence, assoc)) ->
       let _ = dprint(fun () -> "Pragma found for " ^ (Id.render_name name)) in
       if fix = Ext.Sgn.Prefix then
         OpPragmas.addPragma name fix (Some precedence) assoc
       else
         begin
           let args_expected = match fix with
             | Ext.Sgn.Postfix -> 1
             | Ext.Sgn.Infix   -> 2 in
           let actual =
             try
               Some (Typ.args_of_name name)
             with
             | _ ->
                try
                  Some (Term.args_of_name name)
                with
                | _ -> None
           in
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
       let (apx_tau, apxK) = Index.comptypdef (cT, cK) in
       let ((cD,tau), i, cK) = Reconstruct.comptypdef loc a (apx_tau, apxK) in
       dprintf
         begin fun p ->
         p.fmt "typedef %a : %a = %a"
           Id.print a
           (P.fmt_ppr_cmp_kind Int.LF.Empty P.l0) cK
           (P.fmt_ppr_cmp_typ cD P.l0) tau
         end;
       Monitor.timer
         ("Type abbrev. : Kind Check", fun () -> Check.Comp.checkKind Int.LF.Empty cK);
       Monitor.timer
         ("Type abbrev. : Type Check", fun () -> Check.Comp.checkTyp cD tau);
       let _a = CompTypDef.add (CompTypDef.mk_entry a i (cD,tau) cK) in
       let sgn = Int.Sgn.CompTypAbbrev(loc, a, cK, tau) in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.CompTyp (loc , a, extK, pflag) ->
       let _ = dprint (fun () -> "Indexing computation-level data-type constant " ^ (string_of_name a)) in
       let apxK = Index.compkind extK in
       let _ = FVar.clear () in
       let _ = dprint (fun () -> "Elaborating data-type declaration " ^ (string_of_name a)) in
       let cK =
         Monitor.timer
           ( "CType Elaboration"
           , fun () ->
             let cK = Reconstruct.compkind apxK in
					   Reconstruct.solve_fvarCnstr Lfrecon.Pibox;
             cK
				   )
       in
       let _ = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
       let (cK', i) =
         Monitor.timer
           ( "Type Abstraction"
           , fun () -> Abstract.compkind cK
           )
       in
       let _ =
         Reconstruct.reset_fvarCnstr ();
			   Unify.resetGlobalCnstrs ();
			   dprintf
           begin fun p ->
           p.fmt "%a : %a"
             Id.print a
             (P.fmt_ppr_cmp_kind Int.LF.Empty P.l0) cK'
           end
       in
	     Monitor.timer
         ( "Type Check"
         , fun () -> Check.Comp.checkKind  Int.LF.Empty cK'
         );
	     dprint
         (fun () ->
           "\nDOUBLE CHECK for data type constant " ^(string_of_name a) ^ " successful!");
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
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] CompCotyp at: %a"
             Syntax.Loc.print loc);
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

       begin
         Reconstruct.reset_fvarCnstr ();
         Unify.resetGlobalCnstrs ();
         dprintf
           begin fun p ->
           p.fmt "%a : %a"
             Id.print a
             (P.fmt_ppr_cmp_kind Int.LF.Empty P.l0) cK'
           end
       end;
       Monitor.timer ("Type Check",
		                  fun () -> Check.Comp.checkKind  Int.LF.Empty cK');
       dprint (fun () ->  "\nDOUBLE CHECK for codata type constant " ^(string_of_name a) ^
                            " successful!");
       let _a = CompCotyp.add (CompCotyp.mk_entry a cK' i) in
       let sgn = Int.Sgn.CompCotyp(loc, a, cK') in
       Store.Modules.addSgnToCurrent sgn;
       sgn


    | Ext.Sgn.CompConst (loc , c, tau) ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] CompConst at: %a"
             Syntax.Loc.print_short loc);
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
	     dprintf
         begin fun p ->
         p.fmt "[recsgn] @[<v>@[<hov>@[%a@] :@ @[%a@]@]@,with %d implicit parameters@]"
           Id.print c
				   (P.fmt_ppr_cmp_typ cD P.l0) tau'
           i
         end;
	     Monitor.timer
         ( "Data-type Constant: Type Check"
         , fun () -> Check.Comp.checkTyp cD tau');
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
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] CompDest at: %a" Syntax.Loc.print_short loc);
       let _         = dprint (fun () -> "\nIndexing computation-level codata-type destructor " ^ (string_of_name c)) in
       let cD = Index.mctx cD in
       let cD = Reconstruct.mctx cD in
       let apx_tau0  = Index.comptyp tau0 in
       let apx_tau1  = Index.comptyp tau1 in
       let _         = dprint (fun () -> "\nElaborating codata-type destructor " ^ (string_of_name c)) in
       let tau0'      = Monitor.timer ("Codata-type Constant: Type Elaboration",
                                       fun () -> Reconstruct.comptyp_cD cD apx_tau0)  in
       let tau1' =
         Monitor.timer
           ( "Codata-type Constant: Type Elaboration"
           , fun () -> Reconstruct.comptyp_cD cD apx_tau1
           )
       in
       let _         = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
       let _         = dprint (fun () -> "Abstracting over comp. type") in
       let (cD1, tau0', tau1', i) = Monitor.timer ("Codata-type Constant: Type Abstraction",
                                                   fun () -> Abstract.codatatyp cD tau0' tau1') in
       dprintf
         begin fun p ->
         p.fmt "[recSgnDecl] [CompDest] @[<v>cD1 = @[%a@]@,tau1' = @[%a@]@]"
           (P.fmt_ppr_lf_mctx P.l0) cD1
           (P.fmt_ppr_cmp_typ cD1 P.l0) tau1'
         end;
       let _         = dprint (fun () -> "Abstracting over comp. type: done") in
       dprintf
         begin fun p ->
         p.fmt "%a : %a :: %a"
           Id.print c
           (P.fmt_ppr_cmp_typ cD1 P.l0) tau0'
           (P.fmt_ppr_cmp_typ cD1 P.l0) tau1'
         end;
       Monitor.timer
         ( "Codata-type Constant: Type Check"
         , fun () -> Check.Comp.checkTyp cD1 tau0');
       Monitor.timer
         ( "Codata-type Constant: Type Check"
         , fun () -> Check.Comp.checkTyp cD1 tau1');
       let cid_ctypfamily = get_target_cid_compcotyp tau0' in
       let _c        = CompDest.add cid_ctypfamily (CompDest.mk_entry c cD1 tau0' tau1' i) in
       let sgn = Int.Sgn.CompDest(loc, c, cD1, tau0', tau1') in
       Store.Modules.addSgnToCurrent sgn;
       sgn


    | Ext.Sgn.Typ (loc, a, extK)   ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Typ at: %a"
             Syntax.Loc.print_short loc);
       let _        = dprint (fun () -> "\nIndexing type constant " ^ (string_of_name a)) in
       let (_, apxK) = Index.kind Index.disambiguate_to_fvars extK in
       let _        = FVar.clear () in

       let _        = dprint (fun () -> "\nElaborating type constant " ^ (string_of_name a)) in

       let tK       =
         Monitor.timer
           ( "Type Elaboration"
           , fun () ->
             let tK = Reconstruct.kind apxK in
             Reconstruct.solve_fvarCnstr Lfrecon.Pi;
             tK
           )
       in

       let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in

       let (tK', i) = Monitor.timer ("Type Abstraction",
                                     fun () -> Abstract.kind tK) in
       begin
         Reconstruct.reset_fvarCnstr ();
			   Unify.resetGlobalCnstrs ();
			   dprintf
           begin fun p ->
           p.fmt "%a : %a"
             Id.print a
             (P.fmt_ppr_lf_kind Int.LF.Null P.l0) tK'
           end;
			   Monitor.timer ("Type Check",
				                fun () -> Check.LF.checkKind Int.LF.Empty Int.LF.Null tK');
			   dprint (fun () ->  "\nDOUBLE CHECK for type constant " ^(string_of_name a) ^
				                      " successful!")
       end;
       let _ = Typeinfo.Sgn.add loc (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Kind tK')) "" in
       let _a = Typ.add (Typ.mk_entry a tK' i) in
       let sgn = Int.Sgn.Typ(loc, _a, tK') in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.Const (loc, c, extT) ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Const at: %a"
             Syntax.Loc.print_short loc);
       let (_, apxT) = Index.typ Index.disambiguate_to_fvars extT in
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

       dprintf
         begin fun p ->
         p.fmt "[recSgnDecl] [Const] %a : %a"
           Id.print c
           (P.fmt_ppr_lf_typ cD Int.LF.Null P.l0) tA
         end;

       let _        = Unify.forceGlobalCnstr (!Unify.globalCnstrs) in
       let (tA', i) = Monitor.timer ("Constant Abstraction",
                                     fun () -> Abstract.typ tA) in
	     begin
         Reconstruct.reset_fvarCnstr ();
			   Unify.resetGlobalCnstrs ();
         dprintf
           begin fun p ->
           p.fmt "[recSgnDecl] [Const] Reconstruction (with abstraction) of constant: %a : %a"
             Id.print c
             (P.fmt_ppr_lf_typ cD Int.LF.Null P.l0) tA'
           end;
			   Monitor.timer
           ( "Constant Check"
           , fun () -> Check.LF.checkTyp Int.LF.Empty Int.LF.Null (tA', S.LF.id));
       end;
       let _ = Typeinfo.Sgn.add loc (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Typ tA')) "" in
	     let _c = Term.add loc constructedType (Term.mk_entry c tA' i) in
       let sgn = Int.Sgn.Const(loc, _c, tA') in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.Schema (loc, g, schema) ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Schema at: %a"
             Syntax.Loc.print_short loc);
       let apx_schema = Index.schema schema in
       let _        = dprint (fun () -> "\nReconstructing schema " ^ (string_of_name g) ^ "\n") in
       let _        = FVar.clear () in
       let sW       = Reconstruct.schema apx_schema in
       begin
         dprintf
           begin fun p ->
           p.fmt "Elaborated schema %a : %a"
             Id.print g
             (P.fmt_ppr_lf_schema P.l0) sW
           end;
			   Reconstruct.solve_fvarCnstr Lfrecon.Pi;
			   Unify.forceGlobalCnstr (!Unify.globalCnstrs);
			   Reconstruct.reset_fvarCnstr ();
			   Unify.resetGlobalCnstrs ()
       end;
       let sW'      = Abstract.schema sW in
	     dprintf
         begin fun p ->
         p.fmt "Schema %a : %a after abstraction"
           Id.print g
           (P.fmt_ppr_lf_schema P.l0) sW'
         end;
       let _ = Check.LF.checkSchemaWf sW' in
       dprint (fun () -> "\nTYPE CHECK for schema " ^ (string_of_name g) ^ " successful" );
       let _s = Schema.add (Schema.mk_entry g sW') in
       let sgn = Int.Sgn.Schema(_s, sW') in
       Store.Modules.addSgnToCurrent sgn;
       sgn



    | Ext.Sgn.Val (loc, x, None, i) ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Val at: %a"
             Syntax.Loc.print_short loc);
       let apx_i = Index.exp' (Var.create ()) i in
	     let (cD, cG) = (Int.LF.Empty, Int.LF.Empty) in
       let (i', (tau, theta)) = Monitor.timer ("Function Elaboration", fun () -> Reconstruct.exp' cG apx_i) in
       Unify.forceGlobalCnstr (!Unify.globalCnstrs);
       let tau' = Whnf.cnormCTyp (tau, theta) in
       let i' = Whnf.cnormExp' (i', Whnf.m_id) in

       dprintf
         begin fun p ->
         p.fmt "[AFTER Reconstruction Val] @[<v 2>let %a : %a =@ %a@]"
           Id.print x
           (P.fmt_ppr_cmp_typ cD P.l0) tau'
           (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i'
         end;
       let cQ, i'' =
         Monitor.timer
           ( "Function Abstraction"
           , fun _ ->
             Abstract.exp (Int.Comp.Syn (loc, i')))
       in
	     storeLeftoverVars cQ loc;
       Monitor.timer
         ( "Function Check"
         , fun _ -> Check.Comp.check cD  cG [] i'' (tau', C.m_id));

	     let v =
         if Holes.none () && is_empty cQ then
	         begin
             let v = Opsem.eval i'' in
             let _x =
               Comp.add loc
                 (fun _ ->
                   Comp.(mk_entry x tau' 0 unchecked_mutual_group (Some v)))
             in
		         Some v
	         end
	       else
           None
       in
       let sgn =
         Int.Sgn.Val(loc, x, tau', i'', v)
       in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.Val (loc, x, Some tau, i) ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Val at %a"
             Syntax.Loc.print_short loc
         );
       let apx_tau = Index.comptyp tau in
	     let (cD, cG) = (Int.LF.Empty, Int.LF.Empty) in
       let tau' = Monitor.timer ("Function Type Elaboration", fun () -> Reconstruct.comptyp apx_tau)  in
       Unify.forceGlobalCnstr (!Unify.globalCnstrs);
       let (tau', _imp) =
         Monitor.timer
           ( "Function Type Abstraction"
           , fun _ -> Abstract.comptyp tau'
           )
       in
       Monitor.timer ("Function Type Check", fun () -> Check.Comp.checkTyp cD tau');
       let apx_i = Index.exp' (Var.create ()) i in
       let i' =
         Monitor.timer
           ( "Function Elaboration"
           , fun _ ->
             Reconstruct.exp cG (Apx.Comp.Syn(loc, apx_i)) (tau', C.m_id)
           )
       in
       let i' = Whnf.cnormExp (i', Whnf.m_id) in
       Unify.forceGlobalCnstr (!Unify.globalCnstrs);
       let tau'    = Whnf.cnormCTyp (tau', C.m_id) in
       dprintf
         (fun p ->
           p.fmt "[AFTER Reconstruction Val - 2] let %s : %a =@,%a"
             (Id.render_name x)
             (P.fmt_ppr_cmp_typ cD P.l0) tau'
             (P.fmt_ppr_cmp_exp_chk cD cG P.l0) i');

       let cQ, i''  =
         Monitor.timer
           ( "Function Abstraction"
           , fun () -> Abstract.exp i'
           )
       in
	     storeLeftoverVars cQ loc;
       Monitor.timer
         ( "Function Check"
         , fun _ ->
           Check.Comp.check cD  cG [] i'' (tau', C.m_id)
         );

	     let v =
         if Holes.none () && is_empty cQ then
           let v = Opsem.eval i'' in
           let _ =
             let open Comp in
             add loc
               begin fun _ ->
               mk_entry x tau' 0 unchecked_mutual_group (Some v)
               end
           in
           Some v
         else
           None
       in
	     let sgn = Int.Sgn.Val(loc, x, tau', i'', v) in
	     Store.Modules.addSgnToCurrent sgn;
	     sgn

    | Ext.Sgn.MRecTyp (loc, recDats) ->
       dprintf
         (fun p ->
           p.fmt "[recsgn] MRecTyp at %a" Loc.print_short loc);
       let recTyps   = List.map (fun (k,_) -> k) recDats in
       let recTyps'  = List.map (recSgnDecl ~pauseHtml:true) recTyps in
       let recConts  = List.map (fun (_,cs) -> cs) recDats in
       let recConts' = List.map (List.map (recSgnDecl ~pauseHtml:true)) recConts in
       let  _  = List.map freeze_from_name recTyps in
       Int.Sgn.MRecTyp (loc, List.map2 (fun x y -> x::y) recTyps' recConts')

    | Ext.Sgn.Theorem (loc, recFuns) ->
       let pos loc x args =
         match Misc.List.index_of (fun a -> a = Some x) args with
         | None -> throw loc (UnboundArg (x, args))
         | Some k -> k + 1 (* index_of is 0-based, but we're 1-based *)
       in

       let mk_total_decl f tau = function
         | None -> `partial (* no declaration -> partial function *)
         | Some d ->
            match d with
            | Ext.Comp.Trust _ -> `trust
            | Ext.Comp.NumericTotal (loc, None) -> `not_recursive
            | Ext.Comp.NumericTotal (loc, Some order) ->
               `inductive (Interactive.elaborate_numeric_order tau order)
            | Ext.Comp.NamedTotal (loc, order, f', args) ->
               (* Validate the inputs: can't have too many args or the wrong name *)
               if not (Total.is_valid_args tau (List.length args)) then
                 raise (Error (loc, TotalArgsError f));

	             if f <> f' then
                 raise (Error (loc, TotalDeclError (f, f')));

               match order with
               | None -> `not_recursive
               | Some order ->
                  (* convert to a numeric order by looking up the
                     positions of the specified arguments;
                     then convert to a proper Order.order.
                   *)
                  let order =
                    Ext.Comp.map_order (fun x -> pos loc x args) order
                    |> Order.of_numeric_order
                  in
                  `inductive order
       in

       (* Collect all totality declarations. *)
       (* and check that all or none of the declarations are present. *)
       let total_decs =
         let prelim_total_decs =
           List.map (fun t -> Ext.Sgn.(t.thm_name, t.thm_order)) recFuns
         in
         let go p =
           Maybe.filter_map
             (fun (name, x) -> if p x then Some (name, x) else None)
             prelim_total_decs
         in
         match
           go Maybe.is_some,
           go Misc.Function.(not ++ Maybe.is_some)
         with
         | [], [] ->
            Error.violation "[recSgn] empty mutual block is impossible"
         | haves, [] ->
            Total.enabled := true;
            Some (List.map Misc.Function.(Maybe.get ++ snd) haves)
         (* safe because they're haves *)
         | [], have_nots -> None
         | haves, have_nots ->
            throw loc
              (MutualTotalDecl (List.map fst haves, List.map fst have_nots))
       in

       let preprocess =
         List.map
           begin fun Ext.Sgn.{ thm_typ; thm_name; thm_loc; thm_body; _ } ->
           let apx_tau = Index.comptyp thm_typ in
           let tau' =
             Monitor.timer
               ( "Function Type Elaboration"
               , fun () -> Reconstruct.comptyp apx_tau
               )
           in
           Unify.forceGlobalCnstr (!Unify.globalCnstrs);
           (* Are some FMVars delayed since we can't infer their
              type? - Not associated with pattsub
            *)
           let (tau', _k) =
             Monitor.timer
               ( "Function Type Abstraction"
               , fun () -> Abstract.comptyp tau'
               )
           in
           Monitor.timer
             ( "Function Type Check"
             , fun () -> Check.Comp.checkTyp Int.LF.Empty tau'
             );

           FCVar.clear ();

           let tau' = Total.strip tau' in
           (* XXX do we need this strip? -je
              AFAIK tau' is not annotated.
            *)

           let register =
             fun total_decs ->
             Comp.add loc
               (fun cid -> Comp.mk_entry thm_name tau' 0 total_decs None)
             |> snd
           in
           ( ( thm_name, thm_body, thm_loc, tau')
           , register
           )
           end
       in

       let (thm_list, registers) = List.split (preprocess recFuns) in

       (* We have the elaborated types of the theorems,
          so we construct the final list of totality declarations for
          this mutual group. *)
       let total_decs =
         Maybe.map
           (List.map2
              (fun (thm_name, _, _, tau) decl ->
                mk_total_decl thm_name tau (Some decl)
                |> Int.Comp.make_total_dec thm_name tau)
              thm_list)
         total_decs
       in

       (* We have the list of all totality declarations for this group,
          so we can register each theorem in the store.
        *)
       let thm_cid_list =
         Comp.add_mutual_group total_decs
         |> Misc.Function.sequence registers
       in

       let reconThm loc (f, cid, thm, tau) =
         let apx_thm = Index.thm (Var.create ()) thm in
         dprint (fun () -> "[reconThm] Indexing theorem done.");
         let thm' =
           Monitor.timer
             ( "Function Elaboration",
               fun () ->
               Reconstruct.thm Int.LF.Empty apx_thm (Total.strip tau, C.m_id)
             )
         in
         dprintf
           begin fun p ->
           p.fmt "[reconThm] @[<v>Elaboration of theorem %a : %a@,result: @[%a@]@]"
             Id.print f
             (P.fmt_ppr_cmp_typ Int.LF.Empty P.l0) tau
             P.fmt_ppr_cmp_thm thm'
           end;
         begin
           try
             Unify.forceGlobalCnstr (!Unify.globalCnstrs)
           with Unify.GlobalCnstrFailure (loc,cnstr) ->
             raise
               ( Check.Comp.Error
                   ( loc
                   , Check.Comp.UnsolvableConstraints (Some f, cnstr)
                   )
               )
         end;

         Unify.resetGlobalCnstrs ();

         dprintf
           begin fun p ->
             p.fmt "[AFTER reconstruction] @[<v>Function %a : %a@,@[%a@]@]"
             Id.print f
             (P.fmt_ppr_cmp_typ Int.LF.Empty P.l0) tau
             P.fmt_ppr_cmp_thm thm'
           end;

         let thm'' = Whnf.cnormThm (thm', Whnf.m_id) in
         let cQ, thm_r =
           Monitor.timer
             ( "Function Abstraction"
             , fun () -> Abstract.thm thm''
             )
         in
         storeLeftoverVars cQ loc;
         (* This abstraction is for detecting leftover metavariables,
            which is an error.
          *)

         let thm_r' = Whnf.cnormThm (thm_r, Whnf.m_id) in

         let tau_ann =
           match
             let open Maybe in
             total_decs
             $ fun ds ->
               Total.lookup_dec f ds
               $ fun d ->
                 Int.Comp.(option_of_total_dec_kind d.order)
                 $> fun order ->
                    Order.list_of_order order
                    |> Maybe.get'
                         (Total.Error
                            ( loc
                            , Total.NotImplemented
                                "lexicographic order not fully supported"))
                    |> Total.annotate tau
                    |> Maybe.get'
                         (Total.Error ( loc , Total.TooManyArg f))
           with
           | None -> tau
           | Some x ->
              dprintf
                begin fun p ->
                p.fmt "[reconThm] @[<v>got annotated type:@,@[%a@]@]"
                  P.(fmt_ppr_cmp_typ Int.LF.Empty l0) x
                end;
              x
         in
         Monitor.timer
           ( "Function Check"
           , fun _ ->
             let total_decs = Maybe.get_default [] total_decs in
             Check.Comp.thm (Some cid) Int.LF.Empty Int.LF.Empty total_decs
               thm_r' (tau_ann, C.m_id)
           );
         (thm_r' , tau)
       in

       if Misc.List.null recFuns then
         Error.violation "[recsgn] no recursive function defined";

       let ds =
         let reconOne (thm_cid, (thm_name, thm_body, thm_loc, thm_typ))  =
           let (e_r' , tau') =
             reconThm loc (thm_name, thm_cid, thm_body, thm_typ)
           in
           dprintf
             begin fun p ->
             p.fmt "[reconRecFun] @[<v>DOUBLE CHECK of function %a at %a successful@,Adding definition to the store.@]"
               Id.print thm_name
               Loc.print_short thm_loc
             end;
           let v =
             Int.(Comp.ThmValue (thm_cid, e_r', LF.MShift 0, Comp.Empty))
           in
           Comp.set_prog thm_cid (Misc.const (Some v));
           let open Int.Sgn in
           { thm_name = thm_cid
           ; thm_body = e_r'
           ; thm_loc
           ; thm_typ = tau'
           }
         in
         List.map reconOne (List.combine thm_cid_list thm_list)
       in
       let decl = Int.Sgn.(Theorem ds) in
       Total.enabled := false;
       (* ^ this looks wrong, but it isn't.
          We enable total when the mutual group has totality
          declarations, and disable it before we process the next
          declaration.
          In other words, it is enabled only during elaboration of a
          mutual group declared to be total.
        *)
       Store.Modules.addSgnToCurrent decl;
       decl

    | Ext.Sgn.Query (loc, name, extT, expected, tries) ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Query at %a"
             Syntax.Loc.print_short loc);
       let (_, apxT) =
         Index.typ Index.disambiguate_to_fvars extT
       in
       dprint (fun () -> "Reconstructing query.");

       FVar.clear ();
       let tA =
         Monitor.timer
           ( "Constant Elaboration"
           , fun () ->
             let tA = Reconstruct.typ Lfrecon.Pi apxT in
             Reconstruct.solve_fvarCnstr Lfrecon.Pi;
             tA)
       in
       let cD = Int.LF.Empty in

       dprintf
         begin fun p ->
         p.fmt "Elaboration of query : %a"
           (P.fmt_ppr_lf_typ cD Int.LF.Null P.l0) tA
         end;

       Unify.forceGlobalCnstr (!Unify.globalCnstrs);

       let (tA', i) =
         Monitor.timer
           ( "Constant Abstraction"
           , fun () -> Abstract.typ tA
           )
       in

       Reconstruct.reset_fvarCnstr ();
       Unify.resetGlobalCnstrs ();
       dprintf
         begin fun p ->
           p.fmt "Reconstruction (with abstraction) of query: %a"
             (P.fmt_ppr_lf_typ cD Int.LF.Null P.l0) tA'
         end;

       Monitor.timer
         ( "Constant Check"
         , fun () ->
           Check.LF.checkTyp Int.LF.Empty Int.LF.Null (tA', S.LF.id)
         );

       Logic.storeQuery name (tA', i) expected tries;

       Int.Sgn.Query(loc, name, (tA', i), expected, tries)

    | Ext.Sgn.Pragma(loc, Ext.Sgn.NamePrag (typ_name, m_name, v_name)) ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Pragma at %a"
             Syntax.Loc.print_short loc);
       begin
         try
           let cid =
             match v_name with
             | None ->
                Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name)) None
             | Some x ->
                Typ.addNameConvention typ_name (Some (Gensym.MVarData.name_gensym m_name))
                  (Some (Gensym.VarData.name_gensym x))
           in
           Store.Cid.NamedHoles.addNameConvention cid m_name v_name;
           Int.Sgn.Pragma(Int.LF.NamePrag cid)
         with _ -> (* XXX this should be more specific *)
           throw loc (UnboundNamePragma typ_name)
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
