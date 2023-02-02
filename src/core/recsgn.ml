open Support.Equality
open Support
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
  | TotalDeclError of Name.t * Name.t
  | MutualTotalDecl
    of Name.t list (* functions with total decls *)
       * Name.t list (* functions without total decls *)
  | NoPositive of string
  | NoStratify of string
  | NoStratifyOrPositive of string
  | TotalArgsError of Name.t
  | IllegalOptsPrag of string
  | IllegalOperatorPrag of Name.t * Fixity.t * int
  | InvalidOpenPrag of string
  | InvalidAbbrev of string list * string
  | UnboundArg of Name.t * Name.t option list
  | UnboundNamePragma of Name.t

exception Error of Syntax.Loc.t * error

let throw loc e = raise (Error (loc, e))

let _ =
  let open Format in
  Error.register_printer
    begin fun (Error (loc, err)) ->
    Error.print_with_location loc
      begin fun ppf ->
      match err with
      | TotalDeclError (f, f') ->
         fprintf ppf
           "Expected totality declaration for %a@.@
           Found totality declaration for %s@."
           Name.pp f
           (Name.string_of_name f')
      | MutualTotalDecl (haves, have_nots) ->
         fprintf ppf "@[<v>%a@,The functions@,  @[<hov>%a@]@,have totality declarations, \
                      but the functions@,  @[<hov>%a@]@,are missing totality declarations."
           pp_print_string
           "This mutual definition block does not have
            consistent totality declarations. Either all or none of
            functions must be declared total."
           (pp_print_list ~pp_sep: Format.comma Name.pp) haves
           (pp_print_list ~pp_sep: Format.comma Name.pp) have_nots
      | NoPositive n ->
         fprintf ppf "Positivity checking of constructor %s fails.@." n
      | NoStratify n ->
         fprintf ppf "Stratification checking of constructor %s fails.@." n

      | NoStratifyOrPositive n ->
         fprintf ppf "Stratification or positivity checking of datatype %s fails.@." n
      | TotalArgsError f ->
         fprintf ppf "Totality declaration for %a takes too many arguments.@."
         Name.pp f

      | UnexpectedSucess ->
         fprintf ppf "Unexpected success: expected failure of type reconstruction for --not'ed declaration."
      | IllegalOptsPrag s ->
         fprintf ppf "\"%s\" pragma must appear before any declarations." s
      | IllegalOperatorPrag(n, f, actual) ->
         let (fix, expected) =
           match f with
           | Fixity.Infix -> ("infix", 2)
           | Fixity.Postfix -> ("postfix", 1)
         in
         fprintf ppf
           "Illegal %s operator %a. Operator declared with %d arguments, but only operators with %d args permitted"
           fix
           Name.pp n
           actual
           expected
      | InvalidOpenPrag s ->
         fprintf ppf "Invalid module in pragma '--open %s'" s
      | InvalidAbbrev (l, s) ->
         fprintf ppf "Invalid module in pragma '--abbrev %s %s'"
           (String.concat "." l) s
      | UnboundArg (a, args) ->
         fprintf ppf "Argument %a does not appear in argument list @[<h>%a@]."
           Name.pp a
           (pp_print_list
              ~pp_sep: Format.comma
              (fun ppf ->
                (Option.eliminate
                   (fun _ -> fprintf ppf "_")
                   (Name.pp ppf))))
           args
      | UnboundNamePragma typ_name ->
         fprintf ppf "Name pragma refers to unbound type %a." Name.pp typ_name
      end
    end

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

let rec get_target_cid_comptyp tau =
  match tau with
  | Int.Comp.TypBase (_, a, _) -> a
  | Int.Comp.TypArr (_, _, tau) -> get_target_cid_comptyp tau
  | Int.Comp.TypPiBox (_, _, tau) -> get_target_cid_comptyp tau
  | _ ->
     Error.violation
       "[get_target_cid_comptyp] no target comp typ"

let rec get_target_cid_compcotyp tau =
  match tau with
  | Int.Comp.TypCobase (_, a, _) -> a
  | Int.Comp.TypArr (_, tau, _) ->
     get_target_cid_compcotyp tau
     (* XXX it's strange that this walks backwards, but is called "get *target*".
        Perhaps for codatatypes this should be "source" ? -je *)
  | Int.Comp.TypPiBox (_, _, tau) -> get_target_cid_compcotyp tau
  | _ ->
     Error.violation
       "[get_target_cid_compcotyp] no target comp cotyp"

let freeze_from_name tau =
  match tau with
  | Ext.Sgn.Typ { identifier; _ } ->
     let a = Typ.index_of_name identifier in
     Typ.freeze a;
     ()
  | Ext.Sgn.CompTyp { identifier; _ } ->
     let a = CompTyp.index_of_name identifier in
     CompTyp.freeze a;
     ()
  | Ext.Sgn.CompCotyp { identifier; _ } ->
     let a = CompCotyp.index_of_name identifier in
     CompCotyp.freeze a;
     ()

let sgnDeclToHtml =
  function
  | Ext.Sgn.Comment { content; _ } -> Html.appendAsComment content
  | d ->
    Html.printing := true;

    let html_buffer = Buffer.create 16 in
    let html_formatter = Format.formatter_of_buffer html_buffer in
    Format.pp_set_margin html_formatter 200;
    Format.fprintf html_formatter "%a" Pretty.Ext.DefaultPrinter.fmt_ppr_sgn_decl d;
    Format.pp_print_flush html_formatter ();
    Html.append (Buffer.contents html_buffer);

    Html.printing := false

let rec apply_global_pragmas =
  function
  | Synext.Sgn.GlobalPragma { pragma=Synext.Sgn.NoStrengthen; _ } :: t ->
     Lfrecon.strengthen := false;
     apply_global_pragmas t
  | Synext.Sgn.GlobalPragma { pragma=Synext.Sgn.Coverage opt; _ } :: t ->
     Coverage.enableCoverage := true;
     begin match opt with
     | `Warn -> Coverage.warningOnly := true
     | `Error -> ()
     end;
     apply_global_pragmas t
  | l -> l

let recSgnDecls decls =
  let leftoverVars : leftover_vars ref = ref [] in
  let is_empty =
    function
    | Int.LF.Empty -> true
    | _ -> false
  in
  let storeLeftoverVars (cQ : Abstract.free_var Int.LF.ctx) (loc : Syntax.Loc.t) : unit =
    match cQ with
    | Int.LF.Empty -> ()
    | _ -> leftoverVars := (cQ, loc) :: !leftoverVars
  in
  let rec recSgnDecls' =
    function
    | [] -> []

    | Ext.Sgn.Pragma { location=loc; pragma=Ext.Sgn.NotPrag } :: not'd_decl :: rest ->
       let not'd_decl_succeeds =
           begin
             try
               ignore (recSgnDecl not'd_decl);
               true
             with
           | _ ->
              Chatter.print 1
                "Reconstruction fails for --not'd declaration@.";
              false
         end in
       if not'd_decl_succeeds
       then raise (Error (loc, UnexpectedSucess))
       else recSgnDecls' rest

    (* %not declaration with nothing following *)
    | [Ext.Sgn.Pragma { pragma=Ext.Sgn.NotPrag; _ }] -> []

    | Ext.Sgn.GlobalPragma { pragma=Ext.Sgn.Coverage `Warn; location } :: rest ->
       raise (Error (location, IllegalOptsPrag "--warncoverage"))
    | Ext.Sgn.GlobalPragma { pragma=Ext.Sgn.Coverage `Error; location } :: rest ->
       raise (Error (location, IllegalOptsPrag "--coverage"))
    | Ext.Sgn.GlobalPragma { pragma=Ext.Sgn.NoStrengthen; location } :: rest ->
       raise (Error (location, IllegalOptsPrag "--nostrengthen"))

    | decl :: rest ->
       let decl' = recSgnDecl decl in
       let rest' = recSgnDecls' rest in
       decl' :: rest'

  and recSgnDecl ?(pauseHtml=false) d =
    Reconstruct.reset_fvarCnstr ();
    FCVar.clear ();
    if !Html.generate && Bool.not pauseHtml
    then sgnDeclToHtml d;
    match d with
    | Ext.Sgn.Comment { location; content } ->
        Int.Sgn.Comment { location; content }
    | Ext.Sgn.Pragma { location=loc; pragma=Ext.Sgn.AbbrevPrag (orig, abbrev) } ->
       begin
         try
           Store.Modules.addAbbrev orig abbrev
         with
         | Not_found -> raise (Error (loc, InvalidAbbrev (orig, abbrev)))
       end;
       Int.Sgn.Pragma { pragma=Int.LF.AbbrevPrag (orig, abbrev) }
    | Ext.Sgn.Pragma { location=loc; pragma=Ext.Sgn.DefaultAssocPrag a } ->
       OpPragmas.default := a;
       Int.Sgn.Pragma { pragma=Int.LF.DefaultAssocPrag a }
    | Ext.Sgn.Pragma { location=loc; pragma=Ext.Sgn.FixPrag (name, fix, precedence, assoc) } ->
       dprintf (fun p -> p.fmt "Pragma found for %a" Name.pp name);
       begin match fix with
       | Fixity.Prefix ->
          OpPragmas.addPragma name fix (Some precedence) assoc
       | (Fixity.Infix | Fixity.Postfix) ->
          let args_expected =
            match fix with
            | Fixity.Postfix -> 1
            | Fixity.Infix -> 2
          in
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
             if args_expected = actual
             then
               OpPragmas.addPragma name fix (Some precedence) assoc
             else
               raise (Error (loc, IllegalOperatorPrag (name, fix, actual)))
       end;
       Int.Sgn.Pragma { pragma=Int.LF.FixPrag (name, fix, precedence, assoc) }

    | Ext.Sgn.CompTypAbbrev { location; identifier; kind=cK; typ=cT } ->
       (* index cT in a context which contains arguments to cK *)
       let (apx_tau, apxK) = Index.comptypdef (cT, cK) in
       let ((cD, tau), i, cK) = Reconstruct.comptypdef location identifier (apx_tau, apxK) in
       dprintf
         begin fun p ->
         p.fmt "typedef %a : %a = %a"
           Name.pp identifier
           (P.fmt_ppr_cmp_kind Int.LF.Empty P.l0) cK
           (P.fmt_ppr_cmp_typ cD P.l0) tau
         end;
       Monitor.timer
         ("Type abbrev. : Kind Check", fun () -> Check.Comp.checkKind Int.LF.Empty cK);
       Monitor.timer
         ("Type abbrev. : Type Check", fun () -> Check.Comp.checkTyp cD tau);
       ignore (CompTypDef.add (fun _ -> CompTypDef.mk_entry identifier i (cD, tau) cK));
       let sgn = Int.Sgn.CompTypAbbrev { location; identifier; kind=cK; typ=tau } in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.CompTyp { location; identifier; kind=extK; datatype_flavour=pflag } ->
       dprint (fun () -> "Indexing computation-level data-type constant " ^ Name.string_of_name identifier);
       let apxK = Index.compkind extK in
       FVar.clear ();
       dprint (fun () -> "Elaborating data-type declaration " ^ Name.string_of_name identifier);
       let cK =
         Monitor.timer
           ( "CType Elaboration"
           , fun () ->
             let cK = Reconstruct.compkind apxK in
             Reconstruct.solve_fvarCnstr Lfrecon.Pibox;
             cK
           )
       in
       Unify.forceGlobalCnstr ();
       let (cK', i) =
         Monitor.timer
           ( "Type Abstraction"
           , fun () -> Abstract.compkind cK
           )
       in
       Reconstruct.reset_fvarCnstr ();
       Unify.resetGlobalCnstrs ();
       dprintf
         begin fun p ->
         p.fmt "%a : %a@."
           Name.pp identifier
           (P.fmt_ppr_cmp_kind Int.LF.Empty P.l0) cK'
         end;
       Monitor.timer
         ( "Type Check"
         , fun () -> Check.Comp.checkKind Int.LF.Empty cK'
         );
       dprintf
         (fun p ->
           p.fmt "DOUBLE CHECK for data type constant %s successful!"
           (Name.string_of_name identifier)
         );
       (* let p =
        *   match pflag with
        *   | None -> Int.Sgn. Noflag
        *   | Some Ext. Sgn.Stratify (loc, x, Name.mk_name (Id.SomeString r), args)
        *     -> Int.Sgn.Stratify (loc, x, Name.mk_name (Id.SomeString r), args)
        *   | Some _ -> Int.Sgn.Positivity
        * in *)

       let p =
         match pflag with
         | Ext.Sgn.StratifiedDatatype -> Int.Sgn.StratifyAll location
         | Ext.Sgn.InductiveDatatype -> Int.Sgn.Positivity
       in
       Total.stratNum := -1;
       ignore (CompTyp.add (fun _ -> CompTyp.mk_entry identifier cK' i p));
       let sgn = Int.Sgn.CompTyp { location; identifier; kind=cK'; positivity_flag=p } in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.CompCotyp { location; identifier; kind=extK } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] CompCotyp at: %a"
             Syntax.Loc.print location);
       dprint (fun () -> "\nIndexing computation-level codata-type constant " ^ Name.string_of_name identifier);
       let apxK = Index.compkind extK in
       FVar.clear ();
       dprint (fun () -> "\nElaborating codata-type declaration " ^ Name.string_of_name identifier);
       let cK =
         Monitor.timer
           ( "CType Elaboration"
           , fun () ->
             let cK = Reconstruct.compkind apxK in
             Reconstruct.solve_fvarCnstr Lfrecon.Pibox;
             cK
           )
       in
       Unify.forceGlobalCnstr ();
       let (cK', i) =
         Monitor.timer
           ( "Type Abstraction"
           , fun () -> Abstract.compkind cK
           )
       in

       Reconstruct.reset_fvarCnstr ();
       Unify.resetGlobalCnstrs ();
       dprintf
         begin fun p ->
         p.fmt "%a : %a"
           Name.pp identifier
           (P.fmt_ppr_cmp_kind Int.LF.Empty P.l0) cK'
         end;
       Monitor.timer
         ( "Type Check"
         , fun () -> Check.Comp.checkKind Int.LF.Empty cK'
         );
       dprint
         (fun () ->
           "\nDOUBLE CHECK for codata type constant " ^ Name.string_of_name identifier ^
             " successful!");
       ignore (CompCotyp.add (fun _ -> CompCotyp.mk_entry identifier cK' i));
       let sgn = Int.Sgn.CompCotyp { location; identifier; kind=cK' } in
       Store.Modules.addSgnToCurrent sgn;
       sgn


    | Ext.Sgn.CompConst { location; identifier; typ=tau } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] CompConst at: %a"
             Syntax.Loc.print_short location);
       dprint (fun () -> "\nIndexing computation-level data-type constructor " ^ Name.string_of_name identifier);
       let apx_tau = Index.comptyp tau in
       let cD = Int.LF.Empty in
       dprint (fun () -> "\nElaborating data-type constructor " ^ Name.string_of_name identifier);
       let tau' =
         Monitor.timer
           ( "Data-type Constant: Type Elaboration"
           , fun () -> Reconstruct.comptyp apx_tau
           )
       in
       Unify.forceGlobalCnstr ();
       dprint (fun () -> "Abstracting over comp. type");
       let (tau', i) =
         Monitor.timer
           ( "Data-type Constant: Type Abstraction"
           , fun () -> Abstract.comptyp tau'
           )
       in
       dprint (fun () -> "Abstracting over comp. type: done");
       dprintf
         begin fun p ->
         p.fmt "[recsgn] @[<v>@[<hov>@[%a@] :@ @[%a@]@]@,with %d implicit parameters@]"
           Name.pp identifier
           (P.fmt_ppr_cmp_typ cD P.l0) tau'
           i
         end;
       Monitor.timer
         ( "Data-type Constant: Type Check"
         , fun () -> Check.Comp.checkTyp cD tau'
         );
       let cid_ctypfamily = get_target_cid_comptyp tau' in

       let flag = (CompTyp.get cid_ctypfamily).CompTyp.Entry.positivity in

       begin match flag with
       | Int.Sgn.Nocheck -> ()
       | Int.Sgn.Positivity ->
          if Total.positive cid_ctypfamily tau'
          then ()
          else raise (Error (location, (NoPositive (Name.string_of_name identifier))))
       | Int.Sgn.Stratify (loc_s, n) ->
          if Total.stratify cid_ctypfamily tau' n
          then ()
          else raise (Error (location, (NoStratify (Name.string_of_name identifier))))
       | Int.Sgn.StratifyAll loc_s ->
          let t = Total.stratifyAll cid_ctypfamily tau' in
          let t' = (t land (!Total.stratNum)) in
          if t'<> 0
          then Total.stratNum := t'
          else raise (Error (loc_s, (NoStratifyOrPositive (R.render_cid_comp_typ cid_ctypfamily) )))
       end;
       (* begin
        *   if true (\* Total.stratifyAll cid_ctypfamily tau'  *\)
        *   then ()
        *   else raise (Error (loc, (NoStratify (string_of_name c))))
        * end; *)

       (* begin
        *   if flag
        *   then
        *     if Total.positive cid_ctypfamily tau'
        *     then ()
        *     else raise (Error (loc, (NoPositive (string_of_name c))))
        *   else ()
        * end; *)
       ignore (CompConst.add cid_ctypfamily (fun _ -> CompConst.mk_entry identifier tau' i));
       let sgn = Int.Sgn.CompConst { location; identifier; typ=tau' } in
       Store.Modules.addSgnToCurrent sgn;
       sgn



    | Ext.Sgn.CompDest
      { location
      ; identifier
      ; mctx=cD
      ; observation_typ=tau0
      ; return_typ=tau1
      } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] CompDest at: %a" Syntax.Loc.print_short location);
       dprint (fun () -> "\nIndexing computation-level codata-type destructor " ^ Name.string_of_name identifier);
       let cD = Index.mctx cD in
       let cD = Reconstruct.mctx cD in
       let apx_tau0 = Index.comptyp tau0 in
       let apx_tau1 = Index.comptyp tau1 in
       dprint (fun () -> "\nElaborating codata-type destructor " ^ Name.string_of_name identifier);
       let tau0' =
         Monitor.timer
           ( "Codata-type Constant: Type Elaboration"
           , fun () -> Reconstruct.comptyp_cD cD apx_tau0
           )
       in
       let tau1' =
         Monitor.timer
           ( "Codata-type Constant: Type Elaboration"
           , fun () -> Reconstruct.comptyp_cD cD apx_tau1
           )
       in
       Unify.forceGlobalCnstr ();
       dprint (fun () -> "Abstracting over comp. type");
       let (cD1, tau0', tau1', i) =
         Monitor.timer
           ( "Codata-type Constant: Type Abstraction"
           , fun () -> Abstract.codatatyp cD tau0' tau1'
           )
       in
       dprintf
         begin fun p ->
         p.fmt "[recSgnDecl] [CompDest] @[<v>cD1 = @[%a@]@,tau1' = @[%a@]@]"
           (P.fmt_ppr_lf_mctx P.l0) cD1
           (P.fmt_ppr_cmp_typ cD1 P.l0) tau1'
         end;
       dprint (fun () -> "Abstracting over comp. type: done");
       dprintf
         begin fun p ->
         p.fmt "%a : %a :: %a"
           Name.pp identifier
           (P.fmt_ppr_cmp_typ cD1 P.l0) tau0'
           (P.fmt_ppr_cmp_typ cD1 P.l0) tau1'
         end;
       Monitor.timer
         ( "Codata-type Constant: Type Check"
         , fun () -> Check.Comp.checkTyp cD1 tau0'
         );
       Monitor.timer
         ( "Codata-type Constant: Type Check"
         , fun () -> Check.Comp.checkTyp cD1 tau1'
         );
       let cid_ctypfamily = get_target_cid_compcotyp tau0' in
       ignore (CompDest.add cid_ctypfamily (fun _ -> CompDest.mk_entry identifier cD1 tau0' tau1' i));
       let sgn =
        Int.Sgn.CompDest
        { location
        ; identifier
        ; mctx=cD1
        ; observation_typ=tau0'
        ; return_typ=tau1'
        } in
       Store.Modules.addSgnToCurrent sgn;
       sgn


    | Ext.Sgn.Typ { location; identifier=a; kind=extK } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Typ at: %a"
             Syntax.Loc.print_short location);
       dprint (fun () -> "\nIndexing type constant " ^ Name.string_of_name a);
       let (_, apxK) = Index.kind Index.disambiguate_to_fvars extK in
       FVar.clear ();

       dprint (fun () -> "\nElaborating type constant " ^ Name.string_of_name a);
       let tK =
         Monitor.timer
           ( "Type Elaboration"
           , fun () ->
             let tK = Reconstruct.kind apxK in
             Reconstruct.solve_fvarCnstr Lfrecon.Pi;
             tK
           )
       in
       Unify.forceGlobalCnstr ();
       let (tK', i) =
         Monitor.timer
           ( "Type Abstraction"
           , fun () -> Abstract.kind tK
           )
       in
       Reconstruct.reset_fvarCnstr ();
       Unify.resetGlobalCnstrs ();
       dprintf
         begin fun p ->
         p.fmt "%a : %a@."
           Name.pp a
           (P.fmt_ppr_lf_kind Int.LF.Null P.l0) tK'
         end;
       Monitor.timer
         ( "Type Check"
         , fun () -> Check.LF.checkKind Int.LF.Empty Int.LF.Null tK'
         );
       dprintf (fun p ->
         p.fmt "DOUBLE CHECK for type constant %s successful!" (Name.string_of_name a)
       );
       Typeinfo.Sgn.add location (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Kind tK')) "";
       let cid = Typ.add (fun _ -> Typ.mk_entry a tK' i) in
       let sgn = Int.Sgn.Typ { location; identifier=cid; kind=tK' } in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.Const { location; identifier=c; typ=extT } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Const at: %a"
             Syntax.Loc.print_short location);
       let (_, apxT) = Index.typ Index.disambiguate_to_fvars extT in
       let rec get_type_family =
         function
         | Apx.LF.Atom (_loc, a, _spine) -> a
         | Apx.LF.PiTyp ((_, _), t) -> get_type_family t
       in
       let constructedType = get_type_family apxT in
       dprint (fun () -> "Reconstructing term constant " ^ (Name.string_of_name c));
       FVar.clear ();
       let tA =
         Monitor.timer
           ( "Constant Elaboration"
           , fun () ->
             let tA = Reconstruct.typ Lfrecon.Pi apxT in
             Reconstruct.solve_fvarCnstr Lfrecon.Pi;
             tA
           )
       in
       let cD = Int.LF.Empty in
       dprintf
         begin fun p ->
         p.fmt "[recSgnDecl] [Const] %a : %a"
           Name.pp c
           (P.fmt_ppr_lf_typ cD Int.LF.Null P.l0) tA
         end;
       Unify.forceGlobalCnstr ();
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
         p.fmt "[recSgnDecl] [Const] Reconstruction (with abstraction) of constant: %a : %a"
           Name.pp c
           (P.fmt_ppr_lf_typ cD Int.LF.Null P.l0) tA'
         end;
       Monitor.timer
         ( "Constant Check"
         , fun () -> Check.LF.checkTyp Int.LF.Empty Int.LF.Null (tA', S.LF.id)
         );
       Typeinfo.Sgn.add location (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Typ tA')) "";
       let cid = Term.add' location constructedType (fun _ -> Term.mk_entry c tA' i) in
       let sgn = Int.Sgn.Const { location; identifier=cid; typ=tA' } in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.Schema { location; identifier=g; schema } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Schema at: %a@."
             Syntax.Loc.print_short location);
       let apx_schema = Index.schema schema in
       dprintf (fun p -> p.fmt "Reconstructing schema %s@." (Name.string_of_name g));
       FVar.clear ();
       let sW = Reconstruct.schema apx_schema in
       dprintf
         begin fun p ->
         p.fmt "Elaborated schema %a : %a"
           Name.pp g
           (P.fmt_ppr_lf_schema P.l0) sW
         end;
       Reconstruct.solve_fvarCnstr Lfrecon.Pi;
       Unify.forceGlobalCnstr ();
       Reconstruct.reset_fvarCnstr ();
       Unify.resetGlobalCnstrs ();
       let sW' = Abstract.schema sW in
       dprintf
         begin fun p ->
         p.fmt "Schema %a : %a after abstraction@."
           Name.pp g
           (P.fmt_ppr_lf_schema P.l0) sW'
         end;
       Check.LF.checkSchemaWf sW';
       dprintf (fun p -> p.fmt "TYPE CHECK for schema %s successful@." (Name.string_of_name g));
       let sch = Schema.add (fun _ -> Schema.mk_entry g sW') in
       let sgn = Int.Sgn.Schema { location; identifier=sch; schema=sW' } in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.Val { location; identifier; typ=None; expression } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Val at: %a"
             Syntax.Loc.print_short location);
       let apx_i = Index.exp Store.Var.empty expression in
       let (cD, cG) = (Int.LF.Empty, Int.LF.Empty) in
       let (i', (tau, theta)) =
         Monitor.timer
           ( "Function Elaboration"
           , fun () -> Reconstruct.exp' cG apx_i
           )
       in
       Unify.forceGlobalCnstr ();
       let tau' = Whnf.cnormCTyp (tau, theta) in
       let expression' = Whnf.cnormExp (i', Whnf.m_id) in

       dprintf
         begin fun p ->
         p.fmt "[AFTER Reconstruction Val] @[<v 2>let %a : %a =@ %a@]"
           Name.pp identifier
           (P.fmt_ppr_cmp_typ cD P.l0) tau'
           (P.fmt_ppr_cmp_exp cD cG P.l0) expression'
         end;
       let cQ, expression'' =
         Monitor.timer
           ( "Function Abstraction"
           , fun _ ->
             Abstract.exp expression'
           )
       in
       storeLeftoverVars cQ location;
       Monitor.timer
         ( "Function Check"
         , fun _ -> Check.Comp.check None cD cG [] expression'' (tau', C.m_id)
         );

       let v =
         if Holes.none () && is_empty cQ
         then
           begin
             let v = Some (Opsem.eval expression'') in
             let open Comp in
             add begin fun _ ->
               let mgid =
                 Comp.add_mutual_group
                   Int.Comp.[{ name = identifier; tau = tau'; order = `not_recursive }]
               in
               mk_entry (Some (Decl.next ())) identifier tau' 0 mgid v
               end
             |> ignore;
             v
           end
         else
           None
       in
       let sgn = Int.Sgn.Val { location; identifier; typ=tau'; expression=expression''; expression_value=v } in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.Val { location; identifier; typ=Some tau; expression } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Val at %a"
             Syntax.Loc.print_short location
         );
       let apx_tau = Index.comptyp tau in
       let (cD, cG) = (Int.LF.Empty, Int.LF.Empty) in
       let tau' =
         Monitor.timer
           ( "Function Type Elaboration"
           , fun () -> Reconstruct.comptyp apx_tau
           )
       in
       Unify.forceGlobalCnstr ();
       let (tau', _) =
         Monitor.timer
           ( "Function Type Abstraction"
           , fun _ -> Abstract.comptyp tau'
           )
       in
       Monitor.timer
         ( "Function Type Check"
         , fun () -> Check.Comp.checkTyp cD tau'
         );
       let apx_i = Index.exp Store.Var.empty expression in
       let i' =
         Monitor.timer
           ( "Function Elaboration"
           , fun _ ->
             Reconstruct.exp cG apx_i (tau', C.m_id)
           )
       in
       let expression' = Whnf.cnormExp (i', Whnf.m_id) in
       Unify.forceGlobalCnstr ();
       let tau' = Whnf.cnormCTyp (tau', C.m_id) in
       dprintf
         begin fun p ->
           p.fmt "[AFTER Reconstruction Val - 2] let %a : %a =@,%a"
             Name.pp identifier
             (P.fmt_ppr_cmp_typ cD P.l0) tau'
             (P.fmt_ppr_cmp_exp cD cG P.l0) expression'
         end;

       let cQ, expression'' =
         Monitor.timer
           ( "Function Abstraction"
           , fun () -> Abstract.exp expression'
           )
       in
       storeLeftoverVars cQ location;
       Monitor.timer
         ( "Function Check"
         , fun _ ->
           Check.Comp.check None cD cG [] expression'' (tau', C.m_id)
         );
       let v =
         if Holes.none () && is_empty cQ
         then
           begin
             let v = Some (Opsem.eval expression'') in
             let open Comp in
             let mgid =
               add_mutual_group
                 Int.Comp.[ {name = identifier; tau = tau'; order = `not_recursive } ]
             in
             add begin fun _ ->
               mk_entry (Some (Decl.next ())) identifier tau' 0 mgid v
               end;
             |> ignore;
             v
           end
         else
           None
       in
       let sgn = Int.Sgn.Val { location; identifier; typ=tau'; expression=expression''; expression_value=v } in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.MRecTyp { location; declarations=recDats } ->
       dprintf
         (fun p ->
           p.fmt "[recsgn] MRecTyp at %a" Loc.print_short location);
       let recTyps = List1.map (fun (k, _) -> k) recDats in
       let recTyps' = List1.map (recSgnDecl ~pauseHtml:true) recTyps in
       let recConts = List1.map (fun (_, cs) -> cs) recDats in
       let recConts' = List1.map (List.map (recSgnDecl ~pauseHtml:true)) recConts in
       List1.iter freeze_from_name recTyps;
       Int.Sgn.MRecTyp
        { location
        ; declarations=List1.map2 (fun x y -> x :: y) recTyps' recConts'
        }

    | Ext.Sgn.Theorems { location; theorems=recFuns } ->
       let pos loc x args =
         match
           List.index_of
             (Option.equal Name.( = ) (Some x))
             args
         with
         | None -> throw loc (UnboundArg (x, args))
         | Some k -> k + 1 (* index_of is 0-based, but we're 1-based *)
       in

       let mk_total_decl f tau = function
         | Ext.Comp.Trust _ -> `trust
         | Ext.Comp.NumericTotal (loc, None) -> `not_recursive
         | Ext.Comp.NumericTotal (loc, Some order) ->
            `inductive (Reconstruct.numeric_order tau order)
         | Ext.Comp.NamedTotal (loc, order, f', args) ->
            (* Validate the inputs: can't have too many args or the wrong name *)
            if Bool.not (Total.is_valid_args tau (List.length args))
            then raise (Error (loc, TotalArgsError f))
            else if Name.(f <> f')
            then raise (Error (loc, TotalDeclError (f, f')))
            else
              begin match order with
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
              end
       in

       (* Collect all totality declarations. *)
       (* and check that all or none of the declarations are present. *)
       let total_decs =
         let prelim_total_decs =
           List1.map (fun (Ext.Sgn.Theorem { name; order; _ }) -> (name, order)) recFuns
         in
         match
            List1.partition
              (fun (_, order) -> Option.is_some order) prelim_total_decs
         with
         | [], [] ->
            Error.violation "[recSgn] empty mutual block is impossible"
         | haves, [] ->
            haves
            |> List.map Fun.(Option.get ++ Pair.snd)
            |> List1.of_list
         (* safe because they're haves *)
         | [], have_nots -> None
         | haves, have_nots ->
            throw location
              (MutualTotalDecl (List.map Pair.fst haves, List.map Pair.fst have_nots))
       in

       let preprocess =
         List1.map
           begin fun (Ext.Sgn.Theorem { typ; name; location; body; _ }) ->
           let apx_tau = Index.comptyp typ in
           let tau' =
             Monitor.timer
               ( "Function Type Elaboration"
               , fun () -> Reconstruct.comptyp apx_tau
               )
           in
           Unify.forceGlobalCnstr ();
           (* Are some FMVars delayed since we can't infer their
              type? - Not associated with pattsub
            *)
           let (tau', _) =
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
             Comp.add begin fun cid ->
               Comp.mk_entry (Some (Decl.next ())) name tau' 0 total_decs None
               end
           in
           ( (name, body, location, tau')
           , register
           )
           end
       in

       let (thm_list, registers) = List1.split (preprocess recFuns) in

       (* We have the elaborated types of the theorems,
          so we construct the final list of totality declarations for
          this mutual group. *)
       let total_decs =
         match total_decs with
         | Some total_decs ->
            List1.map2
              (fun (thm_name, _, _, tau) decl ->
                mk_total_decl thm_name tau decl
                |> Int.Comp.make_total_dec thm_name tau)
              thm_list
              total_decs
         | None ->
            List1.map
              (fun (thm_name, _, _, tau) ->
                Int.Comp.make_total_dec thm_name tau `partial)
              thm_list
       in

       (* We have the list of all totality declarations for this group,
          so we can register each theorem in the store.
        *)
       let thm_cid_list =
          registers
          |> List1.ap_one (Comp.add_mutual_group (List1.to_list total_decs))
       in

       let reconThm loc (f, cid, thm, tau) =
         let apx_thm = Index.thm Store.Var.empty thm in
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
             Name.pp f
             (P.fmt_ppr_cmp_typ Int.LF.Empty P.l0) tau
             P.fmt_ppr_cmp_thm thm'
           end;
         begin
           try
             Unify.forceGlobalCnstr ()
           with
           | Unify.GlobalCnstrFailure (loc, cnstr) ->
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
             Name.pp f
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
           match Total.lookup_dec f (List1.to_list total_decs) with
           | None -> tau
           | Some d ->
              let tau = Total.annotate loc d.Int.Comp.order tau in
              dprintf
                begin fun p ->
                p.fmt "[reconThm] @[<v>got annotated type:@,@[%a@]@]"
                  P.(fmt_ppr_cmp_typ Int.LF.Empty l0) tau
                end;
              tau
         in
         Monitor.timer
           ( "Function Check"
           , fun _ ->
             dprintf
               begin fun p ->
               p.fmt "[recThm] @[<v>begin checking theorem %a.\
                      @,@[<hv 2>total_decs =@ @[<v>%a@]@]\
                      @,tau_ann = @[%a@]@]"
                 Name.pp f
                 (List1.pp ~pp_sep: Format.pp_print_cut
                    P.(fmt_ppr_cmp_total_dec))
                 total_decs
                 P.(fmt_ppr_cmp_typ Int.LF.Empty l0) tau_ann
               end;
             Total.enabled := Total.requires_checking f (List1.to_list total_decs);
             Check.Comp.thm (Some cid) Int.LF.Empty Int.LF.Empty (List1.to_list total_decs) thm_r' (tau_ann, C.m_id);
             Total.enabled := false;
           );
         (thm_r' , tau)
       in

       let ds =
         let reconOne (thm_cid, (thm_name, thm_body, thm_location, thm_typ)) =
           let (e_r', tau') = reconThm thm_location (thm_name, thm_cid, thm_body, thm_typ) in
           dprintf
             begin fun p ->
             p.fmt "[reconRecFun] @[<v>DOUBLE CHECK of function %a at %a successful@,Adding definition to the store.@]"
               Name.pp thm_name
               Loc.print_short thm_location
             end;
           let v = Int.(Comp.ThmValue (thm_cid, e_r', LF.MShift 0, Comp.Empty)) in
           Comp.set_prog thm_cid (Fun.const (Some v));
           Int.Sgn.Theorem
             { name = thm_cid
             ; body = e_r'
             ; location = thm_location
             ; typ = tau'
             }
         in
         List1.map reconOne (List1.combine thm_cid_list thm_list)
       in
       let decl = Int.Sgn.Theorems { location; theorems = ds } in
       Store.Modules.addSgnToCurrent decl;
       decl

    | Ext.Sgn.Query
      { location
      ; name
      ; mctx=cD
      ; typ=extT
      ; expected_solutions=expected
      ; maximum_tries=tries
      } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Query at %a"
             Syntax.Loc.print_short location);
       let (_, apxT) = Index.typ Index.disambiguate_to_fvars extT in
       dprint (fun () -> "Reconstructing query.");
       FVar.clear ();
       let tA =
         Monitor.timer
           ( "Constant Elaboration"
           , fun () ->
             let tA = Reconstruct.typ Lfrecon.Pi apxT in
             Reconstruct.solve_fvarCnstr Lfrecon.Pi;
             tA
           )
       in
       let cD = Index.mctx cD in
       let cD = Reconstruct.mctx cD in
       dprintf
         begin fun p ->
         p.fmt "Elaboration of query : %a"
           (P.fmt_ppr_lf_typ cD Int.LF.Null P.l0) tA
         end;
       Unify.forceGlobalCnstr ();
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
           p.fmt "Reconstruction (with abstraction) of query: %a with %s abstracted variables"
             (P.fmt_ppr_lf_typ cD Int.LF.Null P.l0) tA'
             (string_of_int i)
         end;
       Monitor.timer
         ( "Constant Check"
         , fun () ->
           Check.LF.checkTyp Int.LF.Empty Int.LF.Null (tA', S.LF.id)
         );
       Logic.storeQuery name (tA', i) cD expected tries;
       Int.Sgn.Query
       { location
       ; name
       ; mctx=cD
       ; typ=(tA', i)
       ; expected_solutions=expected
       ; maximum_tries=tries
       }

    | Ext.Sgn.Pragma
      { location=loc
      ; pragma=Ext.Sgn.NamePrag (typ_name, m_name, v_name)
      } ->
       dprintf
         (fun p ->
           p.fmt "[RecSgn Checking] Pragma at %a"
             Syntax.Loc.print_short loc);
       begin match
         try Some (Typ.index_of_name typ_name)
         with Not_found -> None
       with
       | Some cid ->
          let m = Some (Gensym.MVarData.name_gensym m_name) in
          let v = Option.(v_name $> Gensym.VarData.name_gensym) in
          Typ.set_name_convention cid m v;
          Int.Sgn.Pragma { pragma=Int.LF.NamePrag cid }
       | None ->
           throw loc (UnboundNamePragma typ_name)
       end

    | Ext.Sgn.Module { location; identifier; declarations=decls } ->
       let state = Store.Modules.getState () in
       ignore (Store.Modules.instantiateModule identifier);
       let decls' = List.map recSgnDecl decls in

       Store.Modules.setState state;
       let sgn = Int.Sgn.Module { location; identifier; declarations=decls' } in
       Store.Modules.addSgnToCurrent sgn;
       sgn

    | Ext.Sgn.Pragma { location=loc; pragma=Ext.Sgn.OpenPrag n } ->
       try
         let x = Modules.open_module n in
         let sgn = Int.Sgn.Pragma { pragma=Int.LF.OpenPrag x } in
         Store.Modules.addSgnToCurrent sgn;
         sgn
       with
       | Not_found ->
          raise (Error (loc, (InvalidOpenPrag (String.concat "." n))))
  in
  let decls' = recSgnDecls' decls in
  match !leftoverVars with
  | [] -> decls', None
  | _ -> decls', Some !leftoverVars
