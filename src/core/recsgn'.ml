open Support
open Beluga_syntax
module Synint = Syntax.Int

[@@@warning "+A-26-27-4-44"]

module C = Whnf
module S = Substitution
module Unify = Unify.StdTrail
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let dprintf, dprint, _ = Debug.makeFunctions' (Debug.toFlags [ 11 ])

open Debug.Fmt

exception Dangling_not_pragma

exception Unexpected_entry_reconstruction_success

exception Unsupported_recursive_declaration

let () =
  Error.register_exception_printer (function
    | Dangling_not_pragma ->
        Format.dprintf "%a" Format.pp_print_text
          "This `--not' pragma must precede some signature entry."
    | Unexpected_entry_reconstruction_success ->
        Format.dprintf "%a" Format.pp_print_text
          "This signature entry was successfully reconstructed, but the \
           `--not' pragma indicates that it was expected to fail \
           reconstruction."
    | Unsupported_recursive_declaration ->
        Format.dprintf "%a" Format.pp_print_text
          "Reconstruction of this declaration is unsupported in a mutually \
           recursive group of declarations."
    | exn -> Error.raise_unsupported_exception_printing exn)

module type SIGNATURE_RECONSTRUCTION_STATE = sig
  include State.STATE

  val get_leftover_vars :
    (Abstract.free_var Synint.LF.ctx * Location.t) List.t t

  val add_leftover_vars :
    Abstract.free_var Synint.LF.ctx -> Location.t -> Unit.t t

  (** [disable_lf_strengthening ~location] disables the strengthening of LF
      terms and types during LF reconstruction.

      [location] is the location to use for error-reporting in case of
      failure to perform [disable_lf_strengthening ~location]. *)
  val disable_lf_strengthening : location:Location.t -> Unit.t t

  (** [enable_warn_on_coverage_error ~location] sets the error-reporting mode
      of pattern coverage-checking to `warn'.

      [location] is the location to use for error-reporting in case of
      failure to perform [enable_warn_on_coverage_error ~location]. *)
  val enable_warn_on_coverage_error : location:Location.t -> Unit.t t

  (** [enable_raise_on_coverage_error ~location] sets the error-reporting
      mode of pattern coverage-checking to `raise'.

      [location] is the location to use for error-reporting in case of
      failure to perform [enable_raise_on_coverage_error ~location]. *)
  val enable_raise_on_coverage_error : location:Location.t -> Unit.t t

  (** [set_name_generation_bases ~location ~meta_variable_base ?computation_variable_base constant]
      sets the naming convention for name generation of meta-level and
      computation-level variables using [meta_variable_base] and
      [computation_variable_base] respectively for a type-level constant
      [constant].

      [location] is the location to use for error-reporting in case of
      failure to perform
      [set_name_generation_bases ~location ~meta_variable_base ?computation_variable_base constant].*)
  val set_name_generation_bases :
       location:Location.t
    -> meta_variable_base:Identifier.t
    -> ?computation_variable_base:Identifier.t
    -> Qualified_identifier.t
    -> Unit.t t

  val set_default_associativity :
    location:Location.t -> Associativity.t -> Unit.t t

  val set_operator_prefix :
       location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t t

  val set_operator_infix :
       location:Location.t
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t t

  val set_operator_postfix :
       location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t t

  val open_module : location:Location.t -> Qualified_identifier.t -> Unit.t t

  val add_module_abbreviation :
       location:Location.t
    -> Qualified_identifier.t
    -> abbreviation:Identifier.t
    -> Unit.t t

  (** [with_checkpoint m state] is [(state, x)] where [x] is the result of
      running [m] with [state]. Note that the state is rolled back entirely. *)
  val with_checkpoint : 'a t -> 'a t

  (** {1 Indexing} *)

  (** [index_lf_kind kind state] is [(state', kind')] where [kind'] is [kind]
      indexed with respect to [state]. Free variables in [kind] are discarded
      in [state']. *)
  val index_lf_kind : Synext.lf_kind -> Synapx.LF.kind t

  val index_lf_typ : Synext.lf_typ -> Synapx.LF.typ t

  val index_schema : Synext.schema -> Synapx.LF.schema t

  val index_meta_context : Synext.meta_context -> Synapx.LF.mctx t

  val index_closed_comp_typ : Synext.comp_typ -> Synapx.Comp.typ t

  val index_closed_comp_expression :
    Synext.comp_expression -> Synapx.Comp.exp t

  val index_comp_typedef :
       Synext.comp_typ
    -> Synext.comp_kind
    -> (Synapx.Comp.typ * Synapx.Comp.kind) t

  val add_lf_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_typ -> Unit.t t

  val add_lf_term_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_term -> Unit.t t

  val add_schema_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_schema -> Unit.t t

  val add_comp_val :
    ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t t

  val add_comp_typedef :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typdef -> Unit.t t
end

module type SIGNATURE_RECONSTRUCTION = sig
  include State.STATE

  val reconstruct_signature : Synext.signature -> Synint.Sgn.sgn t
end

module Make (Signature_reconstruction_state : SIGNATURE_RECONSTRUCTION_STATE) :
  SIGNATURE_RECONSTRUCTION
    with type state = Signature_reconstruction_state.state = struct
  include Signature_reconstruction_state

  let rec reconstruct_signature signature =
    let { Synext.Signature.global_pragmas; entries } = signature in
    let* () = apply_global_pragmas global_pragmas in
    reconstruct_signature_entries entries

  and apply_global_pragmas global_pragmas =
    traverse_list_void apply_global_pragma global_pragmas

  and apply_global_pragma global_pragma =
    match global_pragma with
    | Synext.Signature.Global_pragma.No_strengthening { location } ->
        disable_lf_strengthening ~location
    | Synext.Signature.Global_pragma.Warn_on_coverage_error { location } ->
        enable_warn_on_coverage_error ~location
    | Synext.Signature.Global_pragma.Raise_error_on_coverage_error
        { location } ->
        enable_raise_on_coverage_error ~location

  (** [reconstruct_signature_entries entries] reconstructs a list of
      signature entries. This in particular handles the reconstruction of
      entries that are not handled independently from one another, such as
      [--not] pragmas. *)
  and reconstruct_signature_entries entries =
    match entries with
    | Synext.Signature.Entry.Pragma
        { location = pragma_location
        ; pragma = Synext.Signature.Pragma.Not _
        }
      :: entries -> (
        match entries with
        | [] -> Error.raise_at1 pragma_location Dangling_not_pragma
        | entry :: entries -> (
            (* The [--not] pragma indicates that we expect [entry] to fail
               reconstruction. So, we perform reconstruction of [entry]
               without keeping track of its side effects. *)
            let* entry_res' =
              try_catch
                (lazy
                  ( with_checkpoint (reconstruct_signature_entry entry)
                  $> fun entry' -> Result.ok entry' ))
                ~on_exn:(fun reconstruction_error ->
                  (* The [--not] pragma was used properly *)
                  return (Result.error reconstruction_error))
            in
            match entry_res' with
            | Result.Ok _ ->
                Error.raise_at2 pragma_location
                  (Synext.location_of_signature_entry entry)
                  Unexpected_entry_reconstruction_success
            | Result.Error _ ->
                Chatter.print 1
                  "Reconstruction fails for --not'd declaration@.";
                reconstruct_signature_entries entries))
    | entry :: entries ->
        let* entry' = reconstruct_signature_entry entry in
        let* entries' = reconstruct_signature_entries entries in
        return (entry' :: entries')
    | [] -> return []

  (** [reconstruct_signature_entry entry] reconstructs a single signature
      entry. *)
  and reconstruct_signature_entry entry =
    match entry with
    | Synext.Signature.Entry.Comment { location; content } ->
        return (Synint.Sgn.Comment { location; content })
    | Synext.Signature.Entry.Pragma { pragma; _ } ->
        let* pragma' = reconstruct_signature_pragma pragma in
        return (Synint.Sgn.Pragma { pragma = pragma' })
    | Synext.Signature.Entry.Declaration { declaration; _ } ->
        reconstruct_signature_declaration declaration

  and reconstruct_signature_pragma pragma =
    match pragma with
    | Synext.Signature.Pragma.Not _ ->
        Error.raise_violation
          "[reconstruct_signature_pragma] --not pragma must be \
           reconstructed with [reconstruct_signature_entries]"
    | Synext.Signature.Pragma.Name
        { location; constant; meta_variable_base; computation_variable_base }
      ->
        let* () =
          set_name_generation_bases ~location ~meta_variable_base
            ?computation_variable_base constant
        in
        let name = Name.make_from_qualified_identifier constant in
        return (Synint.LF.NamePrag name)
    | Synext.Signature.Pragma.Default_associativity
        { associativity; location } ->
        let* () = set_default_associativity ~location associativity in
        return (Synint.LF.DefaultAssocPrag associativity)
    | Synext.Signature.Pragma.Prefix_fixity
        { location; constant; precedence } ->
        let* () = set_operator_prefix ~location ?precedence constant in
        let name = Name.make_from_qualified_identifier constant in
        let associativity = Option.some Associativity.right_associative in
        return
          (Synint.LF.FixPrag (name, Fixity.prefix, precedence, associativity))
    | Synext.Signature.Pragma.Infix_fixity
        { location; constant; precedence; associativity } ->
        let* () =
          set_operator_infix ~location ?precedence ?associativity constant
        in
        let name = Name.make_from_qualified_identifier constant in
        return
          (Synint.LF.FixPrag (name, Fixity.infix, precedence, associativity))
    | Synext.Signature.Pragma.Postfix_fixity
        { location; constant; precedence } ->
        let* () = set_operator_postfix ~location ?precedence constant in
        let name = Name.make_from_qualified_identifier constant in
        let associativity = Option.some Associativity.left_associative in
        return
          (Synint.LF.FixPrag (name, Fixity.postfix, precedence, associativity))
    | Synext.Signature.Pragma.Open_module { location; module_identifier } ->
        let* () = open_module ~location module_identifier in
        return (Synint.LF.OpenPrag module_identifier)
    | Synext.Signature.Pragma.Abbreviation
        { location; module_identifier; abbreviation } ->
        let* () =
          add_module_abbreviation ~location module_identifier ~abbreviation
        in
        let module_identifier_as_list =
          module_identifier |> Qualified_identifier.to_list1 |> List1.to_list
          |> List.map Identifier.show
        in
        return
          (Synint.LF.AbbrevPrag
             (module_identifier_as_list, Identifier.show abbreviation))
    | Synext.Signature.Pragma.Query
        { location
        ; identifier
        ; meta_context
        ; typ
        ; expected_solutions
        ; maximum_tries
        } ->
        reconstruct_query_declaration location identifier meta_context typ
          expected_solutions maximum_tries

  and reconstruct_signature_declaration declaration =
    match declaration with
    | Synext.Signature.Declaration.CompTyp { location; _ }
    | Synext.Signature.Declaration.CompCotyp { location; _ }
    | Synext.Signature.Declaration.CompConst { location; _ }
    | Synext.Signature.Declaration.CompDest { location; _ }
    | Synext.Signature.Declaration.Theorem { location; _ }
    | Synext.Signature.Declaration.Proof { location; _ } ->
        Error.raise_violation ~location
          "[reconstruct_signature_declaration] this kind of signature \
           declaration is only supported within a mutually recursive group \
           of declarations."
    | Synext.Signature.Declaration.Typ { location; identifier; kind } ->
        reconstruct_oldstyle_lf_typ_declaration location identifier kind
    | Synext.Signature.Declaration.Const { location; identifier; typ } ->
        reconstruct_oldstyle_lf_const_declaration location identifier typ
    | Synext.Signature.Declaration.Schema { location; identifier; schema } ->
        reconstruct_schema_declaration location identifier schema
    | Synext.Signature.Declaration.CompTypAbbrev
        { location; identifier; kind; typ } ->
        reconstruct_comp_typ_abbrev_declaration location identifier kind typ
    | Synext.Signature.Declaration.Val
        { location; identifier; typ; expression } ->
        reconstruct_val_declaration location identifier typ expression
    | Synext.Signature.Declaration.Recursive_declarations
        { location; declarations } ->
        reconstruct_recursive_declarations location declarations
    | Synext.Signature.Declaration.Module { location; identifier; entries }
      ->
        reconstruct_module_declaration location identifier entries

  and reconstruct_oldstyle_lf_typ_declaration location identifier extK =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Typ at: %a" Location.print_short location);
    dprintf (fun p ->
        p.fmt "\nIndexing type constant %a" Identifier.pp identifier);
    let* apxK = index_lf_kind extK in
    dprintf (fun p ->
        p.fmt "\nElaborating type constant %a" Identifier.pp identifier);
    Store.FVar.clear ();
    let tK =
      Monitor.timer
        ( "Type Elaboration"
        , fun () ->
            let tK = Reconstruct.kind apxK in
            Reconstruct.solve_fvarCnstr Lfrecon.Pi;
            tK )
    in
    Unify.forceGlobalCnstr ();
    let tK', i =
      Monitor.timer ("Type Abstraction", fun () -> Abstract.kind tK)
    in
    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    dprintf (fun p ->
        p.fmt "%a : %a@." Identifier.pp identifier
          (P.fmt_ppr_lf_kind Synint.LF.Null P.l0)
          tK');
    Monitor.timer
      ( "Type Check"
      , fun () -> Check.LF.checkKind Synint.LF.Empty Synint.LF.Null tK' );
    dprintf (fun p ->
        p.fmt "DOUBLE CHECK for type constant %a successful!" Identifier.pp
          identifier);
    Typeinfo.Sgn.add location
      (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Kind tK'))
      "";
    let cid =
      Store.Cid.Typ.add (fun _cid -> Store.Cid.Typ.mk_entry name tK' i)
    in
    let* () = add_lf_type_constant ~location identifier cid in
    return (Synint.Sgn.Typ { location; identifier = cid; kind = tK' })

  and reconstruct_oldstyle_lf_const_declaration location identifier extT =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Const at: %a" Location.print_short location);
    let* apxT = index_lf_typ extT in
    let rec get_type_family = function
      | Synapx.LF.Atom (_loc, a, _spine) -> a
      | Synapx.LF.PiTyp ((_, _), t) -> get_type_family t
      | Synapx.LF.Sigma _ ->
          Error.raise_violation ~location
            "[reconstruct_oldstyle_lf_const_declaration] unsupported sigma \
             type"
    in
    let constructedType = get_type_family apxT in
    dprintf (fun p ->
        p.fmt "Reconstructing term constant %a" Identifier.pp identifier);
    Store.FVar.clear ();
    let tA =
      Monitor.timer
        ( "Constant Elaboration"
        , fun () ->
            let tA = Reconstruct.typ Lfrecon.Pi apxT in
            Reconstruct.solve_fvarCnstr Lfrecon.Pi;
            tA )
    in
    let cD = Synint.LF.Empty in
    dprintf (fun p ->
        p.fmt "[recSgnDecl] [Const] %a : %a" Identifier.pp identifier
          (P.fmt_ppr_lf_typ cD Synint.LF.Null P.l0)
          tA);
    Unify.forceGlobalCnstr ();
    let tA', i =
      Monitor.timer ("Constant Abstraction", fun () -> Abstract.typ tA)
    in
    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    dprintf (fun p ->
        p.fmt
          "[recSgnDecl] [Const] Reconstruction (with abstraction) of \
           constant: %a : %a"
          Identifier.pp identifier
          (P.fmt_ppr_lf_typ cD Synint.LF.Null P.l0)
          tA');
    Monitor.timer
      ( "Constant Check"
      , fun () ->
          Check.LF.checkTyp Synint.LF.Empty Synint.LF.Null (tA', S.LF.id) );
    Typeinfo.Sgn.add location
      (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Typ tA'))
      "";
    let cid =
      Store.Cid.Term.add' location constructedType (fun _cid ->
          Store.Cid.Term.mk_entry name tA' i)
    in
    let* () = add_lf_term_constant ~location identifier cid in
    return (Synint.Sgn.Const { location; identifier = cid; typ = tA' })

  and reconstruct_schema_declaration location identifier schema =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Schema at: %a@." Location.print_short
          location);
    let* apx_schema = index_schema schema in
    dprintf (fun p ->
        p.fmt "Reconstructing schema %a@." Identifier.pp identifier);
    Store.FVar.clear ();
    let sW = Reconstruct.schema apx_schema in
    dprintf (fun p ->
        p.fmt "Elaborated schema %a : %a" Identifier.pp identifier
          (P.fmt_ppr_lf_schema P.l0)
          sW);
    Reconstruct.solve_fvarCnstr Lfrecon.Pi;
    Unify.forceGlobalCnstr ();
    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    let sW' = Abstract.schema sW in
    dprintf (fun p ->
        p.fmt "Schema %a : %a after abstraction@." Identifier.pp identifier
          (P.fmt_ppr_lf_schema P.l0)
          sW');
    Check.LF.checkSchemaWf sW';
    dprintf (fun p ->
        p.fmt "TYPE CHECK for schema %a successful@." Identifier.pp
          identifier);
    let cid =
      Store.Cid.Schema.add (fun _cid -> Store.Cid.Schema.mk_entry name sW')
    in
    let* () = add_schema_constant ~location identifier cid in
    return (Synint.Sgn.Schema { location; identifier = cid; schema = sW' })

  and reconstruct_comp_typ_abbrev_declaration location identifier cK cT =
    let name = Name.make_from_identifier identifier in
    (* index cT in a context which contains arguments to cK *)
    let* apx_tau, apxK = index_comp_typedef cT cK in
    let (cD, cT), i, cK =
      Reconstruct.comptypdef location name (apx_tau, apxK)
    in
    dprintf (fun p ->
        p.fmt "typedef %a : %a = %a" Identifier.pp identifier
          (P.fmt_ppr_cmp_kind Synint.LF.Empty P.l0)
          cK
          (P.fmt_ppr_cmp_typ cD P.l0)
          cT);
    Monitor.timer
      ( "Type abbrev. : Kind Check"
      , fun () -> Check.Comp.checkKind Synint.LF.Empty cK );
    Monitor.timer
      ("Type abbrev. : Type Check", fun () -> Check.Comp.checkTyp cD cT);
    let cid =
      Store.Cid.CompTypDef.add (fun _cid ->
          Store.Cid.CompTypDef.mk_entry name i (cD, cT) cK)
    in
    let* () = add_comp_typedef ~location identifier cid in
    return (Synint.Sgn.CompTypAbbrev
    { location; identifier = name; kind = cK; typ = cT })

  and reconstruct_val_declaration location identifier typ_opt expression =
    match typ_opt with
    | Option.None ->
        reconstruct_untyped_val_declaration location identifier expression
    | Option.Some typ ->
        reconstruct_typed_val_declaration location identifier typ expression

  and reconstruct_untyped_val_declaration location identifier expression =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Val at: %a" Location.print_short location);
    let* apx_i = index_closed_comp_expression expression in
    let cD, cG = (Synint.LF.Empty, Synint.LF.Empty) in
    let i', (tau, theta) =
      Monitor.timer
        ("Function Elaboration", fun () -> Reconstruct.exp' cG apx_i)
    in
    Unify.forceGlobalCnstr ();
    let tau' = Whnf.cnormCTyp (tau, theta) in
    let expression' = Whnf.cnormExp (i', Whnf.m_id) in

    dprintf (fun p ->
        p.fmt "[AFTER Reconstruction Val] @[<v 2>let %a : %a =@ %a@]"
          Identifier.pp identifier
          (P.fmt_ppr_cmp_typ cD P.l0)
          tau'
          (P.fmt_ppr_cmp_exp cD cG P.l0)
          expression');
    let cQ, expression'' =
      Monitor.timer
        ("Function Abstraction", fun () -> Abstract.exp expression')
    in
    let* () = add_leftover_vars cQ location in
    Monitor.timer
      ( "Function Check"
      , fun () ->
          Check.Comp.check Option.none cD cG [] expression'' (tau', C.m_id)
      );

    let value_opt =
      if Holes.none () && Context.is_empty cQ then
        Option.some (Opsem.eval expression'')
      else Option.none
    in
    let cid =
      Store.Cid.Comp.add (fun _cid ->
          let mgid =
            Store.Cid.Comp.add_mutual_group
              [ { Synint.Comp.name; tau = tau'; order = `not_recursive } ]
          in
          Store.Cid.Comp.mk_entry
            (Option.some (Decl.next ()))
            name tau' 0 mgid value_opt)
    in
    let* () = add_comp_val ~location identifier cid in
    return (Synint.Sgn.Val
    { location
    ; identifier = name
    ; typ = tau'
    ; expression = expression''
    ; expression_value = value_opt
    })

  and reconstruct_typed_val_declaration location identifier tau expression =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Val at %a" Location.print_short location);
    let* apx_tau = index_closed_comp_typ tau in
    let cD, cG = (Synint.LF.Empty, Synint.LF.Empty) in
    let tau' =
      Monitor.timer
        ("Function Type Elaboration", fun () -> Reconstruct.comptyp apx_tau)
    in
    Unify.forceGlobalCnstr ();
    let tau', _ =
      Monitor.timer
        ("Function Type Abstraction", fun () -> Abstract.comptyp tau')
    in
    Monitor.timer
      ("Function Type Check", fun () -> Check.Comp.checkTyp cD tau');
    let* apx_i = index_closed_comp_expression expression in
    let i' =
      Monitor.timer
        ( "Function Elaboration"
        , fun () -> Reconstruct.exp cG apx_i (tau', C.m_id) )
    in
    let expression' = Whnf.cnormExp (i', Whnf.m_id) in
    Unify.forceGlobalCnstr ();
    let tau' = Whnf.cnormCTyp (tau', C.m_id) in
    dprintf (fun p ->
        p.fmt "[AFTER Reconstruction Val - 2] let %a : %a =@ %a"
          Identifier.pp identifier
          (P.fmt_ppr_cmp_typ cD P.l0)
          tau'
          (P.fmt_ppr_cmp_exp cD cG P.l0)
          expression');

    let cQ, expression'' =
      Monitor.timer
        ("Function Abstraction", fun () -> Abstract.exp expression')
    in
    let* () = add_leftover_vars cQ location in
    Monitor.timer
      ( "Function Check"
      , fun _cid ->
          Check.Comp.check Option.none cD cG [] expression'' (tau', C.m_id)
      );
    let value_opt =
      if Holes.none () && Context.is_empty cQ then
        Option.some (Opsem.eval expression'')
      else Option.none
    in
    let cid =
      let mgid =
        Store.Cid.Comp.add_mutual_group
          [ { Synint.Comp.name; tau = tau'; order = `not_recursive } ]
      in
      Store.Cid.Comp.add (fun _cid ->
          Store.Cid.Comp.mk_entry
            (Option.some (Decl.next ()))
            name tau' 0 mgid value_opt)
    in
    let* () = add_comp_val ~location identifier cid in
    return (Synint.Sgn.Val
    { location
    ; identifier = name
    ; typ = tau'
    ; expression = expression''
    ; expression_value = value_opt
    })

  and reconstruct_query_declaration location identifier_opt cD extT
      expected_solutions maximum_tries =
    let name_opt = Option.map Name.make_from_identifier identifier_opt in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Query at %a" Location.print_short location);
    let* apxT = index_lf_typ extT in
    dprint (fun () -> "Reconstructing query.");

    Store.FVar.clear ();
    let tA =
      Monitor.timer
        ( "Constant Elaboration"
        , fun () ->
            let tA = Reconstruct.typ Lfrecon.Pi apxT in
            Reconstruct.solve_fvarCnstr Lfrecon.Pi;
            tA )
    in
    let* cD = index_meta_context cD in
    let cD = Reconstruct.mctx cD in
    dprintf (fun p ->
        p.fmt "Elaboration of query : %a"
          (P.fmt_ppr_lf_typ cD Synint.LF.Null P.l0)
          tA);
    Unify.forceGlobalCnstr ();
    let tA', i =
      Monitor.timer ("Constant Abstraction", fun () -> Abstract.typ tA)
    in
    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    dprintf (fun p ->
        p.fmt
          "Reconstruction (with abstraction) of query: %a with %s \
           abstracted variables"
          (P.fmt_ppr_lf_typ cD Synint.LF.Null P.l0)
          tA' (string_of_int i));
    Monitor.timer
      ( "Constant Check"
      , fun () ->
          Check.LF.checkTyp Synint.LF.Empty Synint.LF.Null (tA', S.LF.id) );
    Logic.storeQuery name_opt (tA', i) cD expected_solutions maximum_tries;
    return
      (Synint.LF.Query
         { location
         ; name = name_opt
         ; mctx = cD
         ; typ = (tA', i)
         ; expected_solutions
         ; maximum_tries
         })

  and reconstruct_module_declaration _location _identifier _entries =
    Obj.magic () (* TODO: *)

  and reconstruct_recursive_declarations location declarations =
    let (List1.T (first_declaration, declarations')) = declarations in
    match first_declaration with
    | Synext.Signature.Declaration.Typ _ ->
        let groups =
          group_recursive_lf_typ_declarations first_declaration declarations'
        in
        reconstruct_recursive_lf_typ_declarations location groups
    | Synext.Signature.Declaration.CompTyp _
    | Synext.Signature.Declaration.CompCotyp _ ->
        let groups =
          group_recursive_comp_typ_declarations first_declaration
            declarations'
        in
        reconstruct_recursive_comp_typ_declarations location groups
    | Synext.Signature.Declaration.Theorem _
    | Synext.Signature.Declaration.Proof _ ->
        let groups =
          group_recursive_theorem_declarations first_declaration
            declarations'
        in
        reconstruct_recursive_theorem_declarations location groups
    | _ ->
        Error.raise_at1
          (Synext.location_of_signature_declaration first_declaration)
          Unsupported_recursive_declaration

  and reconstruct_recursive_lf_typ_declarations location declarations =
    Obj.magic () (* TODO: *)

  and reconstruct_recursive_comp_typ_declarations location declarations =
    Obj.magic () (* TODO: *)

  and reconstruct_recursive_theorem_declarations location declarations =
    Obj.magic () (* TODO: *)

  and group_recursive_lf_typ_declarations first_declaration declarations =
    match first_declaration with
    | Synext.Signature.Declaration.Typ { identifier; kind; _ } -> (
        let lf_term_constant_declarations, declarations' =
          List.take_while_map
            (function
              | Synext.Signature.Declaration.Const { identifier; typ; _ } ->
                  Option.some (identifier, typ)
              | _ -> Option.none)
            declarations
        in
        let lf_typ_declaration =
          `Lf_typ (identifier, kind, lf_term_constant_declarations)
        in
        match declarations' with
        | [] -> List1.singleton lf_typ_declaration
        | first_declaration' :: declarations'' ->
            let lf_typ_declarations =
              group_recursive_lf_typ_declarations first_declaration'
                declarations''
            in
            List1.cons lf_typ_declaration lf_typ_declarations)
    | _ ->
        Error.raise_at1
          (Synext.location_of_signature_declaration first_declaration)
          Unsupported_recursive_declaration

  and group_recursive_theorem_declarations first_declaration declarations =
    match first_declaration with
    | Synext.Signature.Declaration.Theorem
        { identifier; typ; order; body; _ } -> (
        let theorem_declaration = `Theorem (identifier, typ, order, body) in
        match declarations with
        | [] -> List1.singleton theorem_declaration
        | first_declaration' :: declarations'' ->
            let theorem_declarations =
              group_recursive_theorem_declarations first_declaration'
                declarations''
            in
            List1.cons theorem_declaration theorem_declarations)
    | Synext.Signature.Declaration.Proof { identifier; typ; order; body; _ }
      -> (
        let proof_declaration = `Proof (identifier, typ, order, body) in
        match declarations with
        | [] -> List1.singleton proof_declaration
        | first_declaration' :: declarations'' ->
            let theorem_declarations =
              group_recursive_theorem_declarations first_declaration'
                declarations''
            in
            List1.cons proof_declaration theorem_declarations)
    | _ ->
        Error.raise_at1
          (Synext.location_of_signature_declaration first_declaration)
          Unsupported_recursive_declaration

  and group_recursive_comp_typ_declarations first_declaration declarations =
    match first_declaration with
    | Synext.Signature.Declaration.CompTyp
        { identifier; kind; datatype_flavour; _ } -> (
        let comp_constructor_declarations, declarations' =
          List.take_while_map
            (function
              | Synext.Signature.Declaration.CompConst { identifier; typ; _ }
                ->
                  Option.some (identifier, typ)
              | _ -> Option.none)
            declarations
        in
        let comp_typ_declaration =
          match datatype_flavour with
          | `Inductive ->
              `Inductive_comp_typ
                (identifier, kind, comp_constructor_declarations)
          | `Stratified ->
              `Stratified_comp_typ
                (identifier, kind, comp_constructor_declarations)
        in
        match declarations' with
        | [] -> List1.singleton comp_typ_declaration
        | first_declaration' :: declarations'' ->
            let comp_typ_declarations =
              group_recursive_comp_typ_declarations first_declaration'
                declarations''
            in
            List1.cons comp_typ_declaration comp_typ_declarations)
    | Synext.Signature.Declaration.CompCotyp { identifier; kind; _ } -> (
        let comp_destructor_declarations, declarations' =
          List.take_while_map
            (function
              | Synext.Signature.Declaration.CompDest
                  { identifier; observation_type; return_type; _ } ->
                  Option.some (identifier, observation_type, return_type)
              | _ -> Option.none)
            declarations
        in
        let comp_cotyp_declaration =
          `Coinductive_comp_typ
            (identifier, kind, comp_destructor_declarations)
        in
        match declarations' with
        | [] -> List1.singleton comp_cotyp_declaration
        | first_declaration' :: declarations'' ->
            let comp_typ_declarations =
              group_recursive_comp_typ_declarations first_declaration'
                declarations''
            in
            List1.cons comp_cotyp_declaration comp_typ_declarations)
    | _ ->
        Error.raise_at1
          (Synext.location_of_signature_declaration first_declaration)
          Unsupported_recursive_declaration
end
