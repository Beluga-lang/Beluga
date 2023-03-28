open Support
open Beluga_syntax

[@@@warning "+A-4-44"]

exception Unsupported_lf_typ_applicand

exception Unsupported_lf_term_applicand

exception Unsupported_lf_annotated_term_abstraction

exception Unsupported_lf_untyped_pi_kind_parameter

exception Unsupported_lf_untyped_pi_typ_parameter

exception Unsupported_clf_projection_applicand

exception Unsupported_clf_substitution_applicand

exception Unsupported_context_schema_element

exception Unsupported_comp_typ_applicand

exception Unsupported_comp_pattern_applicand

exception Unsupported_copattern_meta_context

exception Duplicate_identifiers_in_schema_some_clause of Identifier.t List2.t

exception
  Duplicate_identifiers_in_schema_block_clause of Identifier.t List2.t

let () =
  Error.register_exception_printer (function
    | Unsupported_lf_typ_applicand ->
        Format.dprintf "Unsupported LF type applicand."
    | Unsupported_lf_term_applicand ->
        Format.dprintf "Unsupported LF term applicand."
    | Unsupported_lf_annotated_term_abstraction ->
        Format.dprintf
          "Type-annotating the parameter of an LF abstraction is not \
           supported."
    | Unsupported_lf_untyped_pi_kind_parameter ->
        Format.dprintf "Unsupported untyped LF Pi-kind parameter."
    | Unsupported_lf_untyped_pi_typ_parameter ->
        Format.dprintf "Unsupported untyped LF Pi-type paramter."
    | Unsupported_clf_projection_applicand ->
        Format.dprintf "Unsupported contextual LF projection applicand."
    | Unsupported_clf_substitution_applicand ->
        Format.dprintf "Unsupported contextual LF substitution applicand."
    | Unsupported_context_schema_element ->
        Format.dprintf "Unsupported nesting of context schema alternations."
    | Unsupported_comp_typ_applicand ->
        Format.dprintf "Unsupported computation-level type applicand."
    | Unsupported_comp_pattern_applicand ->
        Format.dprintf "Unsupported computation-level pattern applicand."
    | Unsupported_copattern_meta_context ->
        Format.dprintf
          "Meta-contexts in computation-level copatterns are unsupported."
    | Duplicate_identifiers_in_schema_some_clause _ ->
        Format.dprintf "Illegal duplicate identifiers in schema some clause."
    | Duplicate_identifiers_in_schema_block_clause _ ->
        Format.dprintf
          "Illegal duplicate identifiers in schema block clause."
    | exn -> Error.raise_unsupported_exception_printing exn)

module type INDEXER = sig
  include State.STATE

  val index_open_lf_kind : Synext.lf_kind -> Synapx.LF.kind t

  val index_closed_lf_kind : Synext.lf_kind -> Synapx.LF.kind t

  val index_open_lf_typ : Synext.lf_typ -> Synapx.LF.typ t

  val index_closed_lf_typ : Synext.lf_typ -> Synapx.LF.typ t

  val index_open_comp_kind : Synext.comp_kind -> Synapx.Comp.kind t

  val index_closed_comp_kind : Synext.comp_kind -> Synapx.Comp.kind t

  val index_open_comp_typ : Synext.comp_typ -> Synapx.Comp.typ t

  val index_closed_comp_typ : Synext.comp_typ -> Synapx.Comp.typ t

  val index_comp_expression : Synext.comp_expression -> Synapx.Comp.exp t

  val index_schema : Synext.schema -> Synapx.LF.schema t

  val index_comp_theorem : Synext.comp_expression -> Synapx.Comp.thm t

  val index_harpoon_proof : Synext.harpoon_proof -> Synapx.Comp.thm t

  val index_computation_typ_abbreviation :
       Synext.comp_typ
    -> Synext.comp_kind
    -> (Synapx.Comp.typ * Synapx.Comp.kind) t

  val index_lf_query :
       Synext.meta_context
    -> Synext.clf_typ
    -> (Synapx.LF.mctx * Synapx.LF.typ) t
end

module Make_indexer (Indexing_state : Index_state.INDEXING_STATE) = struct
  include Indexing_state

  let with_bound_omittable_lf_variable identifier_opt =
    match identifier_opt with
    | Option.None -> with_shifted_lf_context
    | Option.Some identifier -> with_bound_lf_variable identifier

  let[@warning "-32"] with_bound_omittable_meta_variable identifier_opt =
    match identifier_opt with
    | Option.None -> with_shifted_meta_context
    | Option.Some identifier -> with_bound_meta_variable identifier

  let with_bound_omittable_comp_variable identifier_opt =
    match identifier_opt with
    | Option.None -> with_shifted_comp_context
    | Option.Some identifier -> with_bound_comp_variable identifier

  let with_bound_meta_variable' identifier typ =
    match typ with
    | Synext.Meta.Typ.Context_schema _ ->
        with_bound_context_variable identifier
    | Synext.Meta.Typ.Contextual_typ _ -> with_bound_meta_variable identifier
    | Synext.Meta.Typ.Parameter_typ _ ->
        with_bound_parameter_variable identifier
    | Synext.Meta.Typ.Plain_substitution_typ _
    | Synext.Meta.Typ.Renaming_substitution_typ _ ->
        with_bound_substitution_variable identifier

  let with_meta_level_binding_opt identifier_opt typ =
    match identifier_opt with
    | Option.None -> Fun.id
    | Option.Some identifier -> with_bound_meta_variable' identifier typ

  let with_bound_omittable_meta_variable identifier_opt typ =
    match identifier_opt with
    | Option.None -> with_shifted_meta_context
    | Option.Some identifier -> with_bound_meta_variable' identifier typ

  let rec append_lf_spines spine1 spine2 =
    match spine1 with
    | Synapx.LF.Nil -> spine2
    | Synapx.LF.App (x, sub_spine1) ->
        let spine' = append_lf_spines sub_spine1 spine2 in
        Synapx.LF.App (x, spine')

  let rec append_meta_spines spine1 spine2 =
    match spine1 with
    | Synapx.Comp.MetaNil -> spine2
    | Synapx.Comp.MetaApp (x, sub_spine1) ->
        let spine' = append_meta_spines sub_spine1 spine2 in
        Synapx.Comp.MetaApp (x, spine')

  let rec index_lf_kind = function
    | Synext.LF.Kind.Typ _ -> return Synapx.LF.Typ
    | Synext.LF.Kind.Arrow { domain; range; _ } ->
        let* domain' = index_lf_typ domain in
        let* range' = with_shifted_lf_context (index_lf_kind range) in
        let* x = fresh_identifier in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.LF.PiKind
             ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
    | Synext.LF.Kind.Pi
        { parameter_identifier; parameter_type; plicity; body; location }
      -> (
        match parameter_type with
        | Option.None ->
            Error.raise_at1 location Unsupported_lf_untyped_pi_kind_parameter
        | Option.Some parameter_type ->
            let* domain' = index_lf_typ parameter_type in
            let* range' =
              (with_bound_omittable_lf_variable parameter_identifier)
                (index_lf_kind body)
            in
            let* x = fresh_identifier_opt parameter_identifier in
            let x' = Name.make_from_identifier x in
            return
              (Synapx.LF.PiKind
                 ((Synapx.LF.TypDecl (x', domain'), plicity), range')))

  and index_lf_typ = function
    | Synext.LF.Typ.Constant { identifier; location; _ } ->
        let* id = index_of_lf_typ_constant identifier in
        return (Synapx.LF.Atom (location, id, Synapx.LF.Nil))
    | Synext.LF.Typ.Application { applicand; arguments; location } -> (
        match applicand with
        | Synext.LF.Typ.Constant _
        | Synext.LF.Typ.Application _ -> (
            let* applicand' = index_lf_typ applicand in
            match applicand' with
            | Synapx.LF.Atom (_applicand_location, id, spine1') ->
                let* spine2' = index_lf_spine arguments in
                let spine' = append_lf_spines spine1' spine2' in
                return (Synapx.LF.Atom (location, id, spine'))
            | Synapx.LF.PiTyp _
            | Synapx.LF.Sigma _ ->
                assert false
            (* Supported LF type-level applicands are always translated to LF
               atoms *))
        | Synext.LF.Typ.Arrow _
        | Synext.LF.Typ.Pi _ ->
            Error.raise_at1
              (Synext.location_of_lf_typ applicand)
              Unsupported_lf_typ_applicand)
    | Synext.LF.Typ.Arrow { domain; range; _ } ->
        let* domain' = index_lf_typ domain in
        let* range' = with_shifted_lf_context (index_lf_typ range) in
        let* x = fresh_identifier in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.LF.PiTyp
             ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
    | Synext.LF.Typ.Pi
        { parameter_identifier; parameter_type; plicity; body; location }
      -> (
        match parameter_type with
        | Option.None ->
            Error.raise_at1 location Unsupported_lf_untyped_pi_typ_parameter
        | Option.Some parameter_type ->
            let* domain' = index_lf_typ parameter_type in
            let* range' =
              (with_bound_omittable_lf_variable parameter_identifier)
                (index_lf_typ body)
            in
            let* x = fresh_identifier_opt parameter_identifier in
            let x' = Name.make_from_identifier x in
            return
              (Synapx.LF.PiTyp
                 ((Synapx.LF.TypDecl (x', domain'), plicity), range')))

  and index_lf_term = function
    | Synext.LF.Term.Variable { location; identifier } -> (
        index_of_lf_variable_opt identifier >>= function
        | Option.Some offset ->
            let head = Synapx.LF.BVar offset in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine))
        | Option.None ->
            let* () = add_free_lf_variable identifier in
            let name = Name.make_from_identifier identifier in
            let head = Synapx.LF.FVar name in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine)))
    | Synext.LF.Term.Constant { location; identifier; _ } ->
        let* id = index_of_lf_term_constant identifier in
        let head = Synapx.LF.Const id in
        let spine = Synapx.LF.Nil in
        return (Synapx.LF.Root (location, head, spine))
    | Synext.LF.Term.Application { location; applicand; arguments } -> (
        match applicand with
        | Synext.LF.Term.Variable _
        | Synext.LF.Term.Constant _
        | Synext.LF.Term.Application _
        | Synext.LF.Term.Wildcard _ -> (
            let* applicand' = index_lf_term applicand in
            match applicand' with
            | Synapx.LF.Root (_applicand_location, id, spine1') ->
                let* spine2' = index_lf_spine arguments in
                let spine' = append_lf_spines spine1' spine2' in
                return (Synapx.LF.Root (location, id, spine'))
            | Synapx.LF.Lam _
            | Synapx.LF.LFHole _
            | Synapx.LF.Tuple _
            | Synapx.LF.Ann _ ->
                assert false
            (* Supported LF term-level applicands are always translated to LF
               roots *))
        | Synext.LF.Term.Type_annotated _
        | Synext.LF.Term.Abstraction _ ->
            Error.raise_at1
              (Synext.location_of_lf_term applicand)
              Unsupported_lf_term_applicand)
    | Synext.LF.Term.Abstraction
        { location; parameter_identifier; parameter_type; body } -> (
        match parameter_type with
        | Option.None ->
            let* body' =
              (with_bound_omittable_lf_variable parameter_identifier)
                (index_lf_term body)
            in
            let* x = fresh_identifier_opt parameter_identifier in
            let x' = Name.make_from_identifier x in
            return (Synapx.LF.Lam (location, x', body'))
        | Option.Some _typ ->
            Error.raise_at1 location
              Unsupported_lf_annotated_term_abstraction)
    | Synext.LF.Term.Wildcard { location } ->
        let* x = fresh_identifier in
        let x' = Name.make_from_identifier x in
        let head = Synapx.LF.FVar x' in
        let spine = Synapx.LF.Nil in
        return (Synapx.LF.Root (location, head, spine))
    | Synext.LF.Term.Type_annotated { location; term; typ } ->
        let* term' = index_lf_term term in
        let* typ' = index_lf_typ typ in
        return (Synapx.LF.Ann (location, term', typ'))

  and index_lf_spine arguments =
    List1.fold_right
      (fun argument ->
        let* argument' = index_lf_term argument in
        return (Synapx.LF.App (argument', Synapx.LF.Nil)))
      (fun argument spine ->
        let* argument' = index_lf_term argument in
        let* spine' = spine in
        return (Synapx.LF.App (argument', spine')))
      arguments

  let rec index_clf_typ = function
    | Synext.CLF.Typ.Constant { identifier; location; _ } ->
        let* id = index_of_lf_typ_constant identifier in
        let spine = Synapx.LF.Nil in
        return (Synapx.LF.Atom (location, id, spine))
    | Synext.CLF.Typ.Application { applicand; arguments; location } -> (
        match applicand with
        | Synext.CLF.Typ.Constant _
        | Synext.CLF.Typ.Application _ -> (
            let* applicand' = index_clf_typ applicand in
            match applicand' with
            | Synapx.LF.Atom (_applicand_location, id, spine1') ->
                let* spine2' = index_clf_spine arguments in
                let spine' = append_lf_spines spine1' spine2' in
                return (Synapx.LF.Atom (location, id, spine'))
            | Synapx.LF.PiTyp _
            | Synapx.LF.Sigma _ ->
                assert false
            (* Supported contextual LF type-level applicands are always
               translated to LF atoms *))
        | Synext.CLF.Typ.Arrow _
        | Synext.CLF.Typ.Pi _
        | Synext.CLF.Typ.Block _ ->
            Error.raise_at1
              (Synext.location_of_clf_typ applicand)
              Unsupported_lf_typ_applicand)
    | Synext.CLF.Typ.Arrow { domain; range; _ } ->
        let* domain' = index_clf_typ domain in
        let* range' = with_shifted_lf_context (index_clf_typ range) in
        let* x = fresh_identifier in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.LF.PiTyp
             ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
    | Synext.CLF.Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
        let* domain' = index_clf_typ parameter_type in
        let* range' =
          (with_bound_omittable_lf_variable parameter_identifier)
            (index_clf_typ body)
        in
        let* x = fresh_identifier_opt parameter_identifier in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.LF.PiTyp
             ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
    | Synext.CLF.Typ.Block { elements; _ } -> (
        match elements with
        | `Unnamed typ ->
            let* typ' = index_clf_typ typ in
            let identifier = Option.none in
            return (Synapx.LF.Sigma (Synapx.LF.SigmaLast (identifier, typ')))
        | `Record bindings ->
            let* bindings' = index_clf_block_bindings bindings in
            return (Synapx.LF.Sigma bindings'))

  and index_clf_block_bindings bindings =
    List1.fold_right
      (fun (identifier, typ) ->
        let* typ' = index_clf_typ typ in
        let name_opt = Option.some (Name.make_from_identifier identifier) in
        return (Synapx.LF.SigmaLast (name_opt, typ')))
      (fun (identifier, typ) bindings ->
        let* typ' = index_clf_typ typ in
        let name = Name.make_from_identifier identifier in
        let* bindings' = (with_bound_lf_variable identifier) bindings in
        return (Synapx.LF.SigmaElem (name, typ', bindings')))
      bindings

  and index_clf_term = function
    | Synext.CLF.Term.Variable { location; identifier } ->
        let* offset = index_of_lf_variable identifier in
        let head = Synapx.LF.BVar offset in
        let spine = Synapx.LF.Nil in
        return (Synapx.LF.Root (location, head, spine))
    | Synext.CLF.Term.Meta_variable { location; identifier } -> (
        index_of_meta_variable_opt identifier >>= function
        | Option.Some offset ->
            let closure = Option.none in
            let head = Synapx.LF.MVar (Synapx.LF.Offset offset, closure) in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine))
        | Option.None ->
            let* () = add_free_meta_variable identifier in
            let name = Name.make_from_identifier identifier in
            let closure = Option.none in
            let head = Synapx.LF.FMVar (name, closure) in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine)))
    | Synext.CLF.Term.Constant { location; identifier; _ } ->
        let* id = index_of_lf_term_constant identifier in
        let head = Synapx.LF.Const id in
        let spine = Synapx.LF.Nil in
        return (Synapx.LF.Root (location, head, spine))
    | Synext.CLF.Term.Application { location; applicand; arguments } -> (
        match applicand with
        | Synext.CLF.Term.Variable _
        | Synext.CLF.Term.Meta_variable _
        | Synext.CLF.Term.Parameter_variable _
        | Synext.CLF.Term.Constant _
        | Synext.CLF.Term.Substitution _
        | Synext.CLF.Term.Projection _
        | Synext.CLF.Term.Application _
        | Synext.CLF.Term.Hole { variant = `Underscore; _ } -> (
            let* applicand' = index_clf_term applicand in
            match applicand' with
            | Synapx.LF.Root (_applicand_location, id, spine1') ->
                let* spine2' = index_clf_spine arguments in
                let spine' = append_lf_spines spine1' spine2' in
                return (Synapx.LF.Root (location, id, spine'))
            | Synapx.LF.Lam _
            | Synapx.LF.LFHole _
            | Synapx.LF.Tuple _
            | Synapx.LF.Ann _ ->
                assert false
            (* Supported contextual LF term-level applicands are always
               translated to LF roots *))
        | Synext.CLF.Term.Hole { variant = `Labelled _ | `Unlabelled; _ }
        | Synext.CLF.Term.Type_annotated _
        | Synext.CLF.Term.Abstraction _
        | Synext.CLF.Term.Tuple _ ->
            Error.raise_at1
              (Synext.location_of_clf_term applicand)
              Unsupported_lf_term_applicand)
    | Synext.CLF.Term.Abstraction
        { location; parameter_identifier; parameter_type; body } -> (
        match parameter_type with
        | Option.None ->
            let* body' =
              (with_bound_omittable_lf_variable parameter_identifier)
                (index_clf_term body)
            in
            let* x = fresh_identifier_opt parameter_identifier in
            let x' = Name.make_from_identifier x in
            return (Synapx.LF.Lam (location, x', body'))
        | Option.Some _typ ->
            Error.raise_at1 location
              Unsupported_lf_annotated_term_abstraction)
    | Synext.CLF.Term.Hole { variant; location } -> (
        match variant with
        | `Underscore ->
            let head = Synapx.LF.Hole in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine))
        | `Unlabelled ->
            let label = Option.none in
            return (Synapx.LF.LFHole (location, label))
        | `Labelled label ->
            let label = Option.some (Identifier.name label) in
            return (Synapx.LF.LFHole (location, label)))
    | Synext.CLF.Term.Type_annotated { location; term; typ } ->
        let* term' = index_clf_term term in
        let* typ' = index_clf_typ typ in
        return (Synapx.LF.Ann (location, term', typ'))
    | Synext.CLF.Term.Parameter_variable { identifier; location } -> (
        index_of_parameter_variable_opt identifier >>= function
        | Option.Some offset ->
            let closure = Option.none in
            let head = Synapx.LF.PVar (Synapx.LF.Offset offset, closure) in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine))
        | Option.None ->
            let* () = add_free_parameter_variable identifier in
            let name = Name.make_from_identifier identifier in
            let closure = Option.none in
            let head = Synapx.LF.FPVar (name, closure) in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine)))
    | Synext.CLF.Term.Substitution { location; term; substitution } -> (
        let* term' = index_clf_term term in
        (* Only [term'] that is a root with an empty spine and whose head can
           have a substitution can have [substitution] attached to it. *)
        match term' with
        | Synapx.LF.Root (_, Synapx.LF.MVar (cv, Option.None), Synapx.LF.Nil)
          ->
            let* substitution' = index_clf_substitution substitution in
            let head' =
              Synapx.LF.MVar (cv, Option.some substitution')
              (* Attach substitution *)
            in
            return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root (_, Synapx.LF.PVar (cv, Option.None), Synapx.LF.Nil)
          ->
            let* substitution' = index_clf_substitution substitution in
            let head' =
              Synapx.LF.PVar (cv, Option.some substitution')
              (* Attach substitution *)
            in
            return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root (_, Synapx.LF.FMVar (cv, Option.None), Synapx.LF.Nil)
          ->
            let* substitution' = index_clf_substitution substitution in
            let head' =
              Synapx.LF.FMVar (cv, Option.some substitution')
              (* Attach substitution *)
            in
            return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root (_, Synapx.LF.FPVar (cv, Option.None), Synapx.LF.Nil)
          ->
            let* substitution' = index_clf_substitution substitution in
            let head' =
              Synapx.LF.FPVar (cv, Option.some substitution')
              (* Attach substitution *)
            in
            return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root _
        (* Matches roots with non-empty spines, or whose heads do not support
           attaching a substitution. *)
        | Synapx.LF.Lam _
        | Synapx.LF.LFHole _
        | Synapx.LF.Tuple _
        | Synapx.LF.Ann _ ->
            Error.raise_at1
              (Synext.location_of_clf_term term)
              Unsupported_clf_substitution_applicand)
    | Synext.CLF.Term.Projection { location; term; projection } -> (
        let* term' = index_clf_term term in
        match term' with
        | Synapx.LF.Root (_, head, Synapx.LF.Nil) -> (
            match projection with
            | `By_identifier identifier ->
                let name = Name.make_from_identifier identifier in
                let head' = Synapx.LF.Proj (head, Synapx.LF.ByName name) in
                return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
            | `By_position position ->
                let head' =
                  Synapx.LF.Proj (head, Synapx.LF.ByPos position)
                in
                return (Synapx.LF.Root (location, head', Synapx.LF.Nil)))
        | Synapx.LF.Root _
        | Synapx.LF.Lam _
        | Synapx.LF.LFHole _
        | Synapx.LF.Tuple _
        | Synapx.LF.Ann _ ->
            Error.raise_at1 location Unsupported_clf_projection_applicand)
    | Synext.CLF.Term.Tuple { location; terms } ->
        let* tuple = index_clf_tuple terms in
        return (Synapx.LF.Tuple (location, tuple))

  and index_clf_tuple terms =
    List1.fold_right
      (fun last ->
        let* last' = index_clf_term last in
        return (Synapx.LF.Last last'))
      (fun term tuple ->
        let* term' = index_clf_term term in
        let* tuple' = tuple in
        return (Synapx.LF.Cons (term', tuple')))
      terms

  and index_clf_spine spine =
    List1.fold_right
      (fun last ->
        let* last' = index_clf_term last in
        return (Synapx.LF.App (last', Synapx.LF.Nil)))
      (fun term spine ->
        let* term' = index_clf_term term in
        let* spine' = spine in
        return (Synapx.LF.App (term', spine')))
      spine

  and index_clf_term_pattern = function
    | Synext.CLF.Term.Pattern.Variable { location; identifier } ->
        let* offset = index_of_lf_variable identifier in
        let head = Synapx.LF.BVar offset in
        let spine = Synapx.LF.Nil in
        return (Synapx.LF.Root (location, head, spine))
    | Synext.CLF.Term.Pattern.Meta_variable { location; identifier } -> (
        index_of_meta_variable_opt identifier >>= function
        | Option.Some offset ->
            let head = Synapx.LF.BVar offset in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine))
        | Option.None ->
            let* () = add_free_meta_variable identifier in
            let name = Name.make_from_identifier identifier in
            let closure = Option.none in
            let head = Synapx.LF.FMVar (name, closure) in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine)))
    | Synext.CLF.Term.Pattern.Constant { location; identifier; _ } ->
        let* id = index_of_lf_term_constant identifier in
        let head = Synapx.LF.Const id in
        let spine = Synapx.LF.Nil in
        return (Synapx.LF.Root (location, head, spine))
    | Synext.CLF.Term.Pattern.Application { location; applicand; arguments }
      -> (
        match applicand with
        | Synext.CLF.Term.Pattern.Variable _
        | Synext.CLF.Term.Pattern.Meta_variable _
        | Synext.CLF.Term.Pattern.Parameter_variable _
        | Synext.CLF.Term.Pattern.Constant _
        | Synext.CLF.Term.Pattern.Substitution _
        | Synext.CLF.Term.Pattern.Projection _
        | Synext.CLF.Term.Pattern.Application _
        | Synext.CLF.Term.Pattern.Wildcard _ -> (
            let* applicand' = index_clf_term_pattern applicand in
            match applicand' with
            | Synapx.LF.Root (_applicand_location, id, spine1') ->
                let* spine2' = index_clf_spine_pattern arguments in
                let spine' = append_lf_spines spine1' spine2' in
                return (Synapx.LF.Root (location, id, spine'))
            | Synapx.LF.Lam _
            | Synapx.LF.LFHole _
            | Synapx.LF.Tuple _
            | Synapx.LF.Ann _ ->
                assert false
            (* Supported contextual LF term-level applicands are always
               translated to LF roots *))
        | Synext.CLF.Term.Pattern.Type_annotated _
        | Synext.CLF.Term.Pattern.Abstraction _
        | Synext.CLF.Term.Pattern.Tuple _ ->
            Error.raise_at1
              (Synext.location_of_clf_term_pattern applicand)
              Unsupported_lf_term_applicand)
    | Synext.CLF.Term.Pattern.Abstraction
        { location; parameter_identifier; parameter_type; body } -> (
        match parameter_type with
        | Option.None ->
            let* body' =
              (with_bound_omittable_lf_variable parameter_identifier)
                (index_clf_term_pattern body)
            in
            let* x = fresh_identifier_opt parameter_identifier in
            let x' = Name.make_from_identifier x in
            return (Synapx.LF.Lam (location, x', body'))
        | Option.Some _typ ->
            Error.raise_at1 location
              Unsupported_lf_annotated_term_abstraction)
    | Synext.CLF.Term.Pattern.Wildcard { location } ->
        return (Synapx.LF.LFHole (location, Option.none))
    | Synext.CLF.Term.Pattern.Type_annotated { location; term; typ } ->
        let* term' = index_clf_term_pattern term in
        let* typ' = index_clf_typ typ in
        return (Synapx.LF.Ann (location, term', typ'))
    | Synext.CLF.Term.Pattern.Parameter_variable { identifier; location }
      -> (
        index_of_parameter_variable_opt identifier >>= function
        | Option.Some offset ->
            let closure = Option.none in
            let head = Synapx.LF.PVar (Synapx.LF.Offset offset, closure) in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine))
        | Option.None ->
            let* () = add_free_parameter_variable identifier in
            let name = Name.make_from_identifier identifier in
            let closure = Option.none in
            let head = Synapx.LF.FPVar (name, closure) in
            let spine = Synapx.LF.Nil in
            return (Synapx.LF.Root (location, head, spine)))
    | Synext.CLF.Term.Pattern.Substitution { location; term; substitution }
      -> (
        let* term' = index_clf_term_pattern term in
        (* Only [term'] that is a root with an empty spine and whose head can
           have a substitution can have [substitution] attached to it. *)
        match term' with
        | Synapx.LF.Root (_, Synapx.LF.MVar (cv, Option.None), Synapx.LF.Nil)
          ->
            let* substitution' = index_clf_substitution substitution in
            let head' =
              Synapx.LF.MVar (cv, Option.some substitution')
              (* Attach substitution *)
            in
            return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root (_, Synapx.LF.PVar (cv, Option.None), Synapx.LF.Nil)
          ->
            let* substitution' = index_clf_substitution substitution in
            let head' =
              Synapx.LF.PVar (cv, Option.some substitution')
              (* Attach substitution *)
            in
            return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root (_, Synapx.LF.FMVar (cv, Option.None), Synapx.LF.Nil)
          ->
            let* substitution' = index_clf_substitution substitution in
            let head' =
              Synapx.LF.FMVar (cv, Option.some substitution')
              (* Attach substitution *)
            in
            return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root (_, Synapx.LF.FPVar (cv, Option.None), Synapx.LF.Nil)
          ->
            let* substitution' = index_clf_substitution substitution in
            let head' =
              Synapx.LF.FPVar (cv, Option.some substitution')
              (* Attach substitution *)
            in
            return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root _
        (* Matches roots with non-empty spines, or whose heads do not support
           attaching a substitution. *)
        | Synapx.LF.Lam _
        | Synapx.LF.LFHole _
        | Synapx.LF.Tuple _
        | Synapx.LF.Ann _ ->
            Error.raise_at1
              (Synext.location_of_clf_term_pattern term)
              Unsupported_clf_substitution_applicand)
    | Synext.CLF.Term.Pattern.Projection { location; term; projection } -> (
        let* term' = index_clf_term_pattern term in
        match term' with
        | Synapx.LF.Root (_, head, Synapx.LF.Nil) -> (
            match projection with
            | `By_identifier identifier ->
                let name = Name.make_from_identifier identifier in
                let head' = Synapx.LF.Proj (head, Synapx.LF.ByName name) in
                return (Synapx.LF.Root (location, head', Synapx.LF.Nil))
            | `By_position position ->
                let head' =
                  Synapx.LF.Proj (head, Synapx.LF.ByPos position)
                in
                return (Synapx.LF.Root (location, head', Synapx.LF.Nil)))
        | Synapx.LF.Root _
        | Synapx.LF.Lam _
        | Synapx.LF.LFHole _
        | Synapx.LF.Tuple _
        | Synapx.LF.Ann _ ->
            Error.raise_at1 location Unsupported_clf_projection_applicand)
    | Synext.CLF.Term.Pattern.Tuple { location; terms } ->
        let* tuple = index_clf_tuple_pattern terms in
        return (Synapx.LF.Tuple (location, tuple))

  and index_clf_tuple_pattern terms =
    List1.fold_right
      (fun last ->
        let* last' = index_clf_term_pattern last in
        return (Synapx.LF.Last last'))
      (fun term tuple ->
        let* term' = index_clf_term_pattern term in
        let* tuple' = tuple in
        return (Synapx.LF.Cons (term', tuple')))
      terms

  and index_clf_spine_pattern spine =
    List1.fold_right
      (fun last ->
        let* last' = index_clf_term_pattern last in
        return (Synapx.LF.App (last', Synapx.LF.Nil)))
      (fun term spine ->
        let* term' = index_clf_term_pattern term in
        let* spine' = spine in
        return (Synapx.LF.App (term', spine')))
      spine

  and index_clf_substitution =
    (* Not all values [h] of type {!type:Synapx.LF.head} are mapped to
       [Synapx.LF.Head h] when the spine is [Synapx.LF.Nil] because only
       those terms are in the pattern substitution.

       This function was introduced in commit 95578f0e ("Improved parsing of
       substitutions", 2015-05-25). *)
    let to_head_or_obj = function
      | Synapx.LF.Root (_, (Synapx.LF.BVar _ as h), Synapx.LF.Nil)
      | Synapx.LF.Root (_, (Synapx.LF.PVar _ as h), Synapx.LF.Nil)
      | Synapx.LF.Root (_, (Synapx.LF.Proj _ as h), Synapx.LF.Nil) ->
          Synapx.LF.Head h
      | tM -> Synapx.LF.Obj tM
    in
    let rec index_clf_substitution' head terms =
      match (head, terms) with
      | start, h :: s ->
          let* s' = index_clf_substitution' start s in
          let* h' = index_clf_term h in
          let h'' = to_head_or_obj h' in
          return (Synapx.LF.Dot (h'', s'))
      | Synext.CLF.Substitution.Head.None _, [] -> return Synapx.LF.EmptySub
      | Synext.CLF.Substitution.Head.Identity _, [] -> return Synapx.LF.Id
      | ( Synext.CLF.Substitution.Head.Substitution_variable
            { identifier; closure; _ }
        , [] ) -> (
          index_of_substitution_variable_opt identifier >>= function
          | Option.Some offset ->
              let* closure' =
                traverse_option index_clf_substitution closure
              in
              return (Synapx.LF.SVar (Synapx.LF.Offset offset, closure'))
          | Option.None ->
              let* () = add_free_substitution_variable identifier in
              let name = Name.make_from_identifier identifier in
              let* closure' =
                traverse_option index_clf_substitution closure
              in
              return (Synapx.LF.FSVar (name, closure')))
    in
    fun substitution ->
      let { Synext.CLF.Substitution.head; terms; _ } = substitution in
      index_clf_substitution' head terms

  and index_clf_substitution_pattern =
    (* Not all values [h] of type {!type:Synapx.LF.head} are mapped to
       [Synapx.LF.Head h] when the spine is [Synapx.LF.Nil] because only
       those terms are in the pattern substitution.

       This function was introduced in commit 95578f0e ("Improved parsing of
       substitutions", 2015-05-25). *)
    let to_head_or_obj = function
      | Synapx.LF.Root (_, (Synapx.LF.BVar _ as h), Synapx.LF.Nil)
      | Synapx.LF.Root (_, (Synapx.LF.PVar _ as h), Synapx.LF.Nil)
      | Synapx.LF.Root (_, (Synapx.LF.Proj _ as h), Synapx.LF.Nil) ->
          Synapx.LF.Head h
      | tM -> Synapx.LF.Obj tM
    in
    let rec index_clf_substitution' head terms =
      match (head, terms) with
      | start, h :: s ->
          let* s' = index_clf_substitution' start s in
          let* h' = index_clf_term_pattern h in
          let h'' = to_head_or_obj h' in
          return (Synapx.LF.Dot (h'', s'))
      | Synext.CLF.Substitution.Pattern.Head.None _, [] ->
          return Synapx.LF.EmptySub
      | Synext.CLF.Substitution.Pattern.Head.Identity _, [] ->
          return Synapx.LF.Id
      | ( Synext.CLF.Substitution.Pattern.Head.Substitution_variable
            { identifier; closure; _ }
        , [] ) -> (
          index_of_substitution_variable_opt identifier >>= function
          | Option.Some offset ->
              let* closure' =
                traverse_option index_clf_substitution closure
              in
              return (Synapx.LF.SVar (Synapx.LF.Offset offset, closure'))
          | Option.None ->
              let* () = add_free_substitution_variable identifier in
              let name = Name.make_from_identifier identifier in
              let* closure' =
                traverse_option index_clf_substitution closure
              in
              return (Synapx.LF.FSVar (name, closure')))
    in
    fun substitution ->
      let { Synext.CLF.Substitution.Pattern.head; terms; _ } =
        substitution
      in
      index_clf_substitution' head terms

  and with_indexed_clf_context_bindings cPhi bindings f =
    match bindings with
    | [] -> f cPhi
    | x :: xs ->
        with_indexed_clf_context_binding x (fun y ->
            with_indexed_clf_context_bindings (Synapx.LF.DDec (cPhi, y)) xs f)

  and with_indexed_clf_context_binding (identifier, typ_opt) f =
    let name = Name.make_from_identifier identifier in
    match typ_opt with
    | Option.None ->
        with_bound_lf_variable identifier (f (Synapx.LF.TypDeclOpt name))
    | Option.Some typ ->
        let* typ' = index_clf_typ typ in
        with_bound_lf_variable identifier
          (f (Synapx.LF.TypDecl (name, typ')))

  and with_indexed_clf_context :
        'a. Synext.clf_context -> (Synapx.LF.dctx -> 'a t) -> 'a t =
   fun context f ->
    match context with
    | { Synext.CLF.Context.head = Synext.CLF.Context.Head.None _
      ; bindings
      ; _
      } ->
        with_indexed_clf_context_bindings Synapx.LF.Null bindings f
    | { Synext.CLF.Context.head = Synext.CLF.Context.Head.Hole _
      ; bindings
      ; _
      } ->
        with_indexed_clf_context_bindings Synapx.LF.CtxHole bindings f
    | { Synext.CLF.Context.head =
          Synext.CLF.Context.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } -> (
        index_of_context_variable_opt identifier >>= function
        | Option.None ->
            (* A free context variable *)
            let* () = add_free_context_variable identifier in
            let name = Name.make_from_identifier identifier in
            with_indexed_clf_context_bindings
              (Synapx.LF.CtxVar (Synapx.LF.CtxName name)) bindings f
        | Option.Some index ->
            (* A bound context variable *)
            with_indexed_clf_context_bindings
              (Synapx.LF.CtxVar (Synapx.LF.CtxOffset index)) bindings f)

  and index_clf_context context = with_indexed_clf_context context return

  and with_indexed_clf_context_pattern_bindings cPhi bindings f =
    match bindings with
    | [] -> f cPhi
    | x :: xs ->
        with_indexed_clf_context_pattern_binding x (fun y ->
            with_indexed_clf_context_pattern_bindings
              (Synapx.LF.DDec (cPhi, y))
              xs f)

  and with_indexed_clf_context_pattern_binding (identifier, typ) f =
    let name = Name.make_from_identifier identifier in
    let* typ' = index_clf_typ typ in
    with_bound_lf_variable identifier (f (Synapx.LF.TypDecl (name, typ')))

  and with_indexed_clf_context_pattern :
        'a. Synext.clf_context_pattern -> (Synapx.LF.dctx -> 'a t) -> 'a t =
   fun context f ->
    match context with
    | { Synext.CLF.Context.Pattern.head =
          Synext.CLF.Context.Pattern.Head.None _
      ; bindings
      ; _
      } ->
        with_indexed_clf_context_pattern_bindings Synapx.LF.Null bindings f
    | { Synext.CLF.Context.Pattern.head =
          Synext.CLF.Context.Pattern.Head.Hole _
      ; bindings
      ; _
      } ->
        with_indexed_clf_context_pattern_bindings Synapx.LF.CtxHole bindings
          f
    | { Synext.CLF.Context.Pattern.head =
          Synext.CLF.Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } -> (
        index_of_context_variable_opt identifier >>= function
        | Option.None ->
            (* A free context variable *)
            let* () = add_free_context_variable identifier in
            let name = Name.make_from_identifier identifier in
            with_indexed_clf_context_pattern_bindings
              (Synapx.LF.CtxVar (Synapx.LF.CtxName name)) bindings f
        | Option.Some index ->
            (* A bound context variable *)
            with_indexed_clf_context_pattern_bindings
              (Synapx.LF.CtxVar (Synapx.LF.CtxOffset index)) bindings f)

  and index_clf_context_pattern context =
    with_indexed_clf_context_pattern context return

  let rec index_meta_object = function
    | Synext.Meta.Object.Context { location; context } ->
        let* context' = index_clf_context context in
        return (location, Synapx.Comp.CObj context')
    | Synext.Meta.Object.Contextual_term { location; context; term } ->
        with_indexed_clf_context context (fun context' ->
            let* term' = index_clf_term term in
            (* TODO: The approximate syntax should have a [MObj of normal]
               constructor like in the internal syntax. See
               {!Reconstruct.elClObj}. *)
            return
              ( location
              , Synapx.Comp.ClObj
                  ( context'
                  , Synapx.LF.Dot (Synapx.LF.Obj term', Synapx.LF.EmptySub)
                  ) ))
    | Synext.Meta.Object.Plain_substitution { location; domain; range } ->
        with_indexed_clf_context domain (fun domain' ->
            let* range' = index_clf_substitution range in
            return (location, Synapx.Comp.ClObj (domain', range')))
    | Synext.Meta.Object.Renaming_substitution { location; domain; range } ->
        with_indexed_clf_context domain (fun domain' ->
            let* range' = index_clf_substitution range in
            return (location, Synapx.Comp.ClObj (domain', range')))

  and index_meta_type = function
    | Synext.Meta.Typ.Context_schema { schema; _ } ->
        let* index = index_of_schema_constant schema in
        return (Synapx.LF.CTyp index)
    | Synext.Meta.Typ.Contextual_typ { context; typ; _ } ->
        with_indexed_clf_context context (fun context' ->
            let* typ' = index_clf_typ typ in
            return (Synapx.LF.ClTyp (Synapx.LF.MTyp typ', context')))
    | Synext.Meta.Typ.Parameter_typ { context; typ; _ } ->
        with_indexed_clf_context context (fun context' ->
            let* typ' = index_clf_typ typ in
            return (Synapx.LF.ClTyp (Synapx.LF.PTyp typ', context')))
    | Synext.Meta.Typ.Plain_substitution_typ { domain; range; _ } ->
        with_indexed_clf_context domain (fun domain' ->
            with_indexed_clf_context range (fun range' ->
                return
                  (Synapx.LF.ClTyp
                     (Synapx.LF.STyp (Synapx.LF.Subst, range'), domain'))))
    | Synext.Meta.Typ.Renaming_substitution_typ { domain; range; _ } ->
        with_indexed_clf_context domain (fun domain' ->
            with_indexed_clf_context range (fun range' ->
                return
                  (Synapx.LF.ClTyp
                     (Synapx.LF.STyp (Synapx.LF.Ren, range'), domain'))))

  and with_indexed_lf_context_bindings_list1 cPhi (List1.T (x, xs)) f =
    with_indexed_lf_context_binding x (fun y ->
        with_indexed_lf_context_bindings_list (Synapx.LF.Dec (cPhi, y)) xs f)

  and with_indexed_lf_context_bindings_list cPhi bindings f =
    match bindings with
    | [] -> f cPhi
    | x :: xs ->
        with_indexed_lf_context_binding x (fun y ->
            with_indexed_lf_context_bindings_list
              (Synapx.LF.Dec (cPhi, y))
              xs f)

  and with_indexed_lf_context_binding (identifier, typ) f =
    let name = Name.make_from_identifier identifier in
    let* typ' = index_lf_typ typ in
    with_bound_lf_variable identifier (f (Synapx.LF.TypDecl (name, typ')))

  and with_indexed_schema_some_clause some f =
    match some with
    | Option.None -> f Synapx.LF.Empty
    | Option.Some some ->
        with_indexed_lf_context_bindings_list1 Synapx.LF.Empty some f

  and with_indexed_schema_block_clause_bindings_list1 bindings f =
    match bindings with
    | List1.T ((identifier, typ), []) ->
        let name = Name.make_from_identifier identifier in
        let* typ' = index_lf_typ typ in
        f (Synapx.LF.SigmaLast (Option.some name, typ'))
    | List1.T ((identifier, typ), x :: xs) ->
        let name = Name.make_from_identifier identifier in
        let* typ' = index_lf_typ typ in
        with_bound_lf_variable identifier
          (with_indexed_schema_block_clause_bindings_list1 (List1.from x xs)
             (fun tRec -> f (Synapx.LF.SigmaElem (name, typ', tRec))))

  and index_schema_block_clause = function
    | `Record bindings ->
        with_indexed_schema_block_clause_bindings_list1 bindings return
    | `Unnamed typ ->
        let* typ' = index_lf_typ typ in
        return (Synapx.LF.SigmaLast (Option.none, typ'))

  and index_schema = function
    | Synext.Meta.Schema.Alternation { schemas; _ } ->
        let* schemas' = traverse_list2 index_schema_element schemas in
        let schemas'' = List2.to_list schemas' in
        return (Synapx.LF.Schema schemas'')
    | (Synext.Meta.Schema.Constant _ | Synext.Meta.Schema.Element _) as
      element ->
        let* element' = index_schema_element element in
        return (Synapx.LF.Schema [ element' ])

  and schema_some_clause_identifiers = function
    | Option.None -> []
    | Option.Some bindings -> List1.to_list (List1.map Pair.fst bindings)

  and schema_block_clause_identifiers = function
    | `Record bindings -> List1.to_list (List1.map Pair.fst bindings)
    | `Unnamed _typ -> []

  and raise_duplicate_identifiers_exception f duplicates =
    match duplicates with
    | List1.T ((_identifier, duplicates), []) ->
        Error.raise_at
          (List2.to_list1 (List2.map Identifier.location duplicates))
          (f duplicates)
    | List1.T (x1, x2 :: xs) ->
        Error.raise_aggregate_exception
          (List2.map
             (fun (_identifier, duplicates) ->
               Error.located_exception
                 (List2.to_list1 (List2.map Identifier.location duplicates))
                 (f duplicates))
             (List2.from x1 x2 xs))

  and index_schema_element = function
    | Synext.Meta.Schema.Element { some; block; _ } -> (
        match
          Identifier.find_duplicates (schema_some_clause_identifiers some)
        with
        | Option.Some duplicates ->
            raise_duplicate_identifiers_exception
              (fun identifiers ->
                Duplicate_identifiers_in_schema_some_clause identifiers)
              duplicates
        | Option.None -> (
            match
              Identifier.find_duplicates
                (schema_block_clause_identifiers block)
            with
            | Option.Some duplicates ->
                raise_duplicate_identifiers_exception
                  (fun identifiers ->
                    Duplicate_identifiers_in_schema_block_clause identifiers)
                  duplicates
            | Option.None ->
                with_indexed_schema_some_clause some (fun some' ->
                    let* block' = index_schema_block_clause block in
                    return (Synapx.LF.SchElem (some', block')))))
    | Synext.Meta.Schema.Constant { location; _ }
    | Synext.Meta.Schema.Alternation { location; _ } ->
        Error.raise_at1 location Unsupported_context_schema_element

  and index_meta_pattern = function
    | Synext.Meta.Pattern.Context { location; context } ->
        let* context' = index_clf_context_pattern context in
        return (location, Synapx.Comp.CObj context')
    | Synext.Meta.Pattern.Contextual_term { location; context; term } ->
        with_indexed_clf_context_pattern context (fun context' ->
            let* term' = index_clf_term_pattern term in
            (* TODO: The approximate syntax should have a [MObj of normal]
               constructor like in the internal syntax. See
               {!Reconstruct.elClObj}. *)
            return
              ( location
              , Synapx.Comp.ClObj
                  ( context'
                  , Synapx.LF.Dot (Synapx.LF.Obj term', Synapx.LF.EmptySub)
                  ) ))
    | Synext.Meta.Pattern.Plain_substitution { location; domain; range } ->
        with_indexed_clf_context_pattern domain (fun domain' ->
            let* range' = index_clf_substitution_pattern range in
            return (location, Synapx.Comp.ClObj (domain', range')))
    | Synext.Meta.Pattern.Renaming_substitution { location; domain; range }
      ->
        with_indexed_clf_context_pattern domain (fun domain' ->
            let* range' = index_clf_substitution_pattern range in
            return (location, Synapx.Comp.ClObj (domain', range')))

  and with_indexed_meta_context_binding :
        'a.
           Identifier.t * Synext.meta_typ
        -> (Synapx.LF.ctyp_decl -> 'a t)
        -> 'a t =
   fun (identifier, typ) f ->
    let* typ' = index_meta_type typ in
    let name = Name.make_from_identifier identifier in
    let with_bound_declaration =
      match typ with
      | Synext.Meta.Typ.Context_schema _ ->
          with_bound_context_variable identifier
      | Synext.Meta.Typ.Contextual_typ _ ->
          with_bound_meta_variable identifier
      | Synext.Meta.Typ.Parameter_typ _ ->
          with_bound_parameter_variable identifier
      | Synext.Meta.Typ.Plain_substitution_typ _
      | Synext.Meta.Typ.Renaming_substitution_typ _ ->
          with_bound_substitution_variable identifier
    in
    with_bound_declaration
      (f (Synapx.LF.Decl (name, typ', Plicity.explicit)))

  and with_indexed_meta_context_bindings :
        'a.
           (Identifier.t * Synext.meta_typ) list
        -> (Synapx.LF.ctyp_decl List.t -> 'a t)
        -> 'a t =
   fun bindings f ->
    match bindings with
    | [] -> f []
    | x :: xs ->
        with_indexed_meta_context_binding x (fun y ->
            with_indexed_meta_context_bindings xs (fun ys -> f (y :: ys)))

  and with_indexed_meta_context :
        'a. Synext.meta_context -> (Synapx.LF.mctx -> 'a t) -> 'a t =
   fun { Synext.Meta.Context.bindings; _ } f ->
    with_indexed_meta_context_bindings bindings (fun bindings' ->
        f
          (List.fold_left
             (fun accumulator binding' ->
               Synapx.LF.Dec (accumulator, binding'))
             Synapx.LF.Empty bindings'))

  and with_indexed_meta_context_pattern_binding :
        'a.
           Identifier.t * Synext.meta_typ
        -> (Synapx.LF.ctyp_decl -> 'a t)
        -> 'a t =
   fun (identifier, typ) f ->
    let* typ' = index_meta_type typ in
    let* with_bound_declaration =
      match typ with
      | Synext.Meta.Typ.Context_schema _ ->
          let* () = add_free_context_variable identifier in
          return (with_bound_context_variable identifier)
      | Synext.Meta.Typ.Contextual_typ _ ->
          let* () = add_free_meta_variable identifier in
          return (with_bound_meta_variable identifier)
      | Synext.Meta.Typ.Parameter_typ _ ->
          let* () = add_free_parameter_variable identifier in
          return (with_bound_parameter_variable identifier)
      | Synext.Meta.Typ.Plain_substitution_typ _
      | Synext.Meta.Typ.Renaming_substitution_typ _ ->
          let* () = add_free_substitution_variable identifier in
          return (with_bound_substitution_variable identifier)
    in
    let name = Name.make_from_identifier identifier in
    with_bound_declaration
      (f (Synapx.LF.Decl (name, typ', Plicity.explicit)))

  and with_indexed_meta_context_pattern_bindings :
        'a.
           (Identifier.t * Synext.meta_typ) list
        -> (Synapx.LF.ctyp_decl List.t -> 'a t)
        -> 'a t =
   fun bindings f ->
    match bindings with
    | [] -> f []
    | x :: xs ->
        with_indexed_meta_context_pattern_binding x (fun y ->
            with_indexed_meta_context_pattern_bindings xs (fun ys ->
                f (y :: ys)))

  and with_indexed_meta_context_pattern :
        'a. Synext.meta_context -> (Synapx.LF.mctx -> 'a t) -> 'a t =
   fun { Synext.Meta.Context.bindings; _ } f ->
    with_indexed_meta_context_pattern_bindings bindings (fun bindings' ->
        f
          (List.fold_left
             (fun accumulator binding' ->
               Synapx.LF.Dec (accumulator, binding'))
             Synapx.LF.Empty bindings'))

  let rec index_comp_kind = function
    | Synext.Comp.Kind.Ctype { location } ->
        return (Synapx.Comp.Ctype location)
    | Synext.Comp.Kind.Arrow { location; domain; range } ->
        let* domain' = index_meta_type domain in
        let* range' =
          (with_bound_omittable_meta_variable Option.none domain)
            (index_comp_kind range)
        in
        let* x = fresh_identifier in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.Comp.PiKind
             ( location
             , Synapx.LF.Decl (x', domain', Plicity.explicit)
             , range' ))
    | Synext.Comp.Kind.Pi
        { location; parameter_identifier; plicity; parameter_type; body } ->
        let* parameter_type' = index_meta_type parameter_type in
        let* body' =
          (with_bound_omittable_meta_variable parameter_identifier
             parameter_type)
            (index_comp_kind body)
        in
        let* x = fresh_identifier_opt parameter_identifier in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.Comp.PiKind
             (location, Synapx.LF.Decl (x', parameter_type', plicity), body'))

  and index_comp_typ = function
    | Synext.Comp.Typ.Inductive_typ_constant { location; identifier; _ } ->
        let* index = index_of_inductive_comp_constant identifier in
        return (Synapx.Comp.TypBase (location, index, Synapx.Comp.MetaNil))
    | Synext.Comp.Typ.Stratified_typ_constant { location; identifier; _ } ->
        let* index = index_of_stratified_comp_constant identifier in
        return (Synapx.Comp.TypBase (location, index, Synapx.Comp.MetaNil))
    | Synext.Comp.Typ.Coinductive_typ_constant { location; identifier; _ } ->
        let* index = index_of_coinductive_comp_constant identifier in
        return (Synapx.Comp.TypCobase (location, index, Synapx.Comp.MetaNil))
    | Synext.Comp.Typ.Abbreviation_typ_constant { location; identifier; _ }
      ->
        let* index = index_of_abbreviation_comp_constant identifier in
        return (Synapx.Comp.TypDef (location, index, Synapx.Comp.MetaNil))
    | Synext.Comp.Typ.Pi
        { location; parameter_identifier; plicity; parameter_type; body } ->
        let* parameter_type' = index_meta_type parameter_type in
        let* body' =
          (with_bound_omittable_meta_variable parameter_identifier
             parameter_type)
            (index_comp_typ body)
        in
        let* x = fresh_identifier_opt parameter_identifier in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.Comp.TypPiBox
             (location, Synapx.LF.Decl (x', parameter_type', plicity), body'))
    | Synext.Comp.Typ.Arrow { location; domain; range; _ } ->
        let* domain' = index_comp_typ domain in
        let* range' = index_comp_typ range in
        return (Synapx.Comp.TypArr (location, domain', range'))
    | Synext.Comp.Typ.Cross { location; types } ->
        let* types' = traverse_list2 index_comp_typ types in
        return (Synapx.Comp.TypCross (location, types'))
    | Synext.Comp.Typ.Box { location; meta_type } ->
        let* meta_type' = index_meta_type meta_type in
        return (Synapx.Comp.TypBox (location, (location, meta_type')))
    | Synext.Comp.Typ.Application { location; applicand; arguments } -> (
        let* applicand' = index_comp_typ applicand in
        match applicand' with
        | Synapx.Comp.TypBase (_, a', spine1') ->
            let* spine2' = index_meta_spine arguments in
            let spine' = append_meta_spines spine1' spine2' in
            return (Synapx.Comp.TypBase (location, a', spine'))
        | Synapx.Comp.TypCobase (_, a', spine1') ->
            let* spine2' = index_meta_spine arguments in
            let spine' = append_meta_spines spine1' spine2' in
            return (Synapx.Comp.TypCobase (location, a', spine'))
        | Synapx.Comp.TypDef (_, a', spine1') ->
            let* spine2' = index_meta_spine arguments in
            let spine' = append_meta_spines spine1' spine2' in
            return (Synapx.Comp.TypDef (location, a', spine'))
        | Synapx.Comp.TypBox _
        | Synapx.Comp.TypArr _
        | Synapx.Comp.TypCross _
        | Synapx.Comp.TypPiBox _
        | Synapx.Comp.TypInd _ ->
            Error.raise_at1 location Unsupported_comp_typ_applicand)

  and index_comp_expression = function
    | Synext.Comp.Expression.Variable { location; identifier } ->
        let* index = index_of_comp_variable identifier in
        return (Synapx.Comp.Var (location, index))
    | Synext.Comp.Expression.Constructor { location; identifier } ->
        let* index = index_of_comp_constructor identifier in
        return (Synapx.Comp.DataConst (location, index))
    | Synext.Comp.Expression.Program { location; identifier } ->
        let* index = index_of_comp_program identifier in
        return (Synapx.Comp.Const (location, index))
    | Synext.Comp.Expression.Fn { parameters; body; _ } ->
        let rec aux parameters =
          match parameters with
          | [] -> index_comp_expression body
          | (parameter_location, parameter_opt) :: parameters ->
              let* body' =
                with_bound_omittable_comp_variable parameter_opt
                  (aux parameters)
              in
              let location =
                Location.join parameter_location
                  (Synapx.Comp.loc_of_exp body')
              in
              let* parameter = fresh_identifier_opt parameter_opt in
              let name = Name.make_from_identifier parameter in
              return (Synapx.Comp.Fn (location, name, body'))
        in
        aux (List1.to_list parameters)
    | Synext.Comp.Expression.Mlam { parameters; body; _ } ->
        let rec aux parameters =
          match parameters with
          | [] -> index_comp_expression body
          | (parameter_location, (parameter_opt, modifier)) :: parameters ->
              let* body' =
                match parameter_opt with
                | Option.None -> with_shifted_meta_context (aux parameters)
                | Option.Some parameter ->
                    (match modifier with
                    | `Plain -> with_bound_contextual_variable
                    | `Hash -> with_bound_parameter_variable
                    | `Dollar -> with_bound_substitution_variable)
                      parameter (aux parameters)
              in
              let location =
                Location.join parameter_location
                  (Synapx.Comp.loc_of_exp body')
              in
              let* parameter = fresh_identifier_opt parameter_opt in
              let name = Name.make_from_identifier parameter in
              return (Synapx.Comp.MLam (location, name, body'))
        in
        aux (List1.to_list parameters)
    | Synext.Comp.Expression.Fun { location; branches } ->
        let* branches' = traverse_list1 index_cofunction_branch branches in
        let branches_location =
          Location.join_all1_contramap
            (fun { Synext.Comp.Cofunction_branch.location; _ } -> location)
            branches
        in
        let branches'' =
          List.fold_right
            (fun (location, pattern_spine, body) accumulator ->
              Synapx.Comp.ConsFBranch
                (location, (pattern_spine, body), accumulator))
            (List1.to_list branches')
            (Synapx.Comp.NilFBranch branches_location)
        in
        return (Synapx.Comp.Fun (location, branches''))
    | Synext.Comp.Expression.Let
        { location; meta_context; pattern; scrutinee; body } -> (
        let* scrutinee' = index_comp_expression scrutinee in
        let* meta_context', pattern', body' =
          with_free_variables_as_pattern_variables
            ~pattern:
              (with_indexed_meta_context_pattern meta_context
                 (fun meta_context' ->
                   let* pattern' = index_comp_pattern pattern in
                   return (meta_context', pattern')))
            ~expression:(fun (meta_context', pattern') ->
              let* pattern'' = reindex_pattern pattern' in
              let* body' = index_comp_expression body in
              return (meta_context', pattern'', body'))
        in
        (* The approximate syntax does not support general patterns in
           [let]-expressions, so only [let]-expressions with a variable
           pattern are translated to [let]-expressions in the approximate
           syntax. *)
        match (meta_context', pattern') with
        | Synapx.LF.Empty, Synapx.Comp.PatFVar (_location, name) ->
            (* TODO: General [let] pattern expressions would render this case
               obsolete *)
            return (Synapx.Comp.Let (location, scrutinee', (name, body')))
        | Synapx.LF.Empty, Synapx.Comp.PatVar (_location, name, _offset) ->
            (* TODO: General [let] pattern expressions would render this case
               obsolete *)
            return (Synapx.Comp.Let (location, scrutinee', (name, body')))
        | Synapx.LF.Empty, Synapx.Comp.PatTuple (_location, patterns') -> (
            (* TODO: [LetTuple] expressions should be deprecated in favour of
               general [let] pattern expressions *)
            (* [LetTuple] expressions only support variable patterns *)
            match
              List2.traverse
                (function
                  | Synapx.Comp.PatFVar (_location, name) -> Option.some name
                  | Synapx.Comp.PatVar (_location, name, _offset) ->
                      Option.some name
                  | _ -> Option.none)
                patterns'
            with
            | Option.Some variables ->
                return
                  (Synapx.Comp.LetTuple
                     (location, scrutinee', (variables, body')))
            | Option.None ->
                return
                  (Synapx.Comp.Case
                     ( location
                     , Synapx.Comp.PragmaCase
                     , scrutinee'
                     , [ Synapx.Comp.Branch
                           (location, meta_context', pattern', body')
                       ] )))
        | _ ->
            (* TODO: General [let] pattern expressions should be supported *)
            (* The pattern is not a variable pattern, so the [let]-expression
               is translated to a [case]-expression. *)
            return
              (Synapx.Comp.Case
                 ( location
                 , Synapx.Comp.PragmaCase
                 , scrutinee'
                 , [ Synapx.Comp.Branch
                       (location, meta_context', pattern', body')
                   ] )))
    | Synext.Comp.Expression.Box { location; meta_object } ->
        let* meta_object' = index_meta_object meta_object in
        return (Synapx.Comp.Box (location, meta_object'))
    | Synext.Comp.Expression.Impossible { location; scrutinee } ->
        let* scrutinee' = index_comp_expression scrutinee in
        return (Synapx.Comp.Impossible (location, scrutinee'))
    | Synext.Comp.Expression.Case
        { location; scrutinee; check_coverage; branches } ->
        let* scrutinee' = index_comp_expression scrutinee in
        let* branches = traverse_list1 index_case_branch branches in
        let case_pragma =
          if check_coverage then Synapx.Comp.PragmaCase
          else Synapx.Comp.PragmaNotCase
        in
        return
          (Synapx.Comp.Case
             (location, case_pragma, scrutinee', List1.to_list branches))
    | Synext.Comp.Expression.Tuple { location; elements } ->
        let* elements' = traverse_list2 index_comp_expression elements in
        return (Synapx.Comp.Tuple (location, elements'))
    | Synext.Comp.Expression.Hole { location; label } ->
        let name = Option.map Identifier.name label in
        return (Synapx.Comp.Hole (location, name))
    | Synext.Comp.Expression.Box_hole { location } ->
        return (Synapx.Comp.BoxHole location)
    | Synext.Comp.Expression.Application { applicand; arguments; _ } ->
        let* applicand' = index_comp_expression applicand in
        let* arguments' = traverse_list1 index_comp_expression arguments in
        let application' =
          List.fold_left
            (fun applicand' argument' ->
              let location =
                Location.join
                  (Synapx.Comp.loc_of_exp applicand')
                  (Synapx.Comp.loc_of_exp argument')
              in
              Synapx.Comp.Apply (location, applicand', argument'))
            applicand'
            (List1.to_list arguments')
        in
        return application'
    | Synext.Comp.Expression.Observation { location; scrutinee; destructor }
      ->
        let* scrutinee' = index_comp_expression scrutinee in
        let* id = index_of_comp_destructor destructor in
        return (Synapx.Comp.Obs (location, scrutinee', id))
    | Synext.Comp.Expression.Type_annotated { location; expression; typ } ->
        let* expression' = index_comp_expression expression in
        let* typ' = index_comp_typ typ in
        return (Synapx.Comp.Ann (location, expression', typ'))

  and index_meta_spine arguments =
    List1.fold_right
      (fun argument ->
        let* argument' = index_meta_object argument in
        return (Synapx.Comp.MetaApp (argument', Synapx.Comp.MetaNil)))
      (fun argument spine ->
        let* argument' = index_meta_object argument in
        let* spine' = spine in
        return (Synapx.Comp.MetaApp (argument', spine')))
      arguments

  and reindex_pattern = function
    | Synapx.Comp.PatFVar (location, name) ->
        let identifier =
          Identifier.make ~location:(Name.location name) (Name.show name)
        in
        let* offset = index_of_comp_variable identifier in
        return (Synapx.Comp.PatVar (location, name, offset))
    | Synapx.Comp.PatTuple (location, patterns) ->
        let* patterns' = traverse_list2 reindex_pattern patterns in
        return (Synapx.Comp.PatTuple (location, patterns'))
    | Synapx.Comp.PatConst (location, constant, pat_spine) ->
        let* pattern_spine' = reindex_pattern_spine pat_spine in
        return (Synapx.Comp.PatConst (location, constant, pattern_spine'))
    | Synapx.Comp.PatAnn (location, pattern, typ) ->
        let* pattern' = reindex_pattern pattern in
        return (Synapx.Comp.PatAnn (location, pattern', typ))
    | (Synapx.Comp.PatVar _ | Synapx.Comp.PatMetaObj _) as pattern ->
        return pattern

  and reindex_pattern_spine = function
    | Synapx.Comp.PatNil location -> return (Synapx.Comp.PatNil location)
    | Synapx.Comp.PatApp (location, pattern, pat_spine) ->
        let* pattern' = reindex_pattern pattern in
        let* pattern_spine' = reindex_pattern_spine pat_spine in
        return (Synapx.Comp.PatApp (location, pattern', pattern_spine'))
    | Synapx.Comp.PatObs (location, destructor_id, pat_spine) ->
        let* pattern_spine' = reindex_pattern_spine pat_spine in
        return (Synapx.Comp.PatObs (location, destructor_id, pattern_spine'))

  and index_comp_pattern = function
    | Synext.Comp.Pattern.Variable { location; identifier } ->
        let* () = add_computation_pattern_variable identifier in
        let x' = Name.make_from_identifier identifier in
        return (Synapx.Comp.PatFVar (location, x'))
    | Synext.Comp.Pattern.Wildcard { location } ->
        let* x = fresh_identifier in
        let* () = add_computation_pattern_variable x in
        let x' = Name.make_from_identifier x in
        return (Synapx.Comp.PatFVar (location, x'))
    | Synext.Comp.Pattern.Constructor { location; identifier; _ } ->
        let* id = index_of_comp_constructor identifier in
        let spine = Synapx.Comp.PatNil location in
        return (Synapx.Comp.PatConst (location, id, spine))
    | Synext.Comp.Pattern.Meta_object { location; meta_pattern } ->
        let* meta_pattern' = index_meta_pattern meta_pattern in
        return (Synapx.Comp.PatMetaObj (location, meta_pattern'))
    | Synext.Comp.Pattern.Tuple { location; elements } ->
        let* elements' = traverse_list2 index_comp_pattern elements in
        return (Synapx.Comp.PatTuple (location, elements'))
    | Synext.Comp.Pattern.Type_annotated { location; pattern; typ } ->
        let* pattern' = index_comp_pattern pattern in
        let* typ' = index_comp_typ typ in
        return (Synapx.Comp.PatAnn (location, pattern', typ'))
    | Synext.Comp.Pattern.Application { applicand; arguments; _ } -> (
        index_comp_pattern applicand >>= function
        | Synapx.Comp.PatConst (applicand_location, id, Synapx.Comp.PatNil _)
          ->
            let* spine' = index_applicative_comp_pattern_spine arguments in
            return (Synapx.Comp.PatConst (applicand_location, id, spine'))
        | _ ->
            Error.raise_at1
              (Synext.location_of_comp_pattern applicand)
              Unsupported_comp_pattern_applicand)

  and index_applicative_comp_pattern_spine patterns =
    List1.fold_right
      (fun pattern ->
        let* pattern' = index_comp_pattern pattern in
        let location = Synext.location_of_comp_pattern pattern in
        return
          (Synapx.Comp.PatApp
             ( location
             , pattern'
             , Synapx.Comp.PatNil
                 (Location.join_all1_contramap
                    Synext.location_of_comp_pattern patterns) )))
      (fun pattern spine ->
        let* pattern' = index_comp_pattern pattern in
        let* spine' = spine in
        let location = Synext.location_of_comp_pattern pattern in
        return (Synapx.Comp.PatApp (location, pattern', spine')))
      patterns

  and index_case_branch
      { Synext.Comp.Case_branch.location; meta_context; pattern; body } =
    let* meta_context', pattern', body' =
      with_free_variables_as_pattern_variables
        ~pattern:
          (with_indexed_meta_context_pattern meta_context
             (fun meta_context' ->
               let* pattern' = index_comp_pattern pattern in
               return (meta_context', pattern')))
        ~expression:(fun (meta_context', pattern') ->
          let* pattern'' = reindex_pattern pattern' in
          let* body' = index_comp_expression body in
          return (meta_context', pattern'', body'))
    in
    return (Synapx.Comp.Branch (location, meta_context', pattern', body'))

  and index_comp_pattern_with_location pattern =
    let location = Synext.location_of_comp_pattern pattern in
    let* pattern' = index_comp_pattern pattern in
    return (location, pattern')

  and index_comp_copattern
      { Synext.Comp.Copattern.location; patterns; observations } =
    let* patterns' =
      traverse_list index_comp_pattern_with_location patterns
    in
    let* observations' =
      traverse_list
        (fun (destructor, patterns) ->
          let location = Qualified_identifier.location destructor in
          let* index = index_of_comp_destructor destructor in
          let* patterns' =
            traverse_list index_comp_pattern_with_location patterns
          in
          return (location, index, patterns'))
        observations
    in
    let add_patterns' =
      List.fold_right (fun (pattern_location, pattern) accumulator ->
          Synapx.Comp.PatApp (pattern_location, pattern, accumulator))
    in
    let add_observations' =
      List.fold_right (fun (location, destructor, patterns) accumulator ->
          Synapx.Comp.PatObs
            (location, destructor, add_patterns' patterns accumulator))
    in
    return
      (add_patterns' patterns'
         (add_observations' observations' (Synapx.Comp.PatNil location)))

  and index_cofunction_branch
      { Synext.Comp.Cofunction_branch.location
      ; meta_context
      ; copattern
      ; body
      } =
    match meta_context.Synext.Meta.Context.bindings with
    | [] ->
        let* pattern_spine', body' =
          with_free_variables_as_pattern_variables
            ~pattern:(index_comp_copattern copattern)
            ~expression:(fun copattern' ->
              let* copattern'' = reindex_pattern_spine copattern' in
              let* body' = index_comp_expression body in
              return (copattern'', body'))
        in
        return (location, pattern_spine', body')
    | _ -> Error.raise_at1 location Unsupported_copattern_meta_context

  and with_indexed_comp_context_binding :
        'a.
           Identifier.t * Synext.comp_typ
        -> (Synapx.Comp.ctyp_decl -> 'a t)
        -> 'a t =
   fun (identifier, typ) f ->
    let name = Name.make_from_identifier identifier in
    let* typ' = index_comp_typ typ in
    with_bound_comp_variable identifier
      (f (Synapx.Comp.CTypDecl (name, typ')))

  and with_indexed_comp_context_bindings :
        'a.
           (Identifier.t * Synext.comp_typ) List.t
        -> (Synapx.Comp.ctyp_decl List.t -> 'a t)
        -> 'a t =
   fun bindings f ->
    match bindings with
    | [] -> f []
    | x :: xs ->
        with_indexed_comp_context_binding x (fun y ->
            with_indexed_comp_context_bindings xs (fun ys -> f (y :: ys)))

  and with_indexed_comp_context :
        'a. Synext.comp_context -> (Synapx.Comp.gctx -> 'a t) -> 'a t =
   fun { Synext.Comp.Context.bindings; _ } f ->
    with_indexed_comp_context_bindings bindings (fun bindings' ->
        f
          (List.fold_left
             (fun accumulator binding' ->
               Synapx.LF.Dec (accumulator, binding'))
             Synapx.LF.Empty bindings'))

  let rec index_harpoon_proof = function
    | Synext.Harpoon.Proof.Incomplete { location; label } ->
        let name = Option.map Identifier.name label in
        return (Synapx.Comp.Incomplete (location, name))
    | Synext.Harpoon.Proof.Command { location; command; body } ->
        with_indexed_harpoon_command command (fun command' ->
            let* body' = index_harpoon_proof body in
            return (Synapx.Comp.Command (location, command', body')))
    | Synext.Harpoon.Proof.Directive { location; directive } ->
        let* directive = index_harpoon_directive directive in
        return (Synapx.Comp.Directive (location, directive))

  and with_indexed_harpoon_command :
        'a. Synext.harpoon_command -> (Synapx.Comp.command -> 'a t) -> 'a t =
   fun command f ->
    match command with
    | Synext.Harpoon.Command.By { location; expression; assignee } ->
        let* expression' = index_comp_expression expression in
        let x = Name.make_from_identifier assignee in
        with_bound_comp_variable assignee
          (f (Synapx.Comp.By (location, expression', x)))
    | Synext.Harpoon.Command.Unbox
        { location; expression; assignee; modifier } ->
        let* expression' = index_comp_expression expression in
        let x = Name.make_from_identifier assignee in
        with_bound_contextual_variable assignee
          (f (Synapx.Comp.Unbox (location, expression', x, modifier)))

  and index_harpoon_directive = function
    | Synext.Harpoon.Directive.Intros { location; hypothetical } ->
        let* hypothetical' = index_harpoon_hypothetical hypothetical in
        return (Synapx.Comp.Intros (location, hypothetical'))
    | Synext.Harpoon.Directive.Solve { location; solution } ->
        let* solution' = index_comp_expression solution in
        return (Synapx.Comp.Solve (location, solution'))
    | Synext.Harpoon.Directive.Split { location; scrutinee; branches } ->
        let* scrutinee' = index_comp_expression scrutinee in
        let* branches' =
          traverse_list1 index_harpoon_split_branch branches
        in
        return
          (Synapx.Comp.Split (location, scrutinee', List1.to_list branches'))
    | Synext.Harpoon.Directive.Impossible { location; scrutinee } ->
        let* scrutinee' = index_comp_expression scrutinee in
        (* TODO: The approximate syntax should have an [Impossible _]
           constructor *)
        return (Synapx.Comp.Split (location, scrutinee', []))
    | Synext.Harpoon.Directive.Suffices { location; scrutinee; branches } ->
        let* scrutinee' = index_comp_expression scrutinee in
        let* branches' =
          traverse_list index_harpoon_suffices_branch branches
        in
        return (Synapx.Comp.Suffices (location, scrutinee', branches'))

  and index_harpoon_split_branch
      { Synext.Harpoon.Split_branch.location; label; body } =
    let* label' = index_harpoon_split_branch_label label in
    let* body' = index_harpoon_hypothetical body in
    return
      { Synapx.Comp.case_label = label'
      ; branch_body = body'
      ; split_branch_loc = location
      }

  and index_harpoon_split_branch_label = function
    | Synext.Harpoon.Split_branch.Label.Lf_constant { location; identifier }
      ->
        let* _cid = index_of_lf_term_constant identifier in
        let name = Name.make_from_qualified_identifier identifier in
        (* TODO: The approximate syntax should have an [Lf_constant _]
           constructor *)
        return (Synapx.Comp.NamedCase (location, name))
    | Synext.Harpoon.Split_branch.Label.Comp_constant
        { location; identifier } ->
        let* _cid = index_of_comp_constructor identifier in
        let name = Name.make_from_qualified_identifier identifier in
        (* TODO: The approximate syntax should have a [Comp_constant _]
           constructor *)
        return (Synapx.Comp.NamedCase (location, name))
    | Synext.Harpoon.Split_branch.Label.Bound_variable { location } ->
        return (Synapx.Comp.BVarCase location)
    | Synext.Harpoon.Split_branch.Label.Empty_context { location } ->
        return (Synapx.Comp.ContextCase (Synapx.Comp.EmptyContext location))
    | Synext.Harpoon.Split_branch.Label.Extended_context
        { location; schema_element } ->
        return
          (Synapx.Comp.ContextCase
             (Synapx.Comp.ExtendedBy (location, schema_element)))
    | Synext.Harpoon.Split_branch.Label.Parameter_variable
        { location; schema_element; projection } ->
        return (Synapx.Comp.PVarCase (location, schema_element, projection))

  and index_harpoon_suffices_branch
      { Synext.Harpoon.Suffices_branch.location; goal; proof } =
    let* goal' = disallow_free_variables (index_comp_typ goal) in
    let* proof' = index_harpoon_proof proof in
    return (location, goal', proof')

  and index_harpoon_hypothetical = function
    | { Synext.Harpoon.Hypothetical.location
      ; meta_context
      ; comp_context
      ; proof
      } ->
        with_parent_scope
          (with_indexed_meta_context meta_context (fun meta_context' ->
               with_indexed_comp_context comp_context (fun comp_context' ->
                   let* proof' = index_harpoon_proof proof in
                   return
                     Synapx.Comp.
                       { hypotheses =
                           { cD = meta_context'; cG = comp_context' }
                       ; proof = proof'
                       ; hypothetical_loc = location
                       })))

  let index_open_lf_kind kind = allow_free_variables (index_lf_kind kind)

  let index_closed_lf_kind kind =
    disallow_free_variables (index_lf_kind kind)

  let index_open_lf_typ typ = allow_free_variables (index_lf_typ typ)

  let index_closed_lf_typ typ = disallow_free_variables (index_lf_typ typ)

  let index_open_comp_kind kind = allow_free_variables (index_comp_kind kind)

  let index_closed_comp_kind kind =
    disallow_free_variables (index_comp_kind kind)

  let index_open_comp_typ typ = allow_free_variables (index_comp_typ typ)

  let index_closed_comp_typ typ =
    disallow_free_variables (index_comp_typ typ)

  let index_comp_expression expression =
    disallow_free_variables (index_comp_expression expression)

  let index_schema schema = allow_free_variables (index_schema schema)

  let index_comp_theorem theorem =
    disallow_free_variables
      ( index_comp_expression theorem $> fun theorem' ->
        Synapx.Comp.Program theorem' )

  let index_harpoon_proof proof =
    disallow_free_variables
      (index_harpoon_proof proof $> fun proof' -> Synapx.Comp.Proof proof')

  let index_computation_typ_abbreviation typ kind =
    let* kind' = disallow_free_variables (index_comp_kind kind) in
    let rec with_unrolled_kind kind f =
      match kind with
      | Synext.Comp.Kind.Pi { parameter_identifier; parameter_type; body; _ }
        ->
          with_meta_level_binding_opt parameter_identifier parameter_type
            (with_unrolled_kind body f)
      | Synext.Comp.Kind.Arrow { range; _ } -> with_unrolled_kind range f
      | Synext.Comp.Kind.Ctype _ -> f
    in
    let* typ' =
      disallow_free_variables (with_unrolled_kind kind (index_comp_typ typ))
    in
    return (typ', kind')

  let index_lf_query meta_context typ =
    allow_free_variables
      (with_indexed_meta_context meta_context (fun meta_context' ->
           let* typ' = index_clf_typ typ in
           return (meta_context', typ')))
end

module Indexer = struct
  include Index_state.Persistent_indexing_state
  include Make_indexer (Index_state.Persistent_indexing_state)
end
