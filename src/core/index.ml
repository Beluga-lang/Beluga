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
  include Imperative_state.IMPERATIVE_STATE

  val index_open_lf_kind : state -> Synext.lf_kind -> Synapx.LF.kind

  val index_closed_lf_kind : state -> Synext.lf_kind -> Synapx.LF.kind

  val index_open_lf_typ : state -> Synext.lf_typ -> Synapx.LF.typ

  val index_closed_lf_typ : state -> Synext.lf_typ -> Synapx.LF.typ

  val index_open_comp_kind : state -> Synext.comp_kind -> Synapx.Comp.kind

  val index_closed_comp_kind : state -> Synext.comp_kind -> Synapx.Comp.kind

  val index_open_comp_typ : state -> Synext.comp_typ -> Synapx.Comp.typ

  val index_closed_comp_typ : state -> Synext.comp_typ -> Synapx.Comp.typ

  val index_comp_expression :
    state -> Synext.comp_expression -> Synapx.Comp.exp

  val index_schema : state -> Synext.schema -> Synapx.LF.schema

  val index_comp_theorem : state -> Synext.comp_expression -> Synapx.Comp.thm

  val index_harpoon_proof : state -> Synext.harpoon_proof -> Synapx.Comp.thm

  val index_computation_typ_abbreviation :
       state
    -> Synext.comp_typ
    -> Synext.comp_kind
    -> Synapx.Comp.typ * Synapx.Comp.kind
end

module Make_indexer (Indexing_state : Index_state.INDEXING_STATE) = struct
  include Indexing_state

  let with_bound_omittable_lf_variable state identifier_opt f =
    match identifier_opt with
    | Option.None -> with_shifted_lf_context state f
    | Option.Some identifier -> with_bound_lf_variable state identifier f

  let[@warning "-32"] with_bound_omittable_meta_variable state identifier_opt
      =
    match identifier_opt with
    | Option.None -> with_shifted_meta_context state
    | Option.Some identifier -> with_bound_meta_variable state identifier

  let with_bound_omittable_comp_variable state identifier_opt =
    match identifier_opt with
    | Option.None -> with_shifted_comp_context state
    | Option.Some identifier -> with_bound_comp_variable state identifier

  let with_bound_meta_variable' state identifier typ =
    match typ with
    | Synext.Meta.Typ.Context_schema _ ->
        with_bound_context_variable state identifier
    | Synext.Meta.Typ.Contextual_typ _ ->
        with_bound_meta_variable state identifier
    | Synext.Meta.Typ.Parameter_typ _ ->
        with_bound_parameter_variable state identifier
    | Synext.Meta.Typ.Plain_substitution_typ _
    | Synext.Meta.Typ.Renaming_substitution_typ _ ->
        with_bound_substitution_variable state identifier

  let with_meta_level_binding_opt state identifier_opt typ =
    match identifier_opt with
    | Option.None -> with_shifted_meta_context state
    | Option.Some identifier ->
        with_bound_meta_variable' state identifier typ

  let with_bound_omittable_meta_variable state identifier_opt typ =
    match identifier_opt with
    | Option.None -> with_shifted_meta_context state
    | Option.Some identifier ->
        with_bound_meta_variable' state identifier typ

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

  (* Not all values [h] of type {!type:Synapx.LF.head} are mapped to
     [Synapx.LF.Head h] when the spine is [Synapx.LF.Nil] because only those
     terms are in the pattern substitution.

     This function was introduced in commit 95578f0e ("Improved parsing of
     substitutions", 2015-05-25). *)
  let to_head_or_obj = function
    | Synapx.LF.Root (_, (Synapx.LF.BVar _ as h), Synapx.LF.Nil)
    | Synapx.LF.Root (_, (Synapx.LF.PVar _ as h), Synapx.LF.Nil)
    | Synapx.LF.Root (_, (Synapx.LF.Proj _ as h), Synapx.LF.Nil) ->
        Synapx.LF.Head h
    | tM -> Synapx.LF.Obj tM

  let rec index_lf_kind state = function
    | Synext.LF.Kind.Typ _ -> Synapx.LF.Typ
    | Synext.LF.Kind.Arrow { domain; range; location = _ } ->
        let domain' = index_lf_typ state domain in
        let range' =
          with_shifted_lf_context state (fun state ->
              index_lf_kind state range)
        in
        let x = fresh_identifier state in
        let x' = Name.make_from_identifier x in
        Synapx.LF.PiKind
          ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range')
    | Synext.LF.Kind.Pi
        { parameter_identifier; parameter_type; plicity; body; location }
      -> (
        match parameter_type with
        | Option.None ->
            Error.raise_at1 location Unsupported_lf_untyped_pi_kind_parameter
        | Option.Some parameter_type ->
            let domain' = index_lf_typ state parameter_type in
            let range' =
              with_bound_omittable_lf_variable state parameter_identifier
                (fun state -> index_lf_kind state body)
            in
            let x = fresh_identifier_opt state parameter_identifier in
            let x' = Name.make_from_identifier x in
            Synapx.LF.PiKind
              ((Synapx.LF.TypDecl (x', domain'), plicity), range'))

  and index_lf_typ state = function
    | Synext.LF.Typ.Constant { identifier; location } ->
        let id = index_of_lf_type_constant state identifier in
        Synapx.LF.Atom (location, id, Synapx.LF.Nil)
    | Synext.LF.Typ.Application { applicand; arguments; location } -> (
        match applicand with
        | Synext.LF.Typ.Constant _
        | Synext.LF.Typ.Application _ -> (
            let applicand' = index_lf_typ state applicand in
            match applicand' with
            | Synapx.LF.Atom (_applicand_location, id, spine1') ->
                let spine2' = index_lf_spine state arguments in
                let spine' = append_lf_spines spine1' spine2' in
                Synapx.LF.Atom (location, id, spine')
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
    | Synext.LF.Typ.Arrow { domain; range; location = _; orientation = _ } ->
        let domain' = index_lf_typ state domain in
        let range' =
          with_shifted_lf_context state (fun state ->
              index_lf_typ state range)
        in
        let x = fresh_identifier state in
        let x' = Name.make_from_identifier x in
        Synapx.LF.PiTyp
          ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range')
    | Synext.LF.Typ.Pi
        { parameter_identifier; parameter_type; plicity; body; location }
      -> (
        match parameter_type with
        | Option.None ->
            Error.raise_at1 location Unsupported_lf_untyped_pi_typ_parameter
        | Option.Some parameter_type ->
            let domain' = index_lf_typ state parameter_type in
            let range' =
              with_bound_omittable_lf_variable state parameter_identifier
                (fun state -> index_lf_typ state body)
            in
            let x = fresh_identifier_opt state parameter_identifier in
            let x' = Name.make_from_identifier x in
            Synapx.LF.PiTyp
              ((Synapx.LF.TypDecl (x', domain'), plicity), range'))

  and index_lf_term state = function
    | Synext.LF.Term.Variable { location; identifier } -> (
        match index_of_lf_variable_opt state identifier with
        | Option.Some offset ->
            let head = Synapx.LF.BVar offset in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine)
        | Option.None ->
            add_free_lf_variable state identifier;
            let name = Name.make_from_identifier identifier in
            let head = Synapx.LF.FVar name in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine))
    | Synext.LF.Term.Constant { location; identifier } ->
        let id = index_of_lf_term_constant state identifier in
        let head = Synapx.LF.Const id in
        let spine = Synapx.LF.Nil in
        Synapx.LF.Root (location, head, spine)
    | Synext.LF.Term.Application { location; applicand; arguments } -> (
        match applicand with
        | Synext.LF.Term.Variable _
        | Synext.LF.Term.Constant _
        | Synext.LF.Term.Application _
        | Synext.LF.Term.Wildcard _ -> (
            let applicand' = index_lf_term state applicand in
            match applicand' with
            | Synapx.LF.Root (_applicand_location, id, spine1') ->
                let spine2' = index_lf_spine state arguments in
                let spine' = append_lf_spines spine1' spine2' in
                Synapx.LF.Root (location, id, spine')
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
            let body' =
              with_bound_omittable_lf_variable state parameter_identifier
                (fun state -> index_lf_term state body)
            in
            let x = fresh_identifier_opt state parameter_identifier in
            let x' = Name.make_from_identifier x in
            Synapx.LF.Lam (location, x', body')
        | Option.Some _typ ->
            Error.raise_at1 location
              Unsupported_lf_annotated_term_abstraction)
    | Synext.LF.Term.Wildcard { location } ->
        let x = fresh_identifier state in
        let x' = Name.make_from_identifier x in
        let head = Synapx.LF.FVar x' in
        let spine = Synapx.LF.Nil in
        Synapx.LF.Root (location, head, spine)
    | Synext.LF.Term.Type_annotated { location; term; typ } ->
        let term' = index_lf_term state term in
        let typ' = index_lf_typ state typ in
        Synapx.LF.Ann (location, term', typ')

  and index_lf_spine_list state arguments =
    match arguments with
    | [] -> Synapx.LF.Nil
    | x :: xs ->
        let argument' = index_lf_term state x in
        let spine' = index_lf_spine_list state xs in
        Synapx.LF.App (argument', spine')

  and index_lf_spine_list1 state (List1.T (x, xs)) =
    let argument' = index_lf_term state x in
    let spine' = index_lf_spine_list state xs in
    Synapx.LF.App (argument', spine')

  and index_lf_spine state arguments = index_lf_spine_list1 state arguments

  let rec index_clf_typ state = function
    | Synext.CLF.Typ.Constant { identifier; location } ->
        let id = index_of_lf_type_constant state identifier in
        let spine = Synapx.LF.Nil in
        Synapx.LF.Atom (location, id, spine)
    | Synext.CLF.Typ.Application { applicand; arguments; location } -> (
        match applicand with
        | Synext.CLF.Typ.Constant _
        | Synext.CLF.Typ.Application _ -> (
            let applicand' = index_clf_typ state applicand in
            match applicand' with
            | Synapx.LF.Atom (_applicand_location, id, spine1') ->
                let spine2' = index_clf_spine state arguments in
                let spine' = append_lf_spines spine1' spine2' in
                Synapx.LF.Atom (location, id, spine')
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
    | Synext.CLF.Typ.Arrow { domain; range; location = _; orientation = _ }
      ->
        let domain' = index_clf_typ state domain in
        let range' =
          with_shifted_lf_context state (fun state ->
              index_clf_typ state range)
        in
        let x = fresh_identifier state in
        let x' = Name.make_from_identifier x in
        Synapx.LF.PiTyp
          ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range')
    | Synext.CLF.Typ.Pi
        { parameter_identifier; parameter_type; body; plicity; location = _ }
      ->
        let domain' = index_clf_typ state parameter_type in
        let range' =
          with_bound_omittable_lf_variable state parameter_identifier
            (fun state -> index_clf_typ state body)
        in
        let x = fresh_identifier_opt state parameter_identifier in
        let x' = Name.make_from_identifier x in
        Synapx.LF.PiTyp ((Synapx.LF.TypDecl (x', domain'), plicity), range')
    | Synext.CLF.Typ.Block { elements; location = _ } -> (
        match elements with
        | `Unnamed typ ->
            let typ' = index_clf_typ state typ in
            let identifier = Option.none in
            Synapx.LF.Sigma (Synapx.LF.SigmaLast (identifier, typ'))
        | `Record bindings ->
            let bindings' = index_clf_block_bindings state bindings in
            Synapx.LF.Sigma bindings')

  and index_clf_block_bindings_list1 state (List1.T ((identifier, typ), xs))
      =
    match xs with
    | [] ->
        let typ' = index_clf_typ state typ in
        let name_opt = Option.some (Name.make_from_identifier identifier) in
        Synapx.LF.SigmaLast (name_opt, typ')
    | x2 :: xs ->
        let typ' = index_clf_typ state typ in
        let name = Name.make_from_identifier identifier in
        let bindings' =
          with_bound_lf_variable state identifier (fun state ->
              index_clf_block_bindings_list1 state (List1.from x2 xs))
        in
        Synapx.LF.SigmaElem (name, typ', bindings')

  and index_clf_block_bindings state bindings =
    index_clf_block_bindings_list1 state bindings

  and index_clf_term state = function
    | Synext.CLF.Term.Variable { location; identifier } ->
        let offset = index_of_lf_variable state identifier in
        let head = Synapx.LF.BVar offset in
        let spine = Synapx.LF.Nil in
        Synapx.LF.Root (location, head, spine)
    | Synext.CLF.Term.Meta_variable { location; identifier } -> (
        match index_of_meta_variable_opt state identifier with
        | Option.Some offset ->
            let closure = Option.none in
            let head = Synapx.LF.MVar (Synapx.LF.Offset offset, closure) in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine)
        | Option.None ->
            add_free_meta_variable state identifier;
            let name = Name.make_from_identifier identifier in
            let closure = Option.none in
            let head = Synapx.LF.FMVar (name, closure) in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine))
    | Synext.CLF.Term.Constant { location; identifier } ->
        let id = index_of_lf_term_constant state identifier in
        let head = Synapx.LF.Const id in
        let spine = Synapx.LF.Nil in
        Synapx.LF.Root (location, head, spine)
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
            let applicand' = index_clf_term state applicand in
            match applicand' with
            | Synapx.LF.Root (_applicand_location, id, spine1') ->
                let spine2' = index_clf_spine state arguments in
                let spine' = append_lf_spines spine1' spine2' in
                Synapx.LF.Root (location, id, spine')
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
            let body' =
              with_bound_omittable_lf_variable state parameter_identifier
                (fun state -> index_clf_term state body)
            in
            let x = fresh_identifier_opt state parameter_identifier in
            let x' = Name.make_from_identifier x in
            Synapx.LF.Lam (location, x', body')
        | Option.Some _typ ->
            Error.raise_at1 location
              Unsupported_lf_annotated_term_abstraction)
    | Synext.CLF.Term.Hole { variant; location } -> (
        match variant with
        | `Underscore ->
            let head = Synapx.LF.Hole in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine)
        | `Unlabelled ->
            let label = Option.none in
            Synapx.LF.LFHole (location, label)
        | `Labelled label ->
            let label = Option.some (Identifier.name label) in
            Synapx.LF.LFHole (location, label))
    | Synext.CLF.Term.Type_annotated { location; term; typ } ->
        let term' = index_clf_term state term in
        let typ' = index_clf_typ state typ in
        Synapx.LF.Ann (location, term', typ')
    | Synext.CLF.Term.Parameter_variable { identifier; location } -> (
        match index_of_parameter_variable_opt state identifier with
        | Option.Some offset ->
            let closure = Option.none in
            let head = Synapx.LF.PVar (Synapx.LF.Offset offset, closure) in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine)
        | Option.None ->
            add_free_parameter_variable state identifier;
            let name = Name.make_from_identifier identifier in
            let closure = Option.none in
            let head = Synapx.LF.FPVar (name, closure) in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine))
    | Synext.CLF.Term.Substitution
        { location = location1
        ; term =
            Synext.CLF.Term.Projection
              { location = _location2
              ; term =
                  Synext.CLF.Term.Parameter_variable
                    { location = _location3; identifier }
              ; projection
              }
        ; substitution
        } -> (
        (* FIXME: Ideally, it should be the case that [#p.1[..]] and
           [#p[..].1] have different meanings, because the following hacky
           swapping of the substitution and projection misleads the user into
           thinking those notations are equivalent. The notation [#p.1[..]]
           should instead always be rejected (and never printed back to the
           user). *)
        (* The external syntax supports [#p.1[..]] as [(#p.1)[..]], but the
           approximate syntax expects [(#p[..]).1]. *)
        match index_of_parameter_variable_opt state identifier with
        | Option.Some offset -> (
            let substitution' = index_clf_substitution state substitution in
            let head =
              Synapx.LF.PVar
                (Synapx.LF.Offset offset, Option.Some substitution')
            in
            match projection with
            | `By_identifier identifier ->
                let name = Name.make_from_identifier identifier in
                let head' = Synapx.LF.Proj (head, Synapx.LF.ByName name) in
                Synapx.LF.Root (location1, head', Synapx.LF.Nil)
            | `By_position position ->
                let head' =
                  Synapx.LF.Proj (head, Synapx.LF.ByPos position)
                in
                Synapx.LF.Root (location1, head', Synapx.LF.Nil))
        | Option.None -> (
            add_free_parameter_variable state identifier;
            let name = Name.make_from_identifier identifier in
            let substitution' = index_clf_substitution state substitution in
            let head = Synapx.LF.FPVar (name, Option.Some substitution') in
            match projection with
            | `By_identifier identifier ->
                let name = Name.make_from_identifier identifier in
                let head' = Synapx.LF.Proj (head, Synapx.LF.ByName name) in
                Synapx.LF.Root (location1, head', Synapx.LF.Nil)
            | `By_position position ->
                let head' =
                  Synapx.LF.Proj (head, Synapx.LF.ByPos position)
                in
                Synapx.LF.Root (location1, head', Synapx.LF.Nil)))
    | Synext.CLF.Term.Substitution { location; term; substitution } -> (
        let term' = index_clf_term state term in
        (* Only [term'] that is a root with an empty spine and whose head can
           have a substitution can have [substitution] attached to it. *)
        match term' with
        | Synapx.LF.Root (_, Synapx.LF.MVar (u, Option.None), Synapx.LF.Nil)
          ->
            let substitution' = index_clf_substitution state substitution in
            let head' =
              Synapx.LF.MVar (u, Option.some substitution')
              (* Attach substitution *)
            in
            Synapx.LF.Root (location, head', Synapx.LF.Nil)
        | Synapx.LF.Root (_, Synapx.LF.FMVar (u, Option.None), Synapx.LF.Nil)
          ->
            let substitution' = index_clf_substitution state substitution in
            let head' =
              Synapx.LF.FMVar (u, Option.some substitution')
              (* Attach substitution *)
            in
            Synapx.LF.Root (location, head', Synapx.LF.Nil)
        | Synapx.LF.Root (_, Synapx.LF.PVar (p, Option.None), Synapx.LF.Nil)
          ->
            let substitution' = index_clf_substitution state substitution in
            let head' =
              Synapx.LF.PVar (p, Option.some substitution')
              (* Attach substitution *)
            in
            Synapx.LF.Root (location, head', Synapx.LF.Nil)
        | Synapx.LF.Root (_, Synapx.LF.FPVar (p, Option.None), Synapx.LF.Nil)
          ->
            let substitution' = index_clf_substitution state substitution in
            let head' =
              Synapx.LF.FPVar (p, Option.some substitution')
              (* Attach substitution *)
            in
            Synapx.LF.Root (location, head', Synapx.LF.Nil)
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
        let term' = index_clf_term state term in
        match term' with
        | Synapx.LF.Root (_, head, Synapx.LF.Nil) -> (
            match projection with
            | `By_identifier identifier ->
                let name = Name.make_from_identifier identifier in
                let head' = Synapx.LF.Proj (head, Synapx.LF.ByName name) in
                Synapx.LF.Root (location, head', Synapx.LF.Nil)
            | `By_position position ->
                let head' =
                  Synapx.LF.Proj (head, Synapx.LF.ByPos position)
                in
                Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root _
        | Synapx.LF.Lam _
        | Synapx.LF.LFHole _
        | Synapx.LF.Tuple _
        | Synapx.LF.Ann _ ->
            Error.raise_at1 location Unsupported_clf_projection_applicand)
    | Synext.CLF.Term.Tuple { location; terms } ->
        let tuple = index_clf_tuple state terms in
        Synapx.LF.Tuple (location, tuple)

  and index_clf_tuple_list1 state (List1.T (x, xs)) =
    match xs with
    | [] ->
        let last' = index_clf_term state x in
        Synapx.LF.Last last'
    | x2 :: xs ->
        let term' = index_clf_term state x in
        let tuple' = index_clf_tuple_list1 state (List1.from x2 xs) in
        Synapx.LF.Cons (term', tuple')

  and index_clf_tuple state terms = index_clf_tuple_list1 state terms

  and index_clf_spine_list state spine =
    match spine with
    | [] -> Synapx.LF.Nil
    | x :: xs ->
        let term' = index_clf_term state x in
        let spine' = index_clf_spine_list state xs in
        Synapx.LF.App (term', spine')

  and index_clf_spine_list1 state (List1.T (x, xs)) =
    let term' = index_clf_term state x in
    let spine' = index_clf_spine_list state xs in
    Synapx.LF.App (term', spine')

  and index_clf_spine state spine = index_clf_spine_list1 state spine

  and index_clf_term_pattern state = function
    | Synext.CLF.Term.Pattern.Variable { location; identifier } ->
        let offset = index_of_lf_variable state identifier in
        let head = Synapx.LF.BVar offset in
        let spine = Synapx.LF.Nil in
        Synapx.LF.Root (location, head, spine)
    | Synext.CLF.Term.Pattern.Meta_variable { location; identifier } -> (
        match index_of_meta_variable_opt state identifier with
        | Option.Some offset ->
            let closure = Option.none in
            let head = Synapx.LF.MVar (Synapx.LF.Offset offset, closure) in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine)
        | Option.None ->
            add_free_meta_variable state identifier;
            let name = Name.make_from_identifier identifier in
            let closure = Option.none in
            let head = Synapx.LF.FMVar (name, closure) in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine))
    | Synext.CLF.Term.Pattern.Constant { location; identifier } ->
        let id = index_of_lf_term_constant state identifier in
        let head = Synapx.LF.Const id in
        let spine = Synapx.LF.Nil in
        Synapx.LF.Root (location, head, spine)
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
            let applicand' = index_clf_term_pattern state applicand in
            match applicand' with
            | Synapx.LF.Root (_applicand_location, id, spine1') ->
                let spine2' = index_clf_spine_pattern state arguments in
                let spine' = append_lf_spines spine1' spine2' in
                Synapx.LF.Root (location, id, spine')
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
            let body' =
              with_bound_omittable_lf_variable state parameter_identifier
                (fun state -> index_clf_term_pattern state body)
            in
            let x = fresh_identifier_opt state parameter_identifier in
            let x' = Name.make_from_identifier x in
            Synapx.LF.Lam (location, x', body')
        | Option.Some _typ ->
            Error.raise_at1 location
              Unsupported_lf_annotated_term_abstraction)
    | Synext.CLF.Term.Pattern.Wildcard { location } ->
        Synapx.LF.Root (location, Synapx.LF.Hole, Synapx.LF.Nil)
    | Synext.CLF.Term.Pattern.Type_annotated { location; term; typ } ->
        let term' = index_clf_term_pattern state term in
        let typ' = index_clf_typ state typ in
        Synapx.LF.Ann (location, term', typ')
    | Synext.CLF.Term.Pattern.Parameter_variable { identifier; location }
      -> (
        match index_of_parameter_variable_opt state identifier with
        | Option.Some offset ->
            let closure = Option.none in
            let head = Synapx.LF.PVar (Synapx.LF.Offset offset, closure) in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine)
        | Option.None ->
            add_free_parameter_variable state identifier;
            let name = Name.make_from_identifier identifier in
            let closure = Option.none in
            let head = Synapx.LF.FPVar (name, closure) in
            let spine = Synapx.LF.Nil in
            Synapx.LF.Root (location, head, spine))
    | Synext.CLF.Term.Pattern.Substitution
        { location = location1
        ; term =
            Synext.CLF.Term.Pattern.Projection
              { location = _location2
              ; term =
                  Synext.CLF.Term.Pattern.Parameter_variable
                    { location = _location3; identifier }
              ; projection
              }
        ; substitution
        } -> (
        (* FIXME: Ideally, it should be the case that [#p.1[..]] and
           [#p[..].1] have different meanings, because the following hacky
           swapping of the substitution and projection misleads the user into
           thinking those notations are equivalent. The notation [#p.1[..]]
           should instead always be rejected (and never printed back to the
           user). *)
        (* The external syntax supports [#p.1[..]] as [(#p.1)[..]], but the
           approximate syntax expects [(#p[..]).1]. *)
        match index_of_parameter_variable_opt state identifier with
        | Option.Some offset -> (
            let substitution' = index_clf_substitution state substitution in
            let head =
              Synapx.LF.PVar
                (Synapx.LF.Offset offset, Option.Some substitution')
            in
            match projection with
            | `By_identifier identifier ->
                let name = Name.make_from_identifier identifier in
                let head' = Synapx.LF.Proj (head, Synapx.LF.ByName name) in
                Synapx.LF.Root (location1, head', Synapx.LF.Nil)
            | `By_position position ->
                let head' =
                  Synapx.LF.Proj (head, Synapx.LF.ByPos position)
                in
                Synapx.LF.Root (location1, head', Synapx.LF.Nil))
        | Option.None -> (
            add_free_parameter_variable state identifier;
            let name = Name.make_from_identifier identifier in
            let substitution' = index_clf_substitution state substitution in
            let head = Synapx.LF.FPVar (name, Option.Some substitution') in
            match projection with
            | `By_identifier identifier ->
                let name = Name.make_from_identifier identifier in
                let head' = Synapx.LF.Proj (head, Synapx.LF.ByName name) in
                Synapx.LF.Root (location1, head', Synapx.LF.Nil)
            | `By_position position ->
                let head' =
                  Synapx.LF.Proj (head, Synapx.LF.ByPos position)
                in
                Synapx.LF.Root (location1, head', Synapx.LF.Nil)))
    | Synext.CLF.Term.Pattern.Substitution { location; term; substitution }
      -> (
        let term' = index_clf_term_pattern state term in
        (* Only [term'] that is a root with an empty spine and whose head can
           have a substitution can have [substitution] attached to it. *)
        match term' with
        | Synapx.LF.Root (_, Synapx.LF.MVar (u, Option.None), Synapx.LF.Nil)
          ->
            let substitution' = index_clf_substitution state substitution in
            let head' =
              Synapx.LF.MVar (u, Option.some substitution')
              (* Attach substitution *)
            in
            Synapx.LF.Root (location, head', Synapx.LF.Nil)
        | Synapx.LF.Root (_, Synapx.LF.FMVar (u, Option.None), Synapx.LF.Nil)
          ->
            let substitution' = index_clf_substitution state substitution in
            let head' =
              Synapx.LF.FMVar (u, Option.some substitution')
              (* Attach substitution *)
            in
            Synapx.LF.Root (location, head', Synapx.LF.Nil)
        | Synapx.LF.Root (_, Synapx.LF.PVar (p, Option.None), Synapx.LF.Nil)
          ->
            let substitution' = index_clf_substitution state substitution in
            let head' =
              Synapx.LF.PVar (p, Option.some substitution')
              (* Attach substitution *)
            in
            Synapx.LF.Root (location, head', Synapx.LF.Nil)
        | Synapx.LF.Root (_, Synapx.LF.FPVar (p, Option.None), Synapx.LF.Nil)
          ->
            let substitution' = index_clf_substitution state substitution in
            let head' =
              Synapx.LF.FPVar (p, Option.some substitution')
              (* Attach substitution *)
            in
            Synapx.LF.Root (location, head', Synapx.LF.Nil)
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
        let term' = index_clf_term_pattern state term in
        match term' with
        | Synapx.LF.Root (_, head, Synapx.LF.Nil) -> (
            match projection with
            | `By_identifier identifier ->
                let name = Name.make_from_identifier identifier in
                let head' = Synapx.LF.Proj (head, Synapx.LF.ByName name) in
                Synapx.LF.Root (location, head', Synapx.LF.Nil)
            | `By_position position ->
                let head' =
                  Synapx.LF.Proj (head, Synapx.LF.ByPos position)
                in
                Synapx.LF.Root (location, head', Synapx.LF.Nil))
        | Synapx.LF.Root _
        | Synapx.LF.Lam _
        | Synapx.LF.LFHole _
        | Synapx.LF.Tuple _
        | Synapx.LF.Ann _ ->
            Error.raise_at1 location Unsupported_clf_projection_applicand)
    | Synext.CLF.Term.Pattern.Tuple { location; terms } ->
        let tuple = index_clf_tuple_pattern state terms in
        Synapx.LF.Tuple (location, tuple)

  and index_clf_tuple_pattern_list1 state (List1.T (x, xs)) =
    match xs with
    | [] ->
        let last' = index_clf_term_pattern state x in
        Synapx.LF.Last last'
    | x2 :: xs ->
        let term' = index_clf_term_pattern state x in
        let tuple' =
          index_clf_tuple_pattern_list1 state (List1.from x2 xs)
        in
        Synapx.LF.Cons (term', tuple')

  and index_clf_tuple_pattern state terms =
    index_clf_tuple_pattern_list1 state terms

  and index_clf_spine_pattern_list1 state (List1.T (x, xs)) =
    match xs with
    | [] ->
        let last' = index_clf_term_pattern state x in
        Synapx.LF.App (last', Synapx.LF.Nil)
    | x2 :: xs ->
        let term' = index_clf_term_pattern state x in
        let spine' =
          index_clf_spine_pattern_list1 state (List1.from x2 xs)
        in
        Synapx.LF.App (term', spine')

  and index_clf_spine_pattern state spine =
    index_clf_spine_pattern_list1 state spine

  and index_clf_substitution state
      { Synext.CLF.Substitution.head; terms; location = _ } =
    let head' =
      match head with
      | Synext.CLF.Substitution.Head.None _ -> Synapx.LF.EmptySub
      | Synext.CLF.Substitution.Head.Identity _ -> Synapx.LF.Id
      | Synext.CLF.Substitution.Head.Substitution_variable
          { identifier; closure; location = _ } -> (
          match index_of_substitution_variable_opt state identifier with
          | Option.Some offset ->
              let closure' =
                traverse_option state index_clf_substitution closure
              in
              Synapx.LF.SVar (Synapx.LF.Offset offset, closure')
          | Option.None ->
              add_free_substitution_variable state identifier;
              let name = Name.make_from_identifier identifier in
              let closure' =
                traverse_option state index_clf_substitution closure
              in
              Synapx.LF.FSVar (name, closure'))
    in
    index_clf_substitution_terms state head' terms

  and index_clf_substitution_terms state substitution' terms =
    match terms with
    | [] -> substitution'
    | term :: rest ->
        let term' = index_clf_term state term in
        index_clf_substitution_terms state
          (Synapx.LF.Dot (to_head_or_obj term', substitution'))
          rest

  and index_clf_substitution_pattern state
      { Synext.CLF.Substitution.Pattern.head; terms; location = _ } =
    let head' =
      match head with
      | Synext.CLF.Substitution.Pattern.Head.None _ -> Synapx.LF.EmptySub
      | Synext.CLF.Substitution.Pattern.Head.Identity _ -> Synapx.LF.Id
      | Synext.CLF.Substitution.Pattern.Head.Substitution_variable
          { identifier; closure; location = _ } -> (
          match index_of_substitution_variable_opt state identifier with
          | Option.Some offset ->
              let closure' =
                traverse_option state index_clf_substitution closure
              in
              Synapx.LF.SVar (Synapx.LF.Offset offset, closure')
          | Option.None ->
              add_free_substitution_variable state identifier;
              let name = Name.make_from_identifier identifier in
              let closure' =
                traverse_option state index_clf_substitution closure
              in
              Synapx.LF.FSVar (name, closure'))
    in
    index_clf_substitution_pattern_terms state head' terms

  and index_clf_substitution_pattern_terms state substitution' terms =
    match terms with
    | [] -> substitution'
    | term :: rest ->
        let term' = index_clf_term_pattern state term in
        index_clf_substitution_pattern_terms state
          (Synapx.LF.Dot (to_head_or_obj term', substitution'))
          rest

  and with_indexed_clf_context_bindings state cPhi bindings f =
    match bindings with
    | [] -> f state cPhi
    | x :: xs ->
        with_indexed_clf_context_binding state x (fun state y ->
            with_indexed_clf_context_bindings state
              (Synapx.LF.DDec (cPhi, y))
              xs f)

  and with_indexed_clf_context_binding state (identifier, typ_opt) f =
    let name = Name.make_from_identifier identifier in
    match typ_opt with
    | Option.None ->
        with_bound_lf_variable state identifier (fun state ->
            f state (Synapx.LF.TypDeclOpt name))
    | Option.Some typ ->
        let typ' = index_clf_typ state typ in
        with_bound_lf_variable state identifier (fun state ->
            f state (Synapx.LF.TypDecl (name, typ')))

  and with_indexed_clf_context :
        'a.
        state -> Synext.clf_context -> (state -> Synapx.LF.dctx -> 'a) -> 'a
      =
   fun state context f ->
    match context with
    | { Synext.CLF.Context.head = Synext.CLF.Context.Head.None _
      ; bindings
      ; location = _
      } ->
        with_indexed_clf_context_bindings state Synapx.LF.Null bindings f
    | { Synext.CLF.Context.head = Synext.CLF.Context.Head.Hole _
      ; bindings
      ; location = _
      } ->
        with_indexed_clf_context_bindings state Synapx.LF.CtxHole bindings f
    | { Synext.CLF.Context.head =
          Synext.CLF.Context.Head.Context_variable
            { identifier; location = _ }
      ; bindings
      ; location = _
      } -> (
        match index_of_context_variable_opt state identifier with
        | Option.None ->
            (* A free context variable *)
            add_free_context_variable state identifier;
            let name = Name.make_from_identifier identifier in
            with_indexed_clf_context_bindings state
              (Synapx.LF.CtxVar (Synapx.LF.CtxName name)) bindings f
        | Option.Some index ->
            (* A bound context variable *)
            with_indexed_clf_context_bindings state
              (Synapx.LF.CtxVar (Synapx.LF.CtxOffset index)) bindings f)

  and index_clf_context state context =
    with_indexed_clf_context state context (fun _state context' -> context')

  and with_indexed_clf_context_pattern_bindings state cPhi bindings f =
    match bindings with
    | [] -> f state cPhi
    | x :: xs ->
        with_indexed_clf_context_pattern_binding state x (fun state y ->
            with_indexed_clf_context_pattern_bindings state
              (Synapx.LF.DDec (cPhi, y))
              xs f)

  and with_indexed_clf_context_pattern_binding state (identifier, typ) f =
    let name = Name.make_from_identifier identifier in
    let typ' = index_clf_typ state typ in
    with_bound_lf_variable state identifier (fun state ->
        f state (Synapx.LF.TypDecl (name, typ')))

  and with_indexed_clf_context_pattern :
        'a.
           state
        -> Synext.clf_context_pattern
        -> (state -> Synapx.LF.dctx -> 'a)
        -> 'a =
   fun state context f ->
    match context with
    | { Synext.CLF.Context.Pattern.head =
          Synext.CLF.Context.Pattern.Head.None _
      ; bindings
      ; location = _
      } ->
        with_indexed_clf_context_pattern_bindings state Synapx.LF.Null
          bindings f
    | { Synext.CLF.Context.Pattern.head =
          Synext.CLF.Context.Pattern.Head.Hole _
      ; bindings
      ; location = _
      } ->
        with_indexed_clf_context_pattern_bindings state Synapx.LF.CtxHole
          bindings f
    | { Synext.CLF.Context.Pattern.head =
          Synext.CLF.Context.Pattern.Head.Context_variable
            { identifier; location = _ }
      ; bindings
      ; location = _
      } -> (
        match index_of_context_variable_opt state identifier with
        | Option.None ->
            (* A free context variable *)
            add_free_context_variable state identifier;
            let name = Name.make_from_identifier identifier in
            with_indexed_clf_context_pattern_bindings state
              (Synapx.LF.CtxVar (Synapx.LF.CtxName name)) bindings f
        | Option.Some index ->
            (* A bound context variable *)
            with_indexed_clf_context_pattern_bindings state
              (Synapx.LF.CtxVar (Synapx.LF.CtxOffset index)) bindings f)

  and index_clf_context_pattern state context =
    with_indexed_clf_context_pattern state context (fun _state context' ->
        context')

  let rec index_meta_object state meta_object =
    match meta_object with
    | Synext.Meta.Object.Context { location; context } ->
        let context' = index_clf_context state context in
        (location, Synapx.Comp.CObj context')
    | Synext.Meta.Object.Contextual_term { location; context; term } ->
        with_indexed_clf_context state context (fun state context' ->
            let term' = index_clf_term state term in
            (* TODO: The approximate syntax should have a [MObj of normal]
               constructor like in the internal syntax. See
               {!Reconstruct.elClObj}. *)
            ( location
            , Synapx.Comp.ClObj
                ( context'
                , Synapx.LF.Dot (to_head_or_obj term', Synapx.LF.EmptySub) )
            ))
    | Synext.Meta.Object.Plain_substitution { location; domain; range } ->
        with_indexed_clf_context state domain (fun state domain' ->
            let range' = index_clf_substitution state range in
            (location, Synapx.Comp.ClObj (domain', range')))
    | Synext.Meta.Object.Renaming_substitution { location; domain; range } ->
        with_indexed_clf_context state domain (fun state domain' ->
            let range' = index_clf_substitution state range in
            (location, Synapx.Comp.ClObj (domain', range')))

  and index_meta_type state = function
    | Synext.Meta.Typ.Context_schema { schema; location = _ } ->
        let index = index_of_schema_constant state schema in
        Synapx.LF.CTyp index
    | Synext.Meta.Typ.Contextual_typ { context; typ; location = _ } ->
        with_indexed_clf_context state context (fun state context' ->
            let typ' = index_clf_typ state typ in
            Synapx.LF.ClTyp (Synapx.LF.MTyp typ', context'))
    | Synext.Meta.Typ.Parameter_typ { context; typ; location = _ } ->
        with_indexed_clf_context state context (fun state context' ->
            let typ' = index_clf_typ state typ in
            Synapx.LF.ClTyp (Synapx.LF.PTyp typ', context'))
    | Synext.Meta.Typ.Plain_substitution_typ { domain; range; location = _ }
      ->
        with_indexed_clf_context state domain (fun state domain' ->
            with_indexed_clf_context state range (fun _state range' ->
                Synapx.LF.ClTyp
                  (Synapx.LF.STyp (Synapx.LF.Subst, range'), domain')))
    | Synext.Meta.Typ.Renaming_substitution_typ
        { domain; range; location = _ } ->
        with_indexed_clf_context state domain (fun state domain' ->
            with_indexed_clf_context state range (fun _state range' ->
                Synapx.LF.ClTyp
                  (Synapx.LF.STyp (Synapx.LF.Ren, range'), domain')))

  and with_indexed_lf_context_bindings_list1 state cPhi (List1.T (x, xs)) f =
    with_indexed_lf_context_binding state x (fun state y ->
        with_indexed_lf_context_bindings_list state
          (Synapx.LF.Dec (cPhi, y))
          xs f)

  and with_indexed_lf_context_bindings_list state cPhi bindings f =
    match bindings with
    | [] -> f state cPhi
    | x :: xs ->
        with_indexed_lf_context_binding state x (fun state y ->
            with_indexed_lf_context_bindings_list state
              (Synapx.LF.Dec (cPhi, y))
              xs f)

  and with_indexed_lf_context_binding state (identifier, typ) f =
    let name = Name.make_from_identifier identifier in
    let typ' = index_lf_typ state typ in
    with_bound_lf_variable state identifier (fun state ->
        f state (Synapx.LF.TypDecl (name, typ')))

  and with_indexed_schema_some_clause state some f =
    match some with
    | Option.None -> f state Synapx.LF.Empty
    | Option.Some some ->
        with_indexed_lf_context_bindings_list1 state Synapx.LF.Empty some f

  and with_indexed_schema_block_clause_bindings_list1 state bindings f =
    match bindings with
    | List1.T ((identifier, typ), []) ->
        let name = Name.make_from_identifier identifier in
        let typ' = index_lf_typ state typ in
        f state (Synapx.LF.SigmaLast (Option.some name, typ'))
    | List1.T ((identifier, typ), x :: xs) ->
        let name = Name.make_from_identifier identifier in
        let typ' = index_lf_typ state typ in
        with_bound_lf_variable state identifier (fun state ->
            with_indexed_schema_block_clause_bindings_list1 state
              (List1.from x xs) (fun state tRec ->
                f state (Synapx.LF.SigmaElem (name, typ', tRec))))

  and index_schema_block_clause state = function
    | `Record bindings ->
        with_indexed_schema_block_clause_bindings_list1 state bindings
          (fun _state context' -> context')
    | `Unnamed typ ->
        let typ' = index_lf_typ state typ in
        Synapx.LF.SigmaLast (Option.none, typ')

  and index_schema state = function
    | Synext.Meta.Schema.Alternation { schemas; location = _ } ->
        let schemas' = traverse_list2 state index_schema_element schemas in
        let schemas'' = List2.to_list schemas' in
        Synapx.LF.Schema schemas''
    | (Synext.Meta.Schema.Constant _ | Synext.Meta.Schema.Element _) as
      element ->
        let element' = index_schema_element state element in
        Synapx.LF.Schema [ element' ]

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

  and index_schema_element state = function
    | Synext.Meta.Schema.Element { some; block; location = _ } -> (
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
                with_indexed_schema_some_clause state some
                  (fun state some' ->
                    let block' = index_schema_block_clause state block in
                    Synapx.LF.SchElem (some', block'))))
    | Synext.Meta.Schema.Constant { location; _ }
    | Synext.Meta.Schema.Alternation { location; _ } ->
        Error.raise_at1 location Unsupported_context_schema_element

  and index_meta_pattern state = function
    | Synext.Meta.Pattern.Context { location; context } ->
        let context' = index_clf_context_pattern state context in
        (location, Synapx.Comp.CObj context')
    | Synext.Meta.Pattern.Contextual_term { location; context; term } ->
        with_indexed_clf_context_pattern state context (fun state context' ->
            let term' = index_clf_term_pattern state term in
            (* TODO: The approximate syntax should have a [MObj of normal]
               constructor like in the internal syntax. See
               {!Reconstruct.elClObj}. *)
            ( location
            , Synapx.Comp.ClObj
                ( context'
                , Synapx.LF.Dot (to_head_or_obj term', Synapx.LF.EmptySub) )
            ))
    | Synext.Meta.Pattern.Plain_substitution { location; domain; range } ->
        with_indexed_clf_context_pattern state domain (fun state domain' ->
            let range' = index_clf_substitution_pattern state range in
            (location, Synapx.Comp.ClObj (domain', range')))
    | Synext.Meta.Pattern.Renaming_substitution { location; domain; range }
      ->
        with_indexed_clf_context_pattern state domain (fun state domain' ->
            let range' = index_clf_substitution_pattern state range in
            (location, Synapx.Comp.ClObj (domain', range')))

  and with_indexed_meta_context_binding state (identifier, typ) f =
    let typ' = index_meta_type state typ in
    let name = Name.make_from_identifier identifier in
    let with_bound_declaration =
      match typ with
      | Synext.Meta.Typ.Context_schema _ -> with_bound_context_variable
      | Synext.Meta.Typ.Contextual_typ _ -> with_bound_meta_variable
      | Synext.Meta.Typ.Parameter_typ _ -> with_bound_parameter_variable
      | Synext.Meta.Typ.Plain_substitution_typ _
      | Synext.Meta.Typ.Renaming_substitution_typ _ ->
          with_bound_substitution_variable
    in
    with_bound_declaration state identifier (fun state ->
        f state (Synapx.LF.Decl (name, typ', Plicity.explicit)))

  and with_indexed_meta_context_bindings state bindings f =
    match bindings with
    | [] -> f state []
    | x :: xs ->
        with_indexed_meta_context_binding state x (fun state y ->
            with_indexed_meta_context_bindings state xs (fun state ys ->
                f state (y :: ys)))

  and with_indexed_meta_context state
      { Synext.Meta.Context.bindings; location = _ } f =
    with_indexed_meta_context_bindings state bindings (fun state bindings' ->
        f state
          (List.fold_left
             (fun accumulator binding' ->
               Synapx.LF.Dec (accumulator, binding'))
             Synapx.LF.Empty bindings'))

  and with_indexed_meta_context_pattern_binding state (identifier, typ) f =
    let typ' = index_meta_type state typ in
    let with_bound_pattern_declaration =
      match typ with
      | Synext.Meta.Typ.Context_schema _ ->
          with_bound_pattern_context_variable
      | Synext.Meta.Typ.Contextual_typ _ -> with_bound_pattern_meta_variable
      | Synext.Meta.Typ.Parameter_typ _ ->
          with_bound_pattern_parameter_variable
      | Synext.Meta.Typ.Plain_substitution_typ _
      | Synext.Meta.Typ.Renaming_substitution_typ _ ->
          with_bound_pattern_substitution_variable
    in
    let name = Name.make_from_identifier identifier in
    with_bound_pattern_declaration state identifier (fun state ->
        f state (Synapx.LF.Decl (name, typ', Plicity.explicit)))

  and with_indexed_meta_context_pattern_bindings state bindings f =
    match bindings with
    | [] -> f state []
    | x :: xs ->
        with_indexed_meta_context_pattern_binding state x (fun state y ->
            with_indexed_meta_context_pattern_bindings state xs
              (fun state ys -> f state (y :: ys)))

  and with_indexed_meta_context_pattern state
      { Synext.Meta.Context.bindings; location = _ } f =
    with_indexed_meta_context_pattern_bindings state bindings
      (fun state bindings' ->
        f state
          (List.fold_left
             (fun accumulator binding' ->
               Synapx.LF.Dec (accumulator, binding'))
             Synapx.LF.Empty bindings'))

  let rec index_comp_kind state = function
    | Synext.Comp.Kind.Ctype { location } -> Synapx.Comp.Ctype location
    | Synext.Comp.Kind.Arrow { location; domain; range } ->
        let domain' = index_meta_type state domain in
        let range' =
          with_bound_omittable_meta_variable state Option.none domain
            (fun state -> index_comp_kind state range)
        in
        let x = fresh_identifier state in
        let x' = Name.make_from_identifier x in
        Synapx.Comp.PiKind
          (location, Synapx.LF.Decl (x', domain', Plicity.explicit), range')
    | Synext.Comp.Kind.Pi
        { location; parameter_identifier; plicity; parameter_type; body } ->
        let parameter_type' = index_meta_type state parameter_type in
        let body' =
          with_bound_omittable_meta_variable state parameter_identifier
            parameter_type (fun state -> index_comp_kind state body)
        in
        let x = fresh_identifier_opt state parameter_identifier in
        let x' = Name.make_from_identifier x in
        Synapx.Comp.PiKind
          (location, Synapx.LF.Decl (x', parameter_type', plicity), body')

  and index_comp_typ state = function
    | Synext.Comp.Typ.Inductive_typ_constant { location; identifier } ->
        let index = index_of_inductive_comp_constant state identifier in
        Synapx.Comp.TypBase (location, index, Synapx.Comp.MetaNil)
    | Synext.Comp.Typ.Stratified_typ_constant { location; identifier } ->
        let index = index_of_stratified_comp_constant state identifier in
        Synapx.Comp.TypBase (location, index, Synapx.Comp.MetaNil)
    | Synext.Comp.Typ.Coinductive_typ_constant { location; identifier } ->
        let index = index_of_coinductive_comp_constant state identifier in
        Synapx.Comp.TypCobase (location, index, Synapx.Comp.MetaNil)
    | Synext.Comp.Typ.Abbreviation_typ_constant { location; identifier } ->
        let index = index_of_abbreviation_comp_constant state identifier in
        Synapx.Comp.TypDef (location, index, Synapx.Comp.MetaNil)
    | Synext.Comp.Typ.Pi
        { location; parameter_identifier; plicity; parameter_type; body } ->
        let parameter_type' = index_meta_type state parameter_type in
        let body' =
          with_bound_omittable_meta_variable state parameter_identifier
            parameter_type (fun state -> index_comp_typ state body)
        in
        let x = fresh_identifier_opt state parameter_identifier in
        let x' = Name.make_from_identifier x in
        Synapx.Comp.TypPiBox
          (location, Synapx.LF.Decl (x', parameter_type', plicity), body')
    | Synext.Comp.Typ.Arrow { location; domain; range; orientation = _ } ->
        let domain' = index_comp_typ state domain in
        let range' = index_comp_typ state range in
        Synapx.Comp.TypArr (location, domain', range')
    | Synext.Comp.Typ.Cross { location; types } ->
        let types' = traverse_list2 state index_comp_typ types in
        Synapx.Comp.TypCross (location, types')
    | Synext.Comp.Typ.Box { location; meta_type } ->
        let meta_type' = index_meta_type state meta_type in
        Synapx.Comp.TypBox (location, (location, meta_type'))
    | Synext.Comp.Typ.Application { location; applicand; arguments } -> (
        let applicand' = index_comp_typ state applicand in
        match applicand' with
        | Synapx.Comp.TypBase (_, a', spine1') ->
            let spine2' = index_meta_spine state arguments in
            let spine' = append_meta_spines spine1' spine2' in
            Synapx.Comp.TypBase (location, a', spine')
        | Synapx.Comp.TypCobase (_, a', spine1') ->
            let spine2' = index_meta_spine state arguments in
            let spine' = append_meta_spines spine1' spine2' in
            Synapx.Comp.TypCobase (location, a', spine')
        | Synapx.Comp.TypDef (_, a', spine1') ->
            let spine2' = index_meta_spine state arguments in
            let spine' = append_meta_spines spine1' spine2' in
            Synapx.Comp.TypDef (location, a', spine')
        | Synapx.Comp.TypBox _
        | Synapx.Comp.TypArr _
        | Synapx.Comp.TypCross _
        | Synapx.Comp.TypPiBox _
        | Synapx.Comp.TypInd _ ->
            Error.raise_at1 location Unsupported_comp_typ_applicand)

  and index_comp_expression state = function
    | Synext.Comp.Expression.Variable { location; identifier } ->
        let index = index_of_comp_variable state identifier in
        Synapx.Comp.Var (location, index)
    | Synext.Comp.Expression.Constructor { location; identifier } ->
        let index = index_of_comp_constructor state identifier in
        Synapx.Comp.DataConst (location, index)
    | Synext.Comp.Expression.Program { location; identifier } ->
        let index = index_of_comp_program state identifier in
        Synapx.Comp.Const (location, index)
    | Synext.Comp.Expression.Fn { parameters; body; location } ->
        let rec aux state parameters =
          match parameters with
          | [] -> index_comp_expression state body
          | (parameter_location, parameter_opt) :: parameters ->
              let body' =
                with_bound_omittable_comp_variable state parameter_opt
                  (fun state -> aux state parameters)
              in
              let location =
                Location.join parameter_location
                  (Synapx.Comp.loc_of_exp body')
              in
              let parameter = fresh_identifier_opt state parameter_opt in
              let name = Name.make_from_identifier parameter in
              Synapx.Comp.Fn (location, name, body')
        in
        let (List1.T ((_first_parameter_location, first_parameter), rest)) =
          parameters
        in
        let body' =
          with_bound_omittable_comp_variable state first_parameter
            (fun state -> aux state rest)
        in
        let parameter = fresh_identifier_opt state first_parameter in
        let name = Name.make_from_identifier parameter in
        Synapx.Comp.Fn (location, name, body')
    | Synext.Comp.Expression.Mlam { parameters; body; location } ->
        let with_mlam_parameter state parameter_opt modifier =
          match parameter_opt with
          | Option.None -> with_shifted_meta_context state
          | Option.Some parameter ->
              (match modifier with
              | `Plain -> with_bound_contextual_variable state
              | `Hash -> with_bound_parameter_variable state
              | `Dollar -> with_bound_substitution_variable state)
                parameter
        in
        let rec aux state parameters =
          match parameters with
          | [] -> index_comp_expression state body
          | (parameter_location, (parameter_opt, modifier)) :: parameters ->
              let body' =
                with_mlam_parameter state parameter_opt modifier
                  (fun state -> aux state parameters)
              in
              let location =
                Location.join parameter_location
                  (Synapx.Comp.loc_of_exp body')
              in
              let parameter = fresh_identifier_opt state parameter_opt in
              let name = Name.make_from_identifier parameter in
              Synapx.Comp.MLam (location, name, body')
        in
        let (List1.T
              ( ( _first_parameter_location
                , (first_parameter, first_parameter_modifier) )
              , rest )) =
          parameters
        in
        let body' =
          with_mlam_parameter state first_parameter first_parameter_modifier
            (fun state -> aux state rest)
        in
        let parameter = fresh_identifier_opt state first_parameter in
        let name = Name.make_from_identifier parameter in
        Synapx.Comp.MLam (location, name, body')
    | Synext.Comp.Expression.Fun { location; branches } ->
        let branches' =
          traverse_list1 state index_cofunction_branch branches
        in
        let branches_location =
          Location.join_all1_contramap
            Synext.location_of_comp_cofunction_branch branches
        in
        let branches'' =
          List.fold_right
            (fun (location, pattern_spine, body) accumulator ->
              Synapx.Comp.ConsFBranch
                (location, (pattern_spine, body), accumulator))
            (List1.to_list branches')
            (Synapx.Comp.NilFBranch branches_location)
        in
        Synapx.Comp.Fun (location, branches'')
    | Synext.Comp.Expression.Let
        { location; meta_context; pattern; scrutinee; body } ->
        let scrutinee' = index_comp_expression state scrutinee in
        with_free_variables_as_pattern_variables state
          ~pattern:(fun state ->
            with_indexed_meta_context_pattern state meta_context
              (fun state meta_context' ->
                let pattern' = index_comp_pattern state pattern in
                (meta_context', pattern')))
          ~expression:(fun state (meta_context', pattern') ->
            let pattern'' = reindex_pattern state pattern' in
            let body' = index_comp_expression state body in
            (* The approximate syntax does not support general patterns in
               [let]-expressions, so only [let]-expressions with a variable
               pattern are translated to [let]-expressions in the approximate
               syntax. *)
            match (meta_context', pattern'') with
            | Synapx.LF.Empty, Synapx.Comp.PatFVar (_location, name) ->
                (* TODO: General [let] pattern expressions would render this
                   case obsolete *)
                Synapx.Comp.Let (location, scrutinee', (name, body'))
            | Synapx.LF.Empty, Synapx.Comp.PatVar (_location, name, _offset)
              ->
                (* TODO: General [let] pattern expressions would render this
                   case obsolete *)
                Synapx.Comp.Let (location, scrutinee', (name, body'))
            | Synapx.LF.Empty, Synapx.Comp.PatTuple (_location, patterns')
              -> (
                (* TODO: [LetTuple] expressions should be deprecated in
                   favour of general [let] pattern expressions *)
                (* [LetTuple] expressions only support variable patterns *)
                match
                  List2.traverse
                    (function
                      | Synapx.Comp.PatFVar (_location, name) ->
                          Option.some name
                      | Synapx.Comp.PatVar (_location, name, _offset) ->
                          Option.some name
                      | _ -> Option.none)
                    patterns'
                with
                | Option.Some variables ->
                    Synapx.Comp.LetTuple
                      (location, scrutinee', (variables, body'))
                | Option.None ->
                    Synapx.Comp.Case
                      ( location
                      , Synapx.Comp.PragmaCase
                      , scrutinee'
                      , [ Synapx.Comp.Branch
                            (location, meta_context', pattern'', body')
                        ] ))
            | _ ->
                (* TODO: General [let] pattern expressions should be
                   supported *)
                (* The pattern is not a variable pattern, so the
                   [let]-expression is translated to a [case]-expression. *)
                Synapx.Comp.Case
                  ( location
                  , Synapx.Comp.PragmaCase
                  , scrutinee'
                  , [ Synapx.Comp.Branch
                        (location, meta_context', pattern'', body')
                    ] ))
    | Synext.Comp.Expression.Box { location; meta_object } ->
        let meta_object' = index_meta_object state meta_object in
        Synapx.Comp.Box (location, meta_object')
    | Synext.Comp.Expression.Impossible { location; scrutinee } ->
        let scrutinee' = index_comp_expression state scrutinee in
        Synapx.Comp.Impossible (location, scrutinee')
    | Synext.Comp.Expression.Case
        { location; scrutinee; check_coverage; branches } ->
        let scrutinee' = index_comp_expression state scrutinee in
        let branches = traverse_list1 state index_case_branch branches in
        let case_pragma =
          if check_coverage then Synapx.Comp.PragmaCase
          else Synapx.Comp.PragmaNotCase
        in
        Synapx.Comp.Case
          (location, case_pragma, scrutinee', List1.to_list branches)
    | Synext.Comp.Expression.Tuple { location; elements } ->
        let elements' =
          traverse_list2 state index_comp_expression elements
        in
        Synapx.Comp.Tuple (location, elements')
    | Synext.Comp.Expression.Hole { location; label } ->
        let name = Option.map Identifier.name label in
        Synapx.Comp.Hole (location, name)
    | Synext.Comp.Expression.Box_hole { location } ->
        Synapx.Comp.BoxHole location
    | Synext.Comp.Expression.Application
        { applicand; arguments; location = _ } ->
        let applicand' = index_comp_expression state applicand in
        let arguments' =
          traverse_list1 state index_comp_expression arguments
        in
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
        application'
    | Synext.Comp.Expression.Observation { location; scrutinee; destructor }
      ->
        let scrutinee' = index_comp_expression state scrutinee in
        let id = index_of_comp_destructor state destructor in
        Synapx.Comp.Obs (location, scrutinee', id)
    | Synext.Comp.Expression.Type_annotated { location; expression; typ } ->
        let expression' = index_comp_expression state expression in
        let typ' = index_comp_typ state typ in
        Synapx.Comp.Ann (location, expression', typ')

  and index_meta_spine_list1 state (List1.T (x, xs)) =
    match xs with
    | [] ->
        let argument' = index_meta_object state x in
        Synapx.Comp.MetaApp (argument', Synapx.Comp.MetaNil)
    | x2 :: xs ->
        let argument' = index_meta_object state x in
        let spine' = index_meta_spine_list1 state (List1.from x2 xs) in
        Synapx.Comp.MetaApp (argument', spine')

  and index_meta_spine state arguments =
    index_meta_spine_list1 state arguments

  and reindex_pattern state = function
    | Synapx.Comp.PatFVar (location, name) ->
        let identifier = Name.to_identifier name in
        let offset = index_of_comp_variable state identifier in
        Synapx.Comp.PatVar (location, name, offset)
    | Synapx.Comp.PatTuple (location, patterns) ->
        let patterns' = traverse_list2 state reindex_pattern patterns in
        Synapx.Comp.PatTuple (location, patterns')
    | Synapx.Comp.PatConst (location, constant, pat_spine) ->
        let pattern_spine' = reindex_pattern_spine state pat_spine in
        Synapx.Comp.PatConst (location, constant, pattern_spine')
    | Synapx.Comp.PatAnn (location, pattern, typ) ->
        let pattern' = reindex_pattern state pattern in
        Synapx.Comp.PatAnn (location, pattern', typ)
    | (Synapx.Comp.PatVar _ | Synapx.Comp.PatMetaObj _) as pattern -> pattern

  and reindex_pattern_spine state = function
    | Synapx.Comp.PatNil location -> Synapx.Comp.PatNil location
    | Synapx.Comp.PatApp (location, pattern, pat_spine) ->
        let pattern' = reindex_pattern state pattern in
        let pattern_spine' = reindex_pattern_spine state pat_spine in
        Synapx.Comp.PatApp (location, pattern', pattern_spine')
    | Synapx.Comp.PatObs (location, destructor_id, pat_spine) ->
        let pattern_spine' = reindex_pattern_spine state pat_spine in
        Synapx.Comp.PatObs (location, destructor_id, pattern_spine')

  and index_comp_pattern state = function
    | Synext.Comp.Pattern.Variable { location; identifier } ->
        add_computation_pattern_variable state identifier;
        let x' = Name.make_from_identifier identifier in
        Synapx.Comp.PatFVar (location, x')
    | Synext.Comp.Pattern.Wildcard { location } ->
        let x = fresh_identifier state in
        add_computation_pattern_variable state x;
        let x' = Name.make_from_identifier x in
        Synapx.Comp.PatFVar (location, x')
    | Synext.Comp.Pattern.Constructor { location; identifier } ->
        let id = index_of_comp_constructor state identifier in
        let spine = Synapx.Comp.PatNil location in
        Synapx.Comp.PatConst (location, id, spine)
    | Synext.Comp.Pattern.Meta_object { location; meta_pattern } ->
        let meta_pattern' = index_meta_pattern state meta_pattern in
        Synapx.Comp.PatMetaObj (location, meta_pattern')
    | Synext.Comp.Pattern.Tuple { location; elements } ->
        let elements' = traverse_list2 state index_comp_pattern elements in
        Synapx.Comp.PatTuple (location, elements')
    | Synext.Comp.Pattern.Type_annotated { location; pattern; typ } ->
        let pattern' = index_comp_pattern state pattern in
        let typ' = index_comp_typ state typ in
        Synapx.Comp.PatAnn (location, pattern', typ')
    | Synext.Comp.Pattern.Application { applicand; arguments; location = _ }
      -> (
        match index_comp_pattern state applicand with
        | Synapx.Comp.PatConst (applicand_location, id, Synapx.Comp.PatNil _)
          ->
            let spine' =
              index_applicative_comp_pattern_spine state arguments
            in
            Synapx.Comp.PatConst (applicand_location, id, spine')
        | _ ->
            Error.raise_at1
              (Synext.location_of_comp_pattern applicand)
              Unsupported_comp_pattern_applicand)

  and index_applicative_comp_pattern_spine_list1 state
      (List1.T (x, xs) as patterns) =
    match xs with
    | [] ->
        let pattern' = index_comp_pattern state x in
        let location = Synext.location_of_comp_pattern x in
        Synapx.Comp.PatApp
          ( location
          , pattern'
          , Synapx.Comp.PatNil
              (Location.join_all1_contramap Synext.location_of_comp_pattern
                 patterns) )
    | x2 :: xs ->
        let pattern' = index_comp_pattern state x in
        let spine' =
          index_applicative_comp_pattern_spine_list1 state (List1.from x2 xs)
        in
        let location = Synext.location_of_comp_pattern x in
        Synapx.Comp.PatApp (location, pattern', spine')

  and index_applicative_comp_pattern_spine state patterns =
    index_applicative_comp_pattern_spine_list1 state patterns

  and index_case_branch state
      { Synext.Comp.Case_branch.location; meta_context; pattern; body } =
    with_free_variables_as_pattern_variables state
      ~pattern:(fun state ->
        with_indexed_meta_context_pattern state meta_context
          (fun state meta_context' ->
            let pattern' = index_comp_pattern state pattern in
            (meta_context', pattern')))
      ~expression:(fun state (meta_context', pattern') ->
        let pattern'' = reindex_pattern state pattern' in
        let body' = index_comp_expression state body in
        Synapx.Comp.Branch (location, meta_context', pattern'', body'))

  and index_comp_pattern_with_location state pattern =
    let location = Synext.location_of_comp_pattern pattern in
    let pattern' = index_comp_pattern state pattern in
    (location, pattern')

  and index_comp_copattern state
      { Synext.Comp.Copattern.location; patterns; observations } =
    let patterns' =
      traverse_list state index_comp_pattern_with_location patterns
    in
    let observations' =
      traverse_list state
        (fun state (destructor, patterns) ->
          let location = Qualified_identifier.location destructor in
          let index = index_of_comp_destructor state destructor in
          let patterns' =
            traverse_list state index_comp_pattern_with_location patterns
          in
          (location, index, patterns'))
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
    add_patterns' patterns'
      (add_observations' observations' (Synapx.Comp.PatNil location))

  and index_cofunction_branch state
      { Synext.Comp.Cofunction_branch.location
      ; meta_context
      ; copattern
      ; body
      } =
    match meta_context.Synext.Meta.Context.bindings with
    | [] ->
        with_free_variables_as_pattern_variables state
          ~pattern:(fun state -> index_comp_copattern state copattern)
          ~expression:(fun state copattern' ->
            let copattern'' = reindex_pattern_spine state copattern' in
            let body' = index_comp_expression state body in
            (location, copattern'', body'))
    | _ -> Error.raise_at1 location Unsupported_copattern_meta_context

  and with_indexed_comp_context_binding state (identifier, typ) f =
    let name = Name.make_from_identifier identifier in
    let typ' = index_comp_typ state typ in
    with_bound_comp_variable state identifier (fun state ->
        f state (Synapx.Comp.CTypDecl (name, typ')))

  and with_indexed_comp_context_bindings state bindings f =
    match bindings with
    | [] -> f state []
    | x :: xs ->
        with_indexed_comp_context_binding state x (fun state y ->
            with_indexed_comp_context_bindings state xs (fun state ys ->
                f state (y :: ys)))

  and with_indexed_comp_context state
      { Synext.Comp.Context.bindings; location = _ } f =
    with_indexed_comp_context_bindings state bindings (fun state bindings' ->
        f state
          (List.fold_left (* TODO: Construct the context on the fly *)
             (fun accumulator binding' ->
               Synapx.LF.Dec (accumulator, binding'))
             Synapx.LF.Empty bindings'))

  let rec index_harpoon_proof state = function
    | Synext.Harpoon.Proof.Incomplete { location; label } ->
        let name = Option.map Identifier.name label in
        Synapx.Comp.Incomplete (location, name)
    | Synext.Harpoon.Proof.Command { location; command; body } ->
        with_indexed_harpoon_command state command (fun state command' ->
            let body' = index_harpoon_proof state body in
            Synapx.Comp.Command (location, command', body'))
    | Synext.Harpoon.Proof.Directive { location; directive } ->
        let directive = index_harpoon_directive state directive in
        Synapx.Comp.Directive (location, directive)

  and with_indexed_harpoon_command state command f =
    match command with
    | Synext.Harpoon.Command.By { location; expression; assignee } ->
        let expression' = index_comp_expression state expression in
        let x = Name.make_from_identifier assignee in
        with_bound_comp_variable state assignee (fun state ->
            f state (Synapx.Comp.By (location, expression', x)))
    | Synext.Harpoon.Command.Unbox
        { location; expression; assignee; modifier } ->
        let expression' = index_comp_expression state expression in
        let x = Name.make_from_identifier assignee in
        with_bound_contextual_variable state assignee (fun state ->
            f state (Synapx.Comp.Unbox (location, expression', x, modifier)))

  and index_harpoon_directive state = function
    | Synext.Harpoon.Directive.Intros { location; hypothetical } ->
        let hypothetical' = index_harpoon_hypothetical state hypothetical in
        Synapx.Comp.Intros (location, hypothetical')
    | Synext.Harpoon.Directive.Solve { location; solution } ->
        let solution' = index_comp_expression state solution in
        Synapx.Comp.Solve (location, solution')
    | Synext.Harpoon.Directive.Split { location; scrutinee; branches } ->
        let scrutinee' = index_comp_expression state scrutinee in
        let branches' =
          traverse_list1 state index_harpoon_split_branch branches
        in
        Synapx.Comp.Split (location, scrutinee', List1.to_list branches')
    | Synext.Harpoon.Directive.Impossible { location; scrutinee } ->
        let scrutinee' = index_comp_expression state scrutinee in
        (* TODO: The approximate syntax should have an [Impossible _]
           constructor *)
        Synapx.Comp.Split (location, scrutinee', [])
    | Synext.Harpoon.Directive.Suffices { location; scrutinee; branches } ->
        let scrutinee' = index_comp_expression state scrutinee in
        let branches' =
          traverse_list state index_harpoon_suffices_branch branches
        in
        Synapx.Comp.Suffices (location, scrutinee', branches')

  and index_harpoon_split_branch state
      { Synext.Harpoon.Split_branch.location; label; body } =
    let label' = index_harpoon_split_branch_label state label in
    let body' = index_harpoon_hypothetical state body in
    { Synapx.Comp.case_label = label'
    ; branch_body = body'
    ; split_branch_loc = location
    }

  and index_harpoon_split_branch_label state = function
    | Synext.Harpoon.Split_branch.Label.Lf_constant { location; identifier }
      ->
        let cid = index_of_lf_term_constant state identifier in
        let name = Name.make_from_qualified_identifier identifier in
        Synapx.Comp.Lf_constant (location, name, cid)
    | Synext.Harpoon.Split_branch.Label.Comp_constant
        { location; identifier } ->
        let cid = index_of_comp_constructor state identifier in
        let name = Name.make_from_qualified_identifier identifier in
        Synapx.Comp.Comp_constant (location, name, cid)
    | Synext.Harpoon.Split_branch.Label.Bound_variable { location } ->
        Synapx.Comp.BVarCase location
    | Synext.Harpoon.Split_branch.Label.Empty_context { location } ->
        Synapx.Comp.ContextCase (Synapx.Comp.EmptyContext location)
    | Synext.Harpoon.Split_branch.Label.Extended_context
        { location; schema_element } ->
        Synapx.Comp.ContextCase
          (Synapx.Comp.ExtendedBy (location, schema_element))
    | Synext.Harpoon.Split_branch.Label.Parameter_variable
        { location; schema_element; projection } ->
        Synapx.Comp.PVarCase (location, schema_element, projection)

  and index_harpoon_suffices_branch state
      { Synext.Harpoon.Suffices_branch.location; goal; proof } =
    let goal' = index_comp_typ state goal in
    let proof' = index_harpoon_proof state proof in
    (location, goal', proof')

  and index_harpoon_hypothetical state
      { Synext.Harpoon.Hypothetical.location
      ; meta_context
      ; comp_context
      ; proof
      } =
    with_parent_scope state (fun state ->
        with_indexed_meta_context state meta_context
          (fun state meta_context' ->
            with_indexed_comp_context state comp_context
              (fun state comp_context' ->
                let proof' = index_harpoon_proof state proof in
                Synapx.Comp.
                  { hypotheses = { cD = meta_context'; cG = comp_context' }
                  ; proof = proof'
                  ; hypothetical_loc = location
                  })))

  let index_open_lf_kind state kind =
    allow_free_variables state (fun state -> index_lf_kind state kind)

  let index_closed_lf_kind state kind =
    disallow_free_variables state (fun state -> index_lf_kind state kind)

  let index_open_lf_typ state typ =
    allow_free_variables state (fun state -> index_lf_typ state typ)

  let index_closed_lf_typ state typ =
    disallow_free_variables state (fun state -> index_lf_typ state typ)

  let index_open_comp_kind state kind =
    allow_free_variables state (fun state -> index_comp_kind state kind)

  let index_closed_comp_kind state kind =
    disallow_free_variables state (fun state -> index_comp_kind state kind)

  let index_open_comp_typ state typ =
    allow_free_variables state (fun state -> index_comp_typ state typ)

  let index_closed_comp_typ state typ =
    disallow_free_variables state (fun state -> index_comp_typ state typ)

  let index_comp_expression state expression =
    disallow_free_variables state (fun state ->
        index_comp_expression state expression)

  let index_schema state schema =
    allow_free_variables state (fun state -> index_schema state schema)

  let index_comp_theorem state theorem =
    disallow_free_variables state (fun state ->
        let theorem' = index_comp_expression state theorem in
        Synapx.Comp.Program theorem')

  let index_harpoon_proof state proof =
    disallow_free_variables state (fun state ->
        let proof' =
          with_scope state (fun state -> index_harpoon_proof state proof)
        in
        Synapx.Comp.Proof proof')

  let index_computation_typ_abbreviation state typ kind =
    let kind' =
      disallow_free_variables state (fun state -> index_comp_kind state kind)
    in
    let rec with_unrolled_kind state kind f =
      match kind with
      | Synext.Comp.Kind.Pi
          { parameter_identifier
          ; parameter_type
          ; body
          ; plicity = _
          ; location = _
          } ->
          with_meta_level_binding_opt state parameter_identifier
            parameter_type (fun state -> with_unrolled_kind state body f)
      | Synext.Comp.Kind.Arrow { range; domain = _; location = _ } ->
          with_unrolled_kind state range f
      | Synext.Comp.Kind.Ctype _ -> f state
    in
    let typ' =
      disallow_free_variables state (fun state ->
          with_unrolled_kind state kind (fun state ->
              index_comp_typ state typ))
    in
    (typ', kind')
end

module Indexer = Make_indexer (Index_state.Indexing_state)
