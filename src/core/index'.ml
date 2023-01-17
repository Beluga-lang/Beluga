open Support
open Beluga_syntax

[@@@warning "+A-4-44"]

module Make (Indexing_state : sig
  include State.STATE

  val bind_lf_variable : Identifier.t -> Unit.t t

  val pop_binding : Identifier.t -> Unit.t t

  val fresh_identifier : Identifier.t t

  val index_of_lf_typ_constant : Qualified_identifier.t -> Id.cid_typ t

  val index_of_lf_term_constant : Qualified_identifier.t -> Id.cid_term t

  val index_of_lf_variable : Identifier.t -> Id.offset t

  val index_of_parameter_variable : Identifier.t -> Id.offset t

  val index_of_substitution_variable : Identifier.t -> Id.offset t
end) =
struct
  include Indexing_state

  let fresh_identifier_opt identifier_opt =
    match identifier_opt with
    | Option.Some identifier -> return identifier
    | Option.None -> fresh_identifier

  let with_bound_lf_variable identifier =
    scoped
      ~set:(Indexing_state.bind_lf_variable identifier)
      ~unset:(Indexing_state.pop_binding identifier)

  let rec append_lf_spines spine1 spine2 =
    match spine1 with
    | Synapx.LF.Nil -> spine2
    | Synapx.LF.App (x, sub_spine1) ->
        let spine' = append_lf_spines sub_spine1 spine2 in
        Synapx.LF.App (x, spine')

  exception Unsupported_lf_typ_applicand

  exception Unsupported_lf_term_applicand

  exception Unsupported_lf_annotated_term_abstraction

  exception Unsupported_lf_untyped_pi_kind_parameter

  exception Unsupported_lf_untyped_pi_typ_parameter

  let rec index_lf_kind =
    let index_as_lf_pi_kind ~x ~parameter_type ~body =
      let* domain' = index_lf_typ parameter_type in
      let* range' = (with_bound_lf_variable x) (index_lf_kind body) in
      let x' = Name.make_from_identifier x in
      return
        (Synapx.LF.PiKind
           ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
    in
    function
    | Synext.LF.Kind.Typ _ -> return Synapx.LF.Typ
    | Synext.LF.Kind.Arrow { domain; range; _ } ->
        let* x = fresh_identifier in
        index_as_lf_pi_kind ~x ~parameter_type:domain ~body:range
    | Synext.LF.Kind.Pi
        { parameter_identifier; parameter_type; body; location } -> (
        match parameter_type with
        | Option.None ->
            Error.raise_at1 location Unsupported_lf_untyped_pi_kind_parameter
        | Option.Some parameter_type ->
            let* x = fresh_identifier_opt parameter_identifier in
            index_as_lf_pi_kind ~x ~parameter_type ~body)

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
        let* x = fresh_identifier in
        let* domain' = index_lf_typ domain in
        let* range' = (with_bound_lf_variable x) (index_lf_typ range) in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.LF.PiTyp
             ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
    | Synext.LF.Typ.Pi
        { parameter_identifier; parameter_type; body; location } -> (
        match parameter_type with
        | Option.None ->
            Error.raise_at1 location Unsupported_lf_untyped_pi_typ_parameter
        | Option.Some parameter_type ->
            let* x = fresh_identifier_opt parameter_identifier in
            let* domain' = index_lf_typ parameter_type in
            let* range' = (with_bound_lf_variable x) (index_lf_typ body) in
            let x' = Name.make_from_identifier x in
            return
              (Synapx.LF.PiTyp
                 ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
        )

  and index_lf_term = function
    | Synext.LF.Term.Variable { location; identifier } ->
        let* offset = index_of_lf_variable identifier in
        return
          (Synapx.LF.Root (location, Synapx.LF.BVar offset, Synapx.LF.Nil))
    | Synext.LF.Term.Constant { location; identifier; _ } ->
        let* id = index_of_lf_term_constant identifier in
        return (Synapx.LF.Root (location, Synapx.LF.Const id, Synapx.LF.Nil))
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
            let* x = fresh_identifier_opt parameter_identifier in
            let* body' = (with_bound_lf_variable x) (index_lf_term body) in
            let x' = Name.make_from_identifier x in
            return (Synapx.LF.Lam (location, x', body'))
        | Option.Some _typ ->
            Error.raise_at1 location
              Unsupported_lf_annotated_term_abstraction)
    | Synext.LF.Term.Wildcard { location } ->
        let* x = fresh_identifier in
        let x' = Name.make_from_identifier x in
        let substitution = Option.none in
        let head = Synapx.LF.FMVar (x', substitution) in
        return (Synapx.LF.Root (location, head, Synapx.LF.Nil))
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

  exception Illegal_clf_substitution_variable_outside_substitution

  exception
    Unsupported_clf_substitution_variable_not_at_start_of_substitution

  exception Unsupported_clf_projection_applicand

  exception Unsupported_clf_substitution_applicand

  let rec index_clf_typ = function
    | Synext.CLF.Typ.Constant { identifier; location; _ } ->
        let* id = index_of_lf_typ_constant identifier in
        return (Synapx.LF.Atom (location, id, Synapx.LF.Nil))
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
        let* x = fresh_identifier in
        let* domain' = index_clf_typ domain in
        let* range' = (with_bound_lf_variable x) (index_clf_typ range) in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.LF.PiTyp
             ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
    | Synext.CLF.Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
        let* x = fresh_identifier_opt parameter_identifier in
        let* domain' = index_clf_typ parameter_type in
        let* range' = (with_bound_lf_variable x) (index_clf_typ body) in
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

  and index_clf_block_bindings = function
    | List1.T ((identifier, typ), []) ->
        let* typ' = index_clf_typ typ in
        let name_opt = Option.some (Name.make_from_identifier identifier) in
        return (Synapx.LF.SigmaLast (name_opt, typ'))
    | List1.T ((identifier, typ), x :: xs) ->
        let* typ' = index_clf_typ typ in
        let name = Name.make_from_identifier identifier in
        let* bindings' =
          (with_bound_lf_variable identifier)
            (index_clf_block_bindings (List1.from x xs))
        in
        return (Synapx.LF.SigmaElem (name, typ', bindings'))

  and index_clf_term = function
    | Synext.CLF.Term.Variable { location; identifier } ->
        let* offset = index_of_lf_variable identifier in
        return
          (Synapx.LF.Root (location, Synapx.LF.BVar offset, Synapx.LF.Nil))
    | Synext.CLF.Term.Constant { location; identifier; _ } ->
        let* id = index_of_lf_term_constant identifier in
        return (Synapx.LF.Root (location, Synapx.LF.Const id, Synapx.LF.Nil))
    | Synext.CLF.Term.Application { location; applicand; arguments } -> (
        match applicand with
        | Synext.CLF.Term.Variable _
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
        | Synext.CLF.Term.Substitution_variable _
        | Synext.CLF.Term.Tuple _ ->
            Error.raise_at1
              (Synext.location_of_clf_term applicand)
              Unsupported_lf_term_applicand)
    | Synext.CLF.Term.Abstraction
        { location; parameter_identifier; parameter_type; body } -> (
        match parameter_type with
        | Option.None ->
            let* x = fresh_identifier_opt parameter_identifier in
            let* body' = (with_bound_lf_variable x) (index_clf_term body) in
            let x' = Name.make_from_identifier x in
            return (Synapx.LF.Lam (location, x', body'))
        | Option.Some _typ ->
            Error.raise_at1 location
              Unsupported_lf_annotated_term_abstraction)
    | Synext.CLF.Term.Hole { variant; location } -> (
        match variant with
        | `Underscore ->
            let head = Synapx.LF.Hole in
            return (Synapx.LF.Root (location, head, Synapx.LF.Nil))
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
    | Synext.CLF.Term.Parameter_variable { identifier; location } ->
        let* offset = index_of_parameter_variable identifier in
        let closure = Option.none in
        let head = Synapx.LF.PVar (Synapx.LF.Offset offset, closure) in
        return (Synapx.LF.Root (location, head, Synapx.LF.Nil))
    | Synext.CLF.Term.Substitution_variable { location; _ } ->
        Error.raise_at1 location
          Illegal_clf_substitution_variable_outside_substitution
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
        let* tuple =
          List1.fold_right
            (fun last ->
              let* last' = index_clf_term last in
              return (Synapx.LF.Last last'))
            (fun term tuple ->
              let* term' = index_clf_term term in
              let* tuple' = tuple in
              return (Synapx.LF.Cons (term', tuple')))
            terms
        in
        return (Synapx.LF.Tuple (location, tuple))

  and index_clf_substitution =
    (* TODO: It is unclear why not all values [h] of type
       {!type:Synapx.LF.head} are mapped to [Synapx.LF.Head h] when the spine
       is [Synapx.LF.Nil]. This function was introduced in commit 95578f0e
       ("Improved parsing of substitutions", 2015-05-25). *)
    let to_head_or_obj = function
      | Synapx.LF.Root (_, (Synapx.LF.BVar _ as h), Synapx.LF.Nil)
      | Synapx.LF.Root (_, (Synapx.LF.PVar _ as h), Synapx.LF.Nil)
      | Synapx.LF.Root (_, (Synapx.LF.Proj _ as h), Synapx.LF.Nil) ->
          Synapx.LF.Head h
      | tM -> Synapx.LF.Obj tM
    in
    let index_clf_term = function
      | Synext.CLF.Term.Substitution_variable { location; _ } ->
          Error.raise_at1 location
            Unsupported_clf_substitution_variable_not_at_start_of_substitution
      | x -> index_clf_term x
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
        , [] ) ->
          let* offset = index_of_substitution_variable identifier in
          let* closure' = traverse_option index_clf_substitution closure in
          return (Synapx.LF.SVar (Synapx.LF.Offset offset, closure'))
    in
    fun substitution ->
      let { Synext.CLF.Substitution.head; terms; _ } = substitution in
      index_clf_substitution' head terms

  and index_clf_spine arguments =
    List1.fold_right
      (fun argument ->
        let* argument' = index_clf_term argument in
        return (Synapx.LF.App (argument', Synapx.LF.Nil)))
      (fun argument spine ->
        let* argument' = index_clf_term argument in
        let* spine' = spine in
        return (Synapx.LF.App (argument', spine')))
      arguments
end
