open Support
open Beluga_syntax

[@@@warning "-A-4-44"]

module Make (Indexing_state : sig
  include State.STATE

  val bind_lf_variable : Identifier.t -> Unit.t t

  val bind_meta_variable : Identifier.t -> Unit.t t

  val bind_comp_variable : Identifier.t -> Unit.t t

  val pop_binding : Identifier.t -> Unit.t t

  (** [fresh_identifier state] is [(state', identifier)] where [identifier]
      is an identifier that is not bound in [state]. This is used in the
      indexing of arrow types to Pi-types, and to generate parameter
      identifiers for lambda abstractions. In order to avoid potential
      captures, [identifier] is not a valid identifier for the parser. *)
  val fresh_identifier : Identifier.t t

  val fresh_identifier_opt : Identifier.t Option.t -> Identifier.t t

  val index_of_lf_typ_constant : Qualified_identifier.t -> Id.cid_typ t

  val index_of_lf_term_constant : Qualified_identifier.t -> Id.cid_term t

  val index_of_inductive_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_typ t

  val index_of_stratified_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_typ t

  val index_of_coinductive_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_cotyp t

  val index_of_abbreviation_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_typdef t

  val index_of_schema_constant : Qualified_identifier.t -> Id.cid_schema t

  val index_of_comp_destructor : Qualified_identifier.t -> Id.cid_comp_dest t

  val index_of_lf_variable : Identifier.t -> Id.offset t

  val index_of_parameter_variable : Identifier.t -> Id.offset t

  val index_of_substitution_variable : Identifier.t -> Id.offset t

  val index_of_context_variable : Identifier.t -> Id.offset t

  val with_bound_lf_variable : Identifier.t -> 'a t -> 'a t

  val with_meta_variable : Identifier.t -> 'a t -> 'a t

  val with_bound_comp_variable : Identifier.t -> 'a t -> 'a t

  val with_pattern_variables_checkpoint :
    pattern:'a t -> expression:'b t -> ('a * 'b) t

  val with_bindings_checkpoint : 'a t -> 'a t
end) =
struct
  include Indexing_state

  let fresh_identifier_opt identifier_opt =
    match identifier_opt with
    | Option.Some identifier -> return identifier
    | Option.None -> fresh_identifier

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
        (* TODO: Check whether the variable is bound *)
        let* offset = index_of_lf_variable identifier in
        return
          (Synapx.LF.Root (location, Synapx.LF.BVar offset, Synapx.LF.Nil))
    (*= | Synext.LF.Term.Free_variable { location; identifier } ->
        let name = Name.make_from_identifier identifier in
        let closure = Option.none in
        return
          (Synapx.LF.Root
             (location, Synapx.LF.FMVar (name, closure), Synapx.LF.Nil)) *)
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
        (* TODO: Check whether the variable is bound *)
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
        (* TODO: Check whether the variable is bound *)
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

  and index_clf_context = function
    | { Synext.CLF.Context.head = Synext.CLF.Context.Head.None _
      ; bindings = []
      ; _
      } ->
        return Synapx.LF.Null
    | { Synext.CLF.Context.head = Synext.CLF.Context.Head.None _
      ; bindings = _ :: _
      ; _
      } ->
        Obj.magic ()
    | { Synext.CLF.Context.head = Synext.CLF.Context.Head.Hole _
      ; bindings
      ; _
      } ->
        Obj.magic ()
    | { Synext.CLF.Context.head =
          Synext.CLF.Context.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
        let* index = index_of_context_variable identifier in
        Obj.magic ()

  exception Unsupported_context_schema_meta_typ

  exception Unsupported_context_schema_element

  let rec index_meta_object = function
    | Synext.Meta.Object.Context { location; context } ->
        (* TODO: Can be a free [CtxName] *) Obj.magic ()
    | Synext.Meta.Object.Contextual_term { location; context; term } ->
        Obj.magic ()
    | Synext.Meta.Object.Plain_substitution { location; domain; range } ->
        Obj.magic ()
    | Synext.Meta.Object.Renaming_substitution { location; domain; range } ->
        Obj.magic ()

  and index_meta_type = function
    | Synext.Meta.Typ.Context_schema { location; schema } -> (
        match schema with
        | Synext.Meta.Schema.Constant { identifier; _ } ->
            let* index = index_of_schema_constant identifier in
            return (Synapx.LF.CTyp index)
        | Synext.Meta.Schema.Alternation _
        | Synext.Meta.Schema.Element _ ->
            Error.raise_at1 location Unsupported_context_schema_meta_typ)
    | Synext.Meta.Typ.Contextual_typ { context; typ; _ } ->
        let* context', typ' =
          with_bindings_checkpoint
            (seq2 (index_clf_context context) (index_clf_typ typ))
        in
        return (Synapx.LF.ClTyp (Synapx.LF.MTyp typ', context'))
    | Synext.Meta.Typ.Parameter_typ { context; typ; _ } ->
        let* context', typ' =
          with_bindings_checkpoint
            (seq2 (index_clf_context context) (index_clf_typ typ))
        in
        return (Synapx.LF.ClTyp (Synapx.LF.PTyp typ', context'))
    | Synext.Meta.Typ.Plain_substitution_typ { location; domain; range } ->
        Obj.magic ()
    | Synext.Meta.Typ.Renaming_substitution_typ { location; domain; range }
      ->
        Obj.magic ()

  and index_schema = function
    | Synext.Meta.Schema.Alternation { schemas; _ } ->
        let* schemas' = traverse_list2 index_schema_element schemas in
        let schemas'' = List2.to_list schemas' in
        return (Synapx.LF.Schema schemas'')
    | (Synext.Meta.Schema.Constant _ | Synext.Meta.Schema.Element _) as
      element ->
        let* element' = index_schema_element element in
        return (Synapx.LF.Schema [ element' ])

  and index_schema_element = function
    | Synext.Meta.Schema.Element { location; some; block } -> Obj.magic ()
    | Synext.Meta.Schema.Constant { location; _ }
    | Synext.Meta.Schema.Alternation { location; _ } ->
        Error.raise_at1 location Unsupported_context_schema_element

  and index_meta_pattern = function
    | Synext.Meta.Pattern.Context { location; context } -> Obj.magic ()
    | Synext.Meta.Pattern.Contextual_term { location; context; term } ->
        Obj.magic ()
    | Synext.Meta.Pattern.Plain_substitution { location; domain; range } ->
        Obj.magic ()
    | Synext.Meta.Pattern.Renaming_substitution { location; domain; range }
      ->
        Obj.magic ()

  and index_meta_context = function
    | { Synext.Meta.Context.location; bindings } ->
        (* TODO: Traverse and index dependently *) Obj.magic ()

  exception Unsupported_comp_typ_applicand

  exception Unsupported_wildcard_comp_pattern

  let rec index_comp_kind = function
    | Synext.Comp.Kind.Ctype { location } ->
        return (Synapx.Comp.Ctype location)
    | Synext.Comp.Kind.Arrow { location; domain; range } ->
        let* x = fresh_identifier in
        let* domain' = index_meta_type domain in
        let* range' = (with_bound_comp_variable x) (index_comp_kind range) in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.Comp.PiKind
             ( location
             , Synapx.LF.Decl (x', domain', Plicity.explicit)
             , range' ))
    | Synext.Comp.Kind.Pi
        { location; parameter_identifier; plicity; parameter_type; body } ->
        let* x = fresh_identifier_opt parameter_identifier in
        let* parameter_type' = index_meta_type parameter_type in
        let* body' = (with_bound_comp_variable x) (index_comp_kind body) in
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
        let* x = fresh_identifier_opt parameter_identifier in
        let* parameter_type' = index_meta_type parameter_type in
        let* body' = (with_meta_variable x) (index_comp_typ body) in
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
        Obj.magic ()
    | Synext.Comp.Expression.Constructor
        { location; identifier; operator; prefixed } ->
        Obj.magic ()
    | Synext.Comp.Expression.Program
        { location; identifier; operator; prefixed } ->
        Obj.magic ()
    | Synext.Comp.Expression.Fn { location; parameters; body } ->
        Obj.magic ()
    | Synext.Comp.Expression.Mlam { location; parameters; body } ->
        Obj.magic ()
    | Synext.Comp.Expression.Fun { location; branches } -> Obj.magic ()
    | Synext.Comp.Expression.Let { location; pattern; scrutinee; body } -> (
        let* scrutinee' = index_comp_expression scrutinee in
        let* (meta_context', pattern'), body' =
          with_bindings_checkpoint
            (seq2
               (index_comp_pattern_with_meta_type_annotations pattern)
               (index_comp_expression body))
        in
        match pattern with
        | Synext.Comp.Pattern.Variable { identifier; _ } ->
            (* The approximate syntax does not support general patterns in
               [let]-expressions, so only [let]-expressions with a variable
               pattern are translated to [let]-expressions in the approximate
               syntax. *)
            let x' = Name.make_from_identifier identifier in
            return (Synapx.Comp.Let (location, scrutinee', (x', body')))
        | _ ->
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
        Obj.magic ()
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

  and index_comp_pattern = function
    | Synext.Comp.Pattern.Variable { location; identifier } -> Obj.magic ()
    | Synext.Comp.Pattern.Constant { location; identifier; _ } ->
        Obj.magic ()
    | Synext.Comp.Pattern.Meta_object { location; meta_pattern } ->
        let* meta_pattern' = index_meta_pattern meta_pattern in
        return (Synapx.Comp.PatMetaObj (location, meta_pattern'))
    | Synext.Comp.Pattern.Tuple { location; elements } ->
        let* elements' = traverse_list2 index_comp_pattern elements in
        return (Synapx.Comp.PatTuple (location, elements'))
    | Synext.Comp.Pattern.Application { location; applicand; arguments } ->
        Obj.magic ()
    | Synext.Comp.Pattern.Type_annotated { location; pattern; typ } ->
        let* typ' = index_comp_typ typ in
        let* pattern' = index_comp_pattern pattern in
        return (Synapx.Comp.PatAnn (location, pattern', typ'))
    | Synext.Comp.Pattern.Wildcard { location } ->
        (* TODO: Generate a fresh identifier not in the pattern *)
        Error.raise_at1 location Unsupported_wildcard_comp_pattern

  and index_comp_pattern_with_meta_type_annotations = Obj.magic () (* TODO: *)

  and index_branch pattern body =
    let location =
      Location.join
        (Synext.location_of_comp_pattern pattern)
        (Synext.location_of_comp_expression body)
    in
    Obj.magic () (* TODO: *)

  and index_comp_copattern = Obj.magic () (* TODO: *)

  and index_comp_context = function
    | { Synext.Comp.Context.location; bindings } ->
        (* TODO: Traverse and index, dependently? *) Obj.magic ()

  let rec index_harpoon_proof = function
    | Synext.Harpoon.Proof.Incomplete { location; label } ->
        let name = Option.map Identifier.name label in
        return (Synapx.Comp.Incomplete (location, name))
    | Synext.Harpoon.Proof.Command { location; command; body } ->
        let* command', body' =
          with_bindings_checkpoint
            (seq2 (index_harpoon_command command) (index_harpoon_proof body))
        in
        return (Synapx.Comp.Command (location, command', body'))
    | Synext.Harpoon.Proof.Directive { location; directive } -> Obj.magic ()

  and index_harpoon_command = function
    | Synext.Harpoon.Command.By { location; expression; assignee } ->
        let* expression' = index_comp_expression expression in
        let* () = bind_comp_variable assignee in
        let x = Name.make_from_identifier assignee in
        return (Synapx.Comp.By (location, expression', x))
    | Synext.Harpoon.Command.Unbox
        { location; expression; assignee; modifier } ->
        let* expression' = index_comp_expression expression in
        let* () = bind_meta_variable assignee in
        let x = Name.make_from_identifier assignee in
        let modifier' =
          match modifier with
          | Option.Some `Strengthened -> Option.some `strengthened
          | Option.None -> Option.none
        in
        return (Synapx.Comp.Unbox (location, expression', x, modifier'))

  and index_harpoon_directive = function
    | Synext.Harpoon.Directive.Intros { location; hypothetical } ->
        Obj.magic ()
    | Synext.Harpoon.Directive.Solve { location; solution } -> Obj.magic ()
    | Synext.Harpoon.Directive.Split { location; scrutinee; branches } ->
        Obj.magic ()
    | Synext.Harpoon.Directive.Impossible { location; scrutinee } ->
        Obj.magic ()
    | Synext.Harpoon.Directive.Suffices { location; scrutinee; branches } ->
        Obj.magic ()

  and index_harpoon_hypothetical = function
    | { Synext.Harpoon.Hypothetical.location
      ; meta_context
      ; comp_context
      ; proof
      } ->
        let* meta_context', comp_context', proof' =
          with_bindings_checkpoint
            (seq3
               (index_meta_context meta_context)
               (index_comp_context comp_context)
               (index_harpoon_proof proof))
        in
        return
          Synapx.Comp.
            { hypotheses = { cD = meta_context'; cG = comp_context' }
            ; proof = proof'
            ; hypothetical_loc = location
            }
end
