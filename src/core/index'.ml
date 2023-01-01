open Support
open Beluga_syntax

[@@@warning "+A-4-44"]

module Make (Indexing_state : sig
  type t

  val bind_lf_variable : Identifier.t -> t -> t

  val fresh_identifier : t -> Identifier.t

  val index_of_lf_typ_constant : Qualified_identifier.t -> t -> Id.cid_typ

  val index_of_lf_term_constant : Qualified_identifier.t -> t -> Id.cid_term

  val index_of_lf_variable : Identifier.t -> t -> Id.offset
end) =
struct
  include State.Make (Indexing_state)

  let fresh_identifier = get $> Indexing_state.fresh_identifier

  let fresh_identifier_opt identifier_opt =
    match identifier_opt with
    | Option.Some identifier -> return identifier
    | Option.None -> fresh_identifier

  let bind_lf_variable = Indexing_state.bind_lf_variable

  let index_of_lf_typ_constant qualified_identifier =
    get $> Indexing_state.index_of_lf_typ_constant qualified_identifier

  let index_of_lf_term_constant qualified_identifier =
    get $> Indexing_state.index_of_lf_term_constant qualified_identifier

  let index_of_lf_variable identifier =
    get $> Indexing_state.index_of_lf_variable identifier

  exception Unsupported_lf_typ_applicand

  exception Unsupported_lf_term_applicand

  exception Unsupported_lf_annotated_term_abstraction

  let rec append_lf_spines spine1 spine2 =
    match spine1 with
    | Synapx.LF.Nil -> spine2
    | Synapx.LF.App (x, sub_spine1) ->
        let spine' = append_lf_spines sub_spine1 spine2 in
        Synapx.LF.App (x, spine')

  let rec index_lf_kind kind =
    let index_as_lf_pi_kind ~x ~domain ~range =
      let* domain' = index_lf_typ domain in
      let* range' = locally (bind_lf_variable x) (index_lf_kind range) in
      let x' = Name.make_from_identifier x in
      return
        (Synapx.LF.PiKind
           ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
    in
    match kind with
    | Synext.LF.Kind.Typ _ -> return Synapx.LF.Typ
    | Synext.LF.Kind.Arrow { domain; range; _ } ->
        let* x = fresh_identifier in
        index_as_lf_pi_kind ~x ~domain ~range
    | Synext.LF.Kind.Pi { parameter_identifier; parameter_type; body; _ } ->
        let* x = fresh_identifier_opt parameter_identifier in
        index_as_lf_pi_kind ~x ~domain:parameter_type ~range:body

  and index_lf_typ typ =
    match typ with
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
                let* spine2' = index_spine arguments in
                let spine' = append_lf_spines spine1' spine2' in
                return (Synapx.LF.Atom (location, id, spine'))
            | Synapx.LF.PiTyp _
            | Synapx.LF.Sigma _ ->
                assert false
            (* Supported LF type-level applications are always translated to
               LF atoms *))
        | Synext.LF.Typ.Arrow _
        | Synext.LF.Typ.Pi _ ->
            Error.raise_at1
              (Synext.location_of_lf_typ applicand)
              Unsupported_lf_typ_applicand)
    | Synext.LF.Typ.Arrow { domain; range; _ } ->
        let* x = fresh_identifier in
        let* domain' = index_lf_typ domain in
        let* range' = locally (bind_lf_variable x) (index_lf_typ range) in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.LF.PiTyp
             ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))
    | Synext.LF.Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
        let* x = fresh_identifier_opt parameter_identifier in
        let* domain' = index_lf_typ parameter_type in
        let* range' = locally (bind_lf_variable x) (index_lf_typ body) in
        let x' = Name.make_from_identifier x in
        return
          (Synapx.LF.PiTyp
             ((Synapx.LF.TypDecl (x', domain'), Plicity.explicit), range'))

  and index_lf_term term =
    match term with
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
                let* spine2' = index_spine arguments in
                let spine' = append_lf_spines spine1' spine2' in
                return (Synapx.LF.Root (location, id, spine'))
            | Synapx.LF.Lam _
            | Synapx.LF.LFHole _
            | Synapx.LF.Tuple _
            | Synapx.LF.Ann _ ->
                assert false
            (* Supported LF term-level applications are always translated to
               LF roots *))
        | Synext.LF.Term.TypeAnnotated _
        | Synext.LF.Term.Abstraction _ ->
            Error.raise_at1
              (Synext.location_of_lf_term applicand)
              Unsupported_lf_term_applicand)
    | Synext.LF.Term.Abstraction
        { location; parameter_identifier; parameter_type; body } -> (
        match parameter_type with
        | Option.None ->
            let* x = fresh_identifier_opt parameter_identifier in
            let* body' = locally (bind_lf_variable x) (index_lf_term body) in
            let x' = Name.make_from_identifier x in
            return (Synapx.LF.Lam (location, x', body'))
        | Option.Some _typ ->
            Error.raise_at1
              (Synext.location_of_lf_term term)
              Unsupported_lf_annotated_term_abstraction)
    | Synext.LF.Term.Wildcard { location } ->
        let* x = fresh_identifier in
        let x' = Name.make_from_identifier x in
        let substitution = Option.none in
        let head = Synapx.LF.FMVar (x', substitution) in
        return (Synapx.LF.Root (location, head, Synapx.LF.Nil))
    | Synext.LF.Term.TypeAnnotated { location; term; typ } ->
        let* term' = index_lf_term term in
        let* typ' = index_lf_typ typ in
        return (Synapx.LF.Ann (location, term', typ'))

  and index_spine arguments =
    List1.fold_right
      (fun argument ->
        let* argument' = index_lf_term argument in
        return (Synapx.LF.App (argument', Synapx.LF.Nil)))
      (fun argument spine ->
        let* argument' = index_lf_term argument in
        let* spine' = spine in
        return (Synapx.LF.App (argument', spine')))
      arguments
end
