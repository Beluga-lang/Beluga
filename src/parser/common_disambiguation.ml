(** Disambiguation of the parser syntax to the external syntax.

    Elements of the syntax for Beluga require the symbol table for
    disambiguation. This module contains stateful functions for elaborating
    the context-free parser syntax to the data-dependent external syntax. The
    logic for the symbol lookups is repeated in the indexing phase to the
    approximate syntax.

    The "Beluga Language Specification" document contains additional details
    as to which syntactic structures have ambiguities. *)

open Support
open Beluga_syntax

exception Expected_namespace of Qualified_identifier.t

exception Expected_operator of Qualified_identifier.t

exception Unbound_identifier of Identifier.t

exception Unbound_qualified_identifier of Qualified_identifier.t

exception Unbound_namespace of Qualified_identifier.t

exception Bound_lf_type_constant of Qualified_identifier.t

exception Bound_lf_term_constant of Qualified_identifier.t

exception Bound_lf_term_variable of Qualified_identifier.t

exception Bound_meta_variable of Qualified_identifier.t

exception Bound_parameter_variable of Qualified_identifier.t

exception Bound_substitution_variable of Qualified_identifier.t

exception Bound_context_variable of Qualified_identifier.t

exception Bound_schema_constant of Qualified_identifier.t

exception Bound_computation_variable of Qualified_identifier.t

exception Bound_computation_inductive_type_constant of Qualified_identifier.t

exception
  Bound_computation_stratified_type_constant of Qualified_identifier.t

exception
  Bound_computation_coinductive_type_constant of Qualified_identifier.t

exception
  Bound_computation_abbreviation_type_constant of Qualified_identifier.t

exception Bound_computation_term_constructor of Qualified_identifier.t

exception Bound_computation_term_destructor of Qualified_identifier.t

exception Bound_query of Qualified_identifier.t

exception Bound_mquery of Qualified_identifier.t

exception Bound_module of Qualified_identifier.t

exception Bound_program_constant of Qualified_identifier.t

module type BINDINGS_STATE = sig
  include State.STATE

  type data = private
    { location : Location.t
    ; operator : Operator.t Option.t
    }

  type entry = private
    | Lf_type_constant
    | Lf_term_constant
    | Lf_term_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Schema_constant
    | Computation_variable
    | Computation_inductive_type_constant
    | Computation_stratified_type_constant
    | Computation_coinductive_type_constant
    | Computation_abbreviation_type_constant
    | Computation_term_constructor
    | Computation_term_destructor
    | Query
    | MQuery
    | Module
    | Program_constant

  val empty : state

  val get_bindings : (entry * data) List1.t Binding_tree.t t

  val add_lf_term_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_lf_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_lf_term_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_meta_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_context_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_schema_constant : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_computation_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_inductive_computation_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_stratified_computation_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_coinductive_computation_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_abbreviation_computation_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_computation_term_constructor :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_computation_term_destructor :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_query : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_mquery : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_module :
       ?location:Location.t
    -> (entry * data) List1.t Binding_tree.t
    -> Identifier.t
    -> Unit.t t

  val add_program_constant : ?location:Location.t -> Identifier.t -> Unit.t t

  val actual_binding_exn : Qualified_identifier.t -> entry * data -> exn

  val open_namespace : Qualified_identifier.t -> (Unit.t, exn) Result.t t

  val modify_operator :
    Qualified_identifier.t -> (Operator.t -> Operator.t) -> Unit.t t

  val lookup : Qualified_identifier.t -> (entry * data, exn) Result.t t

  val lookup_toplevel : Identifier.t -> (entry * data, exn) Result.t t

  val partial_lookup :
       Qualified_identifier.t
    -> [ `Partially_bound of
         (Identifier.t * (entry * data)) List1.t * Identifier.t List1.t
       | `Totally_bound of (Identifier.t * (entry * data)) List1.t
       | `Totally_unbound of Identifier.t List1.t
       ]
       t

  val with_lf_term_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_meta_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_parameter_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_context_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_substitution_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_comp_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t
end

module type SIGNATURE_STATE = sig
  include State.STATE

  val set_default_associativity : Associativity.t -> Unit.t t

  val get_default_associativity : Associativity.t t
end

(** Module type for the type of state used in disambiguating the parser
    syntax to the external syntax. *)
module type DISAMBIGUATION_STATE = sig
  include State.STATE

  include BINDINGS_STATE with type state := state

  include SIGNATURE_STATE with type state := state
end

(** A minimal disambiguation state backed by nested HAMT data structures with
    plain identifier keys. *)
module Disambiguation_state : DISAMBIGUATION_STATE = struct
  type data =
    { location : Location.t
    ; operator : Operator.t Option.t
    }

  type entry =
    | Lf_type_constant
    | Lf_term_constant
    | Lf_term_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Schema_constant
    | Computation_variable
    | Computation_inductive_type_constant
    | Computation_stratified_type_constant
    | Computation_coinductive_type_constant
    | Computation_abbreviation_type_constant
    | Computation_term_constructor
    | Computation_term_destructor
    | Query
    | MQuery
    | Module
    | Program_constant

  and state =
    { bindings : (entry * data) List1.t Binding_tree.t
          (** Symbol table with checkpoints. *)
    ; default_associativity : Associativity.t
          (** Associativity to use if a pragma for an infix operator does not
              specify an associativity. *)
    }

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let empty =
    { bindings = Binding_tree.empty
    ; default_associativity = Associativity.non_associative
    }

  let[@inline] set_default_associativity default_associativity =
    modify (fun state -> { state with default_associativity })

  let get_default_associativity =
    let* state = get in
    return state.default_associativity

  let get_bindings =
    let* state = get in
    return state.bindings

  let[@inline] set_bindings bindings =
    modify (fun state -> { state with bindings })

  let[@inline] modify_bindings f =
    let* bindings = get_bindings in
    let bindings' = f bindings in
    set_bindings bindings'

  let[@inline] push_binding identifier entry ?subtree bindings =
    let binding_stack' =
      try
        let binding_stack, _subtree =
          Binding_tree.lookup_toplevel identifier bindings
        in
        List1.cons entry binding_stack
      with
      | Binding_tree.Unbound_identifier _identifier -> List1.singleton entry
    in
    Binding_tree.add_toplevel identifier ?subtree binding_stack' bindings

  let[@inline] push_namespace_binding identifier entry subtree bindings =
    push_binding identifier entry ~subtree bindings

  let[@inline] push_binding identifier entry bindings =
    push_binding identifier entry bindings

  let[@inline] pop_binding identifier =
    modify_bindings (fun bindings ->
        let binding_stack, _subtree =
          Binding_tree.lookup_toplevel identifier bindings
        in
        match binding_stack with
        | List1.T (_head_to_discard, []) ->
            Binding_tree.remove identifier bindings
        | List1.T (_head_to_discard, new_head :: stack) ->
            Binding_tree.add_toplevel identifier
              (List1.from new_head stack)
              bindings)

  let[@inline] add_binding identifier entry =
    modify_bindings (push_binding identifier entry)

  let[@inline] add_namespace_binding identifier entry subtree =
    modify_bindings (push_namespace_binding identifier entry subtree)

  let make_entry_location location identifier =
    Option.value location ~default:(Identifier.location identifier)

  let make_entry_data ?location ?operator identifier =
    let location = make_entry_location location identifier in
    { location; operator }

  let add_lf_term_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Lf_term_variable, data) in
    add_binding identifier entry

  let add_lf_type_constant ?location operator identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Lf_type_constant, data) in
    add_binding identifier entry

  let add_lf_term_constant ?location operator identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Lf_term_constant, data) in
    add_binding identifier entry

  let add_meta_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Meta_variable, data) in
    add_binding identifier entry

  let add_parameter_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Parameter_variable, data) in
    add_binding identifier entry

  let add_substitution_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Substitution_variable, data) in
    add_binding identifier entry

  let add_context_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Context_variable, data) in
    add_binding identifier entry

  let add_schema_constant ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Schema_constant, data) in
    add_binding identifier entry

  let add_computation_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Computation_variable, data) in
    add_binding identifier entry

  let add_inductive_computation_type_constant ?location operator identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_inductive_type_constant, data) in
    add_binding identifier entry

  let add_stratified_computation_type_constant ?location operator identifier
      =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_stratified_type_constant, data) in
    add_binding identifier entry

  let add_coinductive_computation_type_constant ?location operator identifier
      =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_coinductive_type_constant, data) in
    add_binding identifier entry

  let add_abbreviation_computation_type_constant ?location operator
      identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_abbreviation_type_constant, data) in
    add_binding identifier entry

  let add_computation_term_constructor ?location operator identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_term_constructor, data) in
    add_binding identifier entry

  let add_computation_term_destructor ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Computation_term_destructor, data) in
    add_binding identifier entry

  let add_query ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Query, data) in
    add_binding identifier entry

  let add_mquery ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (MQuery, data) in
    add_binding identifier entry

  let add_module ?location subtree identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Module, data) in
    add_namespace_binding identifier entry subtree

  let add_program_constant ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Program_constant, data) in
    add_binding identifier entry

  let lookup_toplevel query =
    let* bindings = get_bindings in
    try
      let binding_stack, _subtree =
        Binding_tree.lookup_toplevel query bindings
      in
      return (Result.ok (List1.head binding_stack))
    with
    | Binding_tree.Unbound_identifier _identifier ->
        return (Result.error (Unbound_identifier query))

  let lookup query =
    let* bindings = get_bindings in
    try
      let binding_stack, _subtree = Binding_tree.lookup query bindings in
      return (Result.ok (List1.head binding_stack))
    with
    | Binding_tree.Unbound_identifier identifier ->
        return (Result.error (Unbound_identifier identifier))
    | Binding_tree.Unbound_namespace identifier ->
        return (Result.error (Unbound_namespace identifier))
    | Binding_tree.Unbound_qualified_identifier identifier ->
        return (Result.error (Unbound_qualified_identifier identifier))
    | cause -> return (Result.error cause)

  let rec partial_lookup_nested namespaces identifier tree =
    match namespaces with
    | [] -> (
        try
          let binding_stack, _subtree =
            Binding_tree.lookup_toplevel identifier tree
          in
          let entry = List1.head binding_stack in
          `Totally_bound (List1.singleton (identifier, entry))
        with
        | Binding_tree.Unbound_identifier _ ->
            `Totally_unbound (List1.singleton identifier))
    | x :: xs -> (
        try
          let binding_stack, subtree = Binding_tree.lookup_toplevel x tree in
          let entry = List1.head binding_stack in
          match partial_lookup_nested xs identifier subtree with
          | `Totally_bound xs' -> `Totally_bound (List1.cons (x, entry) xs')
          | `Partially_bound (bound, unbound) ->
              `Partially_bound (List1.cons (x, entry) bound, unbound)
          | `Totally_unbound xs' ->
              `Partially_bound (List1.singleton (x, entry), xs')
        with
        | Binding_tree.Unbound_identifier _ ->
            `Totally_unbound
              (List1.append (List1.from x xs) (List1.singleton identifier)))

  let partial_lookup query =
    let identifier = Qualified_identifier.name query
    and namespaces = Qualified_identifier.namespaces query in
    let* bindings = get_bindings in
    return (partial_lookup_nested namespaces identifier bindings)

  let modify_operator identifier _f =
    lookup identifier >>= function
    | Result.Ok (Lf_type_constant, _entry) -> Obj.magic ()
    | Result.Ok (Lf_term_constant, _entry) -> Obj.magic ()
    | Result.Ok (Computation_inductive_type_constant, _entry) -> Obj.magic ()
    | Result.Ok (Computation_stratified_type_constant, _entry) ->
        Obj.magic ()
    | Result.Ok (Computation_abbreviation_type_constant, _entry) ->
        Obj.magic ()
    | Result.Ok (Computation_coinductive_type_constant, _entry) ->
        Obj.magic ()
    | Result.Ok (Computation_term_constructor, _entry) -> Obj.magic ()
    | Result.Ok (Lf_term_variable, _)
    | Result.Ok (Meta_variable, _)
    | Result.Ok (Parameter_variable, _)
    | Result.Ok (Substitution_variable, _)
    | Result.Ok (Context_variable, _)
    | Result.Ok (Schema_constant, _)
    | Result.Ok (Computation_variable, _)
    | Result.Ok (Computation_term_destructor, _)
    | Result.Ok (Query, _)
    | Result.Ok (MQuery, _)
    | Result.Ok (Module, _)
    | Result.Ok (Program_constant, _) ->
        Error.raise (Expected_operator identifier)
    | Result.Error cause -> Error.raise cause

  let actual_binding_exn identifier (sort, data) =
    let { location; _ } = data in
    match sort with
    | Lf_type_constant ->
        Error.located_exception1 location (Bound_lf_type_constant identifier)
    | Lf_term_constant ->
        Error.located_exception1 location (Bound_lf_term_constant identifier)
    | Lf_term_variable ->
        Error.located_exception1 location (Bound_lf_term_variable identifier)
    | Meta_variable ->
        Error.located_exception1 location (Bound_meta_variable identifier)
    | Parameter_variable ->
        Error.located_exception1 location
          (Bound_parameter_variable identifier)
    | Substitution_variable ->
        Error.located_exception1 location
          (Bound_substitution_variable identifier)
    | Context_variable ->
        Error.located_exception1 location (Bound_context_variable identifier)
    | Schema_constant ->
        Error.located_exception1 location (Bound_schema_constant identifier)
    | Computation_variable ->
        Error.located_exception1 location
          (Bound_computation_variable identifier)
    | Computation_inductive_type_constant ->
        Error.located_exception1 location
          (Bound_computation_inductive_type_constant identifier)
    | Computation_stratified_type_constant ->
        Error.located_exception1 location
          (Bound_computation_stratified_type_constant identifier)
    | Computation_coinductive_type_constant ->
        Error.located_exception1 location
          (Bound_computation_coinductive_type_constant identifier)
    | Computation_abbreviation_type_constant ->
        Error.located_exception1 location
          (Bound_computation_abbreviation_type_constant identifier)
    | Computation_term_constructor ->
        Error.located_exception1 location
          (Bound_computation_term_constructor identifier)
    | Computation_term_destructor ->
        Error.located_exception1 location
          (Bound_computation_term_destructor identifier)
    | Query -> Error.located_exception1 location (Bound_query identifier)
    | MQuery -> Error.located_exception1 location (Bound_mquery identifier)
    | Module -> Error.located_exception1 location (Bound_module identifier)
    | Program_constant ->
        Error.located_exception1 location (Bound_program_constant identifier)

  let open_namespace identifier =
    lookup identifier >>= function
    | Result.Ok (Lf_type_constant, _)
    | Result.Ok (Lf_term_constant, _)
    | Result.Ok (Lf_term_variable, _)
    | Result.Ok (Meta_variable, _)
    | Result.Ok (Parameter_variable, _)
    | Result.Ok (Substitution_variable, _)
    | Result.Ok (Context_variable, _)
    | Result.Ok (Schema_constant, _)
    | Result.Ok (Computation_variable, _)
    | Result.Ok (Computation_inductive_type_constant, _)
    | Result.Ok (Computation_stratified_type_constant, _)
    | Result.Ok (Computation_coinductive_type_constant, _)
    | Result.Ok (Computation_abbreviation_type_constant, _)
    | Result.Ok (Computation_term_constructor, _)
    | Result.Ok (Computation_term_destructor, _)
    | Result.Ok (Query, _)
    | Result.Ok (MQuery, _)
    | Result.Ok (Program_constant, _) ->
        return (Result.error (Expected_namespace identifier))
    | Result.Ok (Module, _) -> Obj.magic ()
    | Result.Error cause -> return (Result.error cause)

  let with_lf_term_variable ?location identifier =
    scoped
      ~set:(add_lf_term_variable ?location identifier)
      ~unset:(pop_binding identifier)

  let with_meta_variable ?location identifier =
    scoped
      ~set:(add_meta_variable ?location identifier)
      ~unset:(pop_binding identifier)

  let with_parameter_variable ?location identifier =
    scoped
      ~set:(add_parameter_variable ?location identifier)
      ~unset:(pop_binding identifier)

  let with_context_variable ?location identifier =
    scoped
      ~set:(add_context_variable ?location identifier)
      ~unset:(pop_binding identifier)

  let with_substitution_variable ?location identifier =
    scoped
      ~set:(add_substitution_variable ?location identifier)
      ~unset:(pop_binding identifier)

  let with_comp_variable ?location identifier =
    scoped
      ~set:(add_computation_variable ?location identifier)
      ~unset:(pop_binding identifier)
end

let pp_exception ppf = function
  | Expected_operator qualified_identifier ->
      Format.fprintf ppf "Expected an operator bound at %a."
        Qualified_identifier.pp qualified_identifier
  | Unbound_identifier identifier ->
      Format.fprintf ppf "Identifier %a is unbound." Identifier.pp identifier
  | Unbound_qualified_identifier qualified_identifier ->
      Format.fprintf ppf "Identifier %a is unbound." Qualified_identifier.pp
        qualified_identifier
  | Unbound_namespace qualified_identifier ->
      Format.fprintf ppf "Unbound namespace %a." Qualified_identifier.pp
        qualified_identifier
  | Expected_namespace qualified_identifier ->
      Format.fprintf ppf "Expected a namespace %a." Qualified_identifier.pp
        qualified_identifier
  | Bound_lf_type_constant qualified_identifier ->
      Format.fprintf ppf "%a is a bound LF type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_lf_term_constant qualified_identifier ->
      Format.fprintf ppf "%a is a bound LF term constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_lf_term_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound LF term variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_meta_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound meta-variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_parameter_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound parameter variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_substitution_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound substitution variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_context_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound context variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_schema_constant qualified_identifier ->
      Format.fprintf ppf "%a is a bound schema constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound computation variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_inductive_type_constant qualified_identifier ->
      Format.fprintf ppf
        "%a is a bound computation-level inductive type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_stratified_type_constant qualified_identifier ->
      Format.fprintf ppf
        "%a is a bound computation-level stratified type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_coinductive_type_constant qualified_identifier ->
      Format.fprintf ppf
        "%a is a bound computation-level coinductive type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_abbreviation_type_constant qualified_identifier ->
      Format.fprintf ppf
        "%a is a bound computation-level abbreviation type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_term_constructor qualified_identifier ->
      Format.fprintf ppf "%a is a bound computation-level term constructor."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_term_destructor qualified_identifier ->
      Format.fprintf ppf "%a is a bound computation-level term destructor."
        Qualified_identifier.pp qualified_identifier
  | Bound_query qualified_identifier ->
      Format.fprintf ppf "%a is a bound query." Qualified_identifier.pp
        qualified_identifier
  | Bound_mquery qualified_identifier ->
      Format.fprintf ppf "%a is a bound mquery." Qualified_identifier.pp
        qualified_identifier
  | Bound_module qualified_identifier ->
      Format.fprintf ppf "%a is a bound module." Qualified_identifier.pp
        qualified_identifier
  | Bound_program_constant qualified_identifier ->
      Format.fprintf ppf "%a is a bound program." Qualified_identifier.pp
        qualified_identifier
  | _ -> raise (Invalid_argument "[pp_exception] unsupported exception")

let () =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify pp_exception exn) with
      | Invalid_argument _ -> Option.none)
