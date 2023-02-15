open Support
open Beluga_syntax

exception Expected_module of Qualified_identifier.t

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

exception Bound_module of Qualified_identifier.t

exception Bound_program_constant of Qualified_identifier.t

module type DISAMBIGUATION_STATE = sig
  include State.STATE

  type data = private
    { location : Location.t
    ; operator : Operator.t option
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
    | Module
    | Program_constant

  val set_default_associativity : Associativity.t -> Unit.t t

  val get_default_associativity : Associativity.t t

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

  val add_program_constant :
    ?location:Location.t -> ?operator:Operator.t -> Identifier.t -> Unit.t t

  exception Unbound_identifier of Identifier.t

  exception Unbound_qualified_identifier of Qualified_identifier.t

  exception Unbound_namespace of Qualified_identifier.t

  val lookup_toplevel : Identifier.t -> (entry * data, exn) Result.t t

  val lookup : Qualified_identifier.t -> (entry * data, exn) Result.t t

  val partial_lookup :
       Qualified_identifier.t
    -> [ `Partially_bound of
         (Identifier.t * (entry * data)) List1.t * Identifier.t List1.t
       | `Totally_bound of (Identifier.t * (entry * data)) List1.t
       | `Totally_unbound of Identifier.t List1.t
       ]
       t

  val partial_lookup' :
       Identifier.t List1.t
    -> [ `Partially_bound of
         (Identifier.t * (entry * data)) List1.t * Identifier.t List1.t
       | `Totally_bound of (Identifier.t * (entry * data)) List1.t
       | `Totally_unbound of Identifier.t List1.t
       ]
       t

  val modify_operator :
    Qualified_identifier.t -> (Operator.t -> Operator.t) -> Unit.t t

  val add_synonym :
       ?location:Location.t
    -> Qualified_identifier.t
    -> Identifier.t
    -> Unit.t t

  val actual_binding_exn : Qualified_identifier.t -> entry * data -> exn

  val open_module : Qualified_identifier.t -> Unit.t t

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

  val with_scope : 'a t -> 'a t

  val with_parent_scope : 'a t -> 'a t

  val add_inner_pattern_binding : Identifier.t -> Unit.t t

  val with_inner_pattern_binding : Identifier.t -> 'a t -> 'a t

  val is_inner_pattern_bound : Identifier.t -> Bool.t t

  exception Duplicate_pattern_variables of Identifier.t List2.t

  val with_pattern_variables : pattern:'a t -> expression:'b t -> ('a * 'b) t

  val with_inner_bound_lf_term_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_inner_bound_meta_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_inner_bound_parameter_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_inner_bound_substitution_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_inner_bound_context_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val add_pattern_lf_term_variable : Identifier.t -> Unit.t t

  val add_pattern_meta_variable : Identifier.t -> Unit.t t

  val add_pattern_parameter_variable : Identifier.t -> Unit.t t

  val add_pattern_substitution_variable : Identifier.t -> Unit.t t

  val add_pattern_context_variable : Identifier.t -> Unit.t t

  val add_pattern_comp_variable : Identifier.t -> Unit.t t

  val update_module_declaration : Qualified_identifier.t -> Unit.t t

  val is_inner_module_declaration : Qualified_identifier.t -> Bool.t t

  val with_module_declarations :
    declarations:'a t -> module_identifier:Identifier.t -> 'a t
end

module Persistent_disambiguation_state : sig
  include DISAMBIGUATION_STATE

  val initial : state
end = struct
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
    | Module
    | Program_constant

  and state =
    | Disambiguation_state of { bindings : (entry * data) Binding_tree.t }
    | Signature_state of
        { state : state
        ; default_associativity : Associativity.t
        }
    | Pattern_state of
        { pattern_state : state
        ; inner_pattern_bindings : Identifier.Set.t
        ; pattern_variables_rev : Identifier.t List.t
        ; expression_state : state
        }
    | Module_state of
        { state : state
        ; declarations : (entry * data) Binding_tree.t
              (* The declarations in the current module *)
        }
    | Scope_state of
        { state : state
        ; bindings : (entry * data) Binding_tree.t
              (* Initially a copy of the binding tree in [state],
                 mutations/lookups only happen to [bindings] *)
        }

  exception Unbound_identifier = Unbound_identifier

  exception Unbound_qualified_identifier = Unbound_qualified_identifier

  exception Unbound_namespace = Unbound_namespace

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let initial =
    Signature_state
      { state = Disambiguation_state { bindings = Binding_tree.empty }
      ; default_associativity = Associativity.non_associative
      }

  let rec nested_set_default_associativity default_associativity = function
    | Disambiguation_state _ ->
        Error.raise_violation "[set_default_associativity] invalid state"
    | Signature_state o -> Signature_state { o with default_associativity }
    | Pattern_state o ->
        let pattern_state' =
          nested_set_default_associativity default_associativity
            o.pattern_state
        in
        Pattern_state { o with pattern_state = pattern_state' }
    | Module_state o ->
        let state' =
          nested_set_default_associativity default_associativity o.state
        in
        Module_state { o with state = state' }
    | Scope_state o ->
        let state' =
          nested_set_default_associativity default_associativity o.state
        in
        Scope_state { o with state = state' }

  let rec nested_get_default_associativity = function
    | Disambiguation_state _ ->
        Error.raise_violation "[get_default_associativity] invalid state"
    | Signature_state o -> o.default_associativity
    | Pattern_state o -> nested_get_default_associativity o.pattern_state
    | Module_state o -> nested_get_default_associativity o.state
    | Scope_state o -> nested_get_default_associativity o.state

  let set_default_associativity default_associativity =
    modify (nested_set_default_associativity default_associativity)

  let get_default_associativity = get $> nested_get_default_associativity

  let[@warning "-23"] rec nested_set_bindings bindings = function
    | Disambiguation_state o -> Disambiguation_state { o with bindings }
    | Signature_state o ->
        let state' = nested_set_bindings bindings o.state in
        Signature_state { o with state = state' }
    | Pattern_state o ->
        let pattern_state' = nested_set_bindings bindings o.pattern_state in
        Pattern_state { o with pattern_state = pattern_state' }
    | Module_state o ->
        let state' = nested_set_bindings bindings o.state in
        Module_state { o with state = state' }
    | Scope_state o -> Scope_state { o with bindings }

  let rec nested_get_bindings = function
    | Disambiguation_state { bindings } -> bindings
    | Signature_state o -> nested_get_bindings o.state
    | Pattern_state o -> nested_get_bindings o.pattern_state
    | Module_state o -> nested_get_bindings o.state
    | Scope_state o -> o.bindings

  let set_bindings bindings = modify (nested_set_bindings bindings)

  let get_bindings = get $> nested_get_bindings

  let[@inline] modify_bindings f =
    let* bindings = get_bindings in
    let bindings' = f bindings in
    set_bindings bindings'

  let[@inline] add_binding identifier entry ?subtree bindings =
    Binding_tree.add_toplevel identifier ?subtree entry bindings

  let[@inline] add_namespace_binding identifier entry subtree =
    modify_bindings (add_binding identifier entry ~subtree)

  let[@inline] add_entry_binding identifier entry =
    modify_bindings (add_binding identifier entry)

  let make_entry_location location identifier =
    Option.value location ~default:(Identifier.location identifier)

  let make_entry_data ?location ?operator identifier =
    let location = make_entry_location location identifier in
    { location; operator }

  let add_module_declaration identifier =
    let* bindings = get_bindings in
    let entry, subtree = Binding_tree.lookup_toplevel identifier bindings in
    modify (function
      | Module_state o ->
          let declarations' =
            Binding_tree.add_toplevel identifier entry ~subtree
              o.declarations
          in
          Module_state { o with declarations = declarations' }
      | (Signature_state _ | Scope_state _) as state -> state
      | Disambiguation_state _
      | Pattern_state _ ->
          Error.raise_violation "[add_module_declaration] invalid state")

  let update_module_declaration identifier =
    let* bindings = get_bindings in
    let entry, subtree = Binding_tree.lookup identifier bindings in
    modify (function
      | Module_state o ->
          let declarations' =
            Binding_tree.add identifier entry ~subtree o.declarations
          in
          Module_state { o with declarations = declarations' }
      | Signature_state _ as state -> state
      | Disambiguation_state _
      | Pattern_state _
      | Scope_state _ ->
          Error.raise_violation "[update_module_declaration] invalid state")

  let is_inner_module_declaration identifier =
    get >>= function
    | Signature_state _ -> return false
    | Module_state o ->
        return
          (Binding_tree.is_qualified_identifier_bound identifier
             o.declarations)
    | Disambiguation_state _
    | Pattern_state _
    | Scope_state _ ->
        Error.raise_violation "[is_inner_module_declaration] invalid state"

  let get_module_declarations =
    get >>= function
    | Disambiguation_state _
    | Signature_state _
    | Pattern_state _
    | Scope_state _ ->
        Error.raise_violation "[get_declarations] invalid state"
    | Module_state o -> return o.declarations

  let add_module ?location subtree identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Module, data) in
    add_namespace_binding identifier entry subtree
    <& add_module_declaration identifier

  let with_module_declarations ~declarations ~module_identifier =
    let* state = get in
    let* () =
      put (Module_state { state; declarations = Binding_tree.empty })
    in
    let* declarations' = declarations in
    let* inner_declarations = get_module_declarations in
    let* () = put state in
    let* () = add_module inner_declarations module_identifier in
    return declarations'

  let add_lf_term_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Lf_term_variable, data) in
    add_entry_binding identifier entry

  let add_meta_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Meta_variable, data) in
    add_entry_binding identifier entry

  let add_parameter_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Parameter_variable, data) in
    add_entry_binding identifier entry

  let add_substitution_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Substitution_variable, data) in
    add_entry_binding identifier entry

  let add_context_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Context_variable, data) in
    add_entry_binding identifier entry

  let add_computation_variable ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Computation_variable, data) in
    add_entry_binding identifier entry

  let add_lf_type_constant ?location operator identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Lf_type_constant, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_lf_term_constant ?location operator identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Lf_term_constant, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_schema_constant ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Schema_constant, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_inductive_computation_type_constant ?location operator identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_inductive_type_constant, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_stratified_computation_type_constant ?location operator identifier
      =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_stratified_type_constant, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_coinductive_computation_type_constant ?location operator identifier
      =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_coinductive_type_constant, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_abbreviation_computation_type_constant ?location operator
      identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_abbreviation_type_constant, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_computation_term_constructor ?location operator identifier =
    let data = make_entry_data ?location ~operator identifier in
    let entry = (Computation_term_constructor, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_computation_term_destructor ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Computation_term_destructor, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_query ?location identifier =
    let data = make_entry_data ?location identifier in
    let entry = (Query, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let add_program_constant ?location ?operator identifier =
    let data = make_entry_data ?location ?operator identifier in
    let entry = (Program_constant, data) in
    add_entry_binding identifier entry <& add_module_declaration identifier

  let lookup_toplevel query =
    let* bindings = get_bindings in
    try return (Binding_tree.lookup_toplevel query bindings) with
    | Binding_tree.Unbound_identifier identifier ->
        Error.raise (Unbound_identifier identifier)

  let lookup_toplevel query =
    try_catch
      (lazy
        (let* entry, _subtree = lookup_toplevel query in
         return (Result.ok entry)))
      ~on_exn:(fun cause -> return (Result.error cause))

  let lookup' query =
    let* bindings = get_bindings in
    try return (Binding_tree.lookup query bindings) with
    | Binding_tree.Unbound_identifier identifier ->
        Error.raise (Unbound_identifier identifier)
    | Binding_tree.Unbound_namespace identifier ->
        Error.raise (Unbound_namespace identifier)
    | Binding_tree.Unbound_qualified_identifier identifier ->
        Error.raise (Unbound_qualified_identifier identifier)
    | cause -> Error.raise cause

  let lookup query =
    try_catch
      (lazy
        (let* entry, _subtree = lookup' query in
         return (Result.ok entry)))
      ~on_exn:(fun cause -> return (Result.error cause))

  let rec partial_lookup_nested namespaces identifier tree =
    match namespaces with
    | [] -> (
        try
          let entry, _subtree =
            Binding_tree.lookup_toplevel identifier tree
          in
          `Totally_bound (List1.singleton (identifier, entry))
        with
        | Binding_tree.Unbound_identifier _ ->
            `Totally_unbound (List1.singleton identifier))
    | x :: xs -> (
        try
          let entry, subtree = Binding_tree.lookup_toplevel x tree in
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

  let partial_lookup' query =
    let namespaces, identifier = List1.unsnoc query in
    let* bindings = get_bindings in
    return (partial_lookup_nested namespaces identifier bindings)

  let partial_lookup query =
    let identifier = Qualified_identifier.name query
    and namespaces = Qualified_identifier.namespaces query in
    get_bindings $> partial_lookup_nested namespaces identifier

  let replace identifier f =
    modify_bindings (fun bindings ->
        try Binding_tree.replace identifier f bindings with
        | Binding_tree.Unbound_identifier identifier ->
            Error.raise (Unbound_identifier identifier)
        | Binding_tree.Unbound_namespace identifier ->
            Error.raise (Unbound_namespace identifier)
        | Binding_tree.Unbound_qualified_identifier identifier ->
            Error.raise (Unbound_qualified_identifier identifier)
        | cause -> Error.raise cause)

  let modify_operator identifier f =
    replace identifier (fun (entry, data) subtree ->
        match data.operator with
        | Option.None ->
            Error.raise_at1
              (Qualified_identifier.location identifier)
              (Expected_operator identifier)
        | Option.Some operator ->
            let operator' = Option.some (f operator) in
            let data' = { data with operator = operator' } in
            ((entry, data'), subtree))

  let add_synonym ?location qualified_identifier synonym =
    let* (entry, data), subtree = lookup' qualified_identifier in
    let location' = Option.value ~default:data.location location in
    let data' = { data with location = location' } in
    modify_bindings (add_binding synonym (entry, data') ~subtree)

  let actual_binding_exn identifier (sort, data) =
    let exn =
      match sort with
      | Lf_type_constant -> Bound_lf_type_constant identifier
      | Lf_term_constant -> Bound_lf_term_constant identifier
      | Lf_term_variable -> Bound_lf_term_variable identifier
      | Meta_variable -> Bound_meta_variable identifier
      | Parameter_variable -> Bound_parameter_variable identifier
      | Substitution_variable -> Bound_substitution_variable identifier
      | Context_variable -> Bound_context_variable identifier
      | Schema_constant -> Bound_schema_constant identifier
      | Computation_variable -> Bound_computation_variable identifier
      | Computation_inductive_type_constant ->
          Bound_computation_inductive_type_constant identifier
      | Computation_stratified_type_constant ->
          Bound_computation_stratified_type_constant identifier
      | Computation_coinductive_type_constant ->
          Bound_computation_coinductive_type_constant identifier
      | Computation_abbreviation_type_constant ->
          Bound_computation_abbreviation_type_constant identifier
      | Computation_term_constructor ->
          Bound_computation_term_constructor identifier
      | Computation_term_destructor ->
          Bound_computation_term_destructor identifier
      | Query -> Bound_query identifier
      | Module -> Bound_module identifier
      | Program_constant -> Bound_program_constant identifier
    in
    let { location; _ } = data in
    Error.located_exception1 location exn

  let open_namespace identifier =
    modify_bindings (Binding_tree.open_namespace identifier)

  let open_module identifier =
    lookup identifier >>= function
    | Result.Ok (Module, _) -> open_namespace identifier
    | Result.Ok _ ->
        Error.raise_at1
          (Qualified_identifier.location identifier)
          (Expected_module identifier)
    | Result.Error cause -> Error.raise cause

  let with_bindings_checkpoint m =
    let* bindings = get_bindings in
    let* x = m in
    let* () = set_bindings bindings in
    return x

  let with_lf_term_variable ?location identifier m =
    with_bindings_checkpoint (add_lf_term_variable ?location identifier &> m)

  let with_meta_variable ?location identifier m =
    with_bindings_checkpoint (add_meta_variable ?location identifier &> m)

  let with_parameter_variable ?location identifier m =
    with_bindings_checkpoint
      (add_parameter_variable ?location identifier &> m)

  let with_context_variable ?location identifier m =
    with_bindings_checkpoint (add_context_variable ?location identifier &> m)

  let with_substitution_variable ?location identifier m =
    with_bindings_checkpoint
      (add_substitution_variable ?location identifier &> m)

  let with_comp_variable ?location identifier m =
    with_bindings_checkpoint
      (add_computation_variable ?location identifier &> m)

  let with_scope m =
    let* state = get in
    let* bindings = get_bindings in
    let* () = put (Scope_state { state; bindings }) in
    let* x = m in
    let* () = put state in
    return x

  let with_parent_scope m =
    let* state = get in
    match state with
    | Scope_state { state = parent_scope; _ } ->
        let* () = put parent_scope in
        let* x = with_scope m in
        let* () = put state in
        return x
    | Disambiguation_state _
    | Signature_state _
    | Pattern_state _
    | Module_state _ ->
        Error.raise_violation "[with_parent_scope] invalid state"

  let[@inline] modify_inner_pattern_bindings f =
    modify (function
      | Pattern_state o ->
          let inner_pattern_bindings' = f o.inner_pattern_bindings in
          Pattern_state
            { o with inner_pattern_bindings = inner_pattern_bindings' }
      | Disambiguation_state _
      | Signature_state _
      | Module_state _
      | Scope_state _ ->
          Error.raise_violation
            "[modify_inner_pattern_bindings] invalid state")

  let get_inner_bindings =
    get >>= function
    | Pattern_state o -> return o.inner_pattern_bindings
    | Disambiguation_state _
    | Signature_state _
    | Module_state _
    | Scope_state _ ->
        Error.raise_violation "[get_inner_bindings] invalid state"

  let add_inner_pattern_binding identifier =
    modify_inner_pattern_bindings (Identifier.Set.add identifier)

  let with_inner_pattern_binding identifier m =
    with_bindings_checkpoint (add_inner_pattern_binding identifier &> m)

  let is_inner_pattern_bound identifier =
    let* inner_pattern_bindings = get_inner_bindings in
    return (Identifier.Set.mem identifier inner_pattern_bindings)

  let add_pattern_variable identifier f =
    modify (function
      | Pattern_state o ->
          let expression_state' = exec f o.expression_state in
          Pattern_state
            { o with
              pattern_variables_rev = identifier :: o.pattern_variables_rev
            ; expression_state = expression_state'
            }
      | Disambiguation_state _
      | Signature_state _
      | Module_state _
      | Scope_state _ ->
          Error.raise_violation "[add_pattern_variable] invalid state")

  let get_pattern_variables_and_expression_state =
    get >>= function
    | Pattern_state o ->
        let pattern_variables = List.rev o.pattern_variables_rev in
        return (pattern_variables, o.expression_state)
    | Disambiguation_state _
    | Signature_state _
    | Module_state _
    | Scope_state _ ->
        Error.raise_violation
          "[get_pattern_variables_and_expression_state] invalid state"

  exception Duplicate_pattern_variables of Identifier.t List2.t

  let with_pattern_variables ~pattern ~expression =
    let* state = get in
    let* () =
      put
        (Pattern_state
           { pattern_state = state
           ; inner_pattern_bindings = Identifier.Set.empty
           ; pattern_variables_rev = []
           ; expression_state = state
           })
    in
    let* pattern' = pattern in
    let* pattern_variables, expression_state =
      get_pattern_variables_and_expression_state
    in
    match Identifier.find_duplicates pattern_variables with
    | Option.Some duplicates ->
        let* () = put state in
        Error.raise (Duplicate_pattern_variables duplicates)
    | Option.None ->
        let* () = put expression_state in
        let* expression' = expression in
        let* () = put state in
        return (pattern', expression')

  let with_inner_bound_lf_term_variable ?location identifier f =
    with_inner_pattern_binding identifier
      (with_lf_term_variable ?location identifier f)

  let with_inner_bound_meta_variable ?location identifier f =
    with_inner_pattern_binding identifier
      (with_meta_variable ?location identifier f)

  let with_inner_bound_parameter_variable ?location identifier f =
    with_inner_pattern_binding identifier
      (with_parameter_variable ?location identifier f)

  let with_inner_bound_substitution_variable ?location identifier f =
    with_inner_pattern_binding identifier
      (with_substitution_variable ?location identifier f)

  let with_inner_bound_context_variable ?location identifier f =
    with_inner_pattern_binding identifier
      (with_context_variable ?location identifier f)

  let add_pattern_lf_term_variable identifier =
    add_pattern_variable identifier (add_lf_term_variable identifier)

  let add_pattern_meta_variable identifier =
    add_pattern_variable identifier (add_meta_variable identifier)

  let add_pattern_parameter_variable identifier =
    add_pattern_variable identifier (add_parameter_variable identifier)

  let add_pattern_substitution_variable identifier =
    add_pattern_variable identifier (add_substitution_variable identifier)

  let add_pattern_context_variable identifier =
    add_pattern_variable identifier (add_context_variable identifier)

  let add_pattern_comp_variable identifier =
    add_pattern_variable identifier (add_computation_variable identifier)
end

let () =
  Error.register_exception_printer (function
    | Expected_operator qualified_identifier ->
        Format.dprintf "Expected an operator bound at %a."
          Qualified_identifier.pp qualified_identifier
    | Unbound_identifier identifier ->
        Format.dprintf "The identifier %a is unbound." Identifier.pp
          identifier
    | Unbound_qualified_identifier qualified_identifier ->
        Format.dprintf "The qualified identifier %a is unbound."
          Qualified_identifier.pp qualified_identifier
    | Unbound_namespace qualified_identifier ->
        Format.dprintf "Unbound namespace %a." Qualified_identifier.pp
          qualified_identifier
    | Expected_module qualified_identifier ->
        Format.dprintf "Expected %a to be a module." Qualified_identifier.pp
          qualified_identifier
    | Bound_lf_type_constant qualified_identifier ->
        Format.dprintf "%a is a bound LF type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_lf_term_constant qualified_identifier ->
        Format.dprintf "%a is a bound LF term constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_lf_term_variable qualified_identifier ->
        Format.dprintf "%a is a bound LF term variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_meta_variable qualified_identifier ->
        Format.dprintf "%a is a bound meta-variable." Qualified_identifier.pp
          qualified_identifier
    | Bound_parameter_variable qualified_identifier ->
        Format.dprintf "%a is a bound parameter variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_substitution_variable qualified_identifier ->
        Format.dprintf "%a is a bound substitution variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_context_variable qualified_identifier ->
        Format.dprintf "%a is a bound context variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_schema_constant qualified_identifier ->
        Format.dprintf "%a is a bound schema constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_variable qualified_identifier ->
        Format.dprintf "%a is a bound computation variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_inductive_type_constant qualified_identifier ->
        Format.dprintf
          "%a is a bound computation-level inductive type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_stratified_type_constant qualified_identifier ->
        Format.dprintf
          "%a is a bound computation-level stratified type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_coinductive_type_constant qualified_identifier ->
        Format.dprintf
          "%a is a bound computation-level coinductive type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_abbreviation_type_constant qualified_identifier ->
        Format.dprintf
          "%a is a bound computation-level abbreviation type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_term_constructor qualified_identifier ->
        Format.dprintf "%a is a bound computation-level term constructor."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_term_destructor qualified_identifier ->
        Format.dprintf "%a is a bound computation-level term destructor."
          Qualified_identifier.pp qualified_identifier
    | Bound_query qualified_identifier ->
        Format.dprintf "%a is a bound query." Qualified_identifier.pp
          qualified_identifier
    | Bound_module qualified_identifier ->
        Format.dprintf "%a is a bound module." Qualified_identifier.pp
          qualified_identifier
    | Bound_program_constant qualified_identifier ->
        Format.dprintf "%a is a bound program." Qualified_identifier.pp
          qualified_identifier
    | exn -> Error.raise_unsupported_exception_printing exn)
