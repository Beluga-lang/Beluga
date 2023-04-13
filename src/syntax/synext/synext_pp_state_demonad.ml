open Support
open Synext_definition
open Common

module Entry = struct
  type t = { operator : Operator.t Option.t }

  let make_lf_type_constant_entry ?location:_ _identifier =
    { operator = Option.none }

  let make_lf_term_constant_entry ?location:_ _identifier =
    { operator = Option.none }

  let make_inductive_computation_type_constant_entry ?location:_ _identifier
      =
    { operator = Option.none }

  let make_stratified_computation_type_constant_entry ?location:_ _identifier
      =
    { operator = Option.none }

  let make_coinductive_computation_type_constant_entry ?location:_
      _identifier =
    { operator = Option.none }

  let make_abbreviation_computation_type_constant_entry ?location:_
      _identifier =
    { operator = Option.none }

  let make_computation_term_constructor_entry ?location:_ _identifier =
    { operator = Option.none }

  let make_computation_term_destructor_entry ?location:_ _identifier =
    { operator = Option.none }

  let make_program_constant_entry ?location:_ _identifier =
    { operator = Option.none }

  let make_schema_constant_entry ?location:_ _identifier =
    { operator = Option.none }

  let make_module_entry ?location:_ _identifier = { operator = Option.none }

  let[@warning "-23"] modify_operator f entry =
    let operator' = f entry.operator in
    { entry with operator = operator' }
end

module Printing_state_demonad = struct
  module Binding_tree = Binding_tree.Hashtbl

  type scope =
    | Module_scope of
        { bindings : Entry.t Binding_tree.t
        ; declarations : Entry.t Binding_tree.t
        }

  type state =
    { mutable formatter : Format.formatter
    ; mutable scopes : scope List1.t
    ; mutable default_precedence : Int.t
    ; mutable default_associativity : Associativity.t
    }

  include (
    Format_state_demonad.Make (struct
      type nonrec state = state

      let get_formatter state = state.formatter
    end) :
      Format_state_demonad.S with type state := state)

  let create_module_scope () =
    Module_scope
      { bindings = Binding_tree.create ()
      ; declarations = Binding_tree.create ()
      }

  let create_initial_state formatter =
    { formatter
    ; scopes = List1.singleton (create_module_scope ())
    ; default_precedence
    ; default_associativity
    }

  let set_formatter state formatter = state.formatter <- formatter

  let get_scope_bindings = function
    | Module_scope { bindings; _ } -> bindings

  let get_current_scope state = List1.head state.scopes

  let get_current_scope_bindings state =
    get_scope_bindings (get_current_scope state)

  let push_scope state scope = state.scopes <- List1.cons scope state.scopes

  let pop_scope state =
    match state.scopes with
    | List1.T (x1, x2 :: xs) ->
        state.scopes <- List1.from x2 xs;
        x1
    | List1.T (_x, []) ->
        Error.raise_violation
          (Format.asprintf "[%s] cannot pop the last scope" __FUNCTION__)

  let set_default_associativity state default_associativity =
    state.default_associativity <- default_associativity

  let get_default_associativity state = state.default_associativity

  let get_default_associativity_opt state = function
    | Option.None -> get_default_associativity state
    | Option.Some associativity -> associativity

  let get_default_precedence state = state.default_precedence

  let set_default_precedence state default_precedence =
    state.default_precedence <- default_precedence

  let get_default_precedence_opt state = function
    | Option.None -> get_default_precedence state
    | Option.Some precedence -> precedence

  let add_binding state identifier ?subtree entry =
    match get_current_scope state with
    | Module_scope { bindings; _ } ->
        Binding_tree.add_toplevel identifier entry ?subtree bindings

  let add_declaration state identifier ?subtree entry =
    match get_current_scope state with
    | Module_scope { bindings; declarations } ->
        Binding_tree.add_toplevel identifier entry ?subtree bindings;
        Binding_tree.add_toplevel identifier entry ?subtree declarations

  let add_lf_type_constant state ?location identifier =
    add_declaration state identifier
      (Entry.make_lf_type_constant_entry ?location identifier)

  let add_lf_term_constant state ?location identifier =
    add_declaration state identifier
      (Entry.make_lf_term_constant_entry ?location identifier)

  let add_schema_constant state ?location identifier =
    add_declaration state identifier
      (Entry.make_schema_constant_entry ?location identifier)

  let add_inductive_computation_type_constant state ?location identifier =
    add_declaration state identifier
      (Entry.make_inductive_computation_type_constant_entry ?location
         identifier)

  let add_stratified_computation_type_constant state ?location identifier =
    add_declaration state identifier
      (Entry.make_stratified_computation_type_constant_entry ?location
         identifier)

  let add_coinductive_computation_type_constant state ?location identifier =
    add_declaration state identifier
      (Entry.make_coinductive_computation_type_constant_entry ?location
         identifier)

  let add_abbreviation_computation_type_constant state ?location identifier =
    add_declaration state identifier
      (Entry.make_abbreviation_computation_type_constant_entry ?location
         identifier)

  let add_computation_term_constructor state ?location identifier =
    add_declaration state identifier
      (Entry.make_computation_term_constructor_entry ?location identifier)

  let add_computation_term_destructor state ?location identifier =
    add_declaration state identifier
      (Entry.make_computation_term_destructor_entry ?location identifier)

  let add_program_constant state ?location identifier =
    add_declaration state identifier
      (Entry.make_program_constant_entry ?location identifier)

  let add_module state ?location identifier f =
    let default_associativity = get_default_associativity state in
    let default_precedence = get_default_precedence state in
    let module_scope = create_module_scope () in
    push_scope state module_scope;
    let x = f state in
    match pop_scope state with
    | Module_scope { declarations; _ } ->
        add_declaration state identifier ~subtree:declarations
          (Entry.make_module_entry ?location identifier);
        set_default_associativity state default_associativity;
        set_default_precedence state default_precedence;
        x

  let rec lookup_in_scopes scopes identifiers =
    match scopes with
    | [] ->
        Error.raise
          (Qualified_identifier.Unbound_qualified_identifier
             (Qualified_identifier.from_list1 identifiers))
    | scope :: scopes -> (
        match
          Binding_tree.maximum_lookup identifiers (get_scope_bindings scope)
        with
        | `Bound result -> result
        | `Partially_bound
            ( bound_segments
            , (identifier, _entry, _subtree)
            , _unbound_segments ) ->
            Error.raise
              (Qualified_identifier.Unbound_namespace
                 (Qualified_identifier.make ~namespaces:bound_segments
                    identifier))
        | `Unbound _ -> lookup_in_scopes scopes identifiers)

  let lookup state query =
    let identifiers = Qualified_identifier.to_list1 query in
    lookup_in_scopes (List1.to_list state.scopes) identifiers

  let lookup_operator state constant =
    let entry, _subtree = lookup state constant in
    entry.Entry.operator

  let lookup_operator_precedence state constant =
    Option.map Operator.precedence (lookup_operator state constant)

  let modify_operator state identifier f =
    let entry, subtree = lookup state identifier in
    let entry' = Entry.modify_operator f entry in
    let bindings = get_current_scope_bindings state in
    if Binding_tree.mem identifier bindings then
      Binding_tree.replace identifier
        (fun _entry _subtree -> (entry', subtree))
        bindings
    else Binding_tree.add identifier ~subtree entry' bindings;
    match get_current_scope state with
    | Module_scope { declarations; _ } ->
        if Binding_tree.mem identifier declarations then
          Binding_tree.replace identifier
            (fun _entry subtree -> (entry', subtree))
            declarations
        else ()

  let[@warning "-23"] make_prefix state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    modify_operator state constant (fun _operator ->
        Option.some (Operator.make_prefix ~precedence))

  let[@warning "-23"] make_infix state ?precedence ?associativity constant =
    let precedence = get_default_precedence_opt state precedence in
    let associativity = get_default_associativity_opt state associativity in
    modify_operator state constant (fun _operator ->
        Option.some (Operator.make_infix ~precedence ~associativity))

  let[@warning "-23"] make_postfix state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    modify_operator state constant (fun _operator ->
        Option.some (Operator.make_postfix ~precedence))

  let open_namespace state identifier =
    let _entry, subtree = lookup state identifier in
    let bindings = get_current_scope_bindings state in
    Binding_tree.add_all bindings subtree

  let open_module state identifier = open_namespace state identifier

  let add_synonym state ?location:_ qualified_identifier synonym =
    let entry, subtree = lookup state qualified_identifier in
    add_binding state synonym ~subtree entry

  let add_abbreviation state module_identifier abbreviation =
    add_synonym state module_identifier abbreviation

  let traverse_option state m x_opt =
    match x_opt with
    | Option.None -> Option.none
    | Option.Some x ->
        let y = m state x in
        Option.some y

  let rec traverse_list state f l =
    match l with
    | [] -> []
    | x :: xs ->
        let y = f state x in
        let ys = traverse_list state f xs in
        y :: ys

  let traverse_list1 state f (List1.T (x, xs)) =
    let y = f state x in
    let ys = traverse_list state f xs in
    List1.from y ys

  let traverse_list2 state f (List2.T (x1, x2, xs)) =
    let y1 = f state x1 in
    let y2 = f state x2 in
    let ys = traverse_list state f xs in
    List2.from y1 y2 ys

  let rec traverse_list_void state f l =
    match l with
    | [] -> ()
    | x :: xs ->
        f state x;
        traverse_list_void state f xs

  let traverse_list1_void state f (List1.T (x, xs)) =
    f state x;
    traverse_list_void state f xs
end
