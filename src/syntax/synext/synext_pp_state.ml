open Support
open Synext_definition
open Syncom

module type PRINTING_STATE = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** @closed *)
  include Format_state.S with type state := state

  val add_module :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val open_module : state -> Qualified_identifier.t -> Unit.t

  val add_abbreviation :
    state -> Qualified_identifier.t -> Identifier.t -> Unit.t

  val set_default_associativity : state -> Associativity.t -> Unit.t

  val get_default_associativity : state -> Associativity.t

  val set_default_precedence : state -> Int.t -> Unit.t

  val get_default_precedence : state -> Int.t

  val add_lf_type_constant :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_lf_term_constant :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_schema_constant :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_inductive_computation_type_constant :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_stratified_computation_type_constant :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_coinductive_computation_type_constant :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_abbreviation_computation_type_constant :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_computation_term_constructor :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_computation_term_destructor :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_program_constant :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_prefix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  val add_infix_notation :
       state
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  val add_postfix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  val add_postponed_prefix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  val add_postponed_infix_notation :
       state
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  val add_postponed_postfix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  val apply_postponed_fixity_pragmas : state -> unit

  val lookup_operator :
    state -> Qualified_identifier.t -> Operator.t Option.t

  val lookup_operator_precedence :
    state -> Qualified_identifier.t -> Int.t Option.t
end

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

  let modify_operator f entry =
    let operator' = f entry.operator in
    { entry with operator = operator' } [@warning "-23"]
end

module Printing_state = struct
  type scope =
    | Module_scope of
        { bindings : Entry.t Binding_tree.t
        ; declarations : Entry.t Binding_tree.t
        }

  (** The type of fixity pragmas that are postponed to be applied at a later
      point. The default precedence and associativity to be used are
      determined where the pragma is declared, hence why those fields are not
      optional like in the external syntax. *)
  type postponed_fixity_pragma =
    | Prefix_fixity of
        { constant : Qualified_identifier.t
        ; precedence : Int.t
        }
    | Infix_fixity of
        { constant : Qualified_identifier.t
        ; precedence : Int.t
        ; associativity : Associativity.t
        }
    | Postfix_fixity of
        { constant : Qualified_identifier.t
        ; precedence : Int.t
        }

  type state =
    { mutable formatter : Format.formatter
    ; mutable scopes : scope List1.t
    ; mutable default_precedence : Int.t
    ; mutable default_associativity : Associativity.t
    ; mutable postponed_fixity_pragmas : postponed_fixity_pragma List.t
          (** The list of fixity pragmas that refer to constants declared
              immediately after them instead of pragmas declared earlier. *)
    }

  include (
    Format_state.Make (struct
      type nonrec state = state

      let get_formatter state = state.formatter
    end) :
      Format_state.S with type state := state)

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
    ; postponed_fixity_pragmas = []
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
        | Binding_tree.Bound { entry; subtree; _ } -> (entry, subtree)
        | Binding_tree.Partially_bound { leading_segments; segment; _ } ->
            Error.raise
              (Qualified_identifier.Unbound_namespace
                 (Qualified_identifier.make ~namespaces:leading_segments
                    segment))
        | Binding_tree.Unbound _ -> lookup_in_scopes scopes identifiers)

  let lookup state query =
    let identifiers = Qualified_identifier.to_list1 query in
    try lookup_in_scopes (List1.to_list state.scopes) identifiers with
    | exn ->
        Error.re_raise
          (Error.located_exception1
             (Qualified_identifier.location query)
             exn)

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

  let add_prefix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    modify_operator state constant (fun _operator ->
        Option.some (Operator.make_prefix ~precedence))

  let add_infix_notation state ?precedence ?associativity constant =
    let precedence = get_default_precedence_opt state precedence in
    let associativity = get_default_associativity_opt state associativity in
    modify_operator state constant (fun _operator ->
        Option.some (Operator.make_infix ~precedence ~associativity))

  let add_postfix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    modify_operator state constant (fun _operator ->
        Option.some (Operator.make_postfix ~precedence))

  let add_postponed_notation state pragma =
    state.postponed_fixity_pragmas <-
      pragma :: state.postponed_fixity_pragmas

  let add_postponed_prefix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    add_postponed_notation state (Prefix_fixity { precedence; constant })

  let add_postponed_infix_notation state ?precedence ?associativity constant
      =
    let precedence = get_default_precedence_opt state precedence in
    let associativity = get_default_associativity_opt state associativity in
    add_postponed_notation state
      (Infix_fixity { precedence; associativity; constant })

  let add_postponed_postfix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    add_postponed_notation state (Postfix_fixity { precedence; constant })

  let apply_postponed_fixity_pragmas =
    let apply_postponed_fixity_pragma state = function
      | Prefix_fixity { constant; precedence } ->
          add_prefix_notation state ~precedence constant
      | Infix_fixity { constant; precedence; associativity } ->
          add_infix_notation state ~precedence ~associativity constant
      | Postfix_fixity { constant; precedence } ->
          add_postfix_notation state ~precedence constant
    in
    fun state ->
      List.iter_rev
        (apply_postponed_fixity_pragma state)
        state.postponed_fixity_pragmas;
      state.postponed_fixity_pragmas <- []

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
end
