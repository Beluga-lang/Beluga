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

exception Bound_module of Qualified_identifier.t

exception Bound_program_constant of Qualified_identifier.t

exception Duplicate_pattern_variables of Identifier.t List2.t

exception Invalid_prefix_pragma of { actual_arity : Int.t }

exception Invalid_infix_pragma of { actual_arity : Int.t }

exception Invalid_postfix_pragma of { actual_arity : Int.t }

let () =
  Error.register_exception_printer (function
    | Expected_operator qualified_identifier ->
        Format.dprintf "Expected %a to be a bound operator."
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
    | Bound_module qualified_identifier ->
        Format.dprintf "%a is a bound module." Qualified_identifier.pp
          qualified_identifier
    | Bound_program_constant qualified_identifier ->
        Format.dprintf "%a is a bound program." Qualified_identifier.pp
          qualified_identifier
    | Duplicate_pattern_variables _ ->
        Format.dprintf "%a" Format.pp_print_text
          "Illegal duplicate pattern variables."
    | Invalid_prefix_pragma { actual_arity } ->
        Format.dprintf "Can't make an operator with arity %d prefix."
          actual_arity
    | Invalid_infix_pragma { actual_arity } ->
        Format.dprintf "Can't make an operator with arity %d infix."
          actual_arity
    | Invalid_postfix_pragma { actual_arity } ->
        Format.dprintf "Can't make an operator with arity %d postfix."
          actual_arity
    | exn -> Error.raise_unsupported_exception_printing exn)

module type DISAMBIGUATION_STATE = sig
  include State.STATE

  type data = private
    { location : Location.t
    ; operator : Operator.t Option.t
    ; arity : Int.t Option.t
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
    | Module
    | Program_constant

  (** {1 Variables} *)

  val add_lf_term_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_meta_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_context_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_computation_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_lf_term_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_meta_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_context_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_computation_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

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

  val with_free_variables_as_pattern_variables :
    pattern:'a t -> expression:'b t -> ('a * 'b) t

  val with_scope : 'a t -> 'a t

  val with_parent_scope : 'a t -> 'a t

  (** {1 Constants} *)

  val add_lf_type_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_lf_term_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_schema_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_inductive_computation_type_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_stratified_computation_type_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_coinductive_computation_type_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_abbreviation_computation_type_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_computation_term_constructor :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_computation_term_destructor :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_program_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_module : ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  (** {1 Lookups} *)

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

  val actual_binding_exn : Qualified_identifier.t -> entry * data -> exn

  (** {1 Signature Operations} *)

  val open_module : Qualified_identifier.t -> Unit.t t

  val get_default_associativity : Associativity.t t

  val set_default_associativity : Associativity.t -> Unit.t t

  val get_default_precedence : Int.t t

  val set_default_precedence : Int.t -> Unit.t t

  val add_prefix_notation :
    ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  val add_infix_notation :
       ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t t

  val add_postfix_notation :
    ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  val lookup_operator : Qualified_identifier.t -> Operator.t Option.t t

  val add_module_abbreviation :
       ?location:Location.t
    -> Qualified_identifier.t
    -> Identifier.t
    -> Unit.t t
end

module Persistent_disambiguation_state = struct
  type data =
    { location : Location.t
    ; operator : Operator.t Option.t
    ; arity : Int.t Option.t
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
    | Module
    | Program_constant

  type bindings = (entry * data) Binding_tree.t

  type substate =
    | Pattern_state of
        { pattern_bindings : bindings
        ; inner_pattern_bindings : (entry * data) List1.t Identifier.Hamt.t
        ; pattern_variables_rev : Identifier.t List.t
        ; expression_bindings : bindings
        }
    | Module_state of
        { bindings : bindings
        ; declarations : bindings
        }
    | Scope_state of
        { bindings : bindings
        ; parent : substate Option.t
        }

  type state =
    { substate : substate
    ; default_associativity : Associativity.t
    ; default_precedence : Int.t
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
    { substate =
        Scope_state { bindings = Binding_tree.empty; parent = Option.none }
    ; default_precedence = Synext.default_precedence
    ; default_associativity = Synext.default_associativity
    }

  let is_entry_variable = function
    | Lf_term_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Computation_variable ->
        true
    | Lf_type_constant
    | Lf_term_constant
    | Schema_constant
    | Computation_inductive_type_constant
    | Computation_stratified_type_constant
    | Computation_coinductive_type_constant
    | Computation_abbreviation_type_constant
    | Computation_term_constructor
    | Computation_term_destructor
    | Module
    | Program_constant ->
        false

  let[@inline] set_default_associativity default_associativity =
    modify (fun state -> { state with default_associativity })

  let get_default_associativity =
    let* state = get in
    return state.default_associativity

  let[@inline] set_default_precedence default_precedence =
    modify (fun state -> { state with default_precedence })

  let get_default_precedence =
    let* state = get in
    return state.default_precedence

  let get_substate =
    let* state = get in
    return state.substate

  let[@inline] set_substate substate =
    modify (fun state -> { state with substate })

  let[@inline] modify_substate f =
    let* substate = get_substate in
    let substate' = f substate in
    set_substate substate'

  let[@inline] set_substate_bindings bindings = function
    | Pattern_state state ->
        Pattern_state { state with pattern_bindings = bindings }
    | Module_state state -> Module_state { state with bindings }
    | Scope_state state -> Scope_state { state with bindings }

  let[@inline] get_substate_bindings = function
    | Pattern_state state -> state.pattern_bindings
    | Module_state state -> state.bindings
    | Scope_state state -> state.bindings

  let[@inline] set_bindings bindings =
    modify_substate (set_substate_bindings bindings)

  let get_bindings = get_substate $> get_substate_bindings

  let[@inline] modify_bindings f =
    let* bindings = get_bindings in
    let bindings' = f bindings in
    set_bindings bindings'

  let[@inline] add_binding identifier entry ?subtree bindings =
    Binding_tree.add_toplevel identifier ?subtree entry bindings

  let make_entry_data ?location ?arity ?operator identifier =
    let location =
      Option.value location ~default:(Identifier.location identifier)
    in
    { location; operator; arity }

  let get_module_declarations =
    get_substate >>= function
    | Module_state substate -> return (Option.some substate.declarations)
    | Pattern_state _
    | Scope_state _ ->
        return Option.none

  let[@inline] set_module_declarations declarations =
    modify_substate (function
      | Module_state substate -> Module_state { substate with declarations }
      | Pattern_state _
      | Scope_state _ ->
          Error.raise_violation "[set_module_declarations] invalid state")

  let[@inline] modify_module_declarations f =
    get_module_declarations >>= function
    | Option.None -> return ()
    | Option.Some declarations ->
        let declarations' = f declarations in
        set_module_declarations declarations'

  (** {1 Variables} *)

  let make_lf_term_variable_entry ?location identifier =
    let data = make_entry_data ?location identifier in
    (Lf_term_variable, data)

  let make_meta_variable_entry ?location identifier =
    let data = make_entry_data ?location identifier in
    (Meta_variable, data)

  let make_parameter_variable_entry ?location identifier =
    let data = make_entry_data ?location identifier in
    (Parameter_variable, data)

  let make_substitution_variable_entry ?location identifier =
    let data = make_entry_data ?location identifier in
    (Substitution_variable, data)

  let make_context_variable_entry ?location identifier =
    let data = make_entry_data ?location identifier in
    (Context_variable, data)

  let make_computation_variable_entry ?location identifier =
    let data = make_entry_data ?location identifier in
    (Computation_variable, data)

  (** {1 Constants} *)

  let make_lf_type_constant_entry ?location ?arity identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Lf_type_constant, data)

  let make_lf_term_constant_entry ?location ?arity identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Lf_term_constant, data)

  let make_schema_constant_entry ?location ?arity identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Schema_constant, data)

  let make_inductive_computation_type_constant_entry ?location ?arity
      identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Computation_inductive_type_constant, data)

  let make_stratified_computation_type_constant_entry ?location ?arity
      identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Computation_stratified_type_constant, data)

  let make_coinductive_computation_type_constant_entry ?location ?arity
      identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Computation_coinductive_type_constant, data)

  let make_abbreviation_computation_type_constant_entry ?location ?arity
      identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Computation_abbreviation_type_constant, data)

  let make_computation_term_constructor_entry ?location ?arity identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Computation_term_constructor, data)

  let make_computation_term_destructor_entry ?location ?arity identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Computation_term_destructor, data)

  let make_program_constant_entry ?location ?arity identifier =
    let data = make_entry_data ?location ?arity identifier in
    (Program_constant, data)

  let make_module_entry ?location identifier _declarations =
    let data = make_entry_data ?location identifier in
    (Module, data)

  (** {1 Free Variables} *)

  let get_inner_pattern_bindings =
    let* state = get in
    match state.substate with
    | Pattern_state substate ->
        return (Option.some substate.inner_pattern_bindings)
    | Module_state _
    | Scope_state _ ->
        return Option.none

  let is_inner_pattern_binding identifier =
    get_inner_pattern_bindings >>= function
    | Option.Some inner_pattern_bindings ->
        return
          (Option.some
             (Identifier.Hamt.mem identifier inner_pattern_bindings))
    | Option.None -> return Option.none

  let push_inner_pattern_binding identifier entry =
    modify (fun state ->
        match state.substate with
        | Pattern_state substate ->
            let entries =
              match
                Identifier.Hamt.find_opt identifier
                  substate.inner_pattern_bindings
              with
              | Option.None -> List1.singleton entry
              | Option.Some entries -> List1.cons entry entries
            in
            { state with
              substate =
                Pattern_state
                  { substate with
                    inner_pattern_bindings =
                      Identifier.Hamt.add identifier entries
                        substate.inner_pattern_bindings
                  }
            }
        | Module_state _
        | Scope_state _ ->
            state)

  let pop_inner_pattern_binding identifier =
    modify (fun state ->
        match state.substate with
        | Pattern_state substate ->
            let inner_pattern_bindings' =
              match
                Identifier.Hamt.find_opt identifier
                  substate.inner_pattern_bindings
              with
              | Option.None ->
                  Error.raise_violation
                    "[pop_inner_pattern_binding] invalid state"
              | Option.Some (List1.T (_entry, [])) ->
                  Identifier.Hamt.remove identifier
                    substate.inner_pattern_bindings
              | Option.Some (List1.T (_x1, x2 :: xs)) ->
                  Identifier.Hamt.add identifier (List1.from x2 xs)
                    substate.inner_pattern_bindings
            in
            { state with
              substate =
                Pattern_state
                  { substate with
                    inner_pattern_bindings = inner_pattern_bindings'
                  }
            }
        | Module_state _
        | Scope_state _ ->
            state)

  let add_inner_pattern_binding = push_inner_pattern_binding

  let add_free_variable identifier f =
    modify (fun state ->
        match state.substate with
        | Pattern_state substate ->
            { state with
              substate =
                Pattern_state
                  { substate with
                    expression_bindings = f substate.expression_bindings
                  ; pattern_variables_rev =
                      identifier :: substate.pattern_variables_rev
                  }
            }
        | Module_state _
        | Scope_state _ ->
            state)

  let add_free_lf_term_variable ?location identifier =
    let entry = make_lf_term_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder
    &> add_free_variable identifier adder
    &> add_inner_pattern_binding identifier entry

  let add_free_meta_variable ?location identifier =
    let entry = make_meta_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder
    &> add_free_variable identifier adder
    &> add_inner_pattern_binding identifier entry

  let add_free_parameter_variable ?location identifier =
    let entry = make_parameter_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder
    &> add_free_variable identifier adder
    &> add_inner_pattern_binding identifier entry

  let add_free_substitution_variable ?location identifier =
    let entry = make_substitution_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder
    &> add_free_variable identifier adder
    &> add_inner_pattern_binding identifier entry

  let add_free_context_variable ?location identifier =
    let entry = make_context_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder
    &> add_free_variable identifier adder
    &> add_inner_pattern_binding identifier entry

  let add_free_computation_variable ?location identifier =
    let entry = make_computation_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    add_free_variable identifier adder

  let add_lf_term_variable ?location identifier =
    let entry = make_lf_term_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder

  let add_meta_variable ?location identifier =
    let entry = make_meta_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder

  let add_parameter_variable ?location identifier =
    let entry = make_parameter_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder

  let add_substitution_variable ?location identifier =
    let entry = make_substitution_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder

  let add_context_variable ?location identifier =
    let entry = make_context_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder

  let add_computation_variable ?location identifier =
    let entry = make_computation_variable_entry ?location identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder

  let add_lf_type_constant ?location ?arity identifier =
    let entry = make_lf_type_constant_entry ?location ?arity identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_lf_term_constant ?location ?arity identifier =
    let entry = make_lf_term_constant_entry ?location ?arity identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_schema_constant ?location ?arity identifier =
    let entry = make_schema_constant_entry ?location ?arity identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_inductive_computation_type_constant ?location ?arity identifier =
    let entry =
      make_inductive_computation_type_constant_entry ?location ?arity
        identifier
    in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_stratified_computation_type_constant ?location ?arity identifier =
    let entry =
      make_stratified_computation_type_constant_entry ?location ?arity
        identifier
    in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_coinductive_computation_type_constant ?location ?arity identifier =
    let entry =
      make_coinductive_computation_type_constant_entry ?location ?arity
        identifier
    in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_abbreviation_computation_type_constant ?location ?arity identifier
      =
    let entry =
      make_abbreviation_computation_type_constant_entry ?location ?arity
        identifier
    in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_computation_term_constructor ?location ?arity identifier =
    let entry =
      make_computation_term_constructor_entry ?location ?arity identifier
    in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_computation_term_destructor ?location ?arity identifier =
    let entry =
      make_computation_term_destructor_entry ?location ?arity identifier
    in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_program_constant ?location ?arity identifier =
    let entry = make_program_constant_entry ?location ?arity identifier in
    let adder = Binding_tree.add_toplevel identifier entry in
    modify_bindings adder <& modify_module_declarations adder

  let add_module ?location identifier m =
    let* state = get in
    let* bindings = get_bindings in
    let* () =
      put
        { state with
          substate =
            Module_state { bindings; declarations = Binding_tree.empty }
        }
    in
    let* x = m in
    get_module_declarations >>= function
    | Option.None -> Error.raise_violation "[add_module] invalid state"
    | Option.Some declarations ->
        let* () = put state in
        let entry = make_module_entry ?location identifier declarations in
        let adder =
          Binding_tree.add_toplevel identifier entry ~subtree:declarations
        in
        let* () =
          modify_bindings adder <& modify_module_declarations adder
        in
        return x

  (** {1 Lookups} *)

  let forget_variables_outside_pattern' inner_pattern_bindings_opt query
      (entry, data) subtree =
    if is_entry_variable entry then
      match inner_pattern_bindings_opt with
      | Option.None -> ((entry, data), subtree)
      | Option.Some inner_pattern_bindings ->
          if Identifier.Hamt.mem query inner_pattern_bindings then
            ((entry, data), subtree)
          else Error.raise (Unbound_identifier query)
    else ((entry, data), subtree)

  let forget_variables_outside_pattern query (entry, data) subtree =
    if is_entry_variable entry then
      is_inner_pattern_binding query >>= function
      | Option.None
      | Option.Some true ->
          return ((entry, data), subtree)
      | Option.Some false -> Error.raise (Unbound_identifier query)
    else return ((entry, data), subtree)

  let lookup_toplevel' query =
    let* bindings = get_bindings in
    try
      let (entry, data), subtree =
        Binding_tree.lookup_toplevel query bindings
      in
      forget_variables_outside_pattern query (entry, data) subtree
    with
    | Binding_tree.Unbound_identifier identifier -> (
        get_inner_pattern_bindings >>= function
        | Option.None -> Error.raise (Unbound_identifier identifier)
        | Option.Some inner_pattern_bindings -> (
            match Identifier.Hamt.find_opt query inner_pattern_bindings with
            | Option.Some (List1.T (entry, _)) ->
                return (entry, Binding_tree.empty)
            | Option.None -> Error.raise (Unbound_identifier identifier)))

  let lookup_toplevel query =
    try_catch
      (lazy
        (let* entry, _subtree = lookup_toplevel' query in
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

  let rec partial_lookup_nested inner_pattern_bindings_opt namespaces
      identifier tree =
    match namespaces with
    | [] -> (
        try
          let entry, subtree =
            Binding_tree.lookup_toplevel identifier tree
          in
          (* TODO: Refactor *)
          ignore
            (forget_variables_outside_pattern' inner_pattern_bindings_opt
               identifier entry subtree);
          `Totally_bound (List1.singleton (identifier, entry))
        with
        | Unbound_identifier _
        | Binding_tree.Unbound_identifier _ ->
            `Totally_unbound (List1.singleton identifier))
    | x :: xs -> (
        try
          let entry, subtree = Binding_tree.lookup_toplevel x tree in
          (* TODO: Refactor *)
          ignore
            (forget_variables_outside_pattern' inner_pattern_bindings_opt x
               entry subtree);
          match
            partial_lookup_nested inner_pattern_bindings_opt xs identifier
              subtree
          with
          | `Totally_bound xs' -> `Totally_bound (List1.cons (x, entry) xs')
          | `Partially_bound (bound, unbound) ->
              `Partially_bound (List1.cons (x, entry) bound, unbound)
          | `Totally_unbound xs' ->
              `Partially_bound (List1.singleton (x, entry), xs')
        with
        | Unbound_identifier _
        | Binding_tree.Unbound_identifier _ ->
            `Totally_unbound
              (List1.append (List1.from x xs) (List1.singleton identifier)))

  let partial_lookup' query =
    let namespaces, identifier = List1.unsnoc query in
    let* inner_pattern_bindings_opt = get_inner_pattern_bindings in
    let* bindings = get_bindings in
    return
      (partial_lookup_nested inner_pattern_bindings_opt namespaces identifier
         bindings)

  let partial_lookup query =
    let identifier = Qualified_identifier.name query
    and namespaces = Qualified_identifier.namespaces query in
    let* inner_pattern_bindings_opt = get_inner_pattern_bindings in
    get_bindings
    $> partial_lookup_nested inner_pattern_bindings_opt namespaces identifier

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

  let with_inner_bound_entry identifier entry m =
    let* () = push_inner_pattern_binding identifier entry in
    let* x = m in
    let* () = pop_inner_pattern_binding identifier in
    return x

  let with_inner_bound_lf_term_variable ?location identifier m =
    let entry = make_lf_term_variable_entry ?location identifier in
    with_inner_bound_entry identifier entry m

  let with_inner_bound_meta_variable ?location identifier m =
    let entry = make_meta_variable_entry ?location identifier in
    with_inner_bound_entry identifier entry m

  let with_inner_bound_parameter_variable ?location identifier m =
    let entry = make_parameter_variable_entry ?location identifier in
    with_inner_bound_entry identifier entry m

  let with_inner_bound_context_variable ?location identifier m =
    let entry = make_context_variable_entry ?location identifier in
    with_inner_bound_entry identifier entry m

  let with_inner_bound_substitution_variable ?location identifier m =
    let entry = make_substitution_variable_entry ?location identifier in
    with_inner_bound_entry identifier entry m

  let with_lf_term_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_lf_term_variable identifier
         (add_lf_term_variable ?location identifier &> m))

  let with_meta_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_meta_variable identifier
         (add_meta_variable ?location identifier &> m))

  let with_parameter_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_parameter_variable identifier
         (add_parameter_variable ?location identifier &> m))

  let with_context_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_context_variable identifier
         (add_context_variable ?location identifier &> m))

  let with_substitution_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_substitution_variable identifier
         (add_substitution_variable ?location identifier &> m))

  let with_comp_variable ?location identifier m =
    with_bindings_checkpoint
      (add_computation_variable ?location identifier &> m)

  let with_scope m =
    let* state = get in
    let* bindings = get_bindings in
    let* () =
      put
        { state with
          substate =
            Scope_state { bindings; parent = Option.some state.substate }
        }
    in
    let* x = m in
    let* () = put state in
    return x

  let with_parent_scope m =
    let* state = get in
    match state.substate with
    | Scope_state { parent; _ } -> (
        match parent with
        | Option.Some parent ->
            let* () = put { state with substate = parent } in
            let* x = with_scope m in
            let* () = put state in
            return x
        | Option.None ->
            Error.raise_violation "[with_parent_scope] invalid state")
    | Pattern_state _
    | Module_state _ ->
        Error.raise_violation "[with_parent_scope] invalid state"

  let get_pattern_variables_and_expression_state =
    let* state = get in
    match state.substate with
    | Pattern_state o ->
        let pattern_variables = List.rev o.pattern_variables_rev in
        return (pattern_variables, o.expression_bindings)
    | Module_state _
    | Scope_state _ ->
        Error.raise_violation
          "[get_pattern_variables_and_expression_state] invalid state"

  let raise_duplicate_identifiers_exception f duplicates =
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

  let with_free_variables_as_pattern_variables ~pattern ~expression =
    let* state = get in
    let* bindings = get_bindings in
    let* () =
      put
        { state with
          substate =
            Pattern_state
              { pattern_bindings = bindings
              ; inner_pattern_bindings = Identifier.Hamt.empty
              ; pattern_variables_rev = []
              ; expression_bindings = bindings
              }
        }
    in
    let* pattern' = pattern in
    let* pattern_variables, expression_bindings =
      get_pattern_variables_and_expression_state
    in
    match Identifier.find_duplicates pattern_variables with
    | Option.Some duplicates ->
        let* () = put state in
        raise_duplicate_identifiers_exception
          (fun identifiers -> Duplicate_pattern_variables identifiers)
          duplicates
    | Option.None ->
        let* () = put state in
        let* () = set_bindings expression_bindings in
        let* expression' = expression in
        let* () = put state in
        return (pattern', expression')

  let lookup_operator =
    lookup >=> function
    | Result.Ok (_, { operator; _ }) -> return operator
    | Result.Error _ -> return Option.none

  let update_module_declaration identifier =
    modify (fun state ->
        match state.substate with
        | Module_state o -> (
            try
              let entry, subtree =
                Binding_tree.lookup identifier o.declarations
              in
              let declarations' =
                Binding_tree.add identifier entry ~subtree o.declarations
              in
              { state with
                substate =
                  Module_state { o with declarations = declarations' }
              }
            with
            | Binding_tree.Unbound_identifier _
            | Binding_tree.Unbound_qualified_identifier _
            | Binding_tree.Unbound_namespace _ ->
                state)
        | Pattern_state _
        | Scope_state _ ->
            state)

  let modify_operator identifier f =
    let* (entry, data), subtree = lookup' identifier in
    match data.arity with
    | Option.Some arity ->
        let operator' = f data.operator ~arity in
        let data' = { data with operator = operator' } in
        modify_bindings (Binding_tree.add identifier (entry, data') ~subtree)
        &> update_module_declaration identifier
    | Option.None ->
        Error.raise_at1
          (Qualified_identifier.location identifier)
          (Expected_operator identifier)

  let get_default_precedence_opt = function
    | Option.None -> get_default_precedence
    | Option.Some precedence -> return precedence

  let get_default_associativity_opt = function
    | Option.None -> get_default_associativity
    | Option.Some associativity -> return associativity

  let add_prefix_notation ?precedence constant =
    let* precedence = get_default_precedence_opt precedence in
    modify_operator constant (fun _operator ~arity ->
        if arity = 1 then Option.some (Operator.make_prefix ~precedence)
        else
          Error.raise_at1
            (Qualified_identifier.location constant)
            (Invalid_prefix_pragma { actual_arity = arity }))

  let add_infix_notation ?precedence ?associativity constant =
    let* precedence = get_default_precedence_opt precedence in
    let* associativity = get_default_associativity_opt associativity in
    modify_operator constant (fun _operator ~arity ->
        if arity = 2 then
          Option.some (Operator.make_infix ~associativity ~precedence)
        else
          Error.raise_at1
            (Qualified_identifier.location constant)
            (Invalid_infix_pragma { actual_arity = arity }))

  let add_postfix_notation ?precedence constant =
    let* precedence = get_default_precedence_opt precedence in
    modify_operator constant (fun _operator ~arity ->
        if arity = 1 then Option.some (Operator.make_postfix ~precedence)
        else
          Error.raise_at1
            (Qualified_identifier.location constant)
            (Invalid_postfix_pragma { actual_arity = arity }))

  let add_module_abbreviation ?location module_identifier abbreviation =
    lookup module_identifier >>= function
    | Result.Ok (Module, _) ->
        add_synonym ?location module_identifier abbreviation
    | Result.Ok entry ->
        Error.raise_at1
          (Qualified_identifier.location module_identifier)
          (Error.composite_exception2 (Expected_module module_identifier)
             (actual_binding_exn module_identifier entry))
    | Result.Error cause ->
        Error.raise_at1
          (Qualified_identifier.location module_identifier)
          cause
end
