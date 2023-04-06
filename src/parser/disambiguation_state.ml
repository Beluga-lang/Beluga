open Support
open Beluga_syntax

exception Expected_module of Qualified_identifier.t

exception Expected_operator of Qualified_identifier.t

exception Bound_lf_type_constant of Qualified_identifier.t

exception Bound_lf_term_constant of Qualified_identifier.t

exception Bound_lf_variable of Qualified_identifier.t

exception Bound_meta_variable of Qualified_identifier.t

exception Bound_parameter_variable of Qualified_identifier.t

exception Bound_substitution_variable of Qualified_identifier.t

exception Bound_context_variable of Qualified_identifier.t

exception Bound_contextual_variable of Qualified_identifier.t

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

exception Invalid_prefix_pragma of { actual_arity : Int.t Option.t }

exception Invalid_infix_pragma of { actual_arity : Int.t Option.t }

exception Invalid_postfix_pragma of { actual_arity : Int.t Option.t }

let () =
  Error.register_exception_printer (function
    | Expected_operator qualified_identifier ->
        Format.dprintf
          "Expected %a to be a constant that can be made into an operator."
          Qualified_identifier.pp qualified_identifier
    | Expected_module qualified_identifier ->
        Format.dprintf "Expected %a to be a module." Qualified_identifier.pp
          qualified_identifier
    | Bound_lf_type_constant qualified_identifier ->
        Format.dprintf "%a is a bound LF type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_lf_term_constant qualified_identifier ->
        Format.dprintf "%a is a bound LF term constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_lf_variable qualified_identifier ->
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
    | Bound_contextual_variable qualified_identifier ->
        Format.dprintf "%a is a bound contextual variable."
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
    | Invalid_prefix_pragma { actual_arity } -> (
        match actual_arity with
        | Option.Some actual_arity ->
            Format.dprintf
              "Can't make an operator with arity %d prefix.@ Prefix \
               operators must have arity 1."
              actual_arity
        | Option.None ->
            Format.dprintf
              "Can't make a constant into a prefix operator if it is \
               untyped.")
    | Invalid_infix_pragma { actual_arity } -> (
        match actual_arity with
        | Option.Some actual_arity ->
            Format.dprintf
              "Can't make an operator with arity %d infix.@ Infix operators \
               must have arity 2."
              actual_arity
        | Option.None ->
            Format.dprintf
              "Can't make a constant into an infix operator if it is \
               untyped.")
    | Invalid_postfix_pragma { actual_arity } -> (
        match actual_arity with
        | Option.Some actual_arity ->
            Format.dprintf
              "Can't make an operator with arity %d postfix.@ Postfix \
               operators must have arity 1."
              actual_arity
        | Option.None ->
            Format.dprintf
              "Can't make a constant into a postfix operator if it is \
               untyped.")
    | exn -> Error.raise_unsupported_exception_printing exn)

module type ENTRY = sig
  type t

  val is_lf_variable : t -> Bool.t

  val is_meta_variable : t -> Bool.t

  val is_parameter_variable : t -> Bool.t

  val is_substitution_variable : t -> Bool.t

  val is_context_variable : t -> Bool.t

  val is_computation_variable : t -> Bool.t

  val is_variable : t -> Bool.t

  val is_lf_type_constant : t -> Bool.t

  val is_lf_term_constant : t -> Bool.t

  val is_schema_constant : t -> Bool.t

  val is_computation_inductive_type_constant : t -> Bool.t

  val is_computation_stratified_type_constant : t -> Bool.t

  val is_computation_coinductive_type_constant : t -> Bool.t

  val is_computation_abbreviation_type_constant : t -> Bool.t

  val is_computation_term_constructor : t -> Bool.t

  val is_computation_term_destructor : t -> Bool.t

  val is_program_constant : t -> Bool.t

  val is_module : t -> Bool.t
end

module Entry = struct
  type t =
    { binding_location : Location.t
    ; desc : desc
    }

  and desc =
    | Lf_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Contextual_variable
    | Computation_variable
    | Lf_type_constant of
        { operator : Operator.t Option.t
        ; arity : Int.t Option.t
        }
    | Lf_term_constant of
        { operator : Operator.t Option.t
        ; arity : Int.t Option.t
        }
    | Schema_constant
    | Computation_inductive_type_constant of
        { operator : Operator.t Option.t
        ; arity : Int.t Option.t
        }
    | Computation_stratified_type_constant of
        { operator : Operator.t Option.t
        ; arity : Int.t Option.t
        }
    | Computation_coinductive_type_constant of
        { operator : Operator.t Option.t
        ; arity : Int.t Option.t
        }
    | Computation_abbreviation_type_constant of
        { operator : Operator.t Option.t
        ; arity : Int.t Option.t
        }
    | Computation_term_constructor of
        { operator : Operator.t Option.t
        ; arity : Int.t Option.t
        }
    | Computation_term_destructor
    | Program_constant of
        { operator : Operator.t Option.t
        ; arity : Int.t Option.t
        }
    | Module

  let[@inline] binding_location { binding_location; _ } = binding_location

  let operator entry =
    match entry.desc with
    | Lf_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Contextual_variable
    | Computation_variable
    | Schema_constant
    | Computation_term_destructor
    | Module ->
        Option.none
    | Lf_type_constant { operator; _ }
    | Lf_term_constant { operator; _ }
    | Computation_inductive_type_constant { operator; _ }
    | Computation_stratified_type_constant { operator; _ }
    | Computation_coinductive_type_constant { operator; _ }
    | Computation_abbreviation_type_constant { operator; _ }
    | Computation_term_constructor { operator; _ }
    | Program_constant { operator; _ } ->
        operator

  let actual_binding_exn identifier entry =
    match entry.desc with
    | Lf_type_constant _ -> Bound_lf_type_constant identifier
    | Lf_term_constant _ -> Bound_lf_term_constant identifier
    | Lf_variable -> Bound_lf_variable identifier
    | Meta_variable -> Bound_meta_variable identifier
    | Parameter_variable -> Bound_parameter_variable identifier
    | Substitution_variable -> Bound_substitution_variable identifier
    | Context_variable -> Bound_context_variable identifier
    | Contextual_variable -> Bound_contextual_variable identifier
    | Schema_constant -> Bound_schema_constant identifier
    | Computation_variable -> Bound_computation_variable identifier
    | Computation_inductive_type_constant _ ->
        Bound_computation_inductive_type_constant identifier
    | Computation_stratified_type_constant _ ->
        Bound_computation_stratified_type_constant identifier
    | Computation_coinductive_type_constant _ ->
        Bound_computation_coinductive_type_constant identifier
    | Computation_abbreviation_type_constant _ ->
        Bound_computation_abbreviation_type_constant identifier
    | Computation_term_constructor _ ->
        Bound_computation_term_constructor identifier
    | Computation_term_destructor ->
        Bound_computation_term_destructor identifier
    | Module -> Bound_module identifier
    | Program_constant _ -> Bound_program_constant identifier

  let[@inline] is_variable entry =
    match entry.desc with
    | Lf_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Contextual_variable
    | Computation_variable ->
        true
    | Lf_type_constant _
    | Lf_term_constant _
    | Schema_constant
    | Computation_inductive_type_constant _
    | Computation_stratified_type_constant _
    | Computation_coinductive_type_constant _
    | Computation_abbreviation_type_constant _
    | Computation_term_constructor _
    | Computation_term_destructor
    | Module
    | Program_constant _ ->
        false

  let[@inline] modify_operator ~operator ~not_an_operator entry =
    match entry.desc with
    | Lf_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Contextual_variable
    | Computation_variable
    | Schema_constant
    | Computation_term_destructor
    | Module ->
        not_an_operator ()
    | Lf_type_constant e ->
        let operator', arity' = operator e.operator e.arity in
        { entry with
          desc = Lf_type_constant { operator = operator'; arity = arity' }
        }
    | Lf_term_constant e ->
        let operator', arity' = operator e.operator e.arity in
        { entry with
          desc = Lf_term_constant { operator = operator'; arity = arity' }
        }
    | Computation_inductive_type_constant e ->
        let operator', arity' = operator e.operator e.arity in
        { entry with
          desc =
            Computation_inductive_type_constant
              { operator = operator'; arity = arity' }
        }
    | Computation_stratified_type_constant e ->
        let operator', arity' = operator e.operator e.arity in
        { entry with
          desc =
            Computation_stratified_type_constant
              { operator = operator'; arity = arity' }
        }
    | Computation_coinductive_type_constant e ->
        let operator', arity' = operator e.operator e.arity in
        { entry with
          desc =
            Computation_coinductive_type_constant
              { operator = operator'; arity = arity' }
        }
    | Computation_abbreviation_type_constant e ->
        let operator', arity' = operator e.operator e.arity in
        { entry with
          desc =
            Computation_abbreviation_type_constant
              { operator = operator'; arity = arity' }
        }
    | Computation_term_constructor e ->
        let operator', arity' = operator e.operator e.arity in
        { entry with
          desc =
            Computation_term_constructor
              { operator = operator'; arity = arity' }
        }
    | Program_constant e ->
        { entry with
          desc =
            (let operator', arity' = operator e.operator e.arity in
             Program_constant { operator = operator'; arity = arity' })
        }

  let[@inline] is_lf_variable entry =
    match entry.desc with
    | Lf_variable -> true
    | _ -> false

  let[@inline] is_meta_variable entry =
    match entry.desc with
    | Meta_variable
    | Contextual_variable
      (* Meta-variables are contextual variables as well *) ->
        true
    | _ -> false

  let[@inline] is_parameter_variable entry =
    match entry.desc with
    | Parameter_variable
    | Contextual_variable
      (* Parameter variables are contextual variables as well *) ->
        true
    | _ -> false

  let[@inline] is_substitution_variable entry =
    match entry.desc with
    | Substitution_variable
    | Contextual_variable
      (* Substitution variables are contextual variables as well *) ->
        true
    | _ -> false

  let[@inline] is_context_variable entry =
    match entry.desc with
    | Context_variable
    | Contextual_variable
      (* Contextual variables are contextual variables as well *) ->
        true
    | _ -> false

  let[@inline] is_computation_variable entry =
    match entry.desc with
    | Computation_variable -> true
    | _ -> false

  let[@inline] is_lf_type_constant entry =
    match entry.desc with
    | Lf_type_constant _ -> true
    | _ -> false

  let[@inline] is_lf_term_constant entry =
    match entry.desc with
    | Lf_term_constant _ -> true
    | _ -> false

  let[@inline] is_schema_constant entry =
    match entry.desc with
    | Schema_constant -> true
    | _ -> false

  let[@inline] is_computation_inductive_type_constant entry =
    match entry.desc with
    | Computation_inductive_type_constant _ -> true
    | _ -> false

  let[@inline] is_computation_stratified_type_constant entry =
    match entry.desc with
    | Computation_stratified_type_constant _ -> true
    | _ -> false

  let[@inline] is_computation_coinductive_type_constant entry =
    match entry.desc with
    | Computation_coinductive_type_constant _ -> true
    | _ -> false

  let[@inline] is_computation_abbreviation_type_constant entry =
    match entry.desc with
    | Computation_abbreviation_type_constant _ -> true
    | _ -> false

  let[@inline] is_computation_term_constructor entry =
    match entry.desc with
    | Computation_term_constructor _ -> true
    | _ -> false

  let[@inline] is_computation_term_destructor entry =
    match entry.desc with
    | Computation_term_destructor -> true
    | _ -> false

  let[@inline] is_program_constant entry =
    match entry.desc with
    | Program_constant _ -> true
    | _ -> false

  let[@inline] is_module entry =
    match entry.desc with
    | Module -> true
    | _ -> false

  let[@inline] make_binding_location ?location identifier =
    match location with
    | Option.None -> Identifier.location identifier
    | Option.Some location -> location

  let[@inline] make_entry ?location identifier desc =
    let binding_location = make_binding_location ?location identifier in
    { binding_location; desc }

  let make_lf_variable_entry ?location identifier =
    make_entry ?location identifier Lf_variable

  let make_meta_variable_entry ?location identifier =
    make_entry ?location identifier Meta_variable

  let make_parameter_variable_entry ?location identifier =
    make_entry ?location identifier Parameter_variable

  let make_substitution_variable_entry ?location identifier =
    make_entry ?location identifier Substitution_variable

  let make_context_variable_entry ?location identifier =
    make_entry ?location identifier Context_variable

  let make_contextual_variable_entry ?location identifier =
    make_entry ?location identifier Contextual_variable

  let make_computation_variable_entry ?location identifier =
    make_entry ?location identifier Computation_variable

  let make_lf_type_constant_entry ?location ?operator ?arity identifier =
    make_entry ?location identifier (Lf_type_constant { operator; arity })

  let make_lf_term_constant_entry ?location ?operator ?arity identifier =
    make_entry ?location identifier (Lf_term_constant { operator; arity })

  let make_schema_constant_entry ?location identifier =
    make_entry ?location identifier Schema_constant

  let make_inductive_computation_type_constant_entry ?location ?operator
      ?arity identifier =
    make_entry ?location identifier
      (Computation_inductive_type_constant { operator; arity })

  let make_stratified_computation_type_constant_entry ?location ?operator
      ?arity identifier =
    make_entry ?location identifier
      (Computation_stratified_type_constant { operator; arity })

  let make_coinductive_computation_type_constant_entry ?location ?operator
      ?arity identifier =
    make_entry ?location identifier
      (Computation_coinductive_type_constant { operator; arity })

  let make_abbreviation_computation_type_constant_entry ?location ?operator
      ?arity identifier =
    make_entry ?location identifier
      (Computation_abbreviation_type_constant { operator; arity })

  let make_computation_term_constructor_entry ?location ?operator ?arity
      identifier =
    make_entry ?location identifier
      (Computation_term_constructor { operator; arity })

  let make_computation_term_destructor_entry ?location identifier =
    make_entry ?location identifier Computation_term_destructor

  let make_program_constant_entry ?location ?operator ?arity identifier =
    make_entry ?location identifier (Program_constant { operator; arity })

  let make_module_entry ?location identifier =
    make_entry ?location identifier Module
end

module type DISAMBIGUATION_STATE = sig
  include State.STATE

  module Entry : ENTRY

  (** {1 Variables} *)

  val add_lf_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_meta_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_context_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_computation_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_lf_variable : ?location:Location.t -> Identifier.t -> Unit.t t

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

  val with_bound_lf_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_meta_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_parameter_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_substitution_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_context_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_contextual_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_computation_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_pattern_meta_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_pattern_parameter_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_pattern_substitution_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_pattern_context_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_free_variables_as_pattern_variables :
    pattern:'a t -> expression:('a -> 'b t) -> 'b t

  val with_scope : 'a t -> 'a t

  val with_parent_scope : 'a t -> 'a t

  val with_bindings_checkpoint : 'a t -> 'a t

  (** {1 Constants} *)

  val add_lf_type_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_lf_term_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_schema_constant : ?location:Location.t -> Identifier.t -> Unit.t t

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
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_program_constant :
    ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t t

  val add_module : ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  (** {1 Lookups} *)

  exception Unbound_identifier of Identifier.t

  exception Unbound_qualified_identifier of Qualified_identifier.t

  exception Unbound_namespace of Qualified_identifier.t

  val lookup_toplevel : Identifier.t -> (Entry.t, exn) Result.t t

  val lookup : Qualified_identifier.t -> (Entry.t, exn) Result.t t

  val maximum_lookup :
       Identifier.t List1.t
    -> [ `Unbound of Identifier.t List1.t
       | `Partially_bound of
         Identifier.t List.t
         * (Identifier.t * Entry.t)
         * Identifier.t List1.t
       | `Bound of Qualified_identifier.t * Entry.t
       ]
       t

  val actual_binding_exn : Qualified_identifier.t -> Entry.t -> exn

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
  module Binding_tree = Binding_tree.Hamt
  module Entry = Entry

  type bindings = Entry.t Binding_tree.t

  type substate =
    | Pattern_state of
        { pattern_bindings : bindings
        ; inner_pattern_bindings : Entry.t List1.t Identifier.Hamt.t
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

  exception Unbound_identifier = Identifier.Unbound_identifier

  exception
    Unbound_qualified_identifier = Qualified_identifier
                                   .Unbound_qualified_identifier

  exception Unbound_namespace = Qualified_identifier.Unbound_namespace

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let initial_state =
    { substate =
        Module_state
          { bindings = Binding_tree.empty
          ; declarations = Binding_tree.empty
          }
    ; default_precedence = Synext.default_precedence
    ; default_associativity = Synext.default_associativity
    }

  let[@inline] set_default_associativity default_associativity =
    modify (fun state -> { state with default_associativity })

  let get_default_associativity =
    let* state = get in
    return state.default_associativity

  let[@inline] get_default_associativity_opt = function
    | Option.None -> get_default_associativity
    | Option.Some associativity -> return associativity

  let[@inline] set_default_precedence default_precedence =
    modify (fun state -> { state with default_precedence })

  let get_default_precedence =
    let* state = get in
    return state.default_precedence

  let[@inline] get_default_precedence_opt = function
    | Option.None -> get_default_precedence
    | Option.Some precedence -> return precedence

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

  (** {1 Free Variables} *)

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
                    (Format.asprintf "[%s] invalid state" __FUNCTION__)
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

  let push_entry identifier entry bindings =
    let entries' =
      match Identifier.Hamt.find_opt identifier bindings with
      | Option.None -> List1.singleton entry
      | Option.Some entries -> List1.cons entry entries
    in
    Identifier.Hamt.add identifier entries' bindings

  let add_free_lf_level_variable identifier entry =
    modify (fun state ->
        match state.substate with
        | Pattern_state substate ->
            { state with
              substate =
                Pattern_state
                  { substate with
                    inner_pattern_bindings =
                      push_entry identifier entry
                        substate.inner_pattern_bindings
                  ; expression_bindings =
                      Binding_tree.add_toplevel identifier entry
                        substate.expression_bindings
                  ; pattern_variables_rev =
                      identifier :: substate.pattern_variables_rev
                  }
            }
        | Module_state _
        | Scope_state _ ->
            state)

  let add_free_meta_level_variable identifier entry =
    modify (fun state ->
        match state.substate with
        | Pattern_state substate ->
            { state with
              substate =
                Pattern_state
                  { substate with
                    inner_pattern_bindings =
                      push_entry identifier entry
                        substate.inner_pattern_bindings
                  ; expression_bindings =
                      Binding_tree.add_toplevel identifier entry
                        substate.expression_bindings
                  ; pattern_variables_rev =
                      identifier :: substate.pattern_variables_rev
                  }
            }
        | Module_state _
        | Scope_state _ ->
            state)

  let add_free_comp_level_variable identifier entry =
    modify (fun state ->
        match state.substate with
        | Pattern_state substate ->
            { state with
              substate =
                Pattern_state
                  { substate with
                    expression_bindings =
                      Binding_tree.add_toplevel identifier entry
                        substate.expression_bindings
                  ; pattern_variables_rev =
                      identifier :: substate.pattern_variables_rev
                  }
            }
        | Module_state _
        | Scope_state _ ->
            state)

  let add_free_lf_variable ?location identifier =
    add_free_lf_level_variable identifier
      (Entry.make_lf_variable_entry ?location identifier)

  let add_free_meta_variable ?location identifier =
    add_free_meta_level_variable identifier
      (Entry.make_meta_variable_entry ?location identifier)

  let add_free_parameter_variable ?location identifier =
    add_free_meta_level_variable identifier
      (Entry.make_parameter_variable_entry ?location identifier)

  let add_free_substitution_variable ?location identifier =
    add_free_meta_level_variable identifier
      (Entry.make_substitution_variable_entry ?location identifier)

  let add_free_context_variable ?location identifier =
    add_free_meta_level_variable identifier
      (Entry.make_context_variable_entry ?location identifier)

  let add_free_computation_variable ?location identifier =
    add_free_comp_level_variable identifier
      (Entry.make_computation_variable_entry ?location identifier)

  let[@inline] add_binding identifier ?subtree entry =
    modify_bindings (Binding_tree.add_toplevel identifier ?subtree entry)

  let[@inline] add_declaration identifier ?subtree entry =
    let* () = add_binding identifier ?subtree entry in
    modify_substate (function
      | Module_state state ->
          let declarations' =
            Binding_tree.add_toplevel identifier ?subtree entry
              state.declarations
          in
          Module_state { state with declarations = declarations' }
      | Pattern_state _ ->
          Error.raise_violation
            (Format.asprintf "[%s] invalid pattern disambiguation state"
               __FUNCTION__)
      | Scope_state _ ->
          Error.raise_violation
            (Format.asprintf "[%s] invalid scope disambiguation state"
               __FUNCTION__))

  let add_lf_variable ?location identifier =
    add_binding identifier
      (Entry.make_lf_variable_entry ?location identifier)

  let add_meta_variable ?location identifier =
    add_binding identifier
      (Entry.make_meta_variable_entry ?location identifier)

  let add_parameter_variable ?location identifier =
    add_binding identifier
      (Entry.make_parameter_variable_entry ?location identifier)

  let add_substitution_variable ?location identifier =
    add_binding identifier
      (Entry.make_substitution_variable_entry ?location identifier)

  let add_context_variable ?location identifier =
    add_binding identifier
      (Entry.make_context_variable_entry ?location identifier)

  let add_contextual_variable ?location identifier =
    add_binding identifier
      (Entry.make_contextual_variable_entry ?location identifier)

  let add_computation_variable ?location identifier =
    add_binding identifier
      (Entry.make_computation_variable_entry ?location identifier)

  let add_lf_type_constant ?location ?arity identifier =
    add_declaration identifier
      (Entry.make_lf_type_constant_entry ?location ?arity identifier)

  let add_lf_term_constant ?location ?arity identifier =
    add_declaration identifier
      (Entry.make_lf_term_constant_entry ?location ?arity identifier)

  let add_schema_constant ?location identifier =
    add_declaration identifier
      (Entry.make_schema_constant_entry ?location identifier)

  let add_inductive_computation_type_constant ?location ?arity identifier =
    add_declaration identifier
      (Entry.make_inductive_computation_type_constant_entry ?location ?arity
         identifier)

  let add_stratified_computation_type_constant ?location ?arity identifier =
    add_declaration identifier
      (Entry.make_stratified_computation_type_constant_entry ?location ?arity
         identifier)

  let add_coinductive_computation_type_constant ?location ?arity identifier =
    add_declaration identifier
      (Entry.make_coinductive_computation_type_constant_entry ?location
         ?arity identifier)

  let add_abbreviation_computation_type_constant ?location ?arity identifier
      =
    add_declaration identifier
      (Entry.make_abbreviation_computation_type_constant_entry ?location
         ?arity identifier)

  let add_computation_term_constructor ?location ?arity identifier =
    add_declaration identifier
      (Entry.make_computation_term_constructor_entry ?location ?arity
         identifier)

  let add_computation_term_destructor ?location identifier =
    add_declaration identifier
      (Entry.make_computation_term_destructor_entry ?location identifier)

  let add_program_constant ?location ?arity identifier =
    add_declaration identifier
      (Entry.make_program_constant_entry ?location ?arity identifier)

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
    get_substate >>= function
    | Module_state substate ->
        let* () = put state in
        let entry = Entry.make_module_entry ?location identifier in
        let* () =
          add_declaration identifier ~subtree:substate.declarations entry
        in
        return x
    | Pattern_state _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid pattern state" __FUNCTION__)
    | Scope_state _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid scope state" __FUNCTION__)

  (** {1 Lookups} *)

  let lookup_toplevel' query =
    get_substate >>= function
    | Pattern_state { pattern_bindings; inner_pattern_bindings; _ } -> (
        try
          let entry, _subtree =
            Binding_tree.lookup_toplevel_filter query
              (fun entry -> Bool.not (Entry.is_variable entry))
              pattern_bindings
          in
          return entry
        with
        | Binding_tree.Unbound_identifier _ -> (
            match Identifier.Hamt.find_opt query inner_pattern_bindings with
            | Option.Some (List1.T (entry, _)) -> return entry
            | Option.None -> Error.raise (Unbound_identifier query)))
    | Module_state _
    | Scope_state _ ->
        let* bindings = get_bindings in
        let entry, _subtree = Binding_tree.lookup_toplevel query bindings in
        return entry

  let lookup_toplevel query =
    try_catch
      (lazy
        (let* entry = lookup_toplevel' query in
         return (Result.ok entry)))
      ~on_exn:(function
        | Binding_tree.Unbound_identifier identifier ->
            return (Result.error (Unbound_identifier identifier))
        | cause -> return (Result.error cause))

  let lookup' query =
    let* bindings = get_bindings in
    return (Binding_tree.lookup query bindings)

  let lookup query =
    try_catch
      (lazy
        (let* entry, _subtree = lookup' query in
         return (Result.ok entry)))
      ~on_exn:(fun cause -> return (Result.error cause))

  let discard_subtree_maximum_lookup query = function
    | `Unbound _ as result -> result
    | `Partially_bound
        (bound_segments, (identifier, entry, _subtree), unbound_segments) ->
        `Partially_bound
          (bound_segments, (identifier, entry), unbound_segments)
    | `Bound (entry, _subtree) ->
        `Bound (Qualified_identifier.from_list1 query, entry)

  let maximum_lookup query =
    get_substate >>= function
    | Pattern_state { pattern_bindings; inner_pattern_bindings; _ } -> (
        match
          discard_subtree_maximum_lookup query
            (Binding_tree.maximum_lookup_filter query
               (fun entry -> Bool.not (Entry.is_variable entry))
               pattern_bindings)
        with
        | `Unbound _ as r -> (
            let (List1.T (x, xs)) = query in
            match Identifier.Hamt.find_opt x inner_pattern_bindings with
            | Option.Some (List1.T (entry, _)) -> (
                match xs with
                | [] ->
                    return
                      (`Bound (Qualified_identifier.make_simple x, entry))
                | y :: ys ->
                    return
                      (`Partially_bound ([], (x, entry), List1.from y ys)))
            | Option.None -> return r)
        | r -> return r)
    | _ ->
        let* bindings = get_bindings in
        return
          (discard_subtree_maximum_lookup query
             (Binding_tree.maximum_lookup query bindings))

  let add_synonym ?location qualified_identifier synonym =
    let* entry, subtree = lookup' qualified_identifier in
    let binding_location' =
      match location with
      | Option.None -> Entry.binding_location entry
      | Option.Some location -> location
    in
    let entry' = Entry.{ entry with binding_location = binding_location' } in
    add_binding synonym ~subtree entry'

  let actual_binding_exn identifier entry =
    Error.located_exception1
      (Entry.binding_location entry)
      (Entry.actual_binding_exn identifier entry)

  let open_namespace identifier =
    modify_bindings (Binding_tree.open_namespace identifier)

  let open_module identifier =
    lookup identifier >>= function
    | Result.Ok { Entry.desc = Entry.Module; _ } -> open_namespace identifier
    | Result.Ok entry ->
        Error.raise_at1
          (Qualified_identifier.location identifier)
          (Error.composite_exception2 (Expected_module identifier)
             (actual_binding_exn identifier entry))
    | Result.Error cause ->
        Error.raise_at1 (Qualified_identifier.location identifier) cause

  let[@inline] [@specialise] with_bindings_checkpoint m =
    let* bindings = get_bindings in
    let* x = m in
    let* () = set_bindings bindings in
    return x

  let with_inner_bound_entry identifier entry m =
    push_inner_pattern_binding identifier entry
    &> m
    <& pop_inner_pattern_binding identifier

  let[@specialise] with_inner_bound_lf_variable ?location identifier =
    with_inner_bound_entry identifier
      (Entry.make_lf_variable_entry ?location identifier)

  let[@specialise] with_inner_bound_meta_variable ?location identifier =
    with_inner_bound_entry identifier
      (Entry.make_meta_variable_entry ?location identifier)

  let[@specialise] with_inner_bound_parameter_variable ?location identifier =
    with_inner_bound_entry identifier
      (Entry.make_parameter_variable_entry ?location identifier)

  let[@specialise] with_inner_bound_substitution_variable ?location
      identifier =
    with_inner_bound_entry identifier
      (Entry.make_substitution_variable_entry ?location identifier)

  let[@specialise] with_inner_bound_context_variable ?location identifier =
    with_inner_bound_entry identifier
      (Entry.make_context_variable_entry ?location identifier)

  let[@specialise] with_inner_bound_contextual_variable ?location identifier
      =
    with_inner_bound_entry identifier
      (Entry.make_contextual_variable_entry ?location identifier)

  let[@specialise] with_bound_lf_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_lf_variable identifier
         (add_lf_variable ?location identifier &> m))

  let[@specialise] with_bound_meta_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_meta_variable identifier
         (add_meta_variable ?location identifier &> m))

  let[@specialise] with_bound_parameter_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_parameter_variable identifier
         (add_parameter_variable ?location identifier &> m))

  let[@specialise] with_bound_substitution_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_substitution_variable identifier
         (add_substitution_variable ?location identifier &> m))

  let[@specialise] with_bound_context_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_context_variable identifier
         (add_context_variable ?location identifier &> m))

  let[@specialise] with_bound_contextual_variable ?location identifier m =
    with_bindings_checkpoint
      (with_inner_bound_contextual_variable identifier
         (add_contextual_variable ?location identifier &> m))

  let[@specialise] with_bound_computation_variable ?location identifier m =
    with_bindings_checkpoint
      (add_computation_variable ?location identifier &> m)

  let[@specialise] with_bound_pattern_meta_variable ?location identifier m =
    let* () = add_free_meta_variable ?location identifier in
    with_bound_meta_variable ?location identifier m

  let[@specialise] with_bound_pattern_parameter_variable ?location identifier
      m =
    let* () = add_free_parameter_variable ?location identifier in
    with_bound_parameter_variable ?location identifier m

  let[@specialise] with_bound_pattern_substitution_variable ?location
      identifier m =
    let* () = add_free_substitution_variable ?location identifier in
    with_bound_substitution_variable ?location identifier m

  let[@specialise] with_bound_pattern_context_variable ?location identifier m
      =
    let* () = add_free_context_variable ?location identifier in
    with_bound_context_variable ?location identifier m

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
            Error.raise_violation
              (Format.asprintf "[%s] no parent scope" __FUNCTION__))
    | Pattern_state _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid pattern state" __FUNCTION__)
    | Module_state _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid module state" __FUNCTION__)

  let get_pattern_variables_and_expression_state =
    let* state = get in
    match state.substate with
    | Pattern_state o ->
        let pattern_variables = List.rev o.pattern_variables_rev in
        return (pattern_variables, o.expression_bindings)
    | Module_state _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid module state" __FUNCTION__)
    | Scope_state _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid scope state" __FUNCTION__)

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
        let* expression' = expression pattern' in
        let* () = put state in
        return expression'

  let lookup_operator =
    lookup >=> function
    | Result.Ok entry -> return (Entry.operator entry)
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
    let* entry, subtree = lookup' identifier in
    let entry' =
      Entry.modify_operator
        ~operator:(fun operator arity ->
          let operator' = f operator ~arity in
          (operator', arity))
        ~not_an_operator:(fun () ->
          Error.raise_at1
            (Qualified_identifier.location identifier)
            (Error.composite_exception2 (Expected_operator identifier)
               (actual_binding_exn identifier entry)))
        entry
    in
    modify_bindings (Binding_tree.add identifier entry' ~subtree)
    &> update_module_declaration identifier

  let add_prefix_notation ?precedence constant =
    let* precedence = get_default_precedence_opt precedence in
    modify_operator constant (fun _operator ~arity ->
        match arity with
        | Option.Some 1 -> Option.some (Operator.make_prefix ~precedence)
        | Option.Some _
        | Option.None ->
            Error.raise_at1
              (Qualified_identifier.location constant)
              (Invalid_prefix_pragma { actual_arity = arity }))

  let add_infix_notation ?precedence ?associativity constant =
    let* precedence = get_default_precedence_opt precedence in
    let* associativity = get_default_associativity_opt associativity in
    modify_operator constant (fun _operator ~arity ->
        match arity with
        | Option.Some 2 ->
            Option.some (Operator.make_infix ~associativity ~precedence)
        | Option.Some _
        | Option.None ->
            Error.raise_at1
              (Qualified_identifier.location constant)
              (Invalid_infix_pragma { actual_arity = arity }))

  let add_postfix_notation ?precedence constant =
    let* precedence = get_default_precedence_opt precedence in
    modify_operator constant (fun _operator ~arity ->
        match arity with
        | Option.Some 1 -> Option.some (Operator.make_postfix ~precedence)
        | Option.Some _
        | Option.None ->
            Error.raise_at1
              (Qualified_identifier.location constant)
              (Invalid_postfix_pragma { actual_arity = arity }))

  let add_module_abbreviation ?location module_identifier abbreviation =
    lookup module_identifier >>= function
    | Result.Ok { Entry.desc = Entry.Module; _ } ->
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
