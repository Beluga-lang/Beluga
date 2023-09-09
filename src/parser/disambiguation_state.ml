open Support
open Beluga_syntax.Syncom

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
        Format.dprintf "Illegal duplicate pattern variables."
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

  let[@inline] binding_location entry = entry.binding_location

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
  include Imperative_state.IMPERATIVE_STATE

  module Entry : ENTRY

  (** {1 Variables} *)

  val add_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_context_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_contextual_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_computation_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_context_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_computation_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val with_bound_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_context_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_contextual_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_computation_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_context_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_free_variables_as_pattern_variables :
    state -> pattern:(state -> 'a) -> expression:(state -> 'a -> 'b) -> 'b

  val with_scope : state -> (state -> 'a) -> 'a

  val with_parent_scope : state -> (state -> 'a) -> 'a

  val with_bindings_checkpoint : state -> (state -> 'a) -> 'a

  (** {1 Constants} *)

  val add_lf_type_constant :
    state -> ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t

  val add_lf_term_constant :
    state -> ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t

  val add_schema_constant :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_inductive_computation_type_constant :
    state -> ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t

  val add_stratified_computation_type_constant :
    state -> ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t

  val add_coinductive_computation_type_constant :
    state -> ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t

  val add_abbreviation_computation_type_constant :
    state -> ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t

  val add_computation_term_constructor :
    state -> ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t

  val add_computation_term_destructor :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_program_constant :
    state -> ?location:Location.t -> ?arity:Int.t -> Identifier.t -> Unit.t

  val add_module :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** {1 Lookups} *)

  exception Unbound_identifier of Identifier.t

  exception Unbound_qualified_identifier of Qualified_identifier.t

  exception Unbound_namespace of Qualified_identifier.t

  val lookup_toplevel : state -> Identifier.t -> Entry.t

  val lookup : state -> Qualified_identifier.t -> Entry.t

  type maximum_lookup_result =
    | Unbound of { segments : Identifier.t List1.t }
    | Partially_bound of
        { leading_segments : Identifier.t List.t
        ; segment : Identifier.t
        ; entry : Entry.t
        ; trailing_segments : Identifier.t List1.t
        }
    | Bound of { entry : Entry.t }

  val maximum_lookup : state -> Identifier.t List1.t -> maximum_lookup_result

  val actual_binding_exn : Qualified_identifier.t -> Entry.t -> exn

  (** {1 Signature Operations} *)

  val open_module : state -> Qualified_identifier.t -> Unit.t

  val get_default_associativity : state -> Associativity.t

  val set_default_associativity : state -> Associativity.t -> Unit.t

  val get_default_precedence : state -> Int.t

  val set_default_precedence : state -> Int.t -> Unit.t

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

  val add_module_abbreviation :
       state
    -> ?location:Location.t
    -> Qualified_identifier.t
    -> Identifier.t
    -> Unit.t
end

module Disambiguation_state = struct
  module Entry = Entry

  exception Unbound_identifier = Identifier.Unbound_identifier

  exception
    Unbound_qualified_identifier = Qualified_identifier
                                   .Unbound_qualified_identifier

  exception Unbound_namespace = Qualified_identifier.Unbound_namespace

  (** A bindings environment is a binding tree of entries. *)
  type bindings = Entry.t Binding_tree.t

  (** A referencing environment is a stack of scopes (LIFO data structure).
      An identifier is unbound in a referencing environment if it is unbound
      in each of its scopes. An identifier is bound to an entry if it is
      bound in one of the scopes. In lookups, the returned entry is the one
      in the first scope that has the identifier bound. *)
  type referencing_environment = scope List1.t

  and scope =
    | Plain_scope of { bindings : bindings }
        (** Plain scopes are scopes without special operations. *)
    | Pattern_scope of
        { pattern_bindings : bindings
              (** The bindings to use to disambiguate nodes in the pattern
                  AST. *)
        ; mutable pattern_variables_rev : Identifier.t List.t
              (** The list of added free variables, in reverse order of
                  addition. *)
        ; expression_bindings : bindings
              (** The bindings to use for disambiguating the expression using
                  the accumulated free variables as bound variables. *)
        }
        (** Pattern scopes are scopes that keep track of added free variables
            in patterns in order to add them to the expression bindings as
            bound variables. *)
    | Module_scope of
        { bindings : bindings
        ; declarations : bindings
        }
        (** Module scopes are scopes that keep track of added declarations in
            order to add them as declarations in the module being
            disambiguated. *)

  (** The type of fixity pragmas that are postponed to be applied at a later
      point. The default precedence and associativity to be used are
      determined where the pragma is declared, hence why those fields are not
      optional like in the parser syntax. *)
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
    { mutable scopes : referencing_environment
    ; mutable default_associativity : Associativity.t
          (** The default associativity to use for user-defined operators. *)
    ; mutable default_precedence : Int.t
          (** The default precedence to use for user-defined operators. *)
    ; mutable postponed_fixity_pragmas : postponed_fixity_pragma List.t
          (** The list of fixity pragmas that refer to constants declared
              immediately after them instead of pragmas declared earlier. *)
    }

  include (
    Imperative_state.Make (struct
      type nonrec state = state
    end) :
      Imperative_state.IMPERATIVE_STATE with type state := state)

  let create_empty_plain_scope () =
    Plain_scope { bindings = Binding_tree.create () }

  let create_plain_scope bindings = Plain_scope { bindings }

  let create_pattern_scope () =
    Pattern_scope
      { pattern_bindings = Binding_tree.create ()
      ; pattern_variables_rev = []
      ; expression_bindings = Binding_tree.create ()
      }

  let create_module_scope () =
    Module_scope
      { bindings = Binding_tree.create ()
      ; declarations = Binding_tree.create ()
      }

  let create_initial_state () =
    { scopes = List1.singleton (create_module_scope ())
    ; default_precedence = Synext.default_precedence
    ; default_associativity = Synext.default_associativity
    ; postponed_fixity_pragmas = []
    }

  let clear_state state =
    state.scopes <- List1.singleton (create_module_scope ());
    state.default_precedence <- Synext.default_precedence;
    state.default_associativity <- Synext.default_associativity

  let get_scope_bindings = function
    | Plain_scope { bindings } -> bindings
    | Module_scope { bindings; _ } -> bindings
    | Pattern_scope { pattern_bindings; _ } -> pattern_bindings

  let set_default_associativity state default_associativity =
    state.default_associativity <- default_associativity

  let get_default_associativity state = state.default_associativity

  let get_default_associativity_opt state = function
    | Option.None -> get_default_associativity state
    | Option.Some associativity -> associativity

  let set_default_precedence state default_precedence =
    state.default_precedence <- default_precedence

  let get_default_precedence state = state.default_precedence

  let get_default_precedence_opt state = function
    | Option.None -> get_default_precedence state
    | Option.Some precedence -> precedence

  let[@inline] push_scope state scope =
    state.scopes <- List1.cons scope state.scopes

  let pop_scope state =
    match state.scopes with
    | List1.T (x1, x2 :: xs) ->
        state.scopes <- List1.from x2 xs;
        x1
    | List1.T (_x, []) ->
        Error.raise_violation
          (Format.asprintf "[%s] cannot pop the last scope" __FUNCTION__)

  let[@inline] get_current_scope state = List1.head state.scopes

  let[@inline] get_current_scope_bindings state =
    get_scope_bindings (get_current_scope state)

  let add_binding state identifier ?subtree entry =
    match get_current_scope state with
    | Plain_scope { bindings }
    | Pattern_scope { pattern_bindings = bindings; _ }
    | Module_scope { bindings; _ } ->
        Binding_tree.add_toplevel identifier entry ?subtree bindings

  let remove_binding state identifier =
    match get_current_scope state with
    | Plain_scope { bindings }
    | Pattern_scope { pattern_bindings = bindings; _ }
    | Module_scope { bindings; _ } ->
        Binding_tree.remove identifier bindings

  (** [add_declaration state identifier ?subtree entry] adds
      [(entry, subtree)] as a declaration in the current module scope, bound
      to [identifier] in [state]. It is assumed that the current scope in
      [state] is indeed a module scope. *)
  let add_declaration state identifier ?subtree entry =
    match get_current_scope state with
    | Plain_scope _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid plain scope disambiguation state"
             __FUNCTION__)
    | Pattern_scope _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid pattern scope disambiguation state"
             __FUNCTION__)
    | Module_scope { bindings; declarations } ->
        Binding_tree.add_toplevel identifier entry ?subtree bindings;
        Binding_tree.add_toplevel identifier entry ?subtree declarations

  let add_lf_variable state ?location identifier =
    add_binding state identifier
      (Entry.make_lf_variable_entry ?location identifier)

  let add_meta_variable state ?location identifier =
    add_binding state identifier
      (Entry.make_meta_variable_entry ?location identifier)

  let add_parameter_variable state ?location identifier =
    add_binding state identifier
      (Entry.make_parameter_variable_entry ?location identifier)

  let add_substitution_variable state ?location identifier =
    add_binding state identifier
      (Entry.make_substitution_variable_entry ?location identifier)

  let add_context_variable state ?location identifier =
    add_binding state identifier
      (Entry.make_context_variable_entry ?location identifier)

  let add_contextual_variable state ?location identifier =
    add_binding state identifier
      (Entry.make_contextual_variable_entry ?location identifier)

  let add_computation_variable state ?location identifier =
    add_binding state identifier
      (Entry.make_computation_variable_entry ?location identifier)

  let add_lf_type_constant state ?location ?arity identifier =
    add_declaration state identifier
      (Entry.make_lf_type_constant_entry ?location ?arity identifier)

  let add_lf_term_constant state ?location ?arity identifier =
    add_declaration state identifier
      (Entry.make_lf_term_constant_entry ?location ?arity identifier)

  let add_schema_constant state ?location identifier =
    add_declaration state identifier
      (Entry.make_schema_constant_entry ?location identifier)

  let add_inductive_computation_type_constant state ?location ?arity
      identifier =
    add_declaration state identifier
      (Entry.make_inductive_computation_type_constant_entry ?location ?arity
         identifier)

  let add_stratified_computation_type_constant state ?location ?arity
      identifier =
    add_declaration state identifier
      (Entry.make_stratified_computation_type_constant_entry ?location ?arity
         identifier)

  let add_coinductive_computation_type_constant state ?location ?arity
      identifier =
    add_declaration state identifier
      (Entry.make_coinductive_computation_type_constant_entry ?location
         ?arity identifier)

  let add_abbreviation_computation_type_constant state ?location ?arity
      identifier =
    add_declaration state identifier
      (Entry.make_abbreviation_computation_type_constant_entry ?location
         ?arity identifier)

  let add_computation_term_constructor state ?location ?arity identifier =
    add_declaration state identifier
      (Entry.make_computation_term_constructor_entry ?location ?arity
         identifier)

  let add_computation_term_destructor state ?location identifier =
    add_declaration state identifier
      (Entry.make_computation_term_destructor_entry ?location identifier)

  let add_program_constant state ?location ?arity identifier =
    add_declaration state identifier
      (Entry.make_program_constant_entry ?location ?arity identifier)

  let add_free_lf_level_variable _state _identifier _entry = ()
  (* There are no pure LF pattern variables, so this intentionally does
     nothing. *)

  let add_free_meta_level_variable state identifier entry =
    match get_current_scope state with
    | Pattern_scope scope ->
        (* Free meta-level variables will have reconstructed binders in the
           pattern meta-context, so they are hereafter considered as bound in
           the pattern. *)
        Binding_tree.add_toplevel identifier entry scope.pattern_bindings;
        Binding_tree.add_toplevel identifier entry scope.expression_bindings;
        scope.pattern_variables_rev <-
          identifier :: scope.pattern_variables_rev
    | Module_scope _
    | Plain_scope _ ->
        () (* Currently not keeping track of free variables. *)

  let add_free_comp_level_variable state identifier entry =
    match get_current_scope state with
    | Pattern_scope scope ->
        Binding_tree.add_toplevel identifier entry scope.expression_bindings;
        scope.pattern_variables_rev <-
          identifier :: scope.pattern_variables_rev
    | Module_scope _
    | Plain_scope _ ->
        () (* Currently not keeping track of free variables. *)

  let add_free_lf_variable state ?location identifier =
    add_free_lf_level_variable state identifier
      (Entry.make_lf_variable_entry ?location identifier)

  let add_free_meta_variable state ?location identifier =
    add_free_meta_level_variable state identifier
      (Entry.make_meta_variable_entry ?location identifier)

  let add_free_parameter_variable state ?location identifier =
    add_free_meta_level_variable state identifier
      (Entry.make_parameter_variable_entry ?location identifier)

  let add_free_substitution_variable state ?location identifier =
    add_free_meta_level_variable state identifier
      (Entry.make_substitution_variable_entry ?location identifier)

  let add_free_context_variable state ?location identifier =
    add_free_meta_level_variable state identifier
      (Entry.make_context_variable_entry ?location identifier)

  let add_free_computation_variable state ?location identifier =
    add_free_comp_level_variable state identifier
      (Entry.make_computation_variable_entry ?location identifier)

  let entry_is_not_variable entry = Bool.not (Entry.is_variable entry)

  let lookup_toplevel_in_scope scope query =
    Binding_tree.lookup_toplevel_opt query (get_scope_bindings scope)

  let lookup_toplevel_in_scopes scopes query =
    List.find_map (fun scope -> lookup_toplevel_in_scope scope query) scopes

  let rec lookup_toplevel_declaration_in_scopes scopes query =
    match scopes with
    | [] -> (* Exhausted the list of scopes to check. *) Option.none
    | scope :: scopes -> (
        let scope_bindings = get_scope_bindings scope in
        match Binding_tree.lookup_toplevel_opt query scope_bindings with
        | Option.Some (entry, subtree) when entry_is_not_variable entry ->
            (* [query] is bound to a declaration in [scope]. *)
            Option.some (entry, subtree)
        | Option.Some _ ->
            (* [query] is bound to a variable in [scope], so any declaration
               in [scopes] bound to [query] is shadowed. *)
            Option.none
        | Option.None ->
            (* [query] is unbound in [scope], so check in the parent
               scopes. *)
            lookup_toplevel_declaration_in_scopes scopes query)

  let internal_lookup_toplevel_opt state query =
    match state.scopes with
    | List1.T ((Pattern_scope _ as scope), scopes) -> (
        (* Overridden behaviour for pattern scopes. Variables can only be
           looked up in that pattern scope, and declarations can only be
           looked up in parent scopes. *)
        match lookup_toplevel_in_scope scope query with
        | Option.Some x -> Option.some x
        | Option.None -> lookup_toplevel_declaration_in_scopes scopes query)
    | List1.T (scope, scopes) ->
        lookup_toplevel_in_scopes (scope :: scopes) query

  (** [lookup_in_scopes scopes identifiers] looks up for an entry bound to
      the qualified identifier formed by [identifiers] successively in
      [scopes]. The qualified identifier being represented as a list of
      identifiers is an optimization. If an entry is fully bound or partially
      bound in a scope, then the search ends. The [scopes] are arranged as a
      stack. *)
  let rec lookup_in_scopes scopes identifiers =
    match scopes with
    | [] ->
        Error.raise
          (Unbound_qualified_identifier
             (Qualified_identifier.from_list1 identifiers))
    | scope :: scopes -> (
        match
          Binding_tree.maximum_lookup identifiers (get_scope_bindings scope)
        with
        | Binding_tree.Bound { entry; subtree; _ } -> (entry, subtree)
        | Binding_tree.Partially_bound { leading_segments; segment; _ } ->
            (* The [leading_segments] are bound in [scope], so any binding
               for [identifiers] in [scopes] is shadowed. *)
            Error.raise
              (Unbound_namespace
                 (Qualified_identifier.make ~namespaces:leading_segments
                    segment))
        | Binding_tree.Unbound _ -> lookup_in_scopes scopes identifiers)

  let rec lookup_declaration_in_scopes scopes identifiers =
    match scopes with
    | [] ->
        (* Exhausted the list of scopes to check. *)
        Error.raise
          (Unbound_qualified_identifier
             (Qualified_identifier.from_list1 identifiers))
    | scope :: scopes -> (
        let scope_bindings = get_scope_bindings scope in
        match Binding_tree.maximum_lookup identifiers scope_bindings with
        | Binding_tree.Bound { entry; subtree; _ }
          when entry_is_not_variable entry ->
            (* [query] is bound to a declaration in [scope]. *)
            (entry, subtree)
        | Binding_tree.Bound _result ->
            (* [query is bound to a variable in [scope], so any declaration
               in [scopes] bound to [query] is shadowed. *)
            assert (List1.length identifiers = 1)
            (* Variables can't be in namespaces *);
            Error.raise
              (Unbound_qualified_identifier
                 (Qualified_identifier.from_list1 identifiers))
        | Binding_tree.Partially_bound { leading_segments; segment; _ } ->
            Error.raise
              (Unbound_namespace
                 (Qualified_identifier.make ~namespaces:leading_segments
                    segment))
        | Binding_tree.Unbound _ ->
            lookup_declaration_in_scopes scopes identifiers)

  (** [internal_lookup state query] is [(entry, subtree)], where [entry] is
      the entry bound to [query] in [state], and [subtree] is the tree of
      bindings in the namespace declared by [entry]. In the case where
      [entry] is a variable or non-namespace constant, then [subtree] is
      empty. {!val:internal_lookup} differs from {!val:lookup} in that
      [subtree] is returned. *)
  let internal_lookup state query =
    let identifiers = Qualified_identifier.to_list1 query in
    match state.scopes with
    | List1.T ((Pattern_scope _ as scope), scopes) -> (
        (* Overridden behaviour for pattern scopes. Variables can only be
           looked up in that pattern scope, and declarations can only be
           looked up in parent scopes. *)
        match
          Binding_tree.maximum_lookup identifiers (get_scope_bindings scope)
        with
        | Binding_tree.Bound { entry; subtree; _ } ->
            (* An inner pattern variable is in scope *) (entry, subtree)
        | Binding_tree.Partially_bound { leading_segments; segment; _ } ->
            (* An inner pattern variable shadowed a namespace *)
            Error.raise
              (Unbound_namespace
                 (Qualified_identifier.make ~namespaces:leading_segments
                    segment))
        | Binding_tree.Unbound _ ->
            lookup_declaration_in_scopes scopes identifiers)
    | List1.T (scope, scopes) ->
        lookup_in_scopes (scope :: scopes) identifiers

  type maximum_lookup_result =
    | Unbound of { segments : Identifier.t List1.t }
    | Partially_bound of
        { leading_segments : Identifier.t List.t
        ; segment : Identifier.t
        ; entry : Entry.t
        ; trailing_segments : Identifier.t List1.t
        }
    | Bound of { entry : Entry.t }

  let rec maximum_lookup_in_scopes scopes identifiers =
    match scopes with
    | [] -> Unbound { segments = identifiers }
    | scope :: scopes -> (
        match
          Binding_tree.maximum_lookup identifiers (get_scope_bindings scope)
        with
        | Binding_tree.Bound { entry; _ } -> Bound { entry }
        | Binding_tree.Partially_bound
            { leading_segments; segment; entry; trailing_segments; _ } ->
            Partially_bound
              { leading_segments; segment; entry; trailing_segments }
        | Binding_tree.Unbound _ ->
            maximum_lookup_in_scopes scopes identifiers)

  let rec maximum_lookup_declaration_in_scopes scopes identifiers =
    match scopes with
    | [] -> Unbound { segments = identifiers }
    | scope :: scopes -> (
        match
          Binding_tree.maximum_lookup identifiers (get_scope_bindings scope)
        with
        | Binding_tree.Bound { entry; _ } ->
            if Entry.is_variable entry then
              Unbound { segments = identifiers }
            else Bound { entry }
        | Binding_tree.Partially_bound
            { leading_segments; segment; entry; trailing_segments; _ } ->
            Partially_bound
              { leading_segments; segment; entry; trailing_segments }
        | Binding_tree.Unbound _ ->
            maximum_lookup_declaration_in_scopes scopes identifiers)

  let maximum_lookup state identifiers =
    match state.scopes with
    | List1.T ((Pattern_scope _ as scope), scopes) -> (
        (* Overridden behaviour for pattern scopes. Variables can only be
           looked up in that pattern scope, and declarations can only be
           looked up in parent scopes. *)
        match
          Binding_tree.maximum_lookup identifiers (get_scope_bindings scope)
        with
        | Binding_tree.Bound { entry; _ } -> Bound { entry }
        | Binding_tree.Partially_bound
            { leading_segments; segment; entry; trailing_segments; _ } ->
            Partially_bound
              { leading_segments; segment; entry; trailing_segments }
        | Binding_tree.Unbound _ ->
            maximum_lookup_declaration_in_scopes scopes identifiers)
    | List1.T (scope, scopes) ->
        maximum_lookup_in_scopes (scope :: scopes) identifiers

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

  let actual_binding_exn identifier entry =
    Error.located_exception1
      (Entry.binding_location entry)
      (Entry.actual_binding_exn identifier entry)

  let modify_operator state identifier f =
    let entry, subtree = internal_lookup state identifier in
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
    (* Update the entry in the current scope only *)
    let bindings = get_current_scope_bindings state in
    if Binding_tree.mem identifier bindings then
      Binding_tree.replace identifier
        (fun _entry _subtree -> (entry', subtree))
        bindings
    else Binding_tree.add identifier ~subtree entry' bindings;
    (* If we're currently in a module scope, additionally update the exported
       declaration *)
    match get_current_scope state with
    | Plain_scope _ -> ()
    | Pattern_scope _ -> ()
    | Module_scope { declarations; _ } ->
        if Binding_tree.mem identifier declarations then
          Binding_tree.replace identifier
            (fun _entry subtree -> (entry', subtree))
            declarations
        else ()

  let add_prefix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    modify_operator state constant (fun _operator ~arity ->
        match arity with
        | Option.Some 1 -> Option.some (Operator.make_prefix ~precedence)
        | Option.Some _
        | Option.None ->
            Error.raise_at1
              (Qualified_identifier.location constant)
              (Invalid_prefix_pragma { actual_arity = arity }))

  let add_infix_notation state ?precedence ?associativity constant =
    let precedence = get_default_precedence_opt state precedence in
    let associativity = get_default_associativity_opt state associativity in
    modify_operator state constant (fun _operator ~arity ->
        match arity with
        | Option.Some 2 ->
            Option.some (Operator.make_infix ~associativity ~precedence)
        | Option.Some _
        | Option.None ->
            Error.raise_at1
              (Qualified_identifier.location constant)
              (Invalid_infix_pragma { actual_arity = arity }))

  let add_postfix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    modify_operator state constant (fun _operator ~arity ->
        match arity with
        | Option.Some 1 -> Option.some (Operator.make_postfix ~precedence)
        | Option.Some _
        | Option.None ->
            Error.raise_at1
              (Qualified_identifier.location constant)
              (Invalid_postfix_pragma { actual_arity = arity }))

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
    let _entry, subtree = internal_lookup state identifier in
    let bindings = get_current_scope_bindings state in
    Binding_tree.add_all bindings subtree

  let open_module state identifier =
    match internal_lookup state identifier with
    | { Entry.desc = Entry.Module; _ }, _ -> (
        try open_namespace state identifier with
        | ( Unbound_identifier _ | Unbound_namespace _
          | Unbound_qualified_identifier _ ) as cause ->
            Error.raise_at1 (Qualified_identifier.location identifier) cause)
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location identifier)
          (Error.composite_exception2 (Expected_module identifier)
             (actual_binding_exn identifier entry))
    | (exception (Unbound_identifier _ as cause))
    | (exception (Unbound_namespace _ as cause))
    | (exception (Unbound_qualified_identifier _ as cause)) ->
        Error.raise_at1 (Qualified_identifier.location identifier) cause

  (** [add_synonym state ?location qualified_identifier synonym] copies the
      binding for [qualified_identifier] in [state] to a new binding with
      identifier [synonym], and binding site [location] if specified. *)
  let add_synonym state ?location qualified_identifier synonym =
    let entry, subtree = internal_lookup state qualified_identifier in
    let binding_location' =
      match location with
      | Option.None -> Entry.binding_location entry
      | Option.Some location -> location
    in
    let entry' = Entry.{ entry with binding_location = binding_location' } in
    add_binding state synonym ~subtree entry'

  let add_module_abbreviation state ?location module_identifier abbreviation
      =
    match internal_lookup state module_identifier with
    | { Entry.desc = Entry.Module; _ }, _ ->
        add_synonym state ?location module_identifier abbreviation
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location module_identifier)
          (Error.composite_exception2 (Expected_module module_identifier)
             (actual_binding_exn module_identifier entry))
    | (exception (Unbound_identifier _ as cause))
    | (exception (Unbound_namespace _ as cause))
    | (exception (Unbound_qualified_identifier _ as cause)) ->
        Error.raise_at1
          (Qualified_identifier.location module_identifier)
          cause

  let with_bound_lf_variable state ?location identifier m =
    add_lf_variable state ?location identifier;
    let x = m state in
    remove_binding state identifier;
    x

  let with_bound_meta_variable state ?location identifier m =
    add_meta_variable state ?location identifier;
    let x = m state in
    remove_binding state identifier;
    x

  let with_bound_parameter_variable state ?location identifier m =
    add_parameter_variable state ?location identifier;
    let x = m state in
    remove_binding state identifier;
    x

  let with_bound_substitution_variable state ?location identifier m =
    add_substitution_variable state ?location identifier;
    let x = m state in
    remove_binding state identifier;
    x

  let with_bound_context_variable state ?location identifier m =
    add_context_variable state ?location identifier;
    let x = m state in
    remove_binding state identifier;
    x

  let with_bound_contextual_variable state ?location identifier m =
    add_contextual_variable state ?location identifier;
    let x = m state in
    remove_binding state identifier;
    x

  let with_bound_computation_variable state ?location identifier m =
    add_computation_variable state ?location identifier;
    let x = m state in
    remove_binding state identifier;
    x

  let push_new_module_scope state =
    let module_scope = create_module_scope () in
    push_scope state module_scope

  let add_module state ?location identifier m =
    let default_associativity = get_default_associativity state in
    let default_precedence = get_default_precedence state in
    push_new_module_scope state;
    let x = m state in
    match
      pop_scope
        state (* We expect the newly pushed module scope to be popped *)
    with
    | Plain_scope _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid plain scope state" __FUNCTION__)
    | Pattern_scope _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid pattern scope state" __FUNCTION__)
    | Module_scope { declarations; _ } ->
        add_declaration state identifier ~subtree:declarations
          (Entry.make_module_entry ?location identifier);
        set_default_associativity state default_associativity;
        set_default_precedence state default_precedence;
        x

  let with_scope state m =
    let scope = create_empty_plain_scope () in
    push_scope state scope;
    let x = m state in
    ignore (pop_scope state);
    x

  let with_parent_scope state m =
    let scope = pop_scope state in
    let x = with_scope state m in
    push_scope state scope;
    x

  let with_bindings_checkpoint state m =
    let original_scopes_count = List1.length state.scopes in
    (* Push a fresh module scope so that [m] may add declarations *)
    push_new_module_scope state;
    Fun.protect
      ~finally:(fun () ->
        let final_scopes_count = List1.length state.scopes in
        let scopes_to_pop_count =
          final_scopes_count - original_scopes_count
        in
        if
          scopes_to_pop_count
          >= 1 (* We expect there to at least be the new module scope *)
        then
          (* We have to count scopes because [m] may add new scopes. This is
             not foolproof because [m] could have discarded too many scopes
             and added some more. *)
          Fun.repeat scopes_to_pop_count (fun () -> ignore (pop_scope state))
        else
          Error.raise_violation
            (Format.asprintf
               "[%s] invalid states, there are fewer scopes than there \
                originally were"
               __FUNCTION__))
      (fun () -> m state)

  let actual_binding_exn identifier entry =
    Error.located_exception1
      (Entry.binding_location entry)
      (Entry.actual_binding_exn identifier entry)

  let with_bound_pattern_meta_variable state ?location identifier m =
    add_free_meta_variable state ?location identifier;
    with_bound_meta_variable state ?location identifier m

  let with_bound_pattern_parameter_variable state ?location identifier m =
    add_free_parameter_variable state ?location identifier;
    with_bound_parameter_variable state ?location identifier m

  let with_bound_pattern_substitution_variable state ?location identifier m =
    add_free_substitution_variable state ?location identifier;
    with_bound_substitution_variable state ?location identifier m

  let with_bound_pattern_context_variable state ?location identifier m =
    add_free_context_variable state ?location identifier;
    with_bound_context_variable state ?location identifier m

  let with_free_variables_as_pattern_variables state
      ~pattern:disambiguate_pattern ~expression:disambiguate_expression =
    let pattern_scope = create_pattern_scope () in
    push_scope state pattern_scope;
    let pattern' = disambiguate_pattern state in
    match pop_scope state (* We expect [pattern_scope] to be popped *) with
    | Plain_scope _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid plain scope state" __FUNCTION__)
    | Module_scope _ ->
        Error.raise_violation
          (Format.asprintf "[%s] invalid module scope state" __FUNCTION__)
    | Pattern_scope
        { pattern_bindings = _; pattern_variables_rev; expression_bindings }
      -> (
        match
          Identifier.find_duplicates (List.rev pattern_variables_rev)
        with
        | Option.Some duplicates ->
            raise_duplicate_identifiers_exception
              (fun identifiers -> Duplicate_pattern_variables identifiers)
              duplicates
        | Option.None ->
            let expression_scope = create_plain_scope expression_bindings in
            push_scope state expression_scope;
            let expression' = disambiguate_expression state pattern' in
            ignore (pop_scope state)
            (* We expect [expression_scope] to be popped *);
            expression')

  let lookup_toplevel state identifier =
    match internal_lookup_toplevel_opt state identifier with
    | Option.Some (entry, _subtree) -> entry
    | Option.None -> Error.raise_notrace (Unbound_identifier identifier)

  let lookup state qualified_identifier =
    let entry, _subtree = internal_lookup state qualified_identifier in
    entry

  let lookup_operator state query =
    match lookup state query with
    | entry -> Entry.operator entry
    | (exception Unbound_identifier _)
    | (exception Unbound_namespace _)
    | (exception Unbound_qualified_identifier _) ->
        Option.none

  let snapshot_scope = function
    | Plain_scope { bindings } ->
        let bindings' = Binding_tree.snapshot bindings in
        Plain_scope { bindings = bindings' }
    | Pattern_scope
        { pattern_bindings; pattern_variables_rev; expression_bindings } ->
        let pattern_bindings' = Binding_tree.snapshot pattern_bindings in
        let expression_bindings' =
          Binding_tree.snapshot expression_bindings
        in
        Pattern_scope
          { pattern_bindings = pattern_bindings'
          ; pattern_variables_rev (* Immutable *)
          ; expression_bindings = expression_bindings'
          }
    | Module_scope { bindings; declarations } ->
        let bindings' = Binding_tree.snapshot bindings in
        let declarations' = Binding_tree.snapshot declarations in
        Module_scope { bindings = bindings'; declarations = declarations' }

  let snapshot_scopes scopes = List1.map snapshot_scope scopes

  let snapshot_state
      { scopes
      ; default_associativity
      ; default_precedence
      ; postponed_fixity_pragmas
      } =
    let scopes' = snapshot_scopes scopes in
    { scopes = scopes'
    ; default_associativity (* Immutable *)
    ; default_precedence (* Immutable *)
    ; postponed_fixity_pragmas (* Immutable *)
    }
end
