open Support
open Beluga_syntax

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

  val set_default_associativity : Associativity.t -> Unit.t t

  val get_default_associativity : Associativity.t t

  val add_lf_term_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_meta_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_context_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_computation_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

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

  val modify_operator :
       Qualified_identifier.t
    -> (Operator.t Option.t -> arity:Int.t -> Operator.t Option.t)
    -> Unit.t t

  val lookup_operator : Qualified_identifier.t -> Operator.t Option.t t
end

module Persistent_disambiguation_state : sig
  include DISAMBIGUATION_STATE

  val initial : state
end
