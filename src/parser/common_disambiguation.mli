open Support
open Beluga_syntax

module type ENTRY = sig
  type t

  val is_lf_variable : t -> Bool.t

  val is_meta_variable : t -> Bool.t

  val is_parameter_variable : t -> Bool.t

  val is_substitution_variable : t -> Bool.t

  val is_context_variable : t -> Bool.t

  val is_computation_variable : t -> Bool.t

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

  val is_variable : t -> Bool.t
end

module type DISAMBIGUATION_STATE = sig
  include State.STATE

  module Entry : ENTRY

  (** {1 Variables} *)

  (** [add_lf_variable ?location identifier state] is [(state', ())] where
      [state'] is derived from [state] by the addition of a bound LF variable
      [identifier] with binding site [location]. If [location = Option.None],
      then [identifier]'s location is used instead.

      This is mostly used for testing. For locally binding an LF variable,
      see {!with_lf_variable}. *)
  val add_lf_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_meta_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_context_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_computation_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_free_lf_variable ?location identifier] is
      [add_lf_variable ?location identifier], with the additional behaviour
      of adding [identifier] as an inner pattern bound identifier and as a
      free variable during pattern disambiguation. *)
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

  (** [with_lf_variable ?location identifier m state] is [(state', x)] where
      [x] is the result of running [m] in the local state derived from
      [state] having [identifier] as a bound LF variable.

      When disambiguating a pattern, [identifier] is additionally added as an
      inner pattern binding.

      For example, the disambiguation of an LF term-level lambda-abstraction
      [\x. m] requires that the parameter [x] is locally added in scope when
      disambiguating the body [m]. This is achieved like this:

      {[
        with_lf_variable x (disambiguate_lf m)
      ]} *)
  val with_lf_variable : ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_meta_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_parameter_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_substitution_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_context_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_contextual_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_comp_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  (** [with_free_variables_as_pattern_variables ~pattern ~expression state]
      is [(state', x')]. This is used to disambiguate [expression] with bound
      variables arising from free variables in [pattern].

      + [pattern] is run with respect to [state] without its bound variables,
        and while keeping track of free variables.
      + [expression] is run with respect to [state] with the addition of the
        tracked free variables from [patterns].

      Lookups performed in [pattern] are more complex. The variables in
      [state] count as being unbound, but the variables with binders in the
      pattern count as bound. Binders in a pattern can be specified or
      reconstructed.

      A variable is specifically inner bound if it is introduced explicitly
      by a lambda abstraction or the pattern meta-context, as an explicit or
      implicit parameter. Free meta-level variables are reconstructed inner
      bound. For instance, assuming [s] and [ctx] are constants:

      - In the pattern [(x, x)], both occurrences of [x] are pattern
        variables, and that pattern is not linear.
      - In the pattern [{M : \[ |- nat\]} \[ |- s M\]], [M] as introduced in
        the meta-context is a pattern variable, and [M] is an inner
        pattern-bound identifier in [s M], so that pattern is linear.
      - In the pattern [\[ |- \x. s x\]], there are no pattern variables.
      - In the pattern [(\[g |- s M\], \[g |- s M\])], [g] and [M] are
        pattern variables in the left projection of the tuple pattern, and
        inner pattern-bound in the right projection of the tuple pattern.
        This is because the pattern is reconstructed as
        [{g : ctx} {M : \[g |- nat\]} (\[g |- s M\], \[g |- s M\])]. *)
  val with_free_variables_as_pattern_variables :
    pattern:'a t -> expression:('a -> 'b t) -> 'b t

  (** [with_scope m] runs [m] in a nested bindings scope that is discarded
      afterwards. *)
  val with_scope : 'a t -> 'a t

  (** [with_parent_scope m] runs [m] in the bindings scope parent to the
      current bindings scope.

      This is used for the disambiguation of Harpoon proof scripts because
      Harpoon hypotheticals are already serialized with all the identifiers
      in the meta-level and computation-level contexts of the proof. *)
  val with_parent_scope : 'a t -> 'a t

  (** {1 Constants} *)

  (** [add_lf_type_constant ?location ?arity identifier state] is
      [(state', ())] where [state'] is derived from [state] by the addition
      of [identifier] as a bound LF type-level constant.

      In the disambiguation of a module's declaration, this also adds the
      constant as one of the module's declarations. *)
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

  (** [add_module ?location identifier m state] is [(state', x)] where [x] is
      the result of running [m] in a module disambiguation state, whereby
      added constants are kept track of as declarations in the module having
      [identifier]. *)
  val add_module : ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  (** {1 Lookups} *)

  exception Unbound_identifier of Identifier.t

  exception Unbound_qualified_identifier of Qualified_identifier.t

  exception Unbound_namespace of Qualified_identifier.t

  val lookup_toplevel : Identifier.t -> (Entry.t, exn) Result.t t

  val lookup : Qualified_identifier.t -> (Entry.t, exn) Result.t t

  val partial_lookup :
       Qualified_identifier.t
    -> [ `Partially_bound of
         (Identifier.t * Entry.t) List1.t * Identifier.t List1.t
       | `Totally_bound of (Identifier.t * Entry.t) List1.t
       | `Totally_unbound of Identifier.t List1.t
       ]
       t

  val partial_lookup' :
       Identifier.t List1.t
    -> [ `Partially_bound of
         (Identifier.t * Entry.t) List1.t * Identifier.t List1.t
       | `Totally_bound of (Identifier.t * Entry.t) List1.t
       | `Totally_unbound of Identifier.t List1.t
       ]
       t

  val actual_binding_exn : Qualified_identifier.t -> Entry.t -> exn

  (** {1 Signature Operations} *)

  val open_module : Qualified_identifier.t -> Unit.t t

  val get_default_associativity : Associativity.t t

  val set_default_associativity : Associativity.t -> Unit.t t

  (** [get_default_precedence state] is [(state', default_precedence)] where
      [default_precedence] is the precedence to use for operators defined by
      the user using a pragma, without specifying the operator's precedence. *)
  val get_default_precedence : Int.t t

  (** [set_default_precedence default_precedence state] is [(state', ())]
      where [state'] is derived from [state] with [default_precedence] as the
      precedence to return from {!get_default_precedence}. *)
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

module Persistent_disambiguation_state : sig
  include DISAMBIGUATION_STATE

  val initial : state
end
