open Support
open Beluga_syntax

(** Abstract definition of entries bound to identifiers. *)
module type ENTRY = sig
  type t

  (** [is_lf_variable entry] is [true] if and only if [entry] describes an LF
      variable. *)
  val is_lf_variable : t -> Bool.t

  (** [is_meta_variable entry] is [true] if [entry] describes an
      meta-variable or a contextual variable.

      Contextual variables exist only because [mlam]-expressions ambiguously
      introduce either a meta-variable, a parameter variable, a substitution
      variable or a context variable. *)
  val is_meta_variable : t -> Bool.t

  (** [is_parameter_variable] is like {!is_meta_variable}, but for entries
      describing parameter variables. *)
  val is_parameter_variable : t -> Bool.t

  (** [is_substitution_variable] is like {!is_meta_variable}, but for entries
      describing parameter variables. *)
  val is_substitution_variable : t -> Bool.t

  (** [is_context_variable] is like {!is_meta_variable}, but for entries
      describing context variables. *)
  val is_context_variable : t -> Bool.t

  (** [is_computation_variable entry] is [true] if and only if [entry]
      describes a computation-level variable. *)
  val is_computation_variable : t -> Bool.t

  (** [is_variable entry] is [true] if and only if [entry] describes an LF
      variable, a meta-level variable, or a computation-level variable.

      This is used to discern between the following two cases when
      disambiguating identifiers in patterns:

      - The case where an exception should be raised because the identifier a
        bound variable of the wrong sort.
      - The case where the identifier should be a free variable shadowing a
        constant. *)
  val is_variable : t -> Bool.t

  (** [is_lf_type_constant entry] is [true] if and only if [entry] describes
      an LF type-level constant. *)
  val is_lf_type_constant : t -> Bool.t

  (** [is_lf_term_constant] is like {!is_lf_type_constant}, but for entries
      describing LF term-level constants. *)
  val is_lf_term_constant : t -> Bool.t

  (** [is_schema_constant] is like {!is_lf_type_constant}, but for entries
      describing context schemas. *)
  val is_schema_constant : t -> Bool.t

  (** [is_computation_inductive_type_constant] is like
      {!is_lf_type_constant}, but for entries describing inductive
      computation-level type constants. *)
  val is_computation_inductive_type_constant : t -> Bool.t

  (** [is_computation_stratified_type_constant] is like
      {!is_lf_type_constant}, but for entries describing stratified
      computation-level type constants. *)
  val is_computation_stratified_type_constant : t -> Bool.t

  (** [is_computation_coinductive_type_constant] is like
      {!is_lf_type_constant}, but for entries describing coinductive
      computation-level type constants. *)
  val is_computation_coinductive_type_constant : t -> Bool.t

  (** [is_computation_abbreviation_type_constant] is like
      {!is_lf_type_constant}, but for entries describing computation-level
      type constant abbreviations (introduced by the Beluga keyword
      [typedef]). *)
  val is_computation_abbreviation_type_constant : t -> Bool.t

  (** [is_computation_term_constructor] is like {!is_lf_type_constant}, but
      for entries describing computation-level constructors. *)
  val is_computation_term_constructor : t -> Bool.t

  (** [is_computation_term_destructor] is like {!is_lf_type_constant}, but
      for entries describing computation-level destructors. *)
  val is_computation_term_destructor : t -> Bool.t

  (** [is_program_constant] is like {!is_lf_type_constant}, but for entries
      describing computation-level programs (introduced by the Beluga keyword
      [rec] or [val]). *)
  val is_program_constant : t -> Bool.t

  (** [is_module] is like {!is_lf_type_constant}, but for entries describing
      modules. *)
  val is_module : t -> Bool.t
end

(** Abstract definition of the state monad for disambiguating parsed Beluga
    signatures. *)
module type DISAMBIGUATION_STATE = sig
  include State.STATE

  module Entry : ENTRY

  (** {1 Variables} *)

  (** [add_lf_variable ?location identifier state] is [(state', ())] where
      [state'] is derived from [state] by the addition of [identifier] as a
      bound LF variable, with binding site [location]. If
      [location = Option.None], then [identifier]'s location is used instead.

      This is mostly used for testing. For locally binding an LF variable,
      see {!with_lf_variable}. *)
  val add_lf_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_meta_variable] is like {!add_lf_variable}, but the identifier is
      added as a bound meta-variable. *)
  val add_meta_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_parameter_variable] is like {!add_lf_variable}, but the identifier
      is added as a bound parameter variable (those variables prefixed by
      ['#'] like ["#p"]). *)
  val add_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_substitution_variable] is like {!add_lf_variable}, but the
      identifier is added as a bound substitution variable (those variables
      prefixed by ['$'] like ["$S"]). *)
  val add_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_context_variable] is like {!add_lf_variable}, but the identifier
      is added as a bound context variable. *)
  val add_context_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_computation_variable] is like {!add_lf_variable}, but the
      identifier is added as a bound computation-level variable. *)
  val add_computation_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_free_lf_variable ?location identifier] is
      [add_lf_variable ?location identifier], with the additional behaviour
      of adding [identifier] as an inner pattern bound identifier and as a
      free variable during pattern disambiguation. This means that
      [identifier] can subsequently be looked up as a bound LF variable
      during pattern disambiguation. This effectively allows free LF
      variables to appear multiple times (non-linearly) in patterns.

      See {!with_free_variables_as_pattern_variables} for the handler for
      converting free variables in patterns to binders for use as bound
      variables in expressions. *)
  val add_free_lf_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_free_meta_variable] is like {!add_free_lf_variable}, but the
      identifier is added as a free meta-variable. *)
  val add_free_meta_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_free_meta_variable] is like {!add_free_lf_variable}, but the
      identifier is added as a free parameter variable. *)
  val add_free_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_free_meta_variable] is like {!add_free_lf_variable}, but the
      identifier is added as a free substitution variable. *)
  val add_free_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_free_meta_variable] is like {!add_free_lf_variable}, but the
      identifier is added as a free context variable. *)
  val add_free_context_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  (** [add_free_computation_variable ?location identifier state] is
      [(state', ())] where [state'] is derived from [state] with the addition
      of [identifier] as a free variable during pattern disambiguation. This
      differs from {!add_free_lf_variable} in that free computation-level
      variables in patterns do not have implicit binders (because they are
      not part of the meta-context), and hence must appear only once
      (linearly) in the overall pattern. *)
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
      is [(state', x')], where [x'] is the result of running [expression]
      with the free variables added in [pattern] as bound variables. This is
      used to disambiguate [expression] with bound variables arising from
      free variables in [pattern].

      + [pattern] is run with respect to [state] while keeping track of free
        variables. Variables bound outside the pattern are ignored in
        lookups.
      + [expression] is run with respect to [state] with the addition of the
        tracked free variables from [patterns] as bound variables.

      Lookups performed in [pattern] are more complex. The variables in
      [state] count as being unbound, but the variables with binders in the
      pattern count as bound. Binders in a pattern can be user-specified, or
      to be reconstructed during abstraction.

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

  (** [lookup_toplevel identifier state] is [(state', Result.Ok entry)] if
      [identifier] resolves to [entry] in [state], and
      [(state', Result.Error (Unbound_identifier identifier))] otherwise. *)
  val lookup_toplevel : Identifier.t -> (Entry.t, exn) Result.t t

  (** [lookup identifier state] is [(state', Result.Ok entry)] if
      [identifier] resolves to [entry] in [state]. Otherwise, it is:

      - [(state', Result.Error (Unbound_identifier ident))] if the first
        segment [ident] in [identifier] is unbound.
      - [(state', Result.Error (Unbound_namespace namespace_identifier))] if
        a segment in [identifier] other than the first or last is unbound.
      - [(state', Result.Error (Unbound_qualified_identifier identifier))] if
        the last segment in [identifier] is unbound. *)
  val lookup : Qualified_identifier.t -> (Entry.t, exn) Result.t t

  (** [maximum_lookup segments state] is [(state', result)] where [result] is
      either:

      - [`Unbound segments] if the first segment in [segments] is unbound in
        [state].
      - [`Partially_bound (leading_segments, (segment, entry), (trailing_segments))]
        if the qualified identifier with namespaces [leading_segments] and
        name [segment] is bound to [entry] in [state].
      - [`Bound (identifier, entry)] if [segments] form a qualified
        identifier bound to [entry] in [state]. *)
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

  (** [actual_binding_exn identifier entry] is an exception reporting what
      sort of [entry] is bound at [identifier]. The exception is annotated
      with the entry's binding location. *)
  val actual_binding_exn : Qualified_identifier.t -> Entry.t -> exn

  (** {1 Signature Operations} *)

  (** [open_module module_identifier state] is [(state', ())] where [state']
      is derived from [state] with the addition of the exported constants
      from the module bound to [module_identifier] as toplevel entries. If
      [module_identifier] is unbound in [state], then an exception is raised. *)
  val open_module : Qualified_identifier.t -> Unit.t t

  (** [get_default_associativity state] is [(state', default_associativity)]
      where [default_associativity] is the associativity to use for infix
      operators defined by the user using a pragma, without specifying the
      infix operator's associativity. *)
  val get_default_associativity : Associativity.t t

  (** [set_default_associativity default_associativity state] is
      [(state', ())] where [state'] is derived from [state] with
      [default_associativity] as the associativity to return from
      {!get_default_associativity}. *)
  val set_default_associativity : Associativity.t -> Unit.t t

  (** [get_default_precedence state] is [(state', default_precedence)] where
      [default_precedence] is the precedence to use for operators defined by
      the user using a pragma, without specifying the operator's precedence. *)
  val get_default_precedence : Int.t t

  (** [set_default_precedence default_precedence state] is [(state', ())]
      where [state'] is derived from [state] with [default_precedence] as the
      precedence to return from {!get_default_precedence}. *)
  val set_default_precedence : Int.t -> Unit.t t

  (** [add_prefix_notation ?precedence identifier state] is [(state', ())]
      where [state'] is derived from [state] by the addition of a prefix
      notation for [identifier]. If [precedence = Option.None], then
      {!get_default_precedence} is used instead.

      An exception is raised if [identifier] is unbound in [state], not bound
      to a constant, or bound to a constant of an unknown or invalid arity. *)
  val add_prefix_notation :
    ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  (** [add_infix_notation ?precedence ?associativity identifier state] is
      [(state', ())] where [state'] is derived from [state] by the addition
      of an infix notation for [identifier]. If [precedence = Option.None],
      then {!get_default_precedence} is used instead. Likewise, if
      [associativity = Option.None], then {!get_default_associativity} is
      used instead.

      An exception is raised if [identifier] is unbound in [state], not bound
      to a constant, or bound to a constant of an unknown or invalid arity. *)
  val add_infix_notation :
       ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t t

  (** [add_postfix_notation ?precedence identifier state] is [(state', ())]
      where [state'] is derived from [state] by the addition of a postfix
      notation for [identifier]. If [precedence = Option.None], then
      {!get_default_precedence} is used instead.

      An exception is raised if [identifier] is unbound in [state], not bound
      to a constant, or bound to a constant of an unknown or invalid arity. *)
  val add_postfix_notation :
    ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  (** [lookup_operator identifier state] is [(state', Option.Some operator)]
      if [identifier] is bound to an operator with descriptor [operator] in
      [state], and [(state', Option.None)] otherwise.

      This is used to resolve operators in the disambiguation of
      applications, which are parsed as lists of expressions. *)
  val lookup_operator : Qualified_identifier.t -> Operator.t Option.t t

  (** [add_module_abbreviation ?location module_identifier abbreviation state]
      is [(state', ())] where [state'] is derived from [state] by the
      addition of the synonym [abbreviation] for the module bound to
      [identifier] in [state].

      An exception is raised if [module_identifier] is unbound in [state], or
      if [module_identifier] is not bound to a module in [state]. *)
  val add_module_abbreviation :
       ?location:Location.t
    -> Qualified_identifier.t
    -> Identifier.t
    -> Unit.t t
end

(** Concrete implementation of {!DISAMBIGUATION_STATE} using a persistent
    (immutable) datastructure. *)
module Persistent_disambiguation_state : sig
  include DISAMBIGUATION_STATE

  val initial_state : state
end
