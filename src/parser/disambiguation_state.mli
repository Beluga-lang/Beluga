(** Definition and implementation of the state required to disambiguate the
    Beluga syntax from the parser AST to the external AST. *)

open Support
open Beluga_syntax.Syncom

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

(** Abstract definition of a disambiguation state.

    A disambiguation state is the auxiliary data structure used during the
    disambiguation phase found in modules {!module:Lf_disambiguation},
    {!module:Clf_disambiguation}, {!module:Meta_disambiguation},
    {!module:Comp_disambiguation}, {!module:Harpoon_disambiguation} and
    {!module:Signature_disambiguation}. This data structure is responsible
    for keeping track of the referencing environment (bindings in scope)
    during the traversal of the parser syntax. In particular, it keeps track
    of user-defined notations (i.e., prefix, infix and postfix notations
    introduced by pragmas) for disambiguating applications. *)
module type DISAMBIGUATION_STATE = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** Recorded data on bindings in Beluga signatures. *)
  module Entry : ENTRY

  (** {1 Variables} *)

  (** [add_lf_variable state ?location identifier] adds [identifier] as a
      bound LF variable, with binding site [location]. If
      [location = Option.None], then [identifier]'s location is used instead.

      This is mostly used for testing. For locally binding an LF variable,
      see {!with_bound_lf_variable}. *)
  val add_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_meta_variable] is like {!add_lf_variable}, but the identifier is
      added as a bound meta-variable. *)
  val add_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_parameter_variable] is like {!add_lf_variable}, but the identifier
      is added as a bound parameter variable (those variables prefixed by
      ['#'] like ["#p"]). *)
  val add_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_substitution_variable] is like {!add_lf_variable}, but the
      identifier is added as a bound substitution variable (those variables
      prefixed by ['$'] like ["$S"]). *)
  val add_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_context_variable] is like {!add_lf_variable}, but the identifier
      is added as a bound context variable. *)
  val add_context_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_computation_variable] is like {!add_lf_variable}, but the
      identifier is added as a bound computation-level variable. *)
  val add_computation_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_free_lf_variable state ?location identifier] is
      [add_lf_variable state ?location identifier], with the additional
      behaviour of adding [identifier] as an inner pattern bound identifier
      and as a free variable during pattern disambiguation. This means that
      [identifier] can subsequently be looked up as a bound LF variable
      during pattern disambiguation. This effectively allows free LF
      variables to appear multiple times (non-linearly) in patterns.

      See {!with_free_variables_as_pattern_variables} for the handler for
      converting free variables in patterns to binders for use as bound
      variables in expressions. *)
  val add_free_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_free_meta_variable] is like {!add_free_lf_variable}, but the
      identifier is added as a free meta-variable. *)
  val add_free_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_free_meta_variable] is like {!add_free_lf_variable}, but the
      identifier is added as a free parameter variable. *)
  val add_free_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_free_meta_variable] is like {!add_free_lf_variable}, but the
      identifier is added as a free substitution variable. *)
  val add_free_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_free_meta_variable] is like {!add_free_lf_variable}, but the
      identifier is added as a free context variable. *)
  val add_free_context_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [add_free_computation_variable state ?location identifier] adds
      [identifier] to [state] as a free variable during pattern
      disambiguation. This differs from {!add_free_lf_variable} in that free
      computation-level variables in patterns do not have implicit binders
      (because they are not part of the meta-context), and hence must appear
      only once (linearly) in the overall pattern. *)
  val add_free_computation_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  (** [with_bound_lf_variable state ?location identifier m] is the result of
      running [m] in the local state derived from [state] having [identifier]
      as a bound LF variable.

      When disambiguating a pattern, [identifier] is also added as an inner
      pattern binding.

      For example, the disambiguation of an LF term-level lambda-abstraction
      [\x. m] requires that the parameter [x] is locally added in scope when
      disambiguating the body [m]. This is achieved like this:

      {[
        with_bound_lf_variable state x (fun state ->
            disambiguate_lf_term state m)
      ]} *)
  val with_bound_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** [with_bound_meta_variable state ?location identifier m] is like
      {!val:with_bound_lf_variable}, except that [identifier] is added to the
      state as a bound meta-variable.

      When disambiguating a pattern, [identifier] is also added as an inner
      pattern binding. *)
  val with_bound_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_context_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** [with_bound_contextual_variable state ?location identifier m] is like
      {!val:with_bound_lf_variable}, except that [identifier] is added to the
      state as a bound contextual variable. This is different from
      {!val:with_bound_meta_variable}, {!val:with_bound_parameter_variable},
      {!with_bound_substitution_variable} and
      {!val:with_bound_context_variable} in that it is unknown whether
      [identifier] should be a meta-variable, parameter variable,
      substitution variable or context variable. This is used in particular
      for [mlam] expressions.

      When disambiguating a pattern, [identifier] is also added as an inner
      pattern binding. *)
  val with_bound_contextual_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** [with_bound_computation_variable state ?location identifier m] is like
      {!val:with_bound_lf_variable}, except that [identifier] is added to the
      state as a bound computation-level variable. *)
  val with_bound_computation_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** [with_bound_pattern_meta_variable state ?location identifier m] is like
      [with_bound_meta_variable state ?location identifier m] except that
      [identifier] is also treated as a free variable so that in
      {!with_free_variables_as_pattern_variables} it can be treated as a
      pattern variable usable in the expression.

      This is used for meta-variables introduced in the meta-context of a
      pattern during case analysis. Those variables are considered bound in
      both the pattern and expression.

      For example, [B] as below is one such bound pattern meta-variable, and
      appears in scope for [?].

      {[
        case x of
        | { B : [g |- o] } [g |- impi \u. D] => ?
      ]} *)
  val with_bound_pattern_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_context_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** [with_free_variables_as_pattern_variables state ~pattern ~expression state]
      is the result of running [expression] with the free variables added in
      [pattern] as bound variables. This is used to disambiguate [expression]
      with bound variables arising from free variables in [pattern].

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
    state -> pattern:(state -> 'a) -> expression:(state -> 'a -> 'b) -> 'b

  (** [with_scope state m] runs [m] in a nested bindings scope that is
      discarded afterwards. *)
  val with_scope : state -> (state -> 'a) -> 'a

  (** [with_parent_scope state m] runs [m] while ignoring the topmost scope.

      This is used for the disambiguation of Harpoon proof scripts because
      Harpoon hypotheticals are already serialized with all the identifiers
      in the meta-level and computation-level contexts of the proof. *)
  val with_parent_scope : state -> (state -> 'a) -> 'a

  (** [with_bindings_checkpoint state m] runs [m] with a checkpoint on the
      bindings' state to backtrack to in case [m] raises an exception.

      This is used for backtracking when disambiguating old-style LF
      type-level and term-level declarations (i.e., [x : X] where [X] may be
      an LF kind or an LF type).

      This is also used in REPLs to safely run parsing functions and recover
      the state in case of a raised exception during disambiguation. *)
  val with_bindings_checkpoint : state -> (state -> 'a) -> 'a

  (** {1 Constants} *)

  (** [add_lf_type_constant state ?location ?arity identifier] adds
      [identifier] as a bound LF type-level constant.

      In the disambiguation of a module's declaration, this also adds the
      constant as one of the module's declarations. *)
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

  (** [add_module state ?location identifier m] is the result of running [m]
      in a module disambiguation state, whereby added constants are kept
      track of as declarations in the module having [identifier]. *)
  val add_module :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  (** {1 Lookups} *)

  exception Unbound_identifier of Identifier.t

  exception Unbound_qualified_identifier of Qualified_identifier.t

  exception Unbound_namespace of Qualified_identifier.t

  (** [lookup_toplevel state identifier] is [entry] if [identifier] resolves
      to [entry] in [state]. If [identifier] is unbound in [state], then
      [Unbound_identifier identifier] is raised. *)
  val lookup_toplevel : state -> Identifier.t -> Entry.t

  (** [lookup state identifier] is [entry] if [identifier] resolves to
      [entry] in [state]. Otherwise:

      - [Unbound_identifier ident)] is raised if the first segment [ident] in
        [identifier] is unbound.
      - [Unbound_namespace namespace_identifier] is raised if a segment in
        [identifier] other than the first or last is unbound.
      - [Unbound_qualified_identifier identifier] is raised if the last
        segment in [identifier] is unbound. *)
  val lookup : state -> Qualified_identifier.t -> Entry.t

  (** [maximum_lookup state segments] is either:

      - [`Unbound segments] if the first segment in [segments] is unbound in
        [state].
      - [`Partially_bound (leading_segments, (segment, entry), (trailing_segments))]
        if the qualified identifier with namespaces [leading_segments] and
        name [segment] is bound to [entry] in [state].
      - [`Bound (identifier, entry)] if [segments] form a qualified
        identifier bound to [entry] in [state]. *)
  val maximum_lookup :
       state
    -> Identifier.t List1.t
    -> [ `Unbound of Identifier.t List1.t
       | `Partially_bound of
         Identifier.t List.t
         * (Identifier.t * Entry.t)
         * Identifier.t List1.t
       | `Bound of Qualified_identifier.t * Entry.t
       ]

  (** [actual_binding_exn identifier entry] is an exception reporting what
      sort of [entry] is bound at [identifier]. The exception is annotated
      with the entry's binding location. *)
  val actual_binding_exn : Qualified_identifier.t -> Entry.t -> exn

  (** {1 Signature Operations} *)

  (** [open_module state module_identifier] adds the exported constants from
      the module bound to [module_identifier] as toplevel entries in [state].
      If [module_identifier] is unbound in [state], then an exception is
      raised. *)
  val open_module : state -> Qualified_identifier.t -> Unit.t

  (** [get_default_associativity state] is the associativity to use for infix
      operators defined by the user using a pragma, without specifying the
      infix operator's associativity. *)
  val get_default_associativity : state -> Associativity.t

  (** [set_default_associativity state default_associativity] sets
      [default_associativity] as the associativity to return from
      {!get_default_associativity}. *)
  val set_default_associativity : state -> Associativity.t -> Unit.t

  (** [get_default_precedence state] is the precedence to use for operators
      defined by the user using a pragma, without specifying the operator's
      precedence. *)
  val get_default_precedence : state -> Int.t

  (** [set_default_precedence state default_precedence] sets
      [default_precedence] as the precedence to return from
      {!get_default_precedence}. *)
  val set_default_precedence : state -> Int.t -> Unit.t

  (** [add_prefix_notation state ?precedence identifier] adds a prefix
      notation for [identifier]. If [precedence = Option.None], then
      {!get_default_precedence} is used instead.

      An exception is raised if [identifier] is unbound in [state], not bound
      to a constant, or bound to a constant of an unknown or invalid arity. *)
  val add_prefix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  (** [add_infix_notation state ?precedence ?associativity identifier] adds
      an infix notation for [identifier]. If [precedence = Option.None], then
      {!get_default_precedence} is used instead. Likewise, if
      [associativity = Option.None], then {!get_default_associativity} is
      used instead.

      An exception is raised if [identifier] is unbound in [state], not bound
      to a constant, or bound to a constant of an unknown or invalid arity. *)
  val add_infix_notation :
       state
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  (** [add_postfix_notation state ?precedence identifier] adds a postfix
      notation for [identifier]. If [precedence = Option.None], then
      {!get_default_precedence} is used instead.

      An exception is raised if [identifier] is unbound in [state], not bound
      to a constant, or bound to a constant of an unknown or invalid arity. *)
  val add_postfix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  (** [lookup_operator state identifier] is [Option.Some operator] if
      [identifier] is bound to an operator with descriptor [operator] in
      [state], and [Option.None] otherwise.

      This is used to resolve operators in the disambiguation of
      applications, which are parsed as lists of expressions. *)
  val lookup_operator :
    state -> Qualified_identifier.t -> Operator.t Option.t

  (** [add_module_abbreviation state ?location module_identifier abbreviation]
      adds the synonym [abbreviation] for the module bound to [identifier] in
      [state].

      An exception is raised if [module_identifier] is unbound in [state], or
      if [module_identifier] is not bound to a module in [state]. *)
  val add_module_abbreviation :
       state
    -> ?location:Location.t
    -> Qualified_identifier.t
    -> Identifier.t
    -> Unit.t
end

(** Concrete implementation of {!module-type:DISAMBIGUATION_STATE} backed by
    a mutable data structure. *)
module Disambiguation_state : sig
  (** @closed *)
  include DISAMBIGUATION_STATE

  (** [create_initial_state ()] is a fresh empty disambiguation state. *)
  val create_initial_state : Unit.t -> state

  (** [clear_state state] resets [state] to its initial state. *)
  val clear_state : state -> Unit.t

  (** [snapshot_state state] is a surface copy of [state], meaning that it is
      effectively a frozen copy of [state]. Only the latest bindings in
      [state] are kept. *)
  val snapshot_state : state -> state
end
