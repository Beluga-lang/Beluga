(** HTML printing state for the concrete syntax.

    The generation of HTML pages corresponding to concrete Beluga signatures
    requires keeping track of HTML IDs for constant declarations (to be
    referred to by anchors), and keeping track of user-defined notations of
    constants for printing applications. This means that module bindings have
    to be kept track of, and pragmas have to be applied during printing.

    @author Marc-Antoine Ouimet *)

open Support
open Beluga_syntax.Syncom

(** Abstract definition for the HTML printing state. *)
module type HTML_PRINTING_STATE = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** @closed *)
  include Format_state.S with type state := state

  val set_formatter : state -> Format.formatter -> Unit.t

  (** [fresh_id state ?prefix identifier] is the unique ID generated from
      [identifier] and [state], and optionally using [prefix]. This ID is
      intended to be used as an HTML ID for anchor elements to refer to. If
      [prefix = Option.Some p], then [id] starts with [p] (this is just for
      aesthetics).

      [state] is updated to keep track of [id] to guarantee that subsequent
      generated IDs are unique. *)
  val fresh_id : state -> ?prefix:String.t -> Identifier.t -> String.t

  (** [preallocate_id state ?prefix identifier] is the unique ID generated
      from [identifier] and [state], and optionally using [prefix] that will
      be bound to the next declaration added to [state] with identifier
      [identifier]. That is, the preallocated ID is reserved for the next
      time we want to generate a fresh ID for [identifier].

      This is used specifically for postponed fixity pragmas. A postponed
      fixity pragma needs an ID reference to the declaration it is attached
      to, but this declaration appears later in the signature file. Hence we
      preallocate an ID for that subsequent declaration, and use it as
      reference for the postponed pragma. *)
  val preallocate_id : state -> ?prefix:String.t -> Identifier.t -> String.t

  val set_current_page : state -> String.t -> Unit.t

  val lookup_reference : state -> Qualified_identifier.t -> String.t

  (** [lookup_id state constant] is the HTML ID for the bound [constant] in
      [state].

      If [constant] is unbound in [state], then an exception is raised. *)
  val lookup_id : state -> Qualified_identifier.t -> String.t

  (** [open_module state module_identifier] adds the bindings in the module
      having identifier [module_identifier] in [state].

      If [module_identifier] is unbound in [state], then an exception is
      raised. *)
  val open_module : state -> Qualified_identifier.t -> Unit.t

  (** [add_abbreviation module_identifier state abbreviation] adds
      [abbreviation] for referring to the module [module_identifier] in
      [state].

      If [module_identifier] is unbound in [state], then an exception is
      raised. *)
  val add_abbreviation :
    state -> Qualified_identifier.t -> Identifier.t -> Unit.t

  (** [set_default_associativity state associativity] sets [associativity] as
      the default associativity for new user-defined infix operators. *)
  val set_default_associativity : state -> Associativity.t -> Unit.t

  (** [get_default_associativity state] is the default associativity for new
      user-defined infix operators. *)
  val get_default_associativity : state -> Associativity.t

  (** [set_default_precedence state precedence] sets [precedence] as the
      default precedence for new user-defined operators. *)
  val set_default_precedence : state -> Int.t -> Unit.t

  (** [get_default_precedence state] is the default precedence for new
      user-defined operators. *)
  val get_default_precedence : state -> Int.t

  val add_lf_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_lf_term_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_schema_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_inductive_computation_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_stratified_computation_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_coinductive_computation_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_abbreviation_computation_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_computation_term_constructor :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_computation_term_destructor :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_program_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  (** [add_module state ?location module_identifier ~id f] is the result of
      [f] when run in a state in a new module with [identifier] and [~id].
      Bindings added by [declarations] are added to the new module only. The
      derived state has [identifier] bound to the newly created module. *)
  val add_module :
       state
    -> ?location:'a
    -> Identifier.t
    -> id:String.t
    -> (state -> 'a)
    -> 'a

  (** [add_prefix_notation state ?precedence constant] sets [constant] as a
      prefix operator with precedence [p] if [precedence = Option.Some p], or
      [state]'s default precedence if [precedence = Option.None].

      If [constant] is unbound in [state], then an exception is raised. *)
  val add_prefix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  (** [add_infix_notation state ?precedence ?associativity constant] sets
      [constant] as an infix operator with:

      - precedence [p] if [precedence = Option.Some p], or [state]'s default
        precedence if [precedence = Option.None].
      - associativity [a] if [associativity = Option.Some a], or [state]'s
        default associativity if [associativity = Option.None].

      If [constant] is unbound in [state], then an exception is raised. *)
  val add_infix_notation :
       state
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  (** [add_postfix_notation state ?precedence constant] sets [constant] as a
      postfix operator with precedence [p] if [precedence = Option.Some p],
      or [state]'s default precedence if [precedence = Option.None].

      If [constant] is unbound, then an exception is raised. *)
  val add_postfix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  (** [add_postponed_prefix_notation state ?precedence identifier] adds a
      postponed prefix notation for [identifier]. If
      [precedence = Option.None], then {!get_default_precedence} is used
      instead.

      This notation is postponed, meaning that it only applies once
      {!val:apply_postponed_fixity_pragmas} is called. *)
  val add_postponed_prefix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  (** [add_postponed_infix_notation state ?precedence ?associativity identifier]
      adds a postponed infix notation for [identifier]. If
      [precedence = Option.None], then {!get_default_precedence} is used
      instead. Likewise, if [associativity = Option.None], then
      {!get_default_associativity} is used instead.

      This notation is postponed, meaning that it only applies once
      {!val:apply_postponed_fixity_pragmas} is called. *)
  val add_postponed_infix_notation :
       state
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  (** [add_postponed_postfix_notation state ?precedence identifier] adds a
      postponed postfix notation for [identifier]. If
      [precedence = Option.None], then {!get_default_precedence} is used
      instead.

      This notation is postponed, meaning that it only applies once
      {!val:apply_postponed_fixity_pragmas} is called. *)
  val add_postponed_postfix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  (** [apply_postponed_fixity_pragmas state] adds in scope the postponed
      prefix, infix and postfix fixity pragmas. This function should be
      called only when the targets of those postponed pragmas are in scope.
      That is, postponed fixity pragmas are applied after the subsequent
      declaration is added, or after a group of mutually recursive
      declarations are added. *)
  val apply_postponed_fixity_pragmas : state -> unit

  (** [lookup_operator state constant] is the operator description
      corresponding to [constant] bound in [state].

      If [constant] is unbound in [state], then an exception is raised. *)
  val lookup_operator :
    state -> Qualified_identifier.t -> Operator.t Option.t

  val lookup_operator_precedence :
    state -> Qualified_identifier.t -> Int.t Option.t
end

(** Concrete implementation of {!HTML_PRINTING_STATE} backed by a (mostly)
    immutable data structure. The instance of {!type:Format.formatter} is
    mutable, and concurrent writes to it will lead to unexpected results. *)
module Html_printing_state : sig
  (** @closed *)
  include HTML_PRINTING_STATE

  (** [create_initial_state ~current_page ppf] constructs an empty printing
      state. *)
  val create_initial_state :
    current_page:String.t -> Format.formatter -> state
end
