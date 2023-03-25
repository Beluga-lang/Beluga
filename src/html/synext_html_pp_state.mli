(** HTML printing state for the concrete syntax.

    The generation of HTML pages corresponding to concrete Beluga signatures
    requires keeping track of HTML IDs for constant declarations (to be
    referred to by anchors), and keeping track of user-defined notations of
    constants for printing applications. This means that module bindings have
    to be kept track of, and pragmas have to be applied during printing.

    @author Marc-Antoine Ouimet *)

open Support
open Beluga_syntax
open Synext

(** Abstract definition for the HTML printing state. *)
module type HTML_PRINTING_STATE = sig
  (** @closed *)
  include State.STATE

  (** @closed *)
  include Format_state.S with type state := state

  (** [fresh_id ?prefix identifier state] is [(state', id)] where [id] is the
      unique ID generated from [identifier] and [state], and optionally using
      [prefix]. This ID is intended to be used as an HTML ID for anchor
      elements to refer to. If [prefix = Option.Some p], then [id] starts
      with [p] (this is just for aesthetics).

      [state'] is [state] updated to keep track of [id] to guarantee that
      subsequent ID generated are unique. *)
  val fresh_id : ?prefix:String.t -> Identifier.t -> String.t t

  (** [add_binding identifier ~id state] is [(state', ())] where [state'] is
      derived from [state] by adding the binding [identifier] with [id] in
      the current module. This shadows the previous binding for [identifier]
      if it exists. *)
  val add_binding : Identifier.t -> id:String.t -> Unit.t t

  (** [add_module identifier ~id declarations state] is
      [(state', declarations')] where [declarations'] is the result of
      [declarations] when run in a state in a new module with [identifier]
      and [~id]. Bindings added by [declarations] are added to the new module
      only. The derived state [state'] has [identifier] bound to the newly
      created module. *)
  val add_module : Identifier.t -> id:String.t -> 'a t -> 'a t

  (** [lookup_id constant state] is [(state', id)] where [id] is the HTML ID
      for the bound [constant] in [state].

      If [constant] is unbound in [state], then an exception is raised. *)
  val lookup_id : Qualified_identifier.t -> String.t t

  (** [open_module module_identifier state] is [(state', ())] where [state']
      is derived from [state] with the addition of the bindings in the module
      having identifier [module_identifier] in [state].

      If [module_identifier] is unbound in [state], then an exception is
      raised. *)
  val open_module : Qualified_identifier.t -> Unit.t t

  (** [add_abbreviation module_identifier abbreviation state] is
      [(state', ())] where [state'] is derived from [state] with the addition
      of [abbreviation] for referring to the module [module_identifier] in
      [state].

      If [module_identifier] is unbound in [state], then an exception is
      raised. *)
  val add_abbreviation : Qualified_identifier.t -> Identifier.t -> Unit.t t

  (** [set_default_associativity associativity state] is [(state', ())] where
      [state'] is derived from [state] with [associativity] as the default
      associativity for new user-defined infix operators. *)
  val set_default_associativity : Associativity.t -> Unit.t t

  (** [get_default_associativity state] is [(state', associativity)] where
      [associativity] is the default associativity for new user-defined infix
      operators. *)
  val get_default_associativity : Associativity.t t

  (** [set_default_precedence precedence state] is [(state', ())] where
      [state'] is derived from [state] with [precedence] as the default
      precedence for new user-defined operators. *)
  val set_default_precedence : Int.t -> Unit.t t

  (** [get_default_precedence state] is [(state', precedence)] where
      [precedence] is the default precedence for new user-defined operators. *)
  val get_default_precedence : Int.t t

  (** [make_prefix ?precedence constant state] is [(state', ())] where
      [state'] is derived from [state] with [constant] set as a prefix
      operator with precedence [p] if [precedence = Option.Some p], or
      [state]'s default precedence if [precedence = Option.None].

      If [constant] is unbound in [state], then an exception is raised. *)
  val make_prefix : ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  (** [make_infix ?precedence ?associativity constant state] is
      [(state', ())] where [state'] is derived from [state] with [constant]
      set as an infix operator with:

      - precedence [p] if [precedence = Option.Some p], or [state]'s default
        precedence if [precedence = Option.None].
      - associativity [a] if [associativity = Option.Some a], or [state]'s
        default associativity if [associativity = Option.None].

      If [constant] is unbound in [state], then an exception is raised. *)
  val make_infix :
       ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t t

  (** [make_postfix ?precedence constant state] is [(state', ())] where
      [state'] is derived from [state] with [constant] set as a postfix
      operator with precedence [p] if [precedence = Option.Some p], or
      [state]'s default precedence if [precedence = Option.None].

      If [constant] is unbound, then an exception is raised. *)
  val make_postfix : ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  (** [lookup_operator constant state] is [(state', operator_opt)] where
      [operator_opt] is the operator description corresponding to [constant]
      bound in [state].

      If [constant] is unbound in [state], then an exception is raised. *)
  val lookup_operator : Qualified_identifier.t -> Operator.t Option.t t
end

(** Concrete implementation of {!HTML_PRINTING_STATE} backed by a (mostly)
    immutable data structure. The instance of {!type:Format.formatter} is
    mutable, and concurrent writes to it will lead to unexpected results. *)
module Html_printing_state : sig
  (** @closed *)
  include HTML_PRINTING_STATE

  (** [make_initial_state ppf] constructs an empty printing state. *)
  val make_initial_state : Format.formatter -> state
end
