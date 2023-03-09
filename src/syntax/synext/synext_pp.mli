open Support
open Common
open Synext_definition

module type PRINTING_STATE = sig
  include State.STATE

  include Format_state.S with type state := state

  val add_binding : Identifier.t -> Unit.t t

  val with_module_declarations : Identifier.t -> 'a t -> 'a t

  val add_module_declaration : Identifier.t -> Unit.t t

  val open_module : Qualified_identifier.t -> Unit.t t

  val add_abbreviation : Qualified_identifier.t -> Identifier.t -> Unit.t t

  val set_default_associativity : Associativity.t -> Unit.t t

  val get_default_associativity : Associativity.t t

  val set_default_precedence : Int.t -> Unit.t t

  val get_default_precedence : Int.t t

  val lookup_operator_precedence : Qualified_identifier.t -> Int.t Option.t t

  val lookup_operator : Qualified_identifier.t -> Operator.t Option.t t

  val make_prefix : ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  val make_infix :
       ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t t

  val make_postfix : ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t
end

module Printing_state : sig
  include PRINTING_STATE

  val initial : Format.formatter -> state

  val set_formatter : Format.formatter -> Unit.t t
end

module type BELUGA_PRINTER = sig
  include State.STATE

  val pp_signature_file : signature_file -> Unit.t t
end

module Make_pretty_printer (Printing_state : PRINTING_STATE) :
  BELUGA_PRINTER with type state = Printing_state.state
