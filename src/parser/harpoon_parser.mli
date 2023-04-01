open Support
open Beluga_syntax
open Common_parser

module type HARPOON_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val harpoon_proof : Synprs.harpoon_proof t

  val interactive_harpoon_command : Synprs.harpoon_repl_command t

  val interactive_harpoon_command_sequence :
    Synprs.harpoon_repl_command List.t t

  val next_theorem : [> `next of Identifier.t | `quit ] t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Located_token.t
                 and type location = Location.t)
    (Meta_parser : Meta_parser.META_PARSER
                     with type token = Parser.token
                      and type input = Parser.input
                      and type state = Parser.state
                      and type location = Parser.location)
    (Comp_parser : Comp_parser.COMP_PARSER
                     with type token = Parser.token
                      and type input = Parser.input
                      and type state = Parser.state
                      and type location = Parser.location) :
  HARPOON_PARSER
    with type token = Parser.token
     and type input = Parser.input
     and type state = Parser.state
     and type location = Parser.location
[@@warning "-67"]
