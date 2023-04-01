open Beluga_syntax
open Common_parser

module type COMP_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val comp_kind : Synprs.comp_sort_object t

  val comp_typ : Synprs.comp_sort_object t

  val comp_pattern : Synprs.comp_pattern_object t

  val comp_copattern : Synprs.comp_copattern_object t

  val comp_expression : Synprs.comp_expression_object t

  val comp_context : Synprs.comp_context_object t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Located_token.t
                 and type location = Location.t)
    (Meta_parser : Meta_parser.META_PARSER
                     with type token = Parser.token
                      and type input = Parser.input
                      and type state = Parser.state
                      and type location = Parser.location) :
  COMP_PARSER
    with type token = Parser.token
     and type input = Parser.input
     and type state = Parser.state
     and type location = Parser.location
[@@warning "-67"]
