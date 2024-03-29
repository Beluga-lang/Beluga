open Beluga_syntax
open Common_parser

module type META_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val schema : Synprs.schema_object t

  val meta_type : Synprs.meta_thing t

  val meta_object : Synprs.meta_thing t

  val meta_pattern : Synprs.meta_thing t

  val meta_context : Synprs.meta_context_object t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Located_token.t
                 and type location = Location.t)
    (Lf_parser : Lf_parser.LF_PARSER
                   with type state = Parser.state
                    and type token = Parser.token
                    and type location = Parser.location)
    (Clf_parser : Clf_parser.CLF_PARSER
                    with type state = Parser.state
                     and type token = Parser.token
                     and type location = Parser.location) :
  META_PARSER
    with type state = Parser.state
     and type token = Parser.token
     and type location = Parser.location
[@@warning "-67"]
