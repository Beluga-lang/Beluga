open Beluga_syntax
open Common_parser

module type LF_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val lf_kind : Synprs.lf_object t

  val lf_typ : Synprs.lf_object t

  val lf_term : Synprs.lf_object t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Located_token.t
                 and type location = Location.t) :
  LF_PARSER
    with type token = Parser.token
     and type input = Parser.input
     and type state = Parser.state
     and type location = Parser.location
