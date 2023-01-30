open Beluga_syntax
open Common_parser

module type CLF_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val clf_typ : Synprs.clf_object t

  val clf_term : Synprs.clf_object t

  val clf_term_pattern : Synprs.clf_object t

  val clf_context : Synprs.clf_context_object t

  val clf_substitution : Synprs.clf_context_object t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Location.t * Token.t
                 and type location = Location.t) :
  CLF_PARSER
    with type token = Parser.token
     and type input = Parser.input
     and type state = Parser.state
     and type location = Parser.location
