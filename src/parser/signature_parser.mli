open Beluga_syntax
open Common_parser

module type SIGNATURE_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val sgn : Synprs.signature t

  val sgn_entry : Synprs.signature_entry t

  val sgn_declaration : Synprs.signature_declaration t

  val trust_totality_declaration : Synprs.signature_totality_declaration t

  val named_totality_declaration : Synprs.signature_totality_declaration t

  val numeric_totality_declaration : Synprs.signature_totality_declaration t

  val totality_declaration : Synprs.signature_totality_declaration t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Location.t * Token.t
                 and type location = Location.t)
    (Lf_parser : Lf_parser.LF_PARSER
                   with type token = Parser.token
                    and type input = Parser.input
                    and type state = Parser.state
                    and type location = Parser.location)
    (Meta_parser : Meta_parser.META_PARSER
                     with type token = Parser.token
                      and type input = Parser.input
                      and type state = Parser.state
                      and type location = Parser.location)
    (Comp_parser : Comp_parser.COMP_PARSER
                     with type token = Parser.token
                      and type input = Parser.input
                      and type state = Parser.state
                      and type location = Parser.location)
    (Harpoon_parser : Harpoon_parser.HARPOON_PARSER
                        with type token = Parser.token
                         and type input = Parser.input
                         and type state = Parser.state
                         and type location = Parser.location) :
  SIGNATURE_PARSER
    with type token = Parser.token
     and type input = Parser.input
     and type state = Parser.state
     and type location = Parser.location
[@@warning "-67"]