(** Parsing and disambiguation of Beluga signatures.

    @author Marc-Atoine Ouimet *)

open Support
open Beluga_syntax

(** {1 Configuration Files} *)

module Config_parser = Config_parser

(** {1 Parsing} *)

module type PARSER_STATE = Common_parser.PARSER_STATE

module Parser_combinator = Parser_combinator
module Token = Token
module Located_token = Located_token
module Common_parser = Common_parser
module Lf_parser = Lf_parser
module Clf_parser = Clf_parser
module Meta_parser = Meta_parser
module Comp_parser = Comp_parser
module Harpoon_parser = Harpoon_parser
module Signature_parser = Signature_parser

module type PARSING = sig
  include
    PARSER_STATE
      with type token = Located_token.t
       and type location = Location.t

  include
    Parser_combinator.PARSER
      with type state := state
       and type location := location
       and type token := token
       and type input = token Seq.t

  include
    Common_parser.COMMON_PARSER
      with type state := state
       and type location := location
       and type token := token
       and type input := input

  include Lf_parser.LF_PARSER with type state := state

  include Clf_parser.CLF_PARSER with type state := state

  include Meta_parser.META_PARSER with type state := state

  include Comp_parser.COMP_PARSER with type state := state

  include Harpoon_parser.HARPOON_PARSER with type state := state

  include Signature_parser.SIGNATURE_PARSER with type state := state
end

module Make_parsing
    (Parser_state : PARSER_STATE
                      with type token = Located_token.t
                       and type location = Location.t) :
  PARSING
    with type state = Parser_state.state
     and type token = Parser_state.token
     and type location = Parser_state.location

(** {1 Disambiguation} *)

module type DISAMBIGUATION_STATE = Disambiguation_state.DISAMBIGUATION_STATE

module Application_disambiguation = Application_disambiguation
module Lf_disambiguation = Lf_disambiguation
module Clf_disambiguation = Clf_disambiguation
module Meta_disambiguation = Meta_disambiguation
module Comp_disambiguation = Comp_disambiguation
module Harpoon_disambiguation = Harpoon_disambiguation
module Signature_disambiguation = Signature_disambiguation

module type DISAMBIGUATION = sig
  include DISAMBIGUATION_STATE

  include Lf_disambiguation.LF_DISAMBIGUATION with type state := state

  include Clf_disambiguation.CLF_DISAMBIGUATION with type state := state

  include Meta_disambiguation.META_DISAMBIGUATION with type state := state

  include Comp_disambiguation.COMP_DISAMBIGUATION with type state := state

  include
    Harpoon_disambiguation.HARPOON_DISAMBIGUATION with type state := state

  include
    Signature_disambiguation.SIGNATURE_DISAMBIGUATION
      with type state := state
end

module Make_disambiguation (Disambiguation_state : DISAMBIGUATION_STATE) :
  DISAMBIGUATION with type state = Disambiguation_state.state

(** {1 Constructors} *)

module Make
    (Parser_state : PARSER_STATE
                      with type token = Located_token.t
                       and type location = Location.t)
    (Disambiguation_state : DISAMBIGUATION_STATE) : sig
  module Parsing : module type of Make_parsing (Parser_state)

  module Disambiguation :
      module type of Make_disambiguation (Disambiguation_state)

  include State.STATE

  val make_state :
       parser_state:Parser_state.state
    -> disambiguation_state:Disambiguation_state.state
    -> state

  val set_parser_state : Parser_state.state -> Unit.t t

  val get_parser_state : Parser_state.state t

  val set_disambiguation_state : Disambiguation_state.state -> Unit.t t

  val get_disambiguation_state : Disambiguation_state.state t

  val parse_and_disambiguate :
       parser:'a Parsing.t
    -> disambiguator:(Disambiguation.state -> 'a -> 'b)
    -> 'b t
end

(** {1 Instances} *)

module Parser : sig
  module Parser_state :
      module type of Parser_combinator.Make_persistent_state (Located_token)

  module Disambiguation_state = Disambiguation_state.Disambiguation_state

  include module type of Make (Parser_state) (Disambiguation_state)

  val make_initial_parser_state_from_channel :
    initial_location:Location.t -> in_channel -> Parser_state.state

  val make_initial_parser_state_from_string :
    initial_location:Location.t -> string -> Parser_state.state

  val make_initial_state_from_channel :
       disambiguation_state:Disambiguation_state.state
    -> initial_location:Location.t
    -> channel:in_channel
    -> state

  val make_initial_state_from_string :
       disambiguation_state:Disambiguation_state.state
    -> initial_location:Location.t
    -> input:string
    -> state

  val read_multi_file_signature : string List1.t -> Synext.signature
end
