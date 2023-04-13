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

(** {1 Disambiguation} *)

module type DISAMBIGUATION_STATE = Disambiguation_state.DISAMBIGUATION_STATE

module Application_disambiguation = Application_disambiguation
module Lf_disambiguation = Lf_disambiguation
module Clf_disambiguation = Clf_disambiguation
module Meta_disambiguation = Meta_disambiguation
module Comp_disambiguation = Comp_disambiguation
module Harpoon_disambiguation = Harpoon_disambiguation
module Signature_disambiguation = Signature_disambiguation

(** {1 Constructors} *)

module Make
    (Parser_state : PARSER_STATE
                      with type token = Located_token.t
                       and type location = Location.t)
    (Disambiguation_state : DISAMBIGUATION_STATE) : sig
  module Parsing : sig
    include module type of Parser_state

    include Parser_combinator.PARSER with type state := state

    include Common_parser.COMMON_PARSER with type state := state

    include Lf_parser.LF_PARSER with type state := state

    include Clf_parser.CLF_PARSER with type state := state

    include Meta_parser.META_PARSER with type state := state

    include Comp_parser.COMP_PARSER with type state := state

    include Harpoon_parser.HARPOON_PARSER with type state := state

    include Signature_parser.SIGNATURE_PARSER with type state := state
  end

  module Disambiguation : sig
    include module type of Disambiguation_state

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

  include State.STATE

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

module Beluga_parser : sig
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
