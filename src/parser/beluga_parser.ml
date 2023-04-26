open Support
open Beluga_syntax

(** {1 Configuration Files} *)

module Config_parser = Config_parser

(** {1 Lexing} *)

module Token = Token
module Located_token = Located_token
module Lexer = Lexer

(** {1 Parsing} *)

module type PARSER_STATE = Parser_combinator.PARSER_STATE

module Parser_combinator = Parser_combinator
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

  include
    Common_parser.COMMON_PARSER
      with type state := state
       and type location := location
       and type token := token

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
                       and type location = Location.t) =
struct
  module Parser_combinator = Parser_combinator.Make (Parser_state)
  module Common_parser = Common_parser.Make (Parser_combinator)
  module Lf_parser = Lf_parser.Make (Common_parser)
  module Clf_parser = Clf_parser.Make (Common_parser)
  module Meta_parser =
    Meta_parser.Make (Common_parser) (Lf_parser) (Clf_parser)
  module Comp_parser = Comp_parser.Make (Common_parser) (Meta_parser)
  module Harpoon_parser =
    Harpoon_parser.Make (Common_parser) (Meta_parser) (Comp_parser)
  module Signature_parser =
    Signature_parser.Make (Common_parser) (Lf_parser) (Clf_parser)
      (Meta_parser)
      (Comp_parser)
      (Harpoon_parser)
  include Parser_state
  include Parser_combinator
  include Common_parser
  include Lf_parser
  include Clf_parser
  include Meta_parser
  include Comp_parser
  include Harpoon_parser
  include Signature_parser
end

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

module Make_disambiguation (Disambiguation_state : DISAMBIGUATION_STATE) =
struct
  module Lf_disambiguator = Lf_disambiguation.Make (Disambiguation_state)
  module Clf_disambiguator = Clf_disambiguation.Make (Disambiguation_state)
  module Meta_disambiguator =
    Meta_disambiguation.Make (Disambiguation_state) (Lf_disambiguator)
      (Clf_disambiguator)
  module Comp_disambiguator =
    Comp_disambiguation.Make (Disambiguation_state) (Meta_disambiguator)
  module Harpoon_disambiguator =
    Harpoon_disambiguation.Make (Disambiguation_state) (Meta_disambiguator)
      (Comp_disambiguator)
  module Signature_disambiguator =
    Signature_disambiguation.Make (Disambiguation_state) (Lf_disambiguator)
      (Clf_disambiguator)
      (Meta_disambiguator)
      (Comp_disambiguator)
      (Harpoon_disambiguator)
  include Disambiguation_state
  include Lf_disambiguator
  include Clf_disambiguator
  include Meta_disambiguator
  include Comp_disambiguator
  include Harpoon_disambiguator
  include Signature_disambiguator
end

(** {1 Constructors} *)

module Make
    (Parser_state : PARSER_STATE
                      with type token = Located_token.t
                       and type location = Location.t)
    (Disambiguation_state : DISAMBIGUATION_STATE) =
struct
  module Parsing = Make_parsing (Parser_state)
  module Disambiguation = Make_disambiguation (Disambiguation_state)

  type parser_state = Parsing.state

  type disambiguation_state = Disambiguation.state

  type state =
    { parser_state : parser_state
    ; disambiguation_state : disambiguation_state
    }

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let[@inline] make_state ~parser_state ~disambiguation_state =
    { parser_state; disambiguation_state }

  let get_parser_state =
    let* state = get in
    return state.parser_state

  let[@inline] set_parser_state parser_state =
    modify (fun state -> { state with parser_state })

  let get_disambiguation_state =
    let* state = get in
    return state.disambiguation_state

  let[@inline] set_disambiguation_state disambiguation_state =
    modify (fun state -> { state with disambiguation_state })

  let parse parser =
    let* parser_state = get_parser_state in
    let parser_state', parsed = Parser_state.run parser parser_state in
    let* () = set_parser_state parser_state' in
    return parsed

  let disambiguate disambiguator =
    let* disambiguation_state = get_disambiguation_state in
    let disambiguated = disambiguator disambiguation_state in
    return disambiguated

  let parse_and_disambiguate ~parser ~disambiguator =
    let* parsed = parse (Parsing.run_exn parser) in
    let* disambiguated =
      disambiguate (fun state -> disambiguator state parsed)
    in
    return disambiguated
end

module Parser = struct
  module Parser_state =
    Parser_combinator.Make_persistent_state (Located_token)
  module Disambiguation_state = Disambiguation_state.Disambiguation_state
  include Make (Parser_state) (Disambiguation_state)

  let make_initial_parser_state_from_channel ~initial_location input =
    let token_sequence = Lexer.lex_input_channel ~initial_location input in
    Parser_state.initial ~initial_location token_sequence

  let make_initial_parser_state_from_string ~initial_location input =
    let token_sequence = Lexer.lex_string ~initial_location input in
    Parser_state.initial ~initial_location token_sequence

  let make_initial_state_from_channel ~disambiguation_state ~initial_location
      ~channel =
    let parser_state =
      make_initial_parser_state_from_channel ~initial_location channel
    in
    make_state ~disambiguation_state ~parser_state

  let make_initial_state_from_string ~disambiguation_state ~initial_location
      ~input =
    let parser_state =
      make_initial_parser_state_from_string ~initial_location input
    in
    make_state ~disambiguation_state ~parser_state

  let read_and_parse_signature filename =
    In_channel.with_open_bin filename (fun in_channel ->
        let initial_location = Location.initial filename in
        let _parser_state', signature =
          Parsing.run_exn
            (Parsing.only Parsing.signature_file)
            (make_initial_parser_state_from_channel ~initial_location
               in_channel)
        in
        signature)

  let read_multi_file_signature files =
    let signature =
      (* For OCaml >= 5, spawn a parallel domain for each call to
         {!read_signature}] *)
      List1.map read_and_parse_signature files
    in
    let signature' =
      Disambiguation.disambiguate_signature
        (Disambiguation_state.create_initial_state ())
        signature
    in
    signature'
end
