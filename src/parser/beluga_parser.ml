open Support
open Beluga_syntax

(** {1 Parsing} *)

module Parser_combinator = Parser_combinator
module Token = Token
module Common_parser = Common_parser
module Lf_parser = Lf_parser
module Clf_parser = Clf_parser
module Meta_parser = Meta_parser
module Comp_parser = Comp_parser
module Harpoon_parser = Harpoon_parser
module Signature_parser = Signature_parser

(** {1 Disambiguation} *)

module Shunting_yard = Shunting_yard
module Application_disambiguation = Application_disambiguation
module Lf_disambiguation = Lf_disambiguation
module Clf_disambiguation = Clf_disambiguation
module Meta_disambiguation = Meta_disambiguation
module Comp_disambiguation = Comp_disambiguation
module Harpoon_disambiguation = Harpoon_disambiguation
module Signature_disambiguation = Signature_disambiguation

(** {1 Constructors} *)

module Make
    (Parser_state : Common_parser.PARSER_STATE
                      with type token = Location.t * Token.t
                       and type location = Location.t)
    (Disambiguation_state : Common_disambiguation.DISAMBIGUATION_STATE) =
struct
  module Parser_combinator = Parser_combinator.Make (Parser_state)
  module Common_parser = Common_parser.Make (Parser_combinator)
  module Lf_parser = Lf_parser.Make (Common_parser)
  module Clf_parser = Clf_parser.Make (Common_parser)
  module Meta_parser = Meta_parser.Make (Common_parser) (Clf_parser)
  module Comp_parser = Comp_parser.Make (Common_parser) (Meta_parser)
  module Harpoon_parser =
    Harpoon_parser.Make (Common_parser) (Meta_parser) (Comp_parser)
  module Signature_parser =
    Signature_parser.Make (Common_parser) (Lf_parser) (Meta_parser)
      (Comp_parser)
      (Harpoon_parser)

  module Persistent_pattern_disambiguation_state =
    Common_disambiguation.Make_persistent_pattern_disambiguation_state
      (Disambiguation_state)

  module Lf_disambiguator :
    Lf_disambiguation.LF_DISAMBIGUATION
      with type state = Disambiguation_state.state =
    Lf_disambiguation.Make (Disambiguation_state)

  module Clf_disambiguator :
    Clf_disambiguation.CLF_DISAMBIGUATION
      with type state = Disambiguation_state.state =
    Clf_disambiguation.Make (Disambiguation_state)

  module Clf_pattern_disambiguator =
    Clf_disambiguation.Make_pattern_disambiguator
      (Disambiguation_state)
      (Persistent_pattern_disambiguation_state)

  module Meta_disambiguator :
    Meta_disambiguation.META_DISAMBIGUATION
      with type state = Disambiguation_state.state =
    Meta_disambiguation.Make (Disambiguation_state) (Clf_disambiguator)

  module Meta_pattern_disambiguator =
    Meta_disambiguation.Make_pattern_disambiguator
      (Disambiguation_state)
      (Persistent_pattern_disambiguation_state)
      (Clf_pattern_disambiguator)

  module Comp_disambiguator :
    Comp_disambiguation.COMP_DISAMBIGUATION
      with type state = Disambiguation_state.state =
    Comp_disambiguation.Make
      (Disambiguation_state)
      (Persistent_pattern_disambiguation_state)
      (Meta_disambiguator)
      (Meta_pattern_disambiguator)

  module Harpoon_disambiguator :
    Harpoon_disambiguation.HARPOON_DISAMBIGUATION
      with type state = Disambiguation_state.state =
    Harpoon_disambiguation.Make (Disambiguation_state) (Meta_disambiguator)
      (Comp_disambiguator)

  module Signature_disambiguator :
    Signature_disambiguation.SIGNATURE_DISAMBIGUATION
      with type state = Disambiguation_state.state =
    Signature_disambiguation.Make (Disambiguation_state) (Lf_disambiguator)
      (Meta_disambiguator)
      (Comp_disambiguator)
      (Harpoon_disambiguator)

  include Parser_combinator
  include Common_parser
  include Lf_parser
  include Clf_parser
  include Meta_parser
  include Comp_parser
  include Harpoon_parser
  include Signature_parser
  include Lf_disambiguator
  include Clf_disambiguator
  include Meta_disambiguator
  include Comp_disambiguator
  include Harpoon_disambiguator
  include Signature_disambiguator

  type disambiguation_state = Disambiguation_state.state

  type parser_state = Common_parser.state

  module State = struct
    type state =
      { parser_state : parser_state
      ; disambiguation_state : disambiguation_state
      }

    include (
      State.Make (struct
        type t = state
      end) :
        State.STATE with type state := state)

    let[@inline] make ~disambiguation_state ~parser_state =
      { parser_state; disambiguation_state }

    let[@inline] put_parser_state parser_state =
      modify (fun state -> { state with parser_state })

    let[@inline] put_disambiguation_state disambiguation_state =
      modify (fun state -> { state with disambiguation_state })

    let get_parser_state =
      let* state = get in
      return state.parser_state

    let get_disambiguation_state =
      let* state = get in
      return state.disambiguation_state

    let parse parser =
      let* parser_state = get_parser_state in
      let parser_state', parsed = parser parser_state in
      let* () = put_parser_state parser_state' in
      return parsed

    let disambiguate disambiguator =
      let* disambiguation_state = get_disambiguation_state in
      let disambiguation_state', disambiguated =
        disambiguator disambiguation_state
      in
      let* () = put_disambiguation_state disambiguation_state' in
      return disambiguated
  end

  include State

  type 'a t = ('a, exn) Result.t State.t

  let make_initial_parser_state_from_file ~filename =
    let initial_location = Location.initial filename in
    let token_sequence = Lexer.lex_file ~filename in
    Parser_state.initial ~initial_location token_sequence

  let make_initial_parser_state_from_channel ~initial_location input =
    let token_sequence = Lexer.lex_input_channel ~initial_location input in
    Parser_state.initial ~initial_location token_sequence

  let make_initial_parser_state_from_string ~initial_location input =
    let token_sequence = Lexer.lex_string ~initial_location input in
    Parser_state.initial ~initial_location token_sequence

  let make_initial_state_from_file ~disambiguation_state ~filename =
    let parser_state = make_initial_parser_state_from_file ~filename in
    State.make ~disambiguation_state ~parser_state

  let make_initial_state_from_channel ~disambiguation_state ~initial_location
      ~channel =
    let parser_state =
      make_initial_parser_state_from_channel ~initial_location channel
    in
    State.make ~disambiguation_state ~parser_state

  let make_initial_state_from_string ~disambiguation_state ~initial_location
      ~input =
    let parser_state =
      make_initial_parser_state_from_string ~initial_location input
    in
    State.make ~disambiguation_state ~parser_state

  let parse_and_disambiguate ~parser ~disambiguator =
    let* parsed = parse (run_exn parser) in
    let* disambiguated = disambiguate (disambiguator parsed) in
    return disambiguated

  let parse_only_lf_kind =
    eval
      (parse_and_disambiguate ~parser:(only lf_kind)
         ~disambiguator:disambiguate_lf_kind)

  let parse_only_lf_typ =
    eval
      (parse_and_disambiguate ~parser:(only lf_typ)
         ~disambiguator:disambiguate_lf_typ)

  let parse_only_lf_term =
    eval
      (parse_and_disambiguate ~parser:(only lf_term)
         ~disambiguator:disambiguate_lf_term)

  let parse_only_clf_typ =
    eval
      (parse_and_disambiguate ~parser:(only clf_typ)
         ~disambiguator:disambiguate_clf_typ)

  let parse_only_clf_term =
    eval
      (parse_and_disambiguate ~parser:(only clf_term)
         ~disambiguator:disambiguate_clf_term)

  let parse_only_clf_substitution =
    eval
      (parse_and_disambiguate ~parser:(only clf_substitution)
         ~disambiguator:disambiguate_clf_substitution)

  let parse_only_meta_typ =
    eval
      (parse_and_disambiguate ~parser:(only meta_type)
         ~disambiguator:disambiguate_meta_typ)

  let parse_only_meta_object =
    eval
      (parse_and_disambiguate ~parser:(only meta_object)
         ~disambiguator:disambiguate_meta_object)

  let parse_only_schema =
    eval
      (parse_and_disambiguate ~parser:(only schema)
         ~disambiguator:disambiguate_schema)

  let parse_only_comp_kind =
    eval
      (parse_and_disambiguate ~parser:(only comp_kind)
         ~disambiguator:disambiguate_comp_kind)

  let parse_only_comp_typ =
    eval
      (parse_and_disambiguate ~parser:(only comp_typ)
         ~disambiguator:disambiguate_comp_typ)

  let parse_only_comp_expression =
    eval
      (parse_and_disambiguate ~parser:(only comp_expression)
         ~disambiguator:disambiguate_comp_expression)
end

module Located_token = struct
  type t = Location.t * Token.t

  type location = Location.t

  let location = Pair.fst
end

module Simple_parser_state = Parser_combinator.Make_state (Located_token)
module Simple_disambiguation_state =
  Common_disambiguation.Disambiguation_state
module Simple = Make (Simple_parser_state) (Simple_disambiguation_state)
