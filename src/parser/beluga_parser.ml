open Beluga_syntax

(** {1 Parsing} *)

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
module Simple_disambiguation_state =
  Common_disambiguation.Disambiguation_state

module Make
    (Disambiguation_state : Common_disambiguation.DISAMBIGUATION_STATE) =
struct
  module Lf_parser = Lf_parser.Make (Common_parser.Simple_common_parser)
  module Clf_parser = Clf_parser.Make (Common_parser.Simple_common_parser)
  module Meta_parser =
    Meta_parser.Make (Common_parser.Simple_common_parser) (Clf_parser)
  module Comp_parser =
    Comp_parser.Make (Common_parser.Simple_common_parser) (Meta_parser)
  module Harpoon_parser =
    Harpoon_parser.Make (Common_parser.Simple_common_parser) (Meta_parser)
      (Comp_parser)
  module Signature_parser =
    Signature_parser.Make (Common_parser.Simple_common_parser) (Lf_parser)
      (Meta_parser)
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

  module Harpoon_disambiguation :
    Harpoon_disambiguation.HARPOON_DISAMBIGUATION
      with type state = Disambiguation_state.state =
    Harpoon_disambiguation.Make (Disambiguation_state) (Meta_disambiguator)
      (Comp_disambiguator)

  module Signature_disambiguation :
    Signature_disambiguation.SIGNATURE_DISAMBIGUATION
      with type state = Disambiguation_state.state =
    Signature_disambiguation.Make (Disambiguation_state) (Lf_disambiguator)
      (Meta_disambiguator)
      (Comp_disambiguator)
      (Harpoon_disambiguation)

  type disambiguation_state = Disambiguation_state.state

  type parser_state = Common_parser.Simple_common_parser.state

  module State = struct
    type t =
      { parser_state : parser_state
      ; disambiguation_state : disambiguation_state
      }

    let[@inline] make ~disambiguation_state ~parser_state =
      { parser_state; disambiguation_state }

    let[@inline] set_parser_state parser_state state =
      { state with parser_state }

    let[@inline] set_disambiguation_state disambiguation_state state =
      { state with disambiguation_state }

    let parser_state state = state.parser_state

    let disambiguation_state state = state.disambiguation_state
  end

  type 'a t = State.t -> State.t * ('a, exn) Result.t

  let make_initial_parser_state_from_file ~filename =
    let initial_location = Location.initial filename in
    let token_sequence = Lexer.lex_file ~filename in
    Common_parser.Simple_common_parser.initial_state ~initial_location
      token_sequence

  let make_initial_parser_state_from_channel ~initial_location input =
    let token_sequence = Lexer.lex_input_channel ~initial_location input in
    Common_parser.Simple_common_parser.initial_state ~initial_location
      token_sequence

  let make_initial_parser_state_from_string ~initial_location input =
    let token_sequence = Lexer.lex_string ~initial_location input in
    Common_parser.Simple_common_parser.initial_state ~initial_location
      token_sequence

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

  let parse : State.t -> (parser_state -> parser_state * 'a) -> State.t * 'a
      =
   fun state parse ->
    let parser_state = State.parser_state state in
    let parser_state', parsed = parse parser_state in
    let state' = State.set_parser_state parser_state' state in
    (state', parsed)

  let disambiguate :
         State.t
      -> (disambiguation_state -> disambiguation_state * 'a)
      -> State.t * 'a =
   fun state disambiguate ->
    let disambiguation_state = State.disambiguation_state state in
    let disambiguation_state', disambiguated =
      disambiguate disambiguation_state
    in
    let state' =
      State.set_disambiguation_state disambiguation_state' state
    in
    (state', disambiguated)

  let disambiguate' : State.t -> (disambiguation_state -> 'a) -> State.t * 'a
      =
   fun state disambiguate ->
    let disambiguation_state = State.disambiguation_state state in
    let disambiguated = disambiguate disambiguation_state in
    (state, disambiguated)

  let parse_only parser disambiguator state =
    let only_parser = Common_parser.Simple_common_parser.only parser in
    let state', parsed =
      parse state (Common_parser.Simple_common_parser.run_exn only_parser)
    in
    let _state'', (_disambiguation_state', disambiguated) =
      disambiguate' state' (disambiguator parsed)
    in
    disambiguated

  let parse_only_lf_kind =
    parse_only Lf_parser.lf_kind Lf_disambiguator.disambiguate_lf_kind

  let parse_only_lf_typ =
    parse_only Lf_parser.lf_typ Lf_disambiguator.disambiguate_lf_typ

  let parse_only_lf_term =
    parse_only Lf_parser.lf_term Lf_disambiguator.disambiguate_lf_term

  let parse_only_clf_typ =
    parse_only Clf_parser.clf_typ Clf_disambiguator.disambiguate_clf_typ

  let parse_only_clf_term =
    parse_only Clf_parser.clf_term Clf_disambiguator.disambiguate_clf_term

  let parse_only_clf_substitution =
    parse_only Clf_parser.clf_substitution
      Clf_disambiguator.disambiguate_clf_substitution

  let parse_only_meta_typ =
    parse_only Meta_parser.meta_type Meta_disambiguator.disambiguate_meta_typ

  let parse_only_meta_object =
    parse_only Meta_parser.meta_object
      Meta_disambiguator.disambiguate_meta_object

  let parse_only_schema =
    parse_only Meta_parser.schema Meta_disambiguator.disambiguate_schema

  let parse_only_comp_kind =
    parse_only Comp_parser.comp_kind
      Comp_disambiguator.disambiguate_comp_kind

  let parse_only_comp_typ =
    parse_only Comp_parser.comp_typ Comp_disambiguator.disambiguate_comp_typ

  let parse_only_comp_expression =
    parse_only Comp_parser.comp_expression
      Comp_disambiguator.disambiguate_comp_expression
end

module Simple = Make (Simple_disambiguation_state)
