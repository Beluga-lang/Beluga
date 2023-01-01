open Support
open Beluga_syntax
module Simple_disambiguation_state =
  Common_disambiguation.Disambiguation_state

module Make
    (Disambiguation_state : Common_disambiguation.DISAMBIGUATION_STATE) =
struct
  module Lf_disambiguation = Lf_disambiguation.Make (Disambiguation_state)
  module Clf_disambiguation = Clf_disambiguation.Make (Disambiguation_state)
  module Meta_disambiguation =
    Meta_disambiguation.Make (Disambiguation_state) (Clf_disambiguation)
  module Comp_disambiguation =
    Comp_disambiguation.Make (Disambiguation_state) (Meta_disambiguation)
  module Harpoon_disambiguation =
    Harpoon_disambiguation.Make (Disambiguation_state) (Meta_disambiguation)
      (Comp_disambiguation)
  module Signature_disambiguation =
    Signature_disambiguation.Make (Disambiguation_state) (Lf_disambiguation)
      (Meta_disambiguation)
      (Comp_disambiguation)
      (Harpoon_disambiguation)

  type disambiguation_state = Disambiguation_state.t

  type parser_state = Common_parser.state

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
    Common_parser.initial_state ~last_location:initial_location
      token_sequence

  let make_initial_parser_state_from_channel ~initial_location input =
    let token_sequence = Lexer.lex_input_channel ~initial_location input in
    Common_parser.initial_state ~last_location:initial_location
      token_sequence

  let make_initial_parser_state_from_string ~initial_location input =
    let token_sequence = Lexer.lex_string ~initial_location input in
    Common_parser.initial_state ~last_location:initial_location
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
    let only_parser = Common_parser.only parser in
    let state', parsed = parse state (Common_parser.run_exn only_parser) in
    let _state'', (_disambiguation_state', disambiguated) =
      disambiguate' state' (disambiguator parsed)
    in
    disambiguated

  let parse_only_lf_kind =
    parse_only Lf_parser.lf_object Lf_disambiguation.disambiguate_as_kind

  let parse_only_lf_typ =
    parse_only Lf_parser.lf_object Lf_disambiguation.disambiguate_as_typ

  let parse_only_lf_term =
    parse_only Lf_parser.lf_object Lf_disambiguation.disambiguate_as_term

  let parse_only_clf_typ =
    parse_only Clf_parser.clf_object Clf_disambiguation.disambiguate_as_typ

  let parse_only_clf_term =
    parse_only Clf_parser.clf_object Clf_disambiguation.disambiguate_as_term

  let parse_only_clf_term_pattern =
    parse_only Clf_parser.clf_object
      Clf_disambiguation.disambiguate_as_term_pattern

  let parse_only_clf_substitution =
    parse_only Clf_parser.clf_context_object
      Clf_disambiguation.disambiguate_as_substitution

  let parse_only_clf_substitution_pattern =
    parse_only Clf_parser.clf_context_object
      Clf_disambiguation.disambiguate_as_substitution_pattern

  let parse_only_clf_context =
    parse_only Clf_parser.clf_context_object
      Clf_disambiguation.disambiguate_as_context

  let parse_only_clf_context_pattern =
    parse_only Clf_parser.clf_context_object
      Clf_disambiguation.disambiguate_as_context_pattern

  let parse_only_meta_typ =
    parse_only Meta_parser.meta_thing
      Meta_disambiguation.disambiguate_as_meta_typ

  let parse_only_meta_object =
    parse_only Meta_parser.meta_thing
      Meta_disambiguation.disambiguate_as_meta_object

  let parse_only_meta_pattern =
    parse_only Meta_parser.meta_thing
      Meta_disambiguation.disambiguate_as_meta_pattern

  let parse_only_meta_context =
    parse_only Meta_parser.meta_context
      Meta_disambiguation.disambiguate_as_meta_context

  let parse_only_schema =
    parse_only Meta_parser.schema_object
      Meta_disambiguation.disambiguate_as_schema
end

module Simple = Make (Simple_disambiguation_state)
