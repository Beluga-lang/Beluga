open Support
open Beluga_syntax

(** {1 Configuration Files} *)

module Config_parser = Config_parser

(** {1 Parsing} *)

module type PARSER_STATE = Common_parser.PARSER_STATE

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

module type DISAMBIGUATION_STATE = Common_disambiguation.DISAMBIGUATION_STATE

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
                      with type token = Location.t * Token.t
                       and type location = Location.t)
    (Disambiguation_state : DISAMBIGUATION_STATE) =
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

  type state =
    { parser_state : parser_state
    ; disambiguation_state : disambiguation_state
    }

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let[@inline] make_state ~disambiguation_state ~parser_state =
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
    let parser_state', parsed = Parser_state.run parser parser_state in
    let* () = put_parser_state parser_state' in
    return parsed

  let disambiguate disambiguator =
    let* disambiguation_state = get_disambiguation_state in
    let disambiguation_state', disambiguated =
      Disambiguation_state.run disambiguator disambiguation_state
    in
    let* () = put_disambiguation_state disambiguation_state' in
    return disambiguated

  let parse_and_disambiguate ~parser ~disambiguator =
    let* parsed = parse (run_exn parser) in
    let* disambiguated = disambiguate (disambiguator parsed) in
    return disambiguated

  let parse_only_lf_kind =
    parse_and_disambiguate ~parser:(only lf_kind)
      ~disambiguator:disambiguate_lf_kind

  let parse_only_lf_typ =
    parse_and_disambiguate ~parser:(only lf_typ)
      ~disambiguator:disambiguate_lf_typ

  let parse_only_lf_term =
    parse_and_disambiguate ~parser:(only lf_term)
      ~disambiguator:disambiguate_lf_term

  let parse_only_clf_typ =
    parse_and_disambiguate ~parser:(only clf_typ)
      ~disambiguator:disambiguate_clf_typ

  let parse_only_clf_term =
    parse_and_disambiguate ~parser:(only clf_term)
      ~disambiguator:disambiguate_clf_term

  let parse_only_clf_substitution =
    parse_and_disambiguate ~parser:(only clf_substitution)
      ~disambiguator:disambiguate_clf_substitution

  let parse_only_meta_typ =
    parse_and_disambiguate ~parser:(only meta_type)
      ~disambiguator:disambiguate_meta_typ

  let parse_only_meta_object =
    parse_and_disambiguate ~parser:(only meta_object)
      ~disambiguator:disambiguate_meta_object

  let parse_only_schema =
    parse_and_disambiguate ~parser:(only schema)
      ~disambiguator:disambiguate_schema

  let parse_only_comp_kind =
    parse_and_disambiguate ~parser:(only comp_kind)
      ~disambiguator:disambiguate_comp_kind

  let parse_only_comp_typ =
    parse_and_disambiguate ~parser:(only comp_typ)
      ~disambiguator:disambiguate_comp_typ

  let parse_only_comp_expression =
    parse_and_disambiguate ~parser:(only comp_expression)
      ~disambiguator:disambiguate_comp_expression

  let parse_only_signature =
    parse_and_disambiguate ~parser:(only signature)
      ~disambiguator:disambiguate_signature
end

module Located_token = struct
  type t = Location.t * Token.t

  type location = Location.t

  let location = Pair.fst
end

module Simple = struct
  module Parser_state =
    Parser_combinator.Make_persistent_state (Located_token)

  module Disambiguation_state =
    Common_disambiguation.Persistent_disambiguation_state

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

  let read_signature filename =
    In_channel.with_open_bin filename (fun in_channel ->
        let initial_location = Location.initial filename in
        let _parser_state', signature =
          run_exn (only signature)
            (make_initial_parser_state_from_channel ~initial_location
               in_channel)
        in
        signature)

  let read_signature_entries filename =
    In_channel.with_open_bin filename (fun in_channel ->
        let initial_location = Location.initial filename in
        let _parser_state', entries =
          run_exn
            (only (many signature_entry))
            (make_initial_parser_state_from_channel ~initial_location
               in_channel)
        in
        entries)

  let parse_multi_file_signature files =
    let (List1.T (x, xs)) = files in
    let signature =
      (* For OCaml >= 5, spawn a parallel domain for each call to
         {!read_signature} and {!read_signature_entries}, then join those
         domains before [List.flatten (x_entries :: xs_entries)] *)
      let signature = read_signature x in
      let xs_entries = List.map read_signature_entries xs in
      let { Synprs.Signature.global_pragmas; entries = x_entries } =
        signature
      in
      let entries = List.flatten (x_entries :: xs_entries) in
      let signature' = { Synprs.Signature.global_pragmas; entries } in
      signature'
    in
    let _disambiguation_state', signature' =
      disambiguate_signature signature Disambiguation_state.initial
    in
    signature'
end
