(** Parsing and disambiguation of Beluga signatures.

    Make sure to familiarize yourself with the
    [beluga-language-specification.tex] file which exhaustively details the
    functional requirements of this parser.

    Parsing of Beluga signatures is implemented in three phases:

    + Lexing/tokenization (see {!module:Token} and {!module:Lexer})
    + Context-free parsing (see {!module:Parser_combinator} and modules with
      the suffix [_parser])
    + Context-sensitive disambiguation (see {!module:Disambiguation_state}
      and modules with the suffix [_disambiguation])

    The lexing phase converts UTF-8 encoded input files to tokens using the
    [sedlex] library (see the [dune] file for the pre-processing
    configuration of the {!module:Lexer} module). Tokenization works like in
    other programming language implementations, except for a special handling
    of the dot [.] operator with the [Token.DOT], [Token.DOT_IDENT s] and
    [Token.DOT_INTLIT i] token kinds. See the {!module:Common_parser} module
    for a note on how those tokens are handled.

    The context-free parsing phase is a recursive descent parser implemented
    with parser combinators and selective unlimited backtracking. This phase
    handles parsing of static operators, and constructs a parse tree with
    ambiguous nodes. These ambiguous nodes are qualified and dotted qualified
    identifiers (which may represent projections instead of references to
    constants in namespaces), applications (the juxtaposition of terms and
    user-defined operators), contextual LF substitutions and contexts, and
    old-style LF declarations (LF type-level and term-level declarations).

    The context-sensitive disambiguation phase is a stateful translation from
    the parser syntax to the external syntax. The disambiguation state
    constructs the lexical referencing environment during the traversal so
    that identifiers and qualified identifiers may be resolved to their
    binding sites to determine what kind of AST node to produce. Overloading
    of identifiers is not supported. The disambiguation state is mutable to
    ensure good performance.

    @author Marc-Atoine Ouimet *)

open Support
open Beluga_syntax

(** {1 Configuration Files} *)

module Config_parser = Config_parser

(** {1 Lexing} *)

module Lexer = Lexer

(** {1 Parsing} *)

module type PARSER_STATE = Parser_combinator.PARSER_STATE

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

(** Abstract definition of parsing for Beluga.

    This is a union of the parser module types for Beluga. *)
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

(** Functor creating a Beluga parser using the given implementation of state. *)
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

(** Abstract definition of disambiguation for Beluga.

    This is a union of the disambiguation module types for Beluga. *)
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

(** Functor creating a Beluga disambiguator using the given implementation of
    state. *)
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
