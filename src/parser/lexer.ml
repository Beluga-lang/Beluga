open Support
open Beluga_syntax

exception Unlexable_character of string

exception Mismatched_block_comment

exception Unterminated_block_comment

exception Mismatched_documentation_comment

exception Unterminated_documentation_comment

exception String_literal_unescape_failure of string

(** [get_location lexbuf] is the location of the currently lexed token in
    [lexbuf]. *)
let get_location lexbuf =
  let start_position, stop_position = Sedlexing.lexing_positions lexbuf in
  let filename = start_position.Lexing.pos_fname in
  Location.make_from_lexing_positions ~filename ~start_position
    ~stop_position

(** [set_location location lexbuf] sets the initial location of [lexbuf] to
    [location]. This enables the tracking of locations in the lexer. *)
let set_location location lexbuf =
  let filename = Location.filename location
  and position = Location.start_to_lexing_position location in
  Sedlexing.set_filename lexbuf filename;
  Sedlexing.set_position lexbuf position

let shift_position position n =
  Stdlib.Lexing.{ position with pos_cnum = position.pos_cnum + n }

let ascii_control_character = [%sedlex.regexp? '\000' .. '\031' | '\127']

let digit = [%sedlex.regexp? '0' .. '9']

let reserved_character =
  [%sedlex.regexp?
    ( '.' | ',' | ':' | ';' | '%' | '|' | '"' | '\\' | '(' | ')' | '[' | ']'
    | '{' | '}' | '<' | '>' | 0x22a2 )]

let ident_continue =
  [%sedlex.regexp?
    Sub (any, (ascii_control_character | white_space | reserved_character))]

let ident_start = [%sedlex.regexp? Sub (ident_continue, digit)]

let ident = [%sedlex.regexp? ident_start, Star ident_continue]

let number = [%sedlex.regexp? Plus digit]

let hole = [%sedlex.regexp? '?', Opt ident]

let pragma = [%sedlex.regexp? "--", Plus alphabetic]

let dot_ident = [%sedlex.regexp? '.', ident]

let dot_intlit = [%sedlex.regexp? '.', number]

let hash_ident = [%sedlex.regexp? '#', ident]

let hash_blank = [%sedlex.regexp? "#_"]

let dollar_ident = [%sedlex.regexp? '$', ident]

let dollar_blank = [%sedlex.regexp? "$_"]

let backarrow = [%sedlex.regexp? "<-" | 0x2190]

let arrow = [%sedlex.regexp? "->" | 0x2192]

let turnstile = [%sedlex.regexp? "|-" | 0x22a2]

let turnstile_hash = [%sedlex.regexp? turnstile, '#']

let thick_arrow = [%sedlex.regexp? "=>" | 0x21d2]

let thick_backarrow = [%sedlex.regexp? "<=" | 0x21d0]

let dots = [%sedlex.regexp? ".." | 0x2026]

let string_literal =
  [%sedlex.regexp? '"', Star ('\\', any | Sub (any, ('"' | '\\'))), '"']

let add_utf8_lexeme_to_buffer comment_buffer lexbuf =
  Buffer.add_string comment_buffer (Sedlexing.Utf8.lexeme lexbuf)

(** [tokenize_line_comment lexbuf] tokenizes a line comment starting with
    ['%'] and ending in a newline or the end of input by ignoring the
    lexemes. *)
let rec tokenize_line_comment lexbuf =
  match%sedlex lexbuf with
  | '%' -> tokenize_line_comment lexbuf
  | Compl '\n' -> tokenize_line_comment lexbuf
  | _ -> ()

(** [tokenize_block_comment start_delimiter_locations lexbuf] tokenizes a
    block comment delimited by ["%{"] and ["}%"] from [lexbuf]. Nested block
    comments are supported. [start_delimiter_locations] is a stack of
    locations used both for keeping track of the level of nested block
    comments and for error-reporting. That is,
    [List1.length start_delimiter_locations] is the current level of the
    block comment being tokenized. *)
let rec tokenize_block_comment start_delimiter_locations lexbuf =
  match%sedlex lexbuf with
  | "%{" ->
      tokenize_block_comment
        (List1.cons (get_location lexbuf) start_delimiter_locations)
        lexbuf
  | "}%" -> (
      match start_delimiter_locations with
      | List1.T (_location, []) -> ()
      | List1.T (_location, l :: ls) ->
          tokenize_block_comment (List1.from l ls) lexbuf)
  | any -> tokenize_block_comment start_delimiter_locations lexbuf
  | eof ->
      Error.raise_at1
        (List1.head start_delimiter_locations)
        Unterminated_block_comment
  | _ ->
      let s = Sedlexing.Utf8.lexeme lexbuf in
      Error.raise_at1 (get_location lexbuf) (Unlexable_character s)

(** [tokenize_documentation_comment start_delimiter_locations comment_buffer lexbuf]
    tokenizes a documentation comment delimited by ["%{{"] and ["}}%"] from
    [lexbuf] by adding lexemes to [comment_buffer]. Nested block comments are
    supported. [start_delimiter_locations] is a stack of locations used both
    for keeping track of the level of nested documentation comments and for
    error-reporting. That is, [List1.length start_delimiter_locations] is the
    current level of the documentation comment being tokenized.

    This function is called when the first ["%{{"] has already been
    tokenized, and consequently, the last ["}}%"] is not added to
    [comment_buffer]. *)
let rec tokenize_documentation_comment start_delimiter_locations
    comment_buffer lexbuf =
  match%sedlex lexbuf with
  | "%{{" ->
      add_utf8_lexeme_to_buffer comment_buffer lexbuf;
      tokenize_documentation_comment
        (List1.cons (get_location lexbuf) start_delimiter_locations)
        comment_buffer lexbuf
  | "}}%" -> (
      match start_delimiter_locations with
      | List1.T (_location, []) -> ()
      | List1.T (_location, l :: ls) ->
          add_utf8_lexeme_to_buffer comment_buffer lexbuf;
          tokenize_documentation_comment (List1.from l ls) comment_buffer
            lexbuf)
  | any, Star (Sub (any, ('%' | '}')))
  (* Optimization to add more than one character to [comment_buffer] at a
     time *) ->
      add_utf8_lexeme_to_buffer comment_buffer lexbuf;
      tokenize_documentation_comment start_delimiter_locations comment_buffer
        lexbuf
  | eof ->
      Error.raise_at1
        (List1.head start_delimiter_locations)
        Unterminated_documentation_comment
  | _ ->
      let s = Sedlexing.Utf8.lexeme lexbuf in
      Error.raise_at1 (get_location lexbuf) (Unlexable_character s)

let rec tokenize lexbuf =
  let[@inline] const t = Option.some (get_location lexbuf, t) in
  match%sedlex lexbuf with
  (* comments *)
  | eof -> Option.none
  | white_space -> tokenize lexbuf
  | "%{{" ->
      let start_delimiter_location = get_location lexbuf in
      let documentation_comment_buffer = Buffer.create 32 in
      tokenize_documentation_comment
        (List1.singleton start_delimiter_location)
        documentation_comment_buffer lexbuf;
      let _start_position, stop_position =
        Sedlexing.lexing_positions lexbuf
      in
      let location =
        Location.set_stop
          (Position.make_from_lexing_position stop_position)
          start_delimiter_location
      in
      let contents = Buffer.contents documentation_comment_buffer in
      Option.some (location, Token.BLOCK_COMMENT (String.trim contents))
  | "}}%" ->
      Error.raise_at1 (get_location lexbuf) Mismatched_documentation_comment
  | "%{" ->
      let start_delimiter_location = get_location lexbuf in
      tokenize_block_comment
        (List1.singleton start_delimiter_location)
        lexbuf;
      tokenize lexbuf
  | "}%" -> Error.raise_at1 (get_location lexbuf) Mismatched_block_comment
  | '%' ->
      tokenize_line_comment lexbuf;
      tokenize lexbuf
  (* STRING LITERALS *)
  | string_literal ->
      let s =
        (* Discard ['"'] delimiters *)
        Sedlexing.Utf8.sub_lexeme lexbuf (String.length "\"")
          (Sedlexing.lexeme_length lexbuf
          - String.length "\"" - String.length "\"")
      in
      let s' =
        (* Handle escape sequences *)
        try Scanf.unescaped s with
        | Scanf.Scan_failure s ->
            Error.raise_at1 (get_location lexbuf)
              (String_literal_unescape_failure s)
      in
      const (Token.STRING s')
  (* KEYWORDS *)
  | "and" -> const Token.KW_AND
  | "block" -> const Token.KW_BLOCK
  | "case" -> const Token.KW_CASE
  | "fn" -> const Token.KW_FN
  | "else" -> const Token.KW_ELSE
  | "if" -> const Token.KW_IF
  | "impossible" -> const Token.KW_IMPOSSIBLE
  | "in" -> const Token.KW_IN
  | "let" -> const Token.KW_LET
  | "mlam" -> const Token.KW_MLAM
  | "of" -> const Token.KW_OF
  | "rec" -> const Token.KW_REC
  | "schema" -> const Token.KW_SCHEMA
  | "some" -> const Token.KW_SOME
  | "then" -> const Token.KW_THEN
  | "module" -> const Token.KW_MODULE
  | "struct" -> const Token.KW_STRUCT
  | "end" -> const Token.KW_END
  | "trust" -> const Token.KW_TRUST
  | "total" -> const Token.KW_TOTAL
  | "type" -> const Token.KW_TYPE
  | "ctype" -> const Token.KW_CTYPE
  | "prop" -> const Token.KW_PROP
  | "inductive" -> const Token.KW_INDUCTIVE
  | "coinductive" -> const Token.KW_COINDUCTIVE
  | "stratified" -> const Token.KW_STRATIFIED
  | "LF" -> const Token.KW_LF
  | "fun" -> const Token.KW_FUN
  | "typedef" -> const Token.KW_TYPEDEF
  | "proof" -> const Token.KW_PROOF
  | "by" -> const Token.KW_BY
  | "as" -> const Token.KW_AS
  | "suffices" -> const Token.KW_SUFFICES
  | "toshow" -> const Token.KW_TOSHOW
  (* SYMBOLS *)
  | pragma ->
      let prefix_length = String.length "--" in
      let s =
        Sedlexing.Utf8.sub_lexeme lexbuf prefix_length
          (Sedlexing.lexeme_length lexbuf - prefix_length)
      in
      const (Token.PRAGMA s)
  | backarrow -> const Token.BACKARROW
  | arrow -> const Token.ARROW
  | thick_arrow -> const Token.THICK_ARROW
  | turnstile -> const Token.TURNSTILE
  | "#[" -> const Token.HASH_LBRACK
  | "$[" -> const Token.DOLLAR_LBRACK
  | "[" -> const Token.LBRACK
  | "]" -> const Token.RBRACK
  | "{" -> const Token.LBRACE
  | "}" -> const Token.RBRACE
  | "#(" -> const Token.HASH_LPAREN
  | "$(" -> const Token.DOLLAR_LPAREN
  | "(" -> const Token.LPAREN
  | ")" -> const Token.RPAREN
  | "<" -> const Token.LANGLE
  | ">" -> const Token.RANGLE
  | "^" -> const Token.HAT
  | "," -> const Token.COMMA
  | "::" -> const Token.DOUBLE_COLON
  | ":" -> const Token.COLON
  | ";" -> const Token.SEMICOLON
  | "|" -> const Token.PIPE
  | "\\" -> const Token.LAMBDA
  | "*" -> const Token.STAR
  | "=" -> const Token.EQUALS
  | "/" -> const Token.SLASH
  | "+" -> const Token.PLUS
  | hole ->
      let prefix_length = String.length "?" in
      let s =
        Sedlexing.Utf8.sub_lexeme lexbuf prefix_length
          (Sedlexing.lexeme_length lexbuf - prefix_length)
      in
      const (Token.HOLE s)
  | "_" -> const Token.UNDERSCORE
  | dots -> const Token.DOTS
  | turnstile_hash -> const Token.TURNSTILE_HASH
  | hash_blank -> const Token.HASH_BLANK
  | dot_ident ->
      (* Adjust location to ignore the leading ['.'] *)
      let prefix_length = String.length "." in
      let s =
        Sedlexing.Utf8.sub_lexeme lexbuf prefix_length
          (Sedlexing.lexeme_length lexbuf - prefix_length)
      in
      let start_position, stop_position =
        Sedlexing.lexing_positions lexbuf
      in
      let filename = start_position.Lexing.pos_fname in
      let location =
        Location.make_from_lexing_positions ~filename
          ~start_position:(shift_position start_position 1)
          ~stop_position
      in
      Option.some (location, Token.DOT_IDENT s)
  | dot_intlit ->
      (* Adjust location to ignore the leading ['.'] *)
      let prefix_length = String.length "." in
      let s =
        Sedlexing.Utf8.sub_lexeme lexbuf prefix_length
          (Sedlexing.lexeme_length lexbuf - prefix_length)
      in
      let n = int_of_string s in
      let start_position, stop_position =
        Sedlexing.lexing_positions lexbuf
      in
      let filename = start_position.Lexing.pos_fname in
      let location =
        Location.make_from_lexing_positions ~filename
          ~start_position:(shift_position start_position 1)
          ~stop_position
      in
      Option.some (location, Token.DOT_INTLIT n)
  | hash_ident ->
      let s = Sedlexing.Utf8.lexeme lexbuf in
      const (Token.HASH_IDENT s)
  | dollar_blank -> const Token.DOLLAR_BLANK
  | dollar_ident ->
      let s = Sedlexing.Utf8.lexeme lexbuf in
      const (Token.DOLLAR_IDENT s)
  | "." -> const Token.DOT
  | "#" -> const Token.HASH
  | "$" -> const Token.DOLLAR
  | number ->
      let n = int_of_string (Sedlexing.Utf8.lexeme lexbuf) in
      const (Token.INTLIT n)
  | ident ->
      let s = Sedlexing.Utf8.lexeme lexbuf in
      const (Token.IDENT s)
  | _ ->
      let s = Sedlexing.Utf8.lexeme lexbuf in
      Error.raise_at1 (get_location lexbuf) (Unlexable_character s)

let make_token_sequence ~initial_location lexer_buffer =
  set_location initial_location lexer_buffer;
  Seq.memoize (Seq.of_gen (fun () -> tokenize lexer_buffer))

let lex_gen ~initial_location input =
  make_token_sequence ~initial_location (Sedlexing.Utf8.from_gen input)

let lex_string ~initial_location input =
  make_token_sequence ~initial_location (Sedlexing.Utf8.from_string input)

let lex_input_channel ~initial_location input =
  lex_gen ~initial_location (Gen.of_in_channel input)

let () =
  Error.register_exception_printer (function
    | Unlexable_character s ->
        Format.dprintf "Unlexable character(s) \"%s\"." s
    | Mismatched_block_comment ->
        Format.dprintf "Unexpected end of block comment."
    | Unterminated_block_comment ->
        (* Workaround format string errors when inputting the documentation
           comment delimiters *)
        let right_delimiter = "}%" in
        Format.dprintf
          "This block comment is missing its closing delimiter `%s'."
          right_delimiter
    | Mismatched_documentation_comment ->
        Format.dprintf "Unexpected end of documentation comment."
    | Unterminated_documentation_comment ->
        (* Workaround format string errors when inputting the documentation
           comment delimiters *)
        let right_delimiter = "}}%" in
        Format.dprintf
          "This documentation comment is missing its closing delimiter `%s'."
          right_delimiter
    | String_literal_unescape_failure s ->
        Format.dprintf
          "The string literal \"%s\" contains invalid escape sequences." s
    | exn -> Error.raise_unsupported_exception_printing exn)
