open Support
open Beluga_syntax

exception Unlexable_character of string

exception Mismatched_block_comment

exception String_literal_unescape_failure of string

(** [get_location lexbuf] is the location of the currently lexed token in
    [lexbuf]. *)
let get_location lexbuf =
  let start_position, stop_position = Sedlexing.lexing_positions lexbuf in
  let filename = start_position.Lexing.pos_fname in
  Location.make_from_lexing_positions ~filename ~start_position
    ~stop_position

let set_location location lexbuf =
  let filename = Location.filename location
  and position = Location.start_to_lexing_position location in
  Sedlexing.set_filename lexbuf filename;
  Sedlexing.set_position lexbuf position

let ascii_control_character = [%sedlex.regexp? '\000' .. '\031' | '\127']

let digit = [%sedlex.regexp? '0' .. '9']

let reserved_character =
  [%sedlex.regexp?
    ( '.' | ',' | ':' | ';' | '%' | '|' | '"' | '\\' | '(' | ')' | '[' | ']'
    | '{' | '}' | '<' | '>' )]

let ident_continue =
  [%sedlex.regexp?
    Sub (any, (ascii_control_character | white_space | reserved_character))]

let ident_start = [%sedlex.regexp? Sub (ident_continue, digit)]

let ident = [%sedlex.regexp? ident_start, Star ident_continue]

let number = [%sedlex.regexp? Plus digit]

let hole = [%sedlex.regexp? '?', Opt ident]

let pragma = [%sedlex.regexp? "--", Plus alphabetic]

let hash_ident = [%sedlex.regexp? '#', ident]

let hash_blank = [%sedlex.regexp? "#_"]

let dollar_ident = [%sedlex.regexp? '$', ident]

let dollar_blank = [%sedlex.regexp? "$_"]

let dot_number = [%sedlex.regexp? '.', number]

let dot_ident = [%sedlex.regexp? '.', ident]

let backarrow = [%sedlex.regexp? "<-" | 0x2190]

let arrow = [%sedlex.regexp? "->" | 0x2192]

let turnstile = [%sedlex.regexp? "|-" | 0x22a2]

let turnstile_hash = [%sedlex.regexp? turnstile, '#']

let thick_arrow = [%sedlex.regexp? "=>" | 0x21d2]

let dots = [%sedlex.regexp? ".." | 0x2026]

let doc_comment_begin = [%sedlex.regexp? "%{{"]

let doc_comment_end = [%sedlex.regexp? "}}%"]

(** Basically, anything that doesn't terminate the block comment. This is
    somewhat tricky to detect. *)
let doc_comment_char =
  [%sedlex.regexp? Compl '}' | '}', Compl '}' | "}}", Compl '%']

let doc_comment =
  [%sedlex.regexp? doc_comment_begin, Star doc_comment_char, doc_comment_end]

let line_comment =
  [%sedlex.regexp?
    '%', Opt (Intersect (Compl '\n', Compl '{'), Star (Compl '\n'))]

let block_comment_begin = [%sedlex.regexp? "%{"]

let block_comment_end = [%sedlex.regexp? "}%"]

let block_comment_char = [%sedlex.regexp? Compl '%' | Compl '}']

let string_literal =
  [%sedlex.regexp? '"', Star ('\\', any | Sub (any, ('"' | '\\'))), '"']

(** Skips the _body_ of a block comment. Calls itself recursively upon
    encountering a nested block comment. Consumes the block_comment_end
    symbol. *)
let rec skip_nested_block_comment lexbuf =
  match%sedlex lexbuf with
  | block_comment_begin ->
      skip_nested_block_comment lexbuf;
      (* for the body of the new comment *)
      skip_nested_block_comment
        lexbuf (* for the remaining characters in this comment *)
  | block_comment_end -> ()
  | any -> skip_nested_block_comment lexbuf
  | _ -> assert false

let rec tokenize lexbuf =
  let[@inline] const t = Option.some (get_location lexbuf, t) in
  match%sedlex lexbuf with
  (* comments *)
  | eof -> Option.none
  | white_space -> tokenize lexbuf
  | block_comment_begin ->
      skip_nested_block_comment lexbuf;
      tokenize lexbuf
  | block_comment_end ->
      Error.raise_at1 (get_location lexbuf) Mismatched_block_comment
  | line_comment -> tokenize lexbuf
  (* STRING LITERALS *)
  | string_literal ->
      let s =
        Sedlexing.Utf8.sub_lexeme lexbuf 1
          (Sedlexing.lexeme_length lexbuf - 2)
      in
      let s' =
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
      let s =
        Sedlexing.Utf8.sub_lexeme lexbuf 2
          (Sedlexing.lexeme_length lexbuf - 2)
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
      let s =
        Sedlexing.Utf8.sub_lexeme lexbuf 1
          (Sedlexing.lexeme_length lexbuf - 1)
      in
      const (Token.HOLE s)
  | "_" -> const Token.UNDERSCORE
  | dot_number ->
      let s =
        Sedlexing.Utf8.sub_lexeme lexbuf 1
          (Sedlexing.lexeme_length lexbuf - 1)
      in
      const (Token.DOT_NUMBER (int_of_string s))
  | dot_ident ->
      let s =
        Sedlexing.Utf8.sub_lexeme lexbuf 1
          (Sedlexing.lexeme_length lexbuf - 1)
      in
      const (Token.DOT_IDENT s)
  | dots -> const Token.DOTS
  | turnstile_hash -> const Token.TURNSTILE_HASH
  | hash_blank -> const Token.HASH_BLANK
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

let lex_file ~filename =
  let initial_location = Location.initial filename in
  Gen.IO.with_in filename (lex_gen ~initial_location)

let lex_input_channel ~initial_location input =
  lex_gen ~initial_location (Gen.of_in_channel input)

let pp_exception ppf = function
  | Unlexable_character s ->
      Format.fprintf ppf "Unlexable character(s) \"%s\"." s
  | Mismatched_block_comment ->
      Format.fprintf ppf "Unexpected end of block comment."
  | String_literal_unescape_failure s ->
      Format.fprintf ppf
        "The string literal \"%s\" contains invalid escape sequences." s
  | _ ->
      Error.raise (Invalid_argument "[pp_exception] unsupported exception")

let () =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify pp_exception exn) with
      | Invalid_argument _ -> Option.none)
