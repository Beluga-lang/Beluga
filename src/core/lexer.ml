open Support

module Loc = Location

type error =
  | UnlexableCharacter of string
  | MismatchedBlockComment
  | Violation of string

exception Error of Loc.t * error

let throw loc e = raise (Error (loc, e))

let _ =
  Error.register_printer'
    (function
     | Error (loc, e) ->
        let open Format in
        Error.print_with_location loc
          (fun ppf ->
            fprintf ppf "lexical error: ";
            match e with
            | UnlexableCharacter c -> fprintf ppf "unrecognizable character(s) %s" c
            | MismatchedBlockComment -> fprintf ppf "unexpected end of block comment"
            | Violation msg -> fprintf ppf "(internal error) %s" msg)
        |> Option.some
     | _ -> None)

let (dprintf, _, _) = Debug.makeFunctions' (Debug.toFlags [11])
(* open Debug.Fmt *)

(** [get_location lexbuf] is the current location of [lexbuf]. *)
let get_location lexbuf =
  let (start_position, stop_position) = Sedlexing.lexing_positions lexbuf in
  let filename = start_position.Lexing.pos_fname in
  Location.make filename ~start_position ~stop_position

let get_lexeme = Sedlexing.Utf8.lexeme

let set_location location lexbuf =
  let filename = Location.filename location in
  Sedlexing.set_filename lexbuf filename;
  (Sedlexing.set_position lexbuf
  @@ Lexing.
       { pos_fname = filename
       ; pos_lnum = Location.start_line location
       ; pos_bol = Location.start_bol location
       ; pos_cnum = Location.start_offset location
       })

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
let digit =        [%sedlex.regexp? '0'..'9']
let number =       [%sedlex.regexp? Plus digit]
let hole =         [%sedlex.regexp? '?', Opt ident]
let pragma =       [%sedlex.regexp? "--", Plus alphabetic]
let hash_ident =   [%sedlex.regexp? '#', ident]
let hash_blank =   [%sedlex.regexp? "#_"]
let dollar_ident = [%sedlex.regexp? '$', ident]
let dollar_blank = [%sedlex.regexp? "$_"]
let dot_number =   [%sedlex.regexp? '.', number]
let dot_ident =   [%sedlex.regexp? '.', ident]
let backarrow =    [%sedlex.regexp? ("<-" | 0x2190)]
let arrow =        [%sedlex.regexp? ("->" | 0x2192)]
let turnstile =    [%sedlex.regexp? ("|-" | 0x22a2)]
let turnstile_hash =    [%sedlex.regexp? turnstile, '#']
let thick_arrow =  [%sedlex.regexp? ("=>" | 0x21d2)]
let dots =         [%sedlex.regexp? (".." | 0x2026)]

let doc_comment_begin = [%sedlex.regexp? "%{{"]
let doc_comment_end =   [%sedlex.regexp? "}}%"]

(** Basically, anything that doesn't terminate the block comment.
    This is somewhat tricky to detect.
 *)
let doc_comment_char = [%sedlex.regexp? Compl '}' | ('}', Compl '}') | ("}}", Compl '%') ]
let doc_comment = [%sedlex.regexp? doc_comment_begin, Star doc_comment_char, doc_comment_end]

let line_comment =
  [%sedlex.regexp?
      '%', Opt(Intersect(Compl '\n', Compl '{'), Star (Compl '\n'))
  ]
let block_comment_begin = [%sedlex.regexp? "%{"]
let block_comment_end = [%sedlex.regexp? "}%"]
let block_comment_char = [%sedlex.regexp? Compl '%' | Compl '}' ]

let string_delimiter = [%sedlex.regexp? '"']

(* XXX This is stupid and doesn't allow any escape characters. *)
let string_literal = [%sedlex.regexp? string_delimiter, Star (Compl '"'), string_delimiter]

(** Skips the _body_ of a block comment.
    Calls itself recursively upon encountering a nested block comment.
    Consumes the block_comment_end symbol. *)
let rec skip_nested_block_comment lexbuf =
  (* let const t = Fun.const t (get_lexeme loc lexbuf) in *)
  match%sedlex lexbuf with
  | block_comment_begin ->
     skip_nested_block_comment lexbuf; (* for the body of the new comment *)
     skip_nested_block_comment lexbuf (* for the remaining characters in this comment *)
  | block_comment_end -> ()
  | any ->
     ignore @@ get_lexeme lexbuf;
     skip_nested_block_comment lexbuf
  | _ ->
     throw (get_location lexbuf) (Violation "catch-all case for skip_nested_block_comment should be unreachable")


let rec tokenize lexbuf =
  let const t = Fun.const t (get_lexeme lexbuf) in
  match%sedlex lexbuf with
  (* comments *)
  | eof -> const Token.EOI
  | white_space ->
     ignore @@ get_lexeme lexbuf;
     tokenize lexbuf
  | block_comment_begin ->
     skip_nested_block_comment lexbuf;
     tokenize lexbuf
  | block_comment_end -> throw (get_location lexbuf) MismatchedBlockComment
  | line_comment -> tokenize lexbuf

  (* STRING LITERALS *)
  | string_literal ->
     let s = get_lexeme lexbuf in
     Token.STRING (String.sub s 1 (String.length s - 2))

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
  | "mlam"  -> const Token.KW_MLAM
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
  | pragma -> Token.PRAGMA (String.drop 2 (get_lexeme lexbuf))
  | backarrow -> const Token.BACKARROW
  | arrow -> const Token.ARROW
  | thick_arrow -> const Token.THICK_ARROW
  | turnstile -> const Token.TURNSTILE
  | "[" -> const Token.LBRACK
  | "]" -> const Token.RBRACK
  | "{" -> const Token.LBRACE
  | "}" -> const Token.RBRACE
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

  | hole -> Token.HOLE (String.drop 1 (get_lexeme lexbuf))
  | "_" -> const Token.UNDERSCORE

  | dot_number -> Token.DOT_NUMBER (int_of_string (String.drop 1 (get_lexeme lexbuf)))
  | dot_ident -> Token.DOT_IDENT (String.drop 1 (get_lexeme lexbuf))
  | dots -> const Token.DOTS
  | turnstile_hash -> Token.TURNSTILE_HASH
  | hash_blank -> Token.HASH_BLANK
  | hash_ident -> Token.HASH_IDENT (get_lexeme lexbuf)
  | dollar_blank -> Token.DOLLAR_BLANK
  | dollar_ident -> Token.DOLLAR_IDENT (get_lexeme lexbuf)
  | "." -> const Token.DOT
  | "#" -> const Token.HASH
  | "$" -> const Token.DOLLAR

  | eof -> const Token.EOI

  | ident -> Token.IDENT (get_lexeme lexbuf)
  | number -> Token.INTLIT (get_lexeme lexbuf |> int_of_string)
  | _ -> throw (get_location lexbuf) (UnlexableCharacter (get_lexeme lexbuf))

(** From a given generator for UTF-8, constructs a generator for tokens.
    Raises `Error` if a lexical error is encountered.
 *)
let mk initial_loc gen =
  let lexbuf = Sedlexing.Utf8.from_gen gen in
  set_location initial_loc lexbuf;
  let next () =
    let t = tokenize lexbuf in
    Some (get_location lexbuf, t)
  in
  next
