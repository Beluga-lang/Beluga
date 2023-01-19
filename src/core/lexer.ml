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
let number = [%sedlex.regexp? Plus digit]
let hole = [%sedlex.regexp? '?', Opt ident]
let pragma = [%sedlex.regexp? "--", Plus alphabetic]
let hash_ident = [%sedlex.regexp? '#', ident]
let hash_blank = [%sedlex.regexp? "#_"]
let dollar_ident = [%sedlex.regexp? '$', ident]
let dollar_blank = [%sedlex.regexp? "$_"]
let dot_number = [%sedlex.regexp? '.', number]
let arrow =       [%sedlex.regexp? ("->" | 0x2192)]
let turnstile =   [%sedlex.regexp? ("|-" | 0x22a2)]
let thick_arrow = [%sedlex.regexp? ("=>" | 0x21d2)]
let dots =        [%sedlex.regexp? (".." | 0x2026)]

let doc_comment_begin = [%sedlex.regexp? "%{{"]
let doc_comment_end = [%sedlex.regexp? "}}%"]

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
  let module T = Token in
  match%sedlex lexbuf with
  (* comments *)
  | eof -> const T.EOI
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
     T.STRING (String.sub s 1 (String.length s - 2))

  (* KEYWORDS *)
  | "and" -> const T.KW_AND
  | "block" -> const T.KW_BLOCK
  | "case" -> const T.KW_CASE
  | "fn" -> const T.KW_FN
  | "else" -> const T.KW_ELSE
  | "if" -> const T.KW_IF
  | "impossible" -> const T.KW_IMPOSSIBLE
  | "in" -> const T.KW_IN
  | "let" -> const T.KW_LET
  | "mlam"  -> const T.KW_MLAM
  | "of" -> const T.KW_OF
  | "rec" -> const T.KW_REC
  | "schema" -> const T.KW_SCHEMA
  | "some" -> const T.KW_SOME
  | "then" -> const T.KW_THEN
  | "module" -> const T.KW_MODULE
  | "struct" -> const T.KW_STRUCT
  | "end" -> const T.KW_END
  | "trust" -> const T.KW_TRUST
  | "total" -> const T.KW_TOTAL
  | "type" -> const T.KW_TYPE
  | "ctype" -> const T.KW_CTYPE
  | "prop" -> const T.KW_PROP
  | "inductive" -> const T.KW_INDUCTIVE
  | "coinductive" -> const T.KW_COINDUCTIVE
  | "stratified" -> const T.KW_STRATIFIED
  | "LF" -> const T.KW_LF
  | "fun" -> const T.KW_FUN
  | "typedef" -> const T.KW_TYPEDEF
  | "proof" -> const T.KW_PROOF
  | "by" -> const T.KW_BY
  | "as" -> const T.KW_AS
  | "suffices" -> const T.KW_SUFFICES
  | "toshow" -> const T.KW_TOSHOW

  (* SYMBOLS *)
  | pragma -> T.PRAGMA (String.drop 2 (get_lexeme lexbuf))
  | arrow -> const T.ARROW
  | thick_arrow -> const T.THICK_ARROW
  | turnstile -> const T.TURNSTILE
  | "[" -> const T.LBRACK
  | "]" -> const T.RBRACK
  | "{" -> const T.LBRACE
  | "}" -> const T.RBRACE
  | "(" -> const T.LPAREN
  | ")" -> const T.RPAREN
  | "<" -> const T.LANGLE
  | ">" -> const T.RANGLE
  | "^" -> const T.HAT
  | "," -> const T.COMMA
  | "::" -> const T.DOUBLE_COLON
  | ":" -> const T.COLON
  | ";" -> const T.SEMICOLON
  | "|" -> const T.PIPE
  | "\\" -> const T.LAMBDA
  | "*" -> const T.STAR
  | "=" -> const T.EQUALS
  | "/" -> const T.SLASH
  | "+" -> const T.PLUS

  | hole -> T.HOLE (String.drop 1 (get_lexeme lexbuf))
  | "_" -> const T.UNDERSCORE

  | dot_number -> T.DOT_NUMBER (int_of_string (String.drop 1 (get_lexeme lexbuf)))
  | dots -> const T.DOTS
  | hash_blank -> T.HASH_BLANK
  | hash_ident -> T.HASH_IDENT (get_lexeme lexbuf)
  | dollar_blank -> T.DOLLAR_BLANK
  | dollar_ident -> T.DOLLAR_IDENT (get_lexeme lexbuf)
  | "." -> const T.DOT
  | "#" -> const T.HASH
  | "$" -> const T.DOLLAR

  | eof -> const T.EOI

  | number -> T.INTLIT (get_lexeme lexbuf |> int_of_string)
  | ident -> T.IDENT (get_lexeme lexbuf)
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
