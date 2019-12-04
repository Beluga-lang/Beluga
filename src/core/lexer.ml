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
        |> Maybe.pure
     | _ -> None)

let (dprintf, _, _) = Debug.makeFunctions' (Debug.toFlags [11])
(* open Debug.Fmt *)

let sym_head = [%sedlex.regexp? id_start | '_']
let sym_tail = [%sedlex.regexp? id_continue | Chars "\'-*+@=^/#?" ]

let ident = [%sedlex.regexp? sym_head, Star sym_tail]
let digit = [%sedlex.regexp? '0'..'9']
let number = [%sedlex.regexp? Plus digit]
let hole = [%sedlex.regexp? '?', Opt ident]
let pragma = [%sedlex.regexp? "--", Plus alphabetic]
let hash_ident = [%sedlex.regexp? '#', ident]
let dollar_ident = [%sedlex.regexp? '$', ident]
let dot_number = [%sedlex.regexp? '.', number]

let shift_by_lexeme lexbuf loc =
  Loc.shift (Sedlexing.lexeme_length lexbuf) loc

let advance_lines (n : int) (lexbuf : Sedlexing.lexbuf) (loc : Loc.t) : Loc.t =
  Loc.move_line n (Loc.shift (Sedlexing.lexeme_length lexbuf) loc)

let advance_line : Sedlexing.lexbuf -> Loc.t -> Loc.t = advance_lines 1

let update_loc loc f = loc := f !loc

let update_loc_by_lexeme loc lexbuf = update_loc loc (shift_by_lexeme lexbuf)

let get_lexeme loc lexbuf =
  update_loc_by_lexeme loc lexbuf;
  Sedlexing.Utf8.lexeme lexbuf

(** Counts the linebreaks in the string and adds them to the
 * location's line counter.
 *)
let count_linebreaks loc s =
  let n = ref 0 in
  String.iter (fun c -> if c = '\n' then incr n) s;
  if !n <> 0 then loc := Loc.move_line !n !loc

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

(** Skips the _body_ of a block comment.
    Calls itself recursively upon encountering a nested block comment.
    Consumes the block_comment_end symbol. *)
let rec skip_nested_block_comment loc lexbuf =
  (* let const t = Misc.const t (get_lexeme loc lexbuf) in *)
  let skip () = update_loc_by_lexeme loc lexbuf in
  match%sedlex lexbuf with
  | block_comment_begin ->
     skip ();
     skip_nested_block_comment loc lexbuf; (* for the body of the new comment *)
     skip_nested_block_comment loc lexbuf (* for the remaining characters in this comment *)
  | block_comment_end -> skip ()
  | any ->
     get_lexeme loc lexbuf |> count_linebreaks loc;
     skip_nested_block_comment loc lexbuf
  | _ ->
     throw !loc (Violation "catch-all case for skip_nested_block_comment should be unreachable")


let rec tokenize loc lexbuf =
  let const t = Misc.const t (get_lexeme loc lexbuf) in
  let skip () = update_loc_by_lexeme loc lexbuf in
  let module T = Token in
  match%sedlex lexbuf with
  (* comments *)
  | eof -> const T.EOI
  | white_space ->
     get_lexeme loc lexbuf |> count_linebreaks loc;
     tokenize loc lexbuf
  | block_comment_begin ->
     skip ();
     skip_nested_block_comment loc lexbuf;
     tokenize loc lexbuf
  | block_comment_end -> throw !loc MismatchedBlockComment
  | line_comment -> skip (); tokenize loc lexbuf

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

  (* SYMBOLS *)
  | pragma -> T.PRAGMA (Misc.String.drop 2 (get_lexeme loc lexbuf))
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
  | "_" -> const T.UNDERSCORE
  | "+" -> const T.PLUS

  | hole -> T.HOLE (Misc.String.drop 1 (get_lexeme loc lexbuf))
  | ident -> T.IDENT (get_lexeme loc lexbuf)

  | dot_number -> T.DOT_NUMBER (int_of_string (Misc.String.drop 1 (get_lexeme loc lexbuf)))
  | dots -> const T.DOTS
  | hash_ident -> T.HASH_IDENT (get_lexeme loc lexbuf)
  | dollar_ident -> T.DOLLAR_IDENT (get_lexeme loc lexbuf)
  | "." -> const T.DOT
  | "#" -> const T.HASH
  | "$" -> const T.DOLLAR

  | eof -> const T.EOI

  | number -> T.INTLIT (get_lexeme loc lexbuf |> int_of_string)
  | _ -> throw !loc (UnlexableCharacter (get_lexeme loc lexbuf))

(** From a given generator for UTF-8, constructs a generator for tokens.
    Raises `Error` if a lexical error is encountered.
 *)
let mk initial_loc gen =
  let lexbuf = Sedlexing.Utf8.from_gen gen in
  let loc = ref initial_loc in
  let next () =
    let t = tokenize loc lexbuf in
    Some (!loc, t)
  in
  next
