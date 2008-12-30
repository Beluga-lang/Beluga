(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

module Loc   = Core.Syntax.Loc (*Camlp4.PreCast.Loc*)
module Token = Token
module Error = Camlp4.Struct.EmptyError

(*******************************)
(* Regular Expression Patterns *)
(*******************************)

(* Matches any utf-8 character that isn't a single character
   keyword. *)
let regexp start_sym = [^ "#%()*,.:;=[]{|}" ' ' '0'-'9' '\n' '\t' ]

let regexp sym       = [^ "#%()*,.:;=[]{|}" ' ' '\n' '\t' ]

(**************************************************)
(* Location Update and Token Generation Functions *)
(**************************************************)

(* Make a {!Token.t} taking no arguments and advance the {!Loc.t ref}. *)
let mk_tok tok loc lexbuf =
    loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  ; Token.print Format.std_formatter tok
  ; Format.fprintf Format.std_formatter "@.@?"
  ; tok

(* Make a {!Token.t} taking a {!string} argument for the current
   lexeme and advance the {!Loc.t ref}. *)
let mk_tok_of_lexeme tok_cons loc lexbuf =
    loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  ; let tok = (tok_cons (Ulexing.utf8_lexeme lexbuf)) in
        Token.print Format.std_formatter tok
      ; Format.fprintf Format.std_formatter "@.@?"
      ; tok

let mk_keyword s = Token.KEYWORD s

let mk_symbol  s = Token.SYMBOL  s

(**********)
(* Lexers *)
(**********)

(** @see http://www.cduce.org/ulex/ See [ulex] for details *)

(* Main lexical analyzer.  Converts a lexeme to a token. *)
let rec lex_token loc = lexer
(*   | "UNIFY_TERM"       -> mk_tok_of_lexeme mk_keyword loc lexbuf *)
(*   | "UNIFY_TYPE"       -> mk_tok_of_lexeme mk_keyword loc lexbuf *)
(*   | "@term"            -> mk_tok_of_lexeme mk_keyword loc lexbuf *)
(*   | "@type"            -> mk_tok_of_lexeme mk_keyword loc lexbuf *)
(*   | "{-#"              -> mk_tok_of_lexeme mk_keyword loc lexbuf *)
(*   | "#-}"              -> mk_tok_of_lexeme mk_keyword loc lexbuf *)
  | "->"
  | "::"
  | "=>"
  | "FN"
  | "block"
  | "box"
  | "case"
  | "fn"
  | "id"
  | "of"
  | "rec"
  | "schema"
  | "some"
  | "type"
  | [ "#%()*,.:;=[]{|}" ] -> mk_tok_of_lexeme mk_keyword loc lexbuf
  | eof                   -> mk_tok           Token.EOI  loc lexbuf
  | start_sym sym*        -> mk_tok_of_lexeme mk_symbol  loc lexbuf

(* Skip comments and advance the location reference. *)
let skip_comment     loc = lexer
  | '%' [^ '\n' ]* '\n'   ->
        loc := Loc.shift     (Ulexing.lexeme_length lexbuf - 1) !loc
      ; loc := Loc.move_line 1                                  !loc

(* Skip non-newline whitespaces and advance the location reference. *)
let skip_whitespaces loc = lexer
  | [ ' ' '\t' ]+         ->
        loc := Loc.shift     (Ulexing.lexeme_length lexbuf)     !loc

(* Skip newlines and advance the location reference. *)
let skip_newlines    loc = lexer
  | '\n'+                 ->
        loc := Loc.move_line (Ulexing.lexeme_length lexbuf) !loc

(******************)
(* Lexer Creation *)
(******************)

type skip_state =
  | Comment
  | Newline
  | Whitespace

let mk () = fun loc strm ->
  let lexbuf        = Ulexing.from_utf8_stream strm
  and loc_ref       = ref loc
  and state         = ref Newline
  and skip_failures = ref 0 (* used to break cycle *) in
  let rec skip ()   =
    if !skip_failures < 3 then
      match !state with
        | Comment    ->
              begin
                try
                    skip_comment     loc_ref lexbuf
                  ; skip_failures := 0
                with
                  | Ulexing.Error ->
                      incr skip_failures
              end
            ; state := Newline
            ; skip ()

        | Newline    ->
              begin
                try
                    skip_newlines    loc_ref lexbuf
                  ; skip_failures := 0
                with
                  | Ulexing.Error ->
                      incr skip_failures
              end
            ; state := Whitespace
            ; skip ()

        | Whitespace ->
              begin
                try
                    skip_whitespaces loc_ref lexbuf
                  ; skip_failures := 0
                with
                  | Ulexing.Error ->
                      incr skip_failures
              end
            ; state := Comment
            ; skip ()
    else
      skip_failures := 0 in
  let next _    =
    try
        skip ()
      ; let tok = Some (lex_token loc_ref lexbuf, !loc_ref) in
          skip ()
        ; tok
    with
      | Ulexing.Error ->
          None
 in
    Stream.from next
