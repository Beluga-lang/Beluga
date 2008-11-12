(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



module Loc   = Core.Syntax.Loc (*Camlp4.PreCast.Loc*)
module Token = Token
module Error = Camlp4.Struct.EmptyError



(*******************************)
(* Regular Expression Patterns *)
(*******************************)


(* Matches any utf-8 character that isn't a single character
   keyword. *)
let regexp start_sym = [^ "%(),.:[]{}" ' ' '0'-'9' '\n' '\t' ]

let regexp sym       = [^ "%(),.:[]{}" ' ' '\n' '\t' ]



(**************************************************)
(* Location Update and Token Generation Functions *)
(**************************************************)


(* Make a {!Token.t} taking no arguments and advance the {!Loc.t ref}. *)
let mk_tok tok loc lexbuf =
    loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  ; tok

(* Make a {!Token.t} taking a {!string} argument for the current
   lexeme and advance the {!Loc.t ref}. *)
let mk_tok_of_lexeme tok_cons loc lexbuf =
    loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  ; let tok = (tok_cons (Ulexing.utf8_lexeme lexbuf)) in
    tok

let mk_keyword s = Token.KEYWORD s

let mk_symbol  s = Token.SYMBOL  s



(**********)
(* Lexers *)
(**********)

(** @see http://www.cduce.org/ulex/ See [ulex] for details *)

(* Main lexical analyzer.  Converts a lexeme to a token. *)
let rec lex_token loc = lexer
  | "Π"              -> mk_tok_of_lexeme mk_keyword loc lexbuf
  | "λ"              -> mk_tok_of_lexeme mk_keyword loc lexbuf
  | "type"           -> mk_tok_of_lexeme mk_keyword loc lexbuf
  | [ "%(),.:[]{}" ] -> mk_tok_of_lexeme mk_keyword loc lexbuf
  | eof              -> mk_tok           Token.EOI  loc lexbuf
  | start_sym sym*   -> mk_tok_of_lexeme mk_symbol  loc lexbuf


(* NOTE: The following two lexers loop endlessly, by design.  The loop
   is broken when a match no longer occurs and an exceptionis
   thrown. *)

(* Skip non-newline whitespaces and advance the location reference. *)
let rec skip_whitespaces loc = lexer
  | [ ' ' '\t' ]+ ->
        loc := Loc.shift     (Ulexing.lexeme_length lexbuf) !loc
      ; skip_newlines    loc lexbuf
(* Skip newlines and advance the location reference. *)
and     skip_newlines    loc = lexer
  | '\n'+         ->
        loc := Loc.move_line (Ulexing.lexeme_length lexbuf) !loc
      ; skip_whitespaces loc lexbuf



(******************)
(* Lexer Creation *)
(******************)

let mk () = fun loc strm ->
  let lexbuf  = Ulexing.from_utf8_stream strm
  and loc_ref = ref loc in
  let next _  =
    try
      begin
      (* Keep trying to skip whitespaces and newlines until we hit a
         non-whitespace or newline character, at which point we will
         throw an exception.

         NOTE: Both `skip_newlines' and `skip_whitespaces' need to
         be called explicitly here for this to work properly, even
         though they begin to call eachother endlessly once one of
         them is called. This is because we may have a scenario
         where there are no regular whitespaces prior to a newline,
         thus `skip_whitespaces' would throw an exception
         immediately without ever calling `skip_newlines'. *)
        try
          skip_newlines    loc_ref lexbuf
        with
          | Ulexing.Error ->
        try
          skip_whitespaces loc_ref lexbuf
        with
          | Ulexing.Error ->
        Some (lex_token loc_ref lexbuf, !loc_ref)
      end
    with
      | Ulexing.Error -> None
  in
    Stream.from next
