(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

module Loc   = Core.Syntax.Loc (*Camlp4.PreCast.Loc*)
module Token = Token
module Error = Camlp4.Struct.EmptyError

(*
Beluga lexical categories:

- Reserved characters (cannot be used anywhere in an ordinary identifier):

        %
        ,  .  :  ;
        (  )  [  ]  {  }
        \
        "
        ::

   Note for Twelf users: the Twelf reserved characters

      %  .  :  [  ]  {  }

   as well as the forbidden character " are also reserved in Beluga.
   However, Beluga also reserves

           ,   ;  (  )  \

   and # is not allowed as the first character in an identifier (but may appear
   subsequently).

- Symbols

      First character:

         ABCDEFGHIJKLMNOPQRSTUVWXYZ
         abcdefghijklmnopqrstuvwxyz
         !  $  &  '  *  +  -  /   : < = > ? @
         ^ _ ` | ~
         
        (and any other UTF-8 character above 127)

     Characters after the first:

         0 1 2 3 4 5 6 7 8 9
         ABCDEFGHIJKLMNOPQRSTUVWXYZ
         abcdefghijklmnopqrstuvwxyz
         !  $  &  '  *  +  -  /   : < = > ? @
         ^ _ ` | ~
         #
         
        (and any other UTF-8 character above 127)

   Keyword symbols:

         |   !
         =  +  *
         <  >
         ->  <-   =>
         FN
         block  case  fn  id  in
         let  mlam  of
         rec  schema  some  type
         %name

     presently reserved but unused:           box

- Single-character symbols that are also permitted as the second/third/...
   character of an identifier:

       #
          
- Integers
         
        Any sequence of '0'-'9' [generates token INTEGER]
*)

(*******************************)
(* Regular Expression Patterns *)
(*******************************)

(* Matches any printable utf-8 character that isn't reserved or a digit *)
let regexp start_sym = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\#" '"'    (* exclude reserved characters *)
                          '0'-'9'                 (*exclude digits *)
                       ]

(* Matches any printable utf-8 character that isn't reserved *)
let regexp sym = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\" '"'    (* exclude reserved characters, but include # *)
                       ]
(* let regexp sym       = [^ '\000'-' '   "!\\#%()*,.:;=[]{|}+<>" ] *)

let regexp digit       = [ '0'-'9' ]

(**************************************************)
(* Location Update and Token Generation Functions *)
(**************************************************)

(* Make a {!Token.t} taking no arguments and advance the {!Loc.t ref}. *)
let mk_tok tok loc lexbuf =
    loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
(*  ; print_string ("mk_tok ADVANCED TO " ^ Loc.to_string !loc ^ "\n") *)
  ; tok

(* Make a {!Token.t} taking a {!string} argument for the current
   lexeme and advance the {!Loc.t ref}. *)
let mk_tok_of_lexeme tok_cons loc lexbuf =
    loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
(*  ; print_string ("mk_tok_of_lexeme ADVANCED TO " ^ Loc.to_string !loc ^ "\n") *)
  ; let tok = (tok_cons (Ulexing.utf8_lexeme lexbuf)) in
      tok

let mk_keyword s = Token.KEYWORD s

let mk_symbol  s = Token.SYMBOL  s

let mk_integer  s = Token.INTEGER s

(**********)
(* Lexers *)
(**********)

(** @see http://www.cduce.org/ulex/ See [ulex] for details *)

(* Main lexical analyzer.  Converts a lexeme to a token. *)
let rec lex_token loc = lexer
  | "->"
  | "<-"
  | "::"
  | "=>"
  | "FN"
(*  | "Sigma" *)
  | "block"
  | "box" (* unused as of 2009-02-18 *)
  | "case"
  | "fn"
  | "id"
  | "in"
  | "let"
  | "mlam"  (* was missing -- added 2009-02-18 *)
  | "of"
  | "rec"
  | "schema"
  | "some"
  | "type"
  | "%name"
(*  | [ "!\\#%()*,.:;=[]{|}+<>" ]  -> mk_tok_of_lexeme mk_keyword loc lexbuf *)

  | [ "%,.:;()[]{}" '\\' '#' '\"']  -> (* reserved character *)
         mk_tok_of_lexeme mk_keyword loc lexbuf

  | eof                       -> mk_tok           Token.EOI  loc lexbuf

  | start_sym sym*            -> mk_tok_of_lexeme mk_symbol  loc lexbuf

  | digit digit*   -> mk_tok_of_lexeme mk_integer loc lexbuf


(* Skip comments and advance the location reference. *)
let skip_comment     loc = lexer
(*   | '%' [^ '\n' ]* '\n'   ->   *)
(*    | '%' ( [^ 'a'-'z' 'A'-'Z' ] [^ '\n']* )? '\n'  -> *)
    | '%' ( [^ '\n' 'n'] [^ '\n']* )? '\n' ->
(*        print_string ("BEF " ^ Loc.to_string !loc ^"   \"" ^ Ulexing.utf8_lexeme lexbuf ^ "\"\n")      ;   *)
        loc := Loc.shift     (Ulexing.lexeme_length lexbuf - 1) !loc
      ; loc := Loc.move_line 1                                  !loc
(*      ; print_string ("AFT " ^ Loc.to_string !loc ^"\n") *)

(* Skip non-newline whitespaces and advance the location reference. *)
let skip_whitespaces loc = lexer
  | [ ' ' '\t' ]+         -> 
       (* print_string ("bef " ^ Loc.to_string !loc ^"   \"" ^ Ulexing.utf8_lexeme lexbuf ^ "\"\n")      ; *)
        loc := Loc.shift     (Ulexing.lexeme_length lexbuf)     !loc
(*    ;    print_string ("aft " ^ Loc.to_string !loc ^"   \"" ^ Ulexing.utf8_lexeme lexbuf ^ "\"\n")   *)


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
