
(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(* module Loc   = Core.Syntax.Loc (*Camlp4.PreCast.Loc*) *)
module Loc   = Syntax.Loc (*Camlp4.PreCast.Loc*) 
module Token = Token
module Error = Camlp4.Struct.EmptyError
let out_channel = open_out "lexing.out";
open Printf

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
         !  $  &  '  *  +  -  /   : = ? @
         ^ _ ` | ~
         
        (and any other UTF-8 character above 127)

     Characters after the first:

         0 1 2 3 4 5 6 7 8 9
         ABCDEFGHIJKLMNOPQRSTUVWXYZ
         abcdefghijklmnopqrstuvwxyz
         !  $  &  '  *  +  -  /   : = ? @
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
         impossible
         let  mlam  of
         rec  schema  some  type 
         bool
         %name %not

     presently reserved but unused:           box

- Single-character symbols that are also permitted as the second/third/...
   character of an identifier:

       #

- Special rules for < and >,
  intended to allow not only < g, x. U .. x > but <g, x. U .. x> too:

     No letter can follow a <
     No letter can PRECEDE a >
     A symbol containing < and/or > can only contain:
      
         !  $  &  '  *  +  -  /   : = ? @
         ^ ` | ~
         # 

- Integers
         
        Any sequence of '0'-'9' [generates token INTLIT]
*)

(*******************************)
(* Regular Expression Patterns *)
(*******************************)

(* Matches any printable utf-8 character that isn't reserved or a digit *)
let regexp start_sym = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\#" '"'    (* exclude reserved characters *)
                          '0'-'9'                 (* exclude digits *)
                          "<>"                    (* exclude < and >, which can only be used with certain other characters *)
                       ]

(* Matches any printable utf-8 character that isn't reserved *)
let regexp sym = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\" '"'    (* exclude reserved characters, but include # *)
                          "<>"                   (* exclude < and > *)
                       ]

let regexp angle_compatible = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\" '"'    (* exclude reserved characters *)
                          'a'-'z'  'A'-'Z' '\''
                          '0'-'9'
                          "<>"
                       ]

let regexp start_angle_compatible = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\" '"'    (* exclude reserved characters *)
                          'a'-'z'  'A'-'Z'
                          '#' '\''
                          '0'-'9'
                          "<>"
                       ]

let regexp letter = [ 'a'-'z' 'A'-'Z' ]

let regexp digit  = [ '0'-'9' ]

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
  ; 
let tok = (tok_cons (Ulexing.utf8_lexeme lexbuf)) in
(*  let _ = print_string ("TOKEN>> " ^ Token.to_string tok ^ "\n") in *)
      tok

let mk_keyword s = Token.KEYWORD s

let mk_symbol  s = Token.SYMBOL  s

let mk_integer  s = Token.INTLIT s

(**********)
(* Lexers *)
(**********)

(** @see http://www.cduce.org/ulex/ See [ulex] for details *)

(* Main lexical analyzer.  Converts a lexeme to a token. *)
let rec lex_token loc = lexer
  | "->" (*->  output_string out_channel "lex token   \n";*)
  | "<-"
  | "::"
  | "=>"
  | "=="
  | "FN"
  | "and"   (* missing, added 2010-07-31 *)
  | "block"
  | "Bool"
  | "case"
  | "fn"
  | "else"
  | "if"
  | "impossible"
  | "in"      
  | "let"
  | "mlam"  (* was missing -- added 2009-02-18 *)
  | "of"
  | "rec"
  | "schema"
  | "some"
  | "then"
  | "type"
  | "ttrue"
  | "ffalse"
  | "%name"
  | "%not"

  | [ "%,.:;()[]{}" '\\' '#' "$" "^" '\"']  -> mk_tok_of_lexeme mk_keyword loc lexbuf 

  | eof                       -> mk_tok           Token.EOI  loc lexbuf

  | ">" (sym | "<" | ">")*  -> mk_tok_of_lexeme mk_symbol  loc lexbuf 

  | start_angle_compatible (sym | "<" | ">")*  -> output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lex_token start angle compatible  \n";
     mk_tok_of_lexeme mk_symbol  loc lexbuf

  | start_sym
     (sym
     | "<"
     | angle_compatible ">" (sym | "<" | ">")*
     )*  -> output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lex_token start sym  \n";
      mk_tok_of_lexeme mk_symbol  loc lexbuf

  | "<" (angle_compatible | "<" | ">") (sym | "<" | ">")*  -> output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lex_token angle compatible sym \n";
      mk_tok_of_lexeme mk_symbol  loc lexbuf

  | "<" (angle_compatible | "<" | ">")?  -> output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lex_token angle compatible  \n";
      mk_tok_of_lexeme mk_symbol  loc lexbuf

  | digit+   -> output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lex_token digit+  \n";
                mk_tok_of_lexeme mk_integer loc lexbuf


let skip_nestable depth loc =
lexer
  | '\n' -> output_string out_channel "crazy comment 1 \n";
      loc := Loc.move_line 1 !loc
  
  | '%'+ [^'{' '%' '\n'] -> output_string out_channel "crazy comment 2 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  
  | [^'\n' '%' '}' ]+ -> output_string out_channel "crazy comment 3 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  
  | '}' [^'%' '\n']+ -> output_string out_channel "crazy comment 4 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc

  | '}' '\n' -> output_string out_channel "crazy comment 5 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf - 1) !loc
    ; loc := Loc.move_line 1 !loc
  
  | '}' '%' -> output_string out_channel "crazy comment 6 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
    ; if !depth <= 0 then 
        ( print_string ("Parse error: \"}%\" with no comment to close\n");
          raise Ulexing.Error )
      else
        depth := !depth - 1
  
  | '%'+ '{' -> output_string out_channel "crazy comment 7 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
    ; depth := !depth + 1

  | '%'+ '\n' -> output_string out_channel "crazy comment 8 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf - 1) !loc
    ; loc := Loc.move_line 1 !loc

let skip_nested_comment loc = lexer
  | '%' '{' -> output_string out_channel "crazy comment 11 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
    ; output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf 1 in skip nested comment \n"
    ; let depth = ref 1 in
      while !depth > 0 do
        skip_nestable depth loc lexbuf ;
      done

  | '}' '%' -> output_string out_channel "crazy comment 12 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
    ; output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf 1 in skip nested comment \n"
    ; ( print_string ("Parse error: \"}%\" with no comment to close\n");
          raise Ulexing.Error )


(* Skip %...\n comments and advance the location reference. *)
let skip_line_comment loc = lexer
  | '%' ( [^ '\n' 'n' '{'] [^ '\n' ]* ) '\n' -> output_string out_channel "crazy comment 9 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf - 1) !loc
      ; output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf 2 in skipcomment \n"
    ; loc := Loc.move_line 1 !loc
  
  | '%' '\n' -> output_string out_channel "crazy comment 10 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf - 1) !loc
     ; output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf 1 in skipcomment \n"
    ; loc := Loc.move_line 1 !loc

(* Skip non-newline whitespace and advance the location reference. *)
let skip_whitespace loc = lexer
  | [ ' ' '\t' ]+         -> 
        loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
        ; output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf in skipwhite space \n"


(* Skip newlines and advance the location reference. *)
let skip_newlines    loc = lexer
  | '\n'+                 ->
        loc := Loc.move_line (Ulexing.lexeme_length lexbuf) !loc

(******************)
(* Lexer Creation *)
(******************)

type skip_state =
  | Comment
  | LineComment
  | Newline
  | Whitespace

let mk () = fun loc strm -> 
  let lexbuf        = Ulexing.from_utf8_stream strm
  and loc_ref       = ref loc
  and state         = ref Newline
  and skip_failures = ref 0 (* used to break cycle *) in
  let rec skip ()   =
    if !skip_failures < 4 then
      match !state with
        | Comment  ->
              begin
                try
                  skip_nested_comment loc_ref lexbuf
                ; skip_failures := 0
                ; output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf in comment \n"
                with
                  | Ulexing.Error ->
                      incr skip_failures
              end
            ; state := LineComment
            ; skip ()

        | LineComment  ->
              begin
                try
                    skip_line_comment loc_ref lexbuf
                  ; skip_failures := 0
                  ; output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf in linecomment \n"
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
                  ; output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf in newline \n"
                with
                  | Ulexing.Error ->
                      incr skip_failures
              end
            ; state := Whitespace
            ; skip ()

        | Whitespace ->
              begin
                try
                    skip_whitespace loc_ref lexbuf
                  ; skip_failures := 0
                  ; output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf in whitespace \n"
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
          output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf in next _ \n";
          skip ()
        ; tok
    with
      | Ulexing.Error ->
          None
 in
    Stream.from next
