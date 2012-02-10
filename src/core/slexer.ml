(* modified de keywords for SASyLF *)
(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(* module Loc   = Core.Syntax.Loc (*Camlp4.PreCast.Loc*) *)
module Loc   = Syntax.Loc (*Camlp4.PreCast.Loc*) 
module Token = Token
module Error = Camlp4.Struct.EmptyError
let out_channel = open_out "lexing.out"

(* file has been modified for sasy ":" is no longer a reserved character and many other changes *)
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
         ->  <-  
         FN
         block  case  id  
         impossible
         mlam  of
         rec  schema  some  type 
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
                       ]

(* Matches any printable utf-8 character that isn't reserved *)
let regexp sym = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\" '"'  (* exclude reserved characters, but include # *)
                       ]

let regexp angle_compatible = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;Γ()[]{}\\" '"'    (* exclude reserved characters *)
                          'a'-'z'  '\'' 
                          '0'-'9'
                       ]

let regexp start_angle_compatible = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;Γ()[]{}\\" '"'    (* exclude reserved characters *)
                          'a'-'z' 
                          '#' '\''
                          '0'-'9'
                       ]

let regexp letter = [ 'a'-'z' 'A'-'Z' ]

let regexp digit  = [ '0'-'9' ]

(**************************************************)
(* Location Update and Token Generation Functions *)
(**************************************************)

(* Make a {!Token.t} taking no arguments and advance the {!Loc.t ref}. *)
let mk_tok tok loc lexbuf =
    loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  ; tok

let mk_tok_of_lexeme tok_cons loc lexbuf =
    loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  ; let tok = (tok_cons (Ulexing.utf8_lexeme lexbuf)) in
      tok

let mk_keyword s = Token.KEYWORD s

let mk_symbol  s = Token.SYMBOL  s

let mk_integer  s = Token.INTLIT s

let mk_lines = Token.LINES

(**********)
(* Lexers *)
(**********)

(** @see http://www.cduce.org/ulex/ See [ulex] for details *)

(* Main lexical analyzer.  Converts a lexeme to a token. *)
let rec lex_token loc = lexer 
  | "<-"
  | "=>"
  | "=="
  | "FN"
  | "and"   (* missing, added 2010-07-31 *)
  | "block"
  | "impossible"
  | "mlam"  (* was missing -- added 2009-02-18 *)
  | "rec"
  | "schema"
  | "some"
  | "type"
  | "%name"
  | "%not"
  | ["--"]+ -> output_string out_channel "made a token of lines \n"; mk_tok Token.LINES  loc lexbuf
  | "::=" -> output_string out_channel "made a token of declaration sign \n"; mk_tok Token.DECLA  loc lexbuf
  | "()" -> output_string out_channel "made a token of empty token \n"; mk_tok Token.EMPTY  loc lexbuf
  | 0x0370 -> output_string out_channel "made a token of turnstyle \n"; mk_tok Token.TSTYLE  loc lexbuf
  | "|-" -> output_string out_channel "made a token of turnstyle \n"; mk_tok Token.TSTYLE  loc lexbuf
  | 0x2200
  | [ "%,.:;()[]{}" '\\' '#' "$" "^" '\"']  -> (* reserved character *)
         mk_tok_of_lexeme mk_keyword loc lexbuf
(********)
  | eof  -> output_string out_channel "made a token of end of file but too stupid to make one of lines \n"; mk_tok Token.EOI  loc lexbuf


  | start_angle_compatible (sym | "<" | ">")*  ->
     mk_tok_of_lexeme mk_symbol  loc lexbuf

  | start_sym
     (sym
     | "<"
     | angle_compatible ">" (sym | "<" | ">")*
     )*  ->
      mk_tok_of_lexeme mk_symbol  loc lexbuf

  | "<" (angle_compatible | "<" | ">") (sym | "<" | ">")*  ->
      mk_tok_of_lexeme mk_symbol  loc lexbuf

  | "<" (angle_compatible | "<" | ">")?  ->
      mk_tok_of_lexeme mk_symbol  loc lexbuf

  | digit+   -> mk_tok_of_lexeme mk_integer loc lexbuf




let skip_nestable depth loc =
lexer
  | '\n' -> output_string out_channel "new line 1 \n";
      loc := Loc.move_line 1 !loc
  
  | '%'+ [^'{' '%' '\n'] -> output_string out_channel "new line 2 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  
  | [^'\n' '/' '*' ]+ -> output_string out_channel "new line 3 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
  
  | '}' [^'%' '\n']+ -> output_string out_channel "new line 4 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc

  | '}' '\n' -> output_string out_channel "new line 5 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf - 1) !loc
    ; loc := Loc.move_line 1 !loc
  
  | '*' '/' -> output_string out_channel "ending of comment \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
    ; if !depth <= 0 then 
        ( print_string ("Parse error: \"}%\" with no comment to close 1  \n");
          raise Ulexing.Error )
      else
        depth := !depth - 1
  
  | '%'+ '{' ->
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
    ; depth := !depth + 1

  | '%'+ '\n' -> output_string out_channel "new line 6 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf - 1) !loc
    ; loc := Loc.move_line 1 !loc


let skip_nested_comment loc = lexer
  | ['/' '*']+ -> output_string out_channel "beginning of comment \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
    ; let depth = ref 1 in
      while !depth > 0 do
        skip_nestable depth loc lexbuf ;
      done

  | '*' '/' ->
      loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc
    ; ( print_string ("Parse error: \"}%\" with no comment to close 2\n");
          raise Ulexing.Error )

(* Skip %...\n comments and advance the location reference. *)
let skip_line_comment loc = lexer
  | "//" ( [^ '\n' 'n' '*'] [^ '\n' ]* ) '\n' -> output_string out_channel "new line 7 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf - 1) !loc
    ; loc := Loc.move_line 1 !loc
  
  | '%' '\n' -> output_string out_channel "new line 8 \n";
      loc := Loc.shift (Ulexing.lexeme_length lexbuf - 1) !loc
    ; loc := Loc.move_line 1 !loc

(* Skip non-newline whitespace and advance the location reference. *)
let skip_whitespace loc = lexer
  | [ ' ' '\t' ]+         -> 
        loc := Loc.shift (Ulexing.lexeme_length lexbuf) !loc


(* Skip newlines and advance the location reference. *)
let skip_newlines    loc = lexer
  | '\n'+                 -> output_string out_channel "new line 9 \n";
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
                  ; output_string out_channel "new line 10 \n"
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
                    skip_whitespace loc_ref lexbuf
                  ; output_string out_channel "white space \n"
                  ; skip_failures := 0
                with
                  | Ulexing.Error ->
                      incr skip_failures
              end
            ; state := Comment
            ; skip ()
    else
      skip_failures := 0 in
  let next _    =  output_string out_channel "test 1 \n";
    try
        skip () ;  output_string out_channel "test 2 \n"
      ; let tok = Some (lex_token loc_ref lexbuf, !loc_ref) in
          output_string out_channel (Ulexing.latin1_lexeme lexbuf) ; output_string out_channel " : lexbuf \n";
          skip ()
        ; tok
    with
      | Ulexing.Error ->
          None
 in
     output_string out_channel "test 3 \n"; Stream.from next
