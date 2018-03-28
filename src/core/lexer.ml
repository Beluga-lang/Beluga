
module Loc   = Syntax.Loc
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
         !  $  &  '  *  +  -  /   : = ? @
         ^ _ ` ~

        (and any other UTF-8 character above 127)

     Characters after the first:

         0 1 2 3 4 5 6 7 8 9
         ABCDEFGHIJKLMNOPQRSTUVWXYZ
         abcdefghijklmnopqrstuvwxyz
         !  $  &  '  *  +  -  /   : = ? @
         ^ _ ` ~
         # |

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
         %name %not #positive #stratified
        
          

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
                          "%,.:;()[]{}\\#|" '"'    (* exclude reserved characters *)
                          '0'-'9'                 (* exclude digits *)
                          "<>"   '`'                 (* exclude < and >, which can only be used with certain other characters *)
                       ]

(* Matches any printable utf-8 character that isn't reserved *)
let regexp sym = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\" '"'    (* exclude reserved characters, but include # *)
                          "<>" '|'     '`'               (* exclude < and > *)
                       ]
(* let regexp sym       = [^ '\000'-' '   "!\\#%()*,.:;=[]{|}+<>" ] *)

let regexp angle_compatible = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\" '"'    (* exclude reserved characters *)
                          'a'-'z'  'A'-'Z' '\''
                          '0'-'9' '`'
                          "<>"
                       ]

let regexp start_angle_compatible = [^ '\000'-' '  '\177'      (* exclude nonprintable ASCII *)
                          "%,.:;()[]{}\\|" '"'    (* exclude reserved characters *)
                          'a'-'z'  'A'-'Z'
                          '#' '\'' 
                          '`'
                          '0'-'9'
                          "<>"
                       ]

let regexp letter = [ 'a'-'z' 'A'-'Z' ]

let regexp digit  = [ '0'-'9' ]

let regexp upper = ['A' - 'Z']
let regexp lower = ['a' - 'z']

(** A question mark followed by a symbol. *)
let regexp hole = '?' ( start_sym sym* ) ?

(** A double-dash followed by a sumbol is a pragma. *)
let regexp pragma = "--" [ 'a'-'z' ]+

(**************************************************)
(* Location Update and Token Generation Functions *)
(**************************************************)

(** Updates `loc` by shifting it according to the length of `lexbuf`. *)
let shift_by_lexeme lexbuf loc =
  Loc.shift (Ulexing.lexeme_length lexbuf) loc

let advance_lines (n : int) (lexbuf : Ulexing.lexbuf) (loc : Loc.t) : Loc.t =
  Loc.move_line n (Loc.shift (Ulexing.lexeme_length lexbuf) loc)

let advance_line : Ulexing.lexbuf -> Loc.t -> Loc.t = advance_lines 1

let update_loc loc f = loc := f !loc

(* Make a {!Token.t} taking a {!string} argument for the current
   lexeme and advance the {!Loc.t ref}. *)
let mk_tok_of_lexeme tok_cons loc lexbuf =
  update_loc loc (shift_by_lexeme lexbuf);
  tok_cons (Ulexing.utf8_lexeme lexbuf)

let mk_keyword s = Token.KEYWORD s

let mk_symbol s = Token.SYMBOL s

let mk_integer s = Token.INTLIT s

let mk_hole s = Token.HOLE s

let mk_comment loc s =
  let n = ref 0 in
  let _ = String.iter (fun c -> if c = '\n' then incr n) s in
  let _ = loc := Loc.move_line !n !loc in Token.COMMENT s

let mk_dots s = Token.DOTS s

let mk_module s = Token.MODULESYM s

(**********)
(* Lexers *)
(**********)

(** @see http://www.cduce.org/ulex/ See [ulex] for details *)

(* Main lexical analyzer.  Converts a lexeme to a token. *)
let lex_token loc = lexer
  | (upper sym* ".")+ lower sym* -> mk_tok_of_lexeme mk_module loc lexbuf
  | (upper sym* ".")+ upper sym* -> mk_tok_of_lexeme (fun x -> Token.UPSYMBOL_LIST x) loc lexbuf
  | "%{{" ([^'}']|(['}'][^'}'])|(['}']['}'][^'%']))* "}}%" -> mk_tok_of_lexeme (mk_comment loc) loc lexbuf
  | upper sym* "." (upper sym* "." | start_sym sym* )+ -> mk_tok_of_lexeme mk_module loc lexbuf

  | "…"
  | ".." -> mk_tok_of_lexeme mk_dots loc lexbuf

  | pragma
  | "->"
  | "<-"
  | "::"
  | "=>"
  | "=="
  | "FN"
  | "and"
  | "block"
  | "Bool"
  | "case"
  | "fn"
  | "else"
  | "if"
  | "impossible"
  | "in"
  | "let"
  | "mlam" 
  | "of"
  | "rec"
  | "schema"
  | "some"
  | "then"
  | "module"
  | "struct"
  | "end"
  | "ttrue"
  | "ffalse"
  | "#positive"
  | "#stratified"
  | "strust"
  | "total"
  | "#opts"
  | "type"
  | "prop"
  | "|-"
  | [ "%,.:;()[]{}|" '\\' '#' "$" "^" '\"']  -> (* reserved character *)
         mk_tok_of_lexeme mk_keyword loc lexbuf

  | hole -> mk_tok_of_lexeme mk_hole loc lexbuf
  | eof ->
     update_loc loc (shift_by_lexeme lexbuf);
     Token.EOI

  | ">" (sym | "<" | ">")*  ->
      mk_tok_of_lexeme mk_symbol  loc lexbuf

  | start_angle_compatible (sym | "<" | ">")*  ->
    mk_tok_of_lexeme mk_symbol  loc lexbuf

  | start_sym
     (sym
     | "<"
     | angle_compatible ">" (sym | "<" | ">")*
     )*  ->  mk_tok_of_lexeme mk_symbol  loc lexbuf

  | "<" (angle_compatible | "<" | ">") (sym | "<" | ">")*  ->
      mk_tok_of_lexeme mk_symbol  loc lexbuf

  | "<" (angle_compatible | "<" | ">")?  ->
      mk_tok_of_lexeme mk_symbol  loc lexbuf

  | digit+   -> mk_tok_of_lexeme mk_integer loc lexbuf

let decrease_comment_depth (depth : int ref) : unit =
  match !depth with
  | 0 -> failwith "Parse error: \"}%\" with no comment to close\n"
  | d when d < 0 -> failwith "Invariant violated: nested comment depth is negative.\n"
  | d -> depth := (d - 1)

let increase_comment_depth (depth : int ref) : unit = incr depth

let regexp newline = ('\r' '\n' | '\r' | '\n')

let skip_nestable depth loc =
  let update_loc = update_loc loc in
  let incr_comment_depth () = increase_comment_depth depth in
  let decr_comment_depth () = decrease_comment_depth depth in
  lexer
  | newline -> update_loc (advance_line lexbuf)

  | '%'+ [^'{' '%' '\n'] -> update_loc (shift_by_lexeme lexbuf)
  | [^'\r' '\n' '%' '}' ]+ -> update_loc (shift_by_lexeme lexbuf)
  | '}' [^'%' '\n']+ -> update_loc (shift_by_lexeme lexbuf)

  | '}' '\n' -> update_loc (advance_line lexbuf)

  | '}' '%' ->
     update_loc (shift_by_lexeme lexbuf);
     decr_comment_depth ()

  | '%' '{' ->
     update_loc (shift_by_lexeme lexbuf);
     incr_comment_depth ()

  | [^ '%' '{' ] -> update_loc (shift_by_lexeme lexbuf)

  | '%'+ '\n' -> update_loc (advance_line lexbuf)

let skip_nested_comment loc =
  let skip_nestable_loop lexbuf =
    let depth = ref 1 in
    while !depth > 0 do
      skip_nestable depth loc lexbuf;
    done
  in
  let update_loc = update_loc loc in
  lexer
  | '%' '{' '\n' ->
     update_loc (advance_line lexbuf);
     skip_nestable_loop lexbuf

  | '%' '{' [^'{'] ->
     update_loc (shift_by_lexeme lexbuf);
     skip_nestable_loop lexbuf

  | [^'}'] '}' '%' ->
     update_loc (shift_by_lexeme lexbuf);
     print_string "Parse error: \"}%\" with no comment to close\n";
     raise Ulexing.Error

(* Skip %...\n comments and advance the location reference. *)
let skip_line_comment loc =
  lexer
  | '%' newline
  | '%' [^ '\r' '\n' '{'] [^ '\r' '\n' ]* newline ->
     update_loc loc (advance_line lexbuf)

(* Skip non-newline whitespace and advance the location reference. *)
let skip_whitespace loc = lexer
  | [ ' ' '\t' ]+ -> update_loc loc (shift_by_lexeme lexbuf)

(* Skip newlines and advance the location reference. *)
let skip_newlines loc =
  let update_loc = update_loc loc in
  lexer
  (* on Windows, "\r\n" is the line terminator, so we have to divide the
  length of the match in two. *)
  | ('\r' '\n')+ ->
     update_loc (advance_lines (Ulexing.lexeme_length lexbuf / 2) lexbuf)
  (* skip lines for Unix and traditional Mac endings *)
  | ('\n' | '\r')+ ->
     update_loc (advance_lines (Ulexing.lexeme_length lexbuf) lexbuf)

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
        | Comment ->
           begin
             try
               skip_nested_comment loc_ref lexbuf;
               skip_failures := 0
             with
             | Ulexing.Error -> incr skip_failures
           end;
           state := LineComment;
           skip ()

        | LineComment ->
           begin
             try
               skip_line_comment loc_ref lexbuf;
               skip_failures := 0
             with
             | Ulexing.Error -> incr skip_failures
           end;
           state := Newline;
           skip ()

        | Newline ->
           begin
             try
               skip_newlines loc_ref lexbuf;
               skip_failures := 0
             with
             | Ulexing.Error -> incr skip_failures
           end;
           state := Whitespace;
           skip ()

        | Whitespace ->
           begin
             try
               skip_whitespace loc_ref lexbuf;
               skip_failures := 0
             with
             | Ulexing.Error -> incr skip_failures
           end;
           state := Comment;
           skip ()
    else
      skip_failures := 0 in

  let next _    =
    try
      skip ();
      (* It is essential to call lex_token _before_ dereferencing
      loc_ref, since lex_token updates this ref with the correct
      location of the token. *)
      let t = lex_token loc_ref lexbuf in
      let tok = Some (t, !loc_ref) in (
          skip ();
          tok
      )
    with
      | Ulexing.Error ->
          None
 in
    Stream.from next
