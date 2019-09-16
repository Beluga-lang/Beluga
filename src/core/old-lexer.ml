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

module Loc = Location

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

let regexp ident = ( start_sym sym* )

let regexp letter = [ 'a'-'z' 'A'-'Z' ]

let regexp digit  = [ '0'-'9' ]

(** A question mark followed by a symbol. *)
let regexp hole = '?' ( ident ) ?

(** A double-dash followed by a sumbol is a pragma. *)
let regexp pragma = "--" [ 'a'-'z' ]+

let regexp dot_ident = "." ( ident )

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
let mk_tok_of_lexeme loc lexbuf =
  update_loc loc (shift_by_lexeme lexbuf);
  Ulexing.utf8_lexeme lexbuf

let mk_comment loc s =
  let n = ref 0 in
  let _ = String.iter (fun c -> if c = '\n' then incr n) s in
  let _ = loc := Loc.move_line !n !loc in Token.BLOCK_COMMENT s

(**********)
(* Lexers *)
(**********)

(** @see http://www.cduce.org/ulex/ See [ulex] for details *)

let const t loc lexbuf = Misc.const t (mk_tok_of_lexeme loc lexbuf)

let regexp arrow = ("->" | 0x2192)
let regexp turnstile = ("|-" | 0x22a2)
let regexp thick_arrow = ("=>" | 0x21d2)
let regexp back_arrow = ("<-" | 0x2190)
let regexp dots = (".." | 0x2026)

(* Main lexical analyzer.  Converts a lexeme to a token. *)
let lex_token loc =
  let module T = Token in
  lexer
  | "%{{" ( [^'}'] | (['}'] [^'}']) | (['}']['}'][^'%'] ))* "}}%" -> mk_comment loc (mk_tok_of_lexeme loc lexbuf)

  (* KEYWORDS *)
  | "and" -> const T.KW_AND loc lexbuf
  | "block" -> const T.KW_BLOCK loc lexbuf
  | "case" -> const T.KW_CASE loc lexbuf
  | "fn" -> const T.KW_FN loc lexbuf
  | "else" -> const T.KW_ELSE loc lexbuf
  | "if" -> const T.KW_IF loc lexbuf
  | "impossible" -> const T.KW_IMPOSSIBLE loc lexbuf
  | "in" -> const T.KW_IN loc lexbuf
  | "let" -> const T.KW_LET loc lexbuf
  | "mlam"  -> const T.KW_MLAM loc lexbuf
  | "of" -> const T.KW_OF loc lexbuf
  | "rec" -> const T.KW_REC loc lexbuf
  | "schema" -> const T.KW_SCHEMA loc lexbuf
  | "some" -> const T.KW_SOME loc lexbuf
  | "then" -> const T.KW_THEN loc lexbuf
  | "module" -> const T.KW_MODULE loc lexbuf
  | "struct" -> const T.KW_STRUCT loc lexbuf
  | "end" -> const T.KW_END loc lexbuf
  | "trust" -> const T.KW_TRUST loc lexbuf
  | "total" -> const T.KW_TOTAL loc lexbuf
  | "type" -> const T.KW_TYPE loc lexbuf
  | "prop" -> const T.KW_PROP loc lexbuf
  | "inductive" -> const T.KW_INDUCTIVE loc lexbuf
  | "coinductive" -> const T.KW_COINDUCTIVE loc lexbuf
  | "stratified" -> const T.KW_STRATIFIED loc lexbuf
  | "LF" -> const T.KW_LF loc lexbuf

  (* SYMBOLS *)
  | dots -> const T.DOTS loc lexbuf
  | pragma -> T.PRAGMA (Misc.String.drop 2 (mk_tok_of_lexeme loc lexbuf))
  | arrow -> const T.ARROW loc lexbuf
  | back_arrow -> const T.BACK_ARROW loc lexbuf
  | thick_arrow -> const T.THICK_ARROW loc lexbuf
  | turnstile -> const T.TURNSTILE loc lexbuf
  | "[" -> const T.LBRACK loc lexbuf
  | "]" -> const T.RBRACK loc lexbuf
  | "{" -> const T.LBRACE loc lexbuf
  | "}" -> const T.RBRACE loc lexbuf
  | "(" -> const T.LPAREN loc lexbuf
  | ")" -> const T.RPAREN loc lexbuf
  | "<" -> const T.LANGLE loc lexbuf
  | ">" -> const T.RANGLE loc lexbuf
  | "^" -> const T.HAT loc lexbuf
  | "," -> const T.COMMA loc lexbuf
  | ":" -> const T.COLON loc lexbuf
  | ";" -> const T.SEMICOLON loc lexbuf
  | "|" -> const T.PIPE loc lexbuf
  | "\\" -> const T.LAMBDA loc lexbuf
  | "*" -> const T.STAR loc lexbuf

  | hole -> T.HOLE (Misc.String.drop 1 (mk_tok_of_lexeme loc lexbuf))
  | ident -> T.IDENT (mk_tok_of_lexeme loc lexbuf)
  | dot_ident -> T.DOT_IDENT (Misc.String.drop 1 (mk_tok_of_lexeme loc lexbuf))
  | "." -> const T.DOT loc lexbuf

  | eof -> const T.EOI loc lexbuf

  | digit+   -> T.INTLIT (mk_tok_of_lexeme loc lexbuf |> int_of_string)

let decrease_comment_depth (depth : int ref) : unit =
  match !depth with
  | 0 -> failwith "Parse error: \"}%\" with no comment to close\n"
  | d when d < 0 -> failwith "Invariant violated: nested comment depth is negative.\n"
  | d -> decr depth

let regexp newline = ('\r' '\n' | '\r' | '\n')

let skip_nestable depth loc =
  let update_loc = update_loc loc in
  let decr_comment_depth () = decrease_comment_depth depth in
  lexer
  | newline -> update_loc (advance_line lexbuf)

  | '%'+ [^'{' '%' '\n'] -> update_loc (shift_by_lexeme lexbuf)
  | [^ '\r' '\n' '%' '}' ]+ -> update_loc (shift_by_lexeme lexbuf)
  | '}' [^'%' '\n']+ -> update_loc (shift_by_lexeme lexbuf)

  | '}' '\n' -> update_loc (advance_line lexbuf)

  | '}' '%' ->
     update_loc (shift_by_lexeme lexbuf);
     decr_comment_depth ()

  | '%' '{' ->
     update_loc (shift_by_lexeme lexbuf);
     incr depth

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
         prerr_string "uh oh!\n";
         None
 in
    Stream.from next |> LinkStream.of_stream
