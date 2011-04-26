(* MinML lexer *)
(* Written as a stream transducer *)

signature LEXER = sig
  datatype token =
           ARROW
         | DARROW
         | TRUE
         | FALSE

         | CASE
         | ELSE
         | END
         | FN
         | FUN
         | IF
         | IN
         | LET
         | REC
         | THEN
         | VAL

         | COMMA
         | LPAREN
         | RPAREN
         | BAR
         | SEMICOLON
         | EQUALS
         | LESSTHAN
         | TIMES
         | MINUS
         | NEGATE
         | PLUS
         | COLON
         | NUMBER of int
         | VAR of string

         | DATATYPE
         | OF

  val lex : char Stream.stream -> token Stream.stream
  val tokenToString : token -> string
end;  (* signature LEXER *)


structure Lexer :> LEXER = struct
  structure S = Stream

  exception LexError of string

  datatype token =
           ARROW
         | DARROW
         | TRUE
         | FALSE

         | CASE
         | ELSE
         | END
         | FN
         | FUN
         | IF
         | IN
         | LET
         | REC
         | THEN
         | VAL

         | COMMA
         | LPAREN
         | RPAREN
         | BAR
         | SEMICOLON
         | EQUALS
         | LESSTHAN
         | TIMES
         | MINUS
         | NEGATE
         | PLUS
         | COLON
         | NUMBER of int
         | VAR of string

         | DATATYPE
         | OF

  fun next s =
      case S.force s of
        S.Nil => raise LexError "Unexpected end of stream."
      | S.Cons result => result
                         
  (* foldfamily :
   * ('a -> bool) -> ('a * 'b -> 'b) -> 'b -> ('b -> 'c) ->
   * ('a * 'a stream) -> ('c * 'a stream) 
   *
   * This handles a string of characters matching a certain
   * function, folding them into a result.
   *)
  fun foldfamily test base combine wrap (c, ins) =
      let
        fun ff b s =
            case next s of
              (c, ss) =>
              if test c then
                ff (combine (c, b)) ss
              else (wrap b, s)
      in
        ff (combine (c, base)) ins
      end

  fun gatherWhile p (acc, s) =
      let
        val (ch, s') = next s
      in
        (* if p ch then gatherWhile p (acc @ [ch], s') *)
        (* else (acc, s) *)
        if p ch then gatherWhile p (ch :: acc, s')
        else (rev acc, s)
      end

  fun readNum (acc, s) = gatherWhile Char.isDigit (acc, s)
      
  fun isalpha #"_" = true
    | isalpha #"'" = true
    | isalpha c = Char.isAlphaNum c

  fun token (#",", s) = (COMMA, s)
    | token (#"(", s) = (LPAREN, s)
    | token (#")", s) = (RPAREN, s)
    | token (#"|", s) = (BAR, s)
    | token (#";", s) = (SEMICOLON, s)
    | token (#"=", s) =
      (* might be equals or the start of a darrow *)
      let in
        case next s of
          (#">", s) => (DARROW, s)
        | _ => (EQUALS, s)
      end
    | token (#"<", s) = (LESSTHAN, s)
    | token (#"*", s) = (TIMES, s)
    | token (#"~", s) = (NEGATE, s)
    | token (#"-", s) = 
      (* might be minus or the start of an arrow *)
      let in
        case next s of
          (#">", s) => (ARROW, s)
        | _ => (MINUS, s)
      end
    | token (#"+", s) = (PLUS, s)
    | token (#":", s) = (COLON, s)
    | token (c, s) =
      if Char.isDigit c then
        let
          val (chars, s) = readNum ([c], s)
        in
          (NUMBER (Option.valOf (Int.fromString (implode chars))), s)
        end
      else if isalpha c then
        foldfamily
            isalpha
            (* "" *)
            []
            (* (fn (a, b) => b ^ str a) *)
            op ::
            (* VAR *)
            (fn foo => VAR (implode (rev foo)))
            (c, s)
      else raise LexError "illegal character"

  (* some "variables" are actually keywords *)
  and keywords (VAR "else") = ELSE
    | keywords (VAR "end") = END
    | keywords (VAR "false") = FALSE
    | keywords (VAR "fn") = FN
    | keywords (VAR "fun") = FUN
    | keywords (VAR "if") = IF
    | keywords (VAR "in") = IN
    | keywords (VAR "let") = LET
    | keywords (VAR "rec") = REC
    | keywords (VAR "then") = THEN
    | keywords (VAR "true") = TRUE
    | keywords (VAR "val") = VAL

    | keywords (VAR "case") = CASE
    | keywords (VAR "datatype") = DATATYPE
    | keywords (VAR "of") = OF

    | keywords t = t

  and lex (s : char S.stream) : token S.stream =
      S.delay (fn () => lex' (S.force s))

  (* n = nesting depth *)
  and eatComment n S.Nil = raise LexError "unclosed comment"
    | eatComment n (S.Cons (#"*", s)) = 
      let in
        case S.force s of
          S.Cons (#")", s) => if n = 1 then S.force s else eatComment (n - 1) (S.force s)
       | rest => eatComment n rest
      end
    | eatComment n (S.Cons (#"(", s)) = 
      let in
        case S.force s of
         S.Cons (#"*", s) => eatComment (n + 1) (S.force s)
       | rest => eatComment n rest
      end
    | eatComment n (S.Cons (ch, s)) = eatComment n (S.force s)

  (* process characters, skipping whitespace and comments *)
  and lex' S.Nil = S.Nil
    | lex' (S.Cons (#" ", s)) = lex' (S.force s)
    | lex' (S.Cons (#"\r", s)) = lex' (S.force s)
    | lex' (S.Cons (#"\t", s)) = lex' (S.force s)
    | lex' (S.Cons (#"\v", s)) = lex' (S.force s)
    | lex' (S.Cons (#"\n", s)) = lex' (S.force s)
    | lex' (S.Cons (stuff as (#"(", s))) =
      let in
        case S.force s of
          S.Cons (#"*", s) =>
          lex' (eatComment 1 (S.force s))
        | _ => let val (t, s) = token stuff
               in
                 S.Cons (keywords t, lex s)
               end
      end
    | lex' (S.Cons r) =
      let
        val (t, s) = token r
      in 
        S.Cons (keywords t, lex s)
      end

  fun tokenToString t = 
      case t of
        ARROW => "ARROW"
      | DARROW => "DARROW"
      | TRUE => "TRUE"
      | FALSE => "FALSE"

      | CASE => "CASE"
      | ELSE => "ELSE"
      | END => "END"
      | FN => "FN"
      | FUN => "FUN"
      | IF => "IF"
      | IN => "IN"
      | LET => "LET"
      | REC => "REC"
      | THEN => "THEN"
      | VAL => "VAL"

      | COMMA => "COMMA"
      | LPAREN => "LPAREN"
      | RPAREN => "RPAREN"
      | BAR => "BAR"
      | SEMICOLON => "SEMICOLON"
      | EQUALS => "EQUALS"
      | LESSTHAN => "LESSTHAN"
      | TIMES => "TIMES"
      | MINUS => "MINUS"
      | PLUS => "PLUS"
      | COLON => "COLON"
      | NEGATE => "NEGATE"
      | NUMBER n => "NUMBER(" ^ Int.toString n ^ ")"
      | VAR v => "VAR(" ^ v ^ ")"

      | DATATYPE => "DATATYPE"
      | OF => "OF"

end;  (* structure Lexer *)
