module type ParserInfo = sig
  module Stream : Types.BasicStream

  type item
end

module type Base = sig
  (** The basic elements processed by the parser.
      Generally for a simple text parser, this is {! char !}
   *)
  type item

  module Stream : Types.BasicStream

  module Token : Annotated.Base with type annotation = Span.t

  (** A semantic location, provided by the user of the parser, used to
      generate nice error messages, specifically of the form "Parse
      error at (line, col) in FOO in BAR in XYZ in ..."
   *)
  type semantic
  
  (** The internal state of the parser. *)
  type state
  
  (** Parse errors. *)
  type parse_error
  
  (** Produces a nice, human-readable version of a parse error. *)
  val string_of_parse_error : parse_error -> string
  
  (** The type of a parser. *)
  type 'a t
  
  (** Runs a parser with backtracking enabled.
  This will allow alternation to succeed if this parser fails even
  while consuming input.
  Note that even in case of failure, the returned parser state will
  have its value of `backtrack_enabled` reset to its original
  value.
  While running with backtracking enabled, the parser will buffer all
  tokens into a stack in order to rewind the input.
  The stack will be flushed once the parser exits backtracking
  mode. *)
  val trying : 'a t -> 'a t
  
  (** Constructs a parser that tries the left parser, and if it fails
  *without consuming input*, tries the right parser.
  In other words, this is an alternation operator on parsers.
  In order to perform alternation *even while consuming input*, the
  parser must fail with `backtrack_enabled = true`. This can be
  achieved by using the `trying` combinator. *)
  val alt : 'a t -> 'a t -> 'a t
  
  (** Causes the current parser to fail with the given message. *)
  val throw : string -> 'a t
  
  (** A parser that observes the head of the input, returning
  {!Pervasives.None} if the parser has reached the end of the input. *)
  val peek : item Token.t option t
  
  (** A variant of {!Mupc.peek} that throws an
   {! unexpected end of file !} error if the stream is empty.
   *)
  val peek' : item Token.t t
  
  (** Reads one token of input. Fails with a parse error if the parse is
      at EOF.
   *)
  val any : item t
  
  (** Transforms the output of a parser with a plain function. *)
  val map : ('a -> 'b) -> 'a t -> 'b t
  
  (** Attaches an arbitrary label to a parser.
      If the parser fails, then this label will appear in the error.
   *)
  val label : string -> 'a t -> 'a t
  
  (** Constructs a parser that doesn't affect its state and simply
      yields the given value.
   *)
  val pure : 'a -> 'a t
  
  (** A sequencing operator for parsers.
      This operator takes a parser on the left and a continuation on the
      right.
      The continuation uses the result of the left parser to construct a
      new parser.
      This operator passes the output state of the left parser to run
      the new parser.
   *)
  val ( $ ) : 'a t -> ('a -> 'b t) -> 'b t
  
  (** A flipped, operator version of `map`. *)
  val ( $> ) : 'a t -> ('a -> 'b) -> 'b t
  
  (** Tries all the parsers from left to right.
      The same caveats regarding input consumption apply as in `alt`.
   *)
  val choice : 'a t list -> 'a t
  
  (** Repeatedly applies a parser until it fails, collecting all
      results.
      The parser could succeed zero times, consuming no input, producing
      an empty list.
      {i Warning:} {! many p !} will enter an infinite loop if {! p !}
      accepts the empty input!
   *)
  val many : 'a t -> 'a list t
  
  (** `some` repeatedly applies a parser until it fails, but must
      succeed at least once.
   *)
  val some : 'a t -> 'a list t
    
  (** Constructs a parser that consumes a single character of input,
      returning it, if that character satisfies the given predicate.
   *)
  val satisfy : (item -> bool) -> item t
  
  (** Matches an item from a given list. *)
  val one_of : item list -> item t
  
  (** {! many_till p pend !} repeatedly applies {! p !}, testing whether
      {! pend !} succeeds between applications.
      Once {! pend !} succeeds, this parser stops, yielding all
      collected parses of {! p !}.
      {i Remark:} it must be possible to backtrack out of {! pend !}!
      If {! pend !} consumes input before failing and does not have
      backtracking enabled, then {! many_till !} will also fail.
   *)
  val many_till : 'a t -> unit t -> 'a list t
  
  (** `some_till` does the same, but `p` must succeed at least once.
      The same input consumption caveats apply as in {! Mupc.many_till !}.
   *)
  val some_till : 'a t -> unit t -> 'a list t
  
  (** Forgets the result of a parser, preserving only its effects. *)
  val void : 'a t -> unit t
  
  (** A parser that succeeds only if the parser is at the beginning of
  a line. *)
  val bol : unit t
  
  (** A parser that succeeds only if the parser is at the end of the
  input. *)
  val eof : unit t
  
  (** {! lookahead p !} runs parser {! p !}, but resets the parser input
  state to its original value. {! lookahead !} fails if the underlying
  parser fails.
  This is useful when used in conjunction with combinators such as
  {! many_till q end !}, since parsing {! end !} could undesirably
  consume input.
  For example, one may want to parse arbitrary text up to the
  beginning of a new command, beginning with "%:", but actually want
  to parse the command after (and the parser for commands first parses the string "%:").
  In that case, the {! end !} parser can be
  {! trying (lookahead (string "%:")) !}.
   *)
  val lookahead : 'a t -> 'a t
  
  (** A parser that simply yields the internal parser state. *)
  val get : state t
  
  (** Gets the location that the parser is currently at. *)
  val get_loc : Loc.t t
  
  (** Gets the current line the parser is on inside the input. *)
  val get_line : int t
  
  (** Constructs an initial parser state from given input. *)
  val initialize : item Token.t Stream.t -> state
  
  (** Runs a parser on a given state. *)
  val parse : 'a t -> state -> state * (parse_error, 'a) Either.t
end

module Make (P : ParserInfo) = struct
  type item = P.item

  module Stream = P.Stream

  module Token : Annotated.Base with type annotation = Span.t =
    Annotated.Make
      (struct
        type t = Span.t
      end)

  type semantic = string list
  
  let string_of_semantic (locs : semantic) : string =
    String.concat ", " (List.map (fun l -> "in " ^ l) locs)
  
  type state =
    { semantic_loc : semantic;
      (** Either we have a head-strict input stream or we've reached
      EOF and recorded the position of the EOF. *)
      input : (Loc.t, item Token.t HeadStrict.t) Either.t Lazy.t;
      stk : item Token.t PureStack.t;
      backtrack_enabled : bool;
      count : int;
    }
  
  let state_span (s : state) : Span.t =
    let open HeadStrict in
    let open Token in
    Either.eliminate
      (fun l -> Span.of_pair' l l)
      (fun i -> i.head.annotation)
      (Lazy.force s.input)
  
  type parse_error =
    { error_span : Span.t;
      error_semantic_loc : semantic;
      error_message : string;
      error_is_recoverable : bool;
    }
  
  let string_of_parse_error (e : parse_error) : string =
    Printf.sprintf "%s: %s %s"
      (Span.to_string e.error_span)
      e.error_message
      (string_of_semantic e.error_semantic_loc)
  
  let error_of_state (msg : string) (s : state) : parse_error =
    { error_span = state_span s;
      error_semantic_loc = s.semantic_loc;
      error_message = msg;
      error_is_recoverable = s.backtrack_enabled;
    }
  
  let push_semantic_loc (l : string) (s : state) : state =
    { s with semantic_loc = l :: s.semantic_loc }
  
  let pop_semantic_loc (s : state) : state =
    { s with semantic_loc = List.tl s.semantic_loc }
  
  exception RewindTooFar

  (** Moves the given number of tokens from the rewind stack back onto
  the input stream. *)
  let rec rewind (n : int) (s : state) : state =
    if n <= 0 then
      s
    else
      match PureStack.pop s.stk with
      | None -> raise RewindTooFar
      | Some (t, stk) ->
         rewind (n - 1)
           { s with
             input =
               begin
                 (* pull out the input eagerly to avoid putting the
                 whole state inside the closure *)
                 let i = Lazy.force s.input in
                 let x = Either.pure (HeadStrict.cons t (lazy (Either.forget i))) in
                 lazy x
               end;
             stk = stk;
             count = s.count - 1;
           }

  (** Decides whether a rewind of the given amount is possible in the
      given parser state.
      Simply put, it checks that there are enough tokens in the input buffer stack.
   *)
  let is_rewind_possible (amount : int) (stk : 'a PureStack.t) : bool =
    PureStack.length stk >= amount

  (** The type of a parser. *)
  type 'a t =
    { run : state -> state * (parse_error, 'a) Either.t }
  
  let map (f : 'a -> 'b) (p : 'a t) : 'b t =
    { run =
        fun s -> Pair.rmap (Either.rmap f) (p.run s)
    }
  
  (** Constructs a parser that doesn't affect its state and simply
  yields the given value. *)
  let pure (x : 'a) : 'a t =
    { run =
        fun s -> (s, Either.pure x)
    }
  
  (** A sequencing operator for parsers.
  This operator takes a parser on the left and a continuation on the
  right.
  The continuation uses the result of the left parser to construct a
  new parser.
  This operator passes the output state of the left parser to run the
  new parser. *)
  let ( $ ) (p : 'a t) (k : 'a -> 'b t) : 'b t =
    { run =
        fun s ->
        let (s', e) = p.run s in
        let open Either in
        match e with
        | Left err -> (s', Left err)
        | Right x -> (k x).run s'
    }
  
  (** A flipped, operator version of `map`. *)
  let ( $> ) (p : 'a t) (f : 'a -> 'b) : 'b t =
    p $ fun x -> pure (f x)
  
  (** A parser that simply yields the internal parser state. *)
  let get : state t =
    { run =
        fun s -> (s, Either.pure s)
    }
  
  (** Gets the location that the parser is currently at. *)
  let get_loc : Loc.t t =
    get $>
      fun s ->
      Either.eliminate
        (fun l -> l)
        (fun t -> t.HeadStrict.head.Token.annotation.Span.start)
        (Lazy.force s.input)
  
  (** Gets the current line the parser is on inside the input,
  i.e. the line at which the last token processed by the parser *ends
  on*. *)
  let get_line : int t =
    get_loc $> fun l -> l.Loc.line
  
  (** Runs a parser with backtracking enabled.
  This will allow alternation to succeed if this parser fails even
  while consuming input.
  Note that even in case of failure, the returned parser state will
  have its value of `backtrack_enabled` reset to its original
  value.
  While running with backtracking enabled, the parser will buffer all
  tokens into a stack in order to rewind the input.
  The stack will be flushed once the parser exits backtracking
  mode. *)
  let trying (p : 'a t) : 'a t =
    { run =
        fun s ->
        (* store the current backtracking state *)
        let b = s.backtrack_enabled in
        (* run the given parser, but with backtracking enabled *)
        let (s, e) = p.run { s with backtrack_enabled = true } in
        ( { s with
            (* restore the old backtracking state *)
            backtrack_enabled = b;
            (* preserve the stack if backtracking is still enabled;
             * otherwise, flush it. *)
            stk = if b then s.stk else PureStack.empty;
          },
          e
        )
    }
  
  (** Constructs a parser that tries the left parser, and if it fails
  *without consuming input*, tries the right parser.
  In other words, this is an alternation operator on parsers.
  In order to perform alternation *even while consuming input*, the
  parser must fail with `backtrack_enabled = true`. This can be
  achieved by using the `trying` combinator. *)
  let alt (p1 : 'a t) (p2 : 'a t) : 'a t =
    { run =
        fun s ->
        (* get the current position in the input stream *)
        let n = s.count in
        (* run the left parser *)
        let (s, e) = p1.run s in
        (* see where we are after running it *)
        let n' = s.count in
        let open Either in
        match e with
        | Left e ->
           (* If the first parser fails without consuming input, or if
              it fails with backtracking enabled *and* there're enough
              tokens on the stack, then we try the next parser.
            *)
           let d = n' - n in
           (* "Without consuming input" is verified by checking that n
              and n' are the same.
              `error_is_recoverable` is set if the parser failed while
              `backtrack_enabled = true`.
            *)
           if d = 0 || e.error_is_recoverable && is_rewind_possible d s.stk then
               p2.run (rewind d s)
           else
             (s, Left e)
        | Right x -> (s, Right x)
    }
  
  let throw (msg : string) : 'a t =
    { run =
        fun s -> (s, Either.Left (error_of_state msg s))
    }
  
  (** Observes the head of the input stream without consuming any
  new input. *)
  let peeks (s : state) : (Loc.t, item Token.t) Either.t =
    let open Either in
    let open HeadStrict in
    Lazy.force s.input $> fun { head; _ } -> head
  
  (** Pops a token from the input stream, if any.
  Returns `Nothing` if the input is already empty. *)
  let car (s : state) : 'c Token.t option * state =
    let open Either in
    let open HeadStrict in
    match s.input with
    | lazy (Left _) ->
       ( None, s )
    | lazy (Right { head; tail })  ->
         ( Some head,
           { s with
             stk =
               if s.backtrack_enabled then
                 PureStack.push head s.stk
               else
                 s.stk;
             count = s.count + 1;
             input =
               lazy
                 (match tail with
                  | lazy None -> Left head.Token.annotation.Span.stop
                  | lazy (Some x) -> Right x
                 )
               ;
           }
         )
  
  (* For `peek` and `peek'` we need to write them in eta-long form
  without using combinators due to the value restriction. *)
  
  let peek : item Token.t option t =
    { run =
        fun s -> (s, Either.pure (Either.forget (peeks s)))
    }
  
  let peek' : item Token.t t =
    { run =
        fun s ->
        let open Either in
        let (s, e) = peek.run s in
        ( s,
          e $ 
            (Maybe.eliminate
              (fun _ -> Left (error_of_state "unexpected end of input" s))
              (fun x -> pure x))
        )
    }
  
  (** A variant of `car` that pops a character from the input, if any,
  but otherwise throws a `parse_error` with the message "unexpected
  end of input". *)
  let any : item t =
    { run =
        fun s ->
        let open Token in
        match car s with
        | (None, s) -> (s, Either.Left (error_of_state "unexpected end of input" s))
        | (Some { value; _ }, s) ->
           ( s, Either.Right value )
    }
  
    (*
  (** Transforms the input state of a parser and runs it. *)
  let state (f : 'c state -> 'c state) (p : ('c, 'a) t) : ('c, 'a) t =
    fun s -> p (f s)
     *)
  
  (** Pushes the given semantic location onto the stack, runs the
  given parser, and pops the semantic location. *)
  let label (l : string) (p : 'a t) : 'a t =
    { run =
        fun s -> Pair.lmap pop_semantic_loc (p.run (push_semantic_loc l s))
    }
  
  (** Tries all the parsers from left to right.
  The same caveats regarding input consumption apply as in `alt`. *)
  let rec choice : 'a t list -> 'a t =
    function
    | [] -> throw "all choices failed"
    | (p :: ps) -> alt p (choice ps)
  
  (** `many` repeatedly applies a parser until it fails, collecting
  all results.  The parser could succeed zero times, consuming no
  input, producing an empty list.
  `some` repeatedly applies a parser until it fails, but must succeed
  at least once. *)
  let rec many (p : 'a t) : 'a list t = alt (some p) (pure [])
  and some (p : 'a t) : 'a list t =
    p $ fun x -> many p $ fun xs -> pure (x :: xs)
    
  (** Constructs a parser that consumes a single character of input,
  returning it, if that character satisfies the given predicate. *)
  let satisfy (f : item -> bool) : item t =
    let open Token in
    (peek' $> fun c -> f c.value) $ 
      function
      | true -> any (* if it passes, then consume a character *)
      | false -> throw "predicate failed"
  
  (** Matches an item from a given list. *)
  let one_of (cs : item list) : item t =
    choice (List.map (fun c -> satisfy (fun c' -> c = c')) cs)
  
  (** `many_till` repeatedly applies the given parser, testing whether
  `pend` succeeds between applications. Once `pend` succeeds, this
  parser stops.
  `some_till` does the same, but `p` must succeed at least once. *)
  let rec many_till (p : 'a t) (pend : unit t) : 'a list t =
    alt (pend $ fun _ -> pure []) (some_till p pend)
  and some_till (p : 'a t) (pend : unit t) : 'a list t =
    p $ fun x -> many_till p pend $ fun xs -> pure (x :: xs)
  
  (** Forgets the result of a parser, preserving only its effects. *)
  let void (p : 'a t) : unit t = map (fun _ -> ()) p
  
  (** A parser that succeeds only if the parser is at the beginning of
  a line. *)
  let bol : unit t =
    let open Loc in
    get_loc $
      fun { bol; offset; _ } ->
      if bol = offset then
        pure ()
      else
        throw "expected to be at beginning of line"
  
  (** A parser that succeeds only if the parser is at the end of the
  input. *)
  let eof : unit t =
    peek $
      Maybe.eliminate
        pure
        (fun _ -> throw "expected to be at end of file")
  
  (** `lookahead p` runs parser `p`, but resets the parser input state
  to its original value. `lookahead` fails if the underlying parser
  fails.
  This is useful when used in conjunction with combinators such as
  `many_till q end`, since the result of parsing `end` is unavailable.
  For example, one may want to parse arbitrary text up to the
  beginning of a new command, beginning with "%:", but actually want
  to parse the command after. In that case, the `end` parser can be
  `trying (lookahead (string "%:"))`. *)
  let lookahead (p : 'a t) : 'a t =
    { run =
        fun s ->
        let n = s.count in
        let (s, e) = p.run s in
        let n' = s.count in
        let d = n' - n in
        if PureStack.length s.stk < d then
          (s, Either.Left (error_of_state "lookahead failed" s))
        else
          (rewind (n' - n) s, e)
    }
  
  let initialize (input : item Token.t Stream.t) : state =
    { input =
        lazy
          (Maybe.eliminate
             (fun _ -> Either.Left Loc.initial)
             (fun s -> Either.Right s)
             (let module M = HeadStrict.OfBasicStream (Stream) in M.f input)
          );
      semantic_loc = [];
      backtrack_enabled = false;
      stk = PureStack.empty;
      count = 0;
    }
  
  let parse (p : 'a t) (s : state) : state * (parse_error, 'a) Either.t =
    p.run s
end

module StringParser = struct
  include Make
            (struct
              type item = char
              module Stream = IStream.AsBasicStream
            end)

  (** Constructs a parser that matches exactly the given string. *)
  let rec string (str : string) : string t =
    if str = "" then
      pure ""
    else
      let (c, str') =
        (str.[0], String.sub str 1 (String.length str - 1))
      in
      label (Printf.sprintf "= %C" c) (satisfy (fun c' -> c = c') $
        fun _ -> string str')
end
