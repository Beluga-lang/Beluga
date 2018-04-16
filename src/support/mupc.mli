(** A parser combinator library.

Microparsec (abbreviated {i mupc} since {i pc} is the symbol for the
parsec unit) is an OCaml implementation of a parser combinator library
similar to Haskell's {i Parsec} library.

Microparsec uses a committed-by-default parsing strategy, whereby
backtracking is selectively enabled when desired. Backtracking is a
relatively expensive operation since Microparsec will buffer all
tokens into a stack until backtracking becomes disabled. That's why
backtracking is opt-in in Microparsec.

Microparsec supports parsing arbitrary streams, not just streams of
characters. Furthermore, Microparsec supports on-line parsing: the
input does not need to be fully available.
 *)

module type ParserInfo = sig
  type item
  module Stream : Types.BasicStream
end

module type Base = sig
  (** The basic elements processed by the parser.
      Generally for a simple text parser, this is {! char !}
   *)
  type item

  module Stream : Types.BasicStream

  module Token : Annotated.Base with type annotation = Span.t

  (**
  A semantic location, provided by the user of the parser, used to
  generate nice error messages, specifically of the form
  "Parse error at (line, col) in FOO in BAR in XYZ in ..."
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
  {!Maybe.Nothing} if the parser has reached the end of the input. *)
  val peek : item Token.t Maybe.t t
  
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
                     
module Make (P : ParserInfo) : Base
       with type item = P.item
       with module Stream = P.Stream

module StringParser : sig
  include Base
          with type item = char
          with module Stream = IStream.AsBasicStream

  (** Parses the given string. *)
  val string : string -> string t
end

