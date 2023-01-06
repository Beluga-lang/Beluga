open Support

module Make (Location : sig
  type t

  val between : start:t -> stop:t -> t

  val raise_at : t List1.t -> exn -> 'a
end) (Token : sig
  type t

  val location : t -> Location.t
end) : sig
  (** The type of input to the parser.

      An input is a persistent sequence of tokens and their locations. That
      is, the sequence can be used as many times as desired, producing the
      same elements every time, just like an immutable list.

      To achieve this easily, use {!Stdlib.Seq.memoize}. *)
  type input = Token.t Seq.t

  type state

  val initial_state : ?last_location:Location.t -> input -> state

  type +'a t = state -> state * ('a, exn) result

  type 'a parser = 'a t

  include Monad.MONAD with type 'a t := 'a t

  include Functor.FUNCTOR with type 'a t := 'a t

  include Apply.APPLY with type 'a t := 'a t

  val run : 'a t -> state -> state * ('a, exn) result

  val run_exn : 'a t -> state -> state * 'a

  val catch :
    'a t -> (state * ('a, exn) result -> state * ('b, exn) result) -> 'b t

  val fail : exn -> 'a t

  val only : 'a t -> 'a t

  val span : 'a t -> (Location.t * 'a) t

  val maybe : 'a t -> 'a option t

  val maybe_default : 'a t -> default:'a -> 'a t

  val void : 'a t -> unit t

  val many : 'a t -> 'a list t

  val some : 'a t -> 'a List1.t t

  val sep_by0 : 'a t -> unit t -> 'a list t

  val sep_by1 : 'a t -> unit t -> 'a List1.t t

  val traverse : ('a -> 'b t) -> 'a list -> 'b list t

  val traverse_void : ('a -> unit t) -> 'a list -> unit t

  val trying : 'a t -> 'a t

  val alt : 'a t -> 'a t -> 'a t

  val choice : 'a t List.t -> 'a t

  val satisfy : (Token.t -> ('a, exn) result) -> 'a t

  val eoi : unit t

  val labelled : string -> 'a t -> 'a t

  val renamed : string -> 'a t -> 'a t
end

module Shunting_yard = Shunting_yard
