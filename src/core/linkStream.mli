(** The LinkStream module defines a type to represent a memoized
    stream of values of a specific type. This is in contrast with
    modules such as Gen and Seq which are not memoizing.

    Brief comparison between the three approaches:
    * Gen.tt wraps a function unit -> 'a that when called
      successively, returns subsequent elements from the stream. Such
      a stream has no notion of "rewinding" or capturing the stream at
      a specific point, but it uses as little structure as possible
      (it's just a function) and so is probably more efficient.
    * Seq.t uses a list-like structure in which cons-cells suspend the
      tail using a function from unit. These functions from unit may
      generate the tail using side-effects, e.g. reading from a file,
      so they are typically unsafe to reread unless you have external
      purity guarantees about the stream.
    * LinkStream.t uses a list-like structure in which
      cons-cells suspend the tail using Lazy.t. This means that once a
      cell is generated, regenerating it merely returns the computed
      value. This is probably the least performant option, since
      Lazy.t needs to do additional work to store the computed results.
      However, it gives us a purity guarantee even if the stream is
      generated using side-effects.

    The purpose of this module is to serve as the input stream for the
    parser combinator library in parser.ml. The reason I developed
    LinkStream instead of using Seq or Gen is precisely that a
    rewinding capability is needed to implement alternation. In
    another parser combinator library (support/mupc.ml) uses OCaml's
    built-in Stream.t, and in order to support rewinding needed to use
    an internal token stack to buffer observed inputs when in a
    backtracking context. This is perhaps more efficicient, as the
    stack is not constructed normally, (so we have more fine-grain
    control over memory usage,) but it is significantly more
    complicated than just using closures to hold on to previous input
    streams.
 *)

type 'a t

(** Converts a Stream into a LinkStream. *)
val of_stream : 'a Stream.t -> 'a t

(** Converts a Gen into a LinkStream. *)
val of_gen : 'a Gen.t -> 'a t

(** Execute a side-effect along with every cell.
    When a cell is computed for the first time, this function will run
    on the computed result.  *)
val iter : ('a -> unit) -> 'a t -> unit

(** Decides if the stream is empty, returning the head and stream tail
    if it is not.
 *)
val observe : 'a t -> ('a * 'a t) option

(** Tells the current position in the stream, as the 0-based index of
    the next cell.
 *)
val position : 'a t -> int
