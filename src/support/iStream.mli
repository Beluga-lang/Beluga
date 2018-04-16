type 'a t =
  { next : unit -> ('a * 'a t) Maybe.t }

type 'a istream = 'a t

val map : ('a -> 'b) -> 'a t -> 'b t

(** Prepend an item to a stream. *)
val cons : (unit -> 'a) -> 'a t -> 'a t

(** Consumes a channel into a stream. *)
val of_channel : in_channel -> char t

(** Extracts a list of leading elements from a stream satisfying a predicate.

{i Warning:} if the stream is infinite and all its items satisfy the
predicate, then this function will never terminate.
 *)
val take_while : ('a -> bool) -> 'a t -> 'a list * ('a * 'a t) Maybe.t

(** A string variant of {!IStream.take_while}. *)
val take_while_str : (char -> bool) -> char t -> string * (char * char t) Maybe.t

(** Constructs an empty stream. *)
val empty : 'a t

module AsBasicStream : Types.BasicStream
       with type 'a t = 'a istream
