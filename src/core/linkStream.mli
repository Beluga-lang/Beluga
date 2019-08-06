type 'a t

val of_stream : 'a Stream.t -> 'a t
val of_gen : 'a Gen.t -> 'a t
val iter : ('a -> unit) -> 'a t -> unit

val observe : 'a t -> ('a * 'a t) option
val position : 'a t -> int
