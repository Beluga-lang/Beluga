include module type of Gen

(** Converts a string into a generator yielding individual characters. *)
val of_string : string -> char Gen.t

(** Constructs a generator yielding successive lines from an input channel
    until it encounters an error. *)
val of_in_channel_lines : in_channel -> string Gen.t

(** [drop_lines g ln] drops the first [ln] elements from the generator [g]. *)
val drop_lines : 'a Gen.t -> int -> unit

(** Transform a character generator into a line generator. This function
    assumes unix line endings, so it is not portable.

    This function also imposes a maximum line length specified via the
    [buffer_size] optional argument. (So that it uses constant memory.) *)
val line_generator : ?buffer_size:int -> char Gen.t -> string Gen.t

(** Sequence a list of generators into one generator. Of course, if any
    generator in the sequence is infinite, subsequent generators will never
    be pulled from. *)
val sequence : 'a Gen.t list -> 'a Gen.t

(** [iter_through f g] is a generator that will execute [f] on each element
    of [g] before yielding it. *)
val iter_through : ('a -> unit) -> 'a Gen.t -> 'a Gen.t
