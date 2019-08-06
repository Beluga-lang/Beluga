(** Create a function mapping an initial location (needed for the file
    name) and a stream of characters to a stream of located tokens. *)
val mk : unit -> (Location.t -> char Stream.t -> (Token.t * Location.t) LinkStream.t)
