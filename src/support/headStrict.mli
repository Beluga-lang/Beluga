type 'a t =
  { head : 'a;
    tail : unit -> 'a t Maybe.t;
  }

(** Construct a head-strict stream from an initial state and a state
transformer. *)
val unfold : 's -> ('s -> ('a * 's) Maybe.t) -> 'a t Maybe.t

module OfBasicStream (S : Types.BasicStream) : sig
  val f : 'a S.t -> 'a t Maybe.t
end

(** Prepend a value to a head-strict stream. *)
val cons : 'a -> (unit -> 'a t Maybe.t) -> 'a t
