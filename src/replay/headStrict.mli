type 'a t =
  { head : 'a;
    tail : 'a t option Lazy.t;
  }

(** Construct a head-strict stream from an initial state and a state
transformer. *)
val unfold : 's -> ('s -> ('a * 's) option) -> 'a t option

module OfBasicStream (S : Types.BasicStream) : sig
  val f : 'a S.t -> 'a t option
end

(** Prepend a value to a head-strict stream. *)
val cons : 'a -> 'a t option Lazy.t -> 'a t
