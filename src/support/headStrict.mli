type 'a t =
  { head : 'a;
    tail : unit -> 'a t option;
  }

(** Construct a head-strict stream from an initial state and a state
transformer. *)
val unfold : 's -> ('s -> ('a * 's) option) -> 'a t option

module OfBasicStream (S : Types.BasicStream) : sig
  val f : 'a S.t -> 'a t option
end

(** Prepend a value to a head-strict stream. *)
val cons : 'a -> (unit -> 'a t option) -> 'a t
