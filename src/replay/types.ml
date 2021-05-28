module type BasicStream = sig
  type 'a t

  (** The observation for streams. *)
  val observe : 'a t -> ('a * 'a t) option

  (** A way to construct a stream from a seed. *)
  val unfold : ('s -> ('a * 's) option) -> 's -> 'a t
end
