module type BasicStream = sig
  type 'a t

  (** The observation for streams. *)
  val observe : 'a t -> ('a * 'a t) Maybe.t

  (** A way to construct a stream from a seed. *)
  val unfold : ('s -> ('a * 's) Maybe.t) -> 's -> 'a t
end
                        
