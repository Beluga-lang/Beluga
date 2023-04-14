(** Hashable types. *)

(** Module type for hashable types.

    Hashable types may be used as keys for {!Hashtbl.Make}. *)
module type HASH = sig
  type t

  (** [hash e] is the hash code computed for [e].

      If [e1] and [e2] as equal, then [hash e1] and [hash e2] must be equal. *)
  val hash : t -> int
end

module Make (T : sig
  type t
end) : HASH with type t = T.t

(** If [val f : 't -> 's], then [contramap hash f] is an instance of {!HASH}
    for values of type ['t] by the {!HASH} instance [hash] for values of type
    ['s]. *)
val contramap :
     (module HASH with type t = 's)
  -> ('t -> 's)
  -> (module HASH with type t = 't)
