(** Module type for types with functions for pretty-printing and converting
    values to readable strings. *)
module type SHOW = sig
  type t

  (** [pp ppf t] emits [t] pretty-printed to [ppf]. *)
  val pp : Format.formatter -> t -> unit

  (** [show t] pretty-prints [t] to a string. *)
  val show : t -> string
end

(** Functor building an implementation of {!SHOW} given a type with a
    pretty-printer. *)
module Make (T : sig
  type t

  val pp : Format.formatter -> t -> unit
end) : SHOW with type t = T.t

(** If [val f : 't -> 's], then [contramap show f] is an instance of {!SHOW}
    for values of type ['t] by the {!SHOW} insance [show] for values of type
    ['s]. *)
val contramap :
     (module SHOW with type t = 's)
  -> ('t -> 's)
  -> (module SHOW with type t = 't)
