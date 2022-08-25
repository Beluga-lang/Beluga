module type SHOW = sig
  type t

  val pp : Format.formatter -> t -> unit

  val show : t -> string
end

module Make (T : sig
  type t

  val pp : Format.formatter -> t -> unit
end) : SHOW with type t = T.t = struct
  include T

  let show = Format.stringify pp
end

let contramap (type t t') (module Show : SHOW with type t = t') (f : t -> t')
    =
  (module Make (struct
    type nonrec t = t

    let pp ppf x = Show.pp ppf (f x)
  end) : SHOW
    with type t = t)
