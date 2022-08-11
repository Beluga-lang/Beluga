module type HASH = sig
  type t

  val hash : t -> int
end

module Make (T : sig
  type t
end) : HASH with type t = T.t = struct
  include T

  let hash = Hashtbl.hash
end

let contramap (type t s) (module Hash : HASH with type t = s) (f : t -> s) =
  (module struct
    type nonrec t = t

    let hash x = Hash.hash (f x)
  end : HASH
    with type t = t)
