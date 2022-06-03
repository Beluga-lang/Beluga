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

let contramap (type t s) (hash : (module HASH with type t = s))
    (f : t -> s) =
  (module struct
    type nonrec t = t

    let hash =
      let (module Hash) = hash in
      fun x -> Hash.hash (f x)
  end : HASH
    with type t = t)
