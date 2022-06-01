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

let contramap (type t t') (hash : (module HASH with type t = t'))
    (f : t -> t') =
  (module struct
    type nonrec t = t

    let hash x =
      let (module Hash) = hash in
      Hash.hash (f x)
  end : HASH
    with type t = t)
