open Support

type t =
  { location : Location.t
  ; name : String.t
  }

let make ~location name = { location; name }

let[@inline] location { location; _ } = location

let[@inline] name { name; _ } = name

module Ord : Support.Ord.ORD with type t = t =
  (val Support.Ord.contramap (module String) name)

include (Ord : Support.Ord.ORD with type t := t)

module Hash : Support.Hash.HASH with type t = t =
  (val Support.Hash.contramap (module String) name)

include (Hash : Support.Hash.HASH with type t := t)

module Hamt = Support.Hamt.Make (struct
  include Ord
  include Hash
end)
