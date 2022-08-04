open Support

type t =
  { location : Location.t
  ; name : String.t
  }

let make ~location name = { location; name }

let[@inline] location { location; _ } = location

let[@inline] name { name; _ } = name

include ((val Ord.contramap (module String) name) : Ord.ORD with type t := t)
