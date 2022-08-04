open Support

type t =
  { location : Location.t
  ; name : Identifier.t
  ; modules : Identifier.t List.t
  }

let make ~location ?(modules = []) name = { location; name; modules }

let[@inline] location { location; _ } = location

let[@inline] name { name; _ } = name

let[@inline] modules { modules; _ } = modules
