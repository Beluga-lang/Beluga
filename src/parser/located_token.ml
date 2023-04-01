open Beluga_syntax

type token = Token.t

type location = Location.t

type t =
  { location : location
  ; token : token
  }

let make ~location ~token = { location; token }

let[@inline] location t = t.location

let[@inline] token t = t.token
