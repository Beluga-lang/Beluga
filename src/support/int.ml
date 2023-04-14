include Stdlib.Int

let of_string = Stdlib.int_of_string

let of_string_opt = Stdlib.int_of_string_opt

module type ORD = Ord.ORD

module Ord : ORD with type t = t = Ord.Make (Stdlib.Int)

include (Ord : ORD with type t := t)

module type HASH = Hash.HASH

module Hash : HASH with type t = t = Hash.Make (Stdlib.Int)

include (Hash : HASH with type t := t)

include (
  Show.Make (struct
    type nonrec t = t

    let pp = Format.pp_print_int
  end) :
    Show.SHOW with type t := t)

module Set = Set.Make (Ord)
module Map = Map.Make (Ord)
