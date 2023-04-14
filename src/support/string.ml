include Stdlib.String

let empty = ""

let unpack s =
  let n = length s in
  let rec unpack i return =
    if i < n then
      let c = get s i in
      unpack (i + 1) (fun cs -> return (c :: cs))
    else return []
  in
  unpack 0 Fun.id

let pack cs =
  let b = Buffer.create 16 in
  List.iter (Buffer.add_char b) cs;
  Buffer.contents b

let drop n s = sub s n (length s - n)

module type ORD = Ord.ORD

module Ord : Ord.ORD with type t = t = Ord.Make (Stdlib.String)

include (Ord : ORD with type t := t)

module type HASH = Hash.HASH

module Hash : HASH with type t := t = Hash.Make (Stdlib.String)

include (Hash : HASH with type t := t)

include (
  Show.Make (struct
    type nonrec t = t

    let pp = Format.pp_print_string
  end) :
    Show.SHOW with type t := t)

module Set = Set.Make (Stdlib.String)
module Map = Map.Make (Stdlib.String)

module Hashtbl = Hashtbl.Make (struct
  include Ord
  include Hash
end)

let is_empty = ( = ) empty

let is_non_empty = ( <> ) empty
