open Support

type t =
  { location : Location.t
  ; name : String.t
  }

let make ?(location = Location.ghost) name = { location; name }

let[@inline] location { location; _ } = location

let[@inline] name { name; _ } = name

module type ORD = Ord.ORD

module Ord : ORD with type t = t = (val Ord.contramap (module String) name)

include (Ord : ORD with type t := t)

module type HASH = Hash.HASH

module Hash : HASH with type t = t =
  (val Hash.contramap (module String) name)

include (Hash : HASH with type t := t)

module Hamt = Hamt.Make (struct
  include Ord
  include Hash
end)

module type SHOW = Show.SHOW

module Set = Set.Make (Ord)
module Map = Map.Make (Ord)

module Hashtbl = Hashtbl.Make (struct
  include Ord
  include Hash
end)

module Show : SHOW with type t = t = struct
  type nonrec t = t

  let pp ppf x = Format.pp_utf_8 ppf (name x)

  let show = name
end

include (Show : SHOW with type t := t)

let find_duplicates identifiers =
  Map.empty
  |> List.fold_right
       (fun identifier identifiers_map ->
         match Map.find_opt identifier identifiers_map with
         | Option.None -> Map.add identifier [ identifier ] identifiers_map
         | Option.Some identifiers ->
             Map.add identifier (identifier :: identifiers) identifiers_map)
       identifiers
  |> Map.filter_map (fun _identifier identifiers ->
         List2.of_list identifiers)
  |> Map.bindings |> List1.of_list
