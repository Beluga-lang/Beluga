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

module Show : SHOW with type t = t =
  (val Show.contramap (module String) name)

include (Show : SHOW with type t := t)

let inspect_duplicates identifiers =
  let duplicates, set =
    List.fold_left
      (fun (duplicates, encountered_identifiers) addition ->
        match Set.find_opt addition encountered_identifiers with
        | Option.Some hit ->
            let duplicates' = addition :: hit :: duplicates in
            (duplicates', encountered_identifiers)
        | Option.None ->
            let encountered_identifiers' =
              Set.add addition encountered_identifiers
            in
            (duplicates, encountered_identifiers'))
      ([], Set.empty) identifiers
  in
  match duplicates with
  | e1 :: e2 :: es -> (Option.some (List2.from e1 e2 es), set)
  | [] -> (Option.none, set)
  | _ -> Error.violation "[Identifier.inspect_duplicates]"

let find_duplicates = Fun.(inspect_duplicates >> Pair.fst)
