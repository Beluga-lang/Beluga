open Support

type t =
  { location : Location.t
  ; name : String.t
  }

let make ?(location = Location.ghost) name = { location; name }

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

module Set = Set.Make (Ord)

module Show : Support.Show.SHOW with type t = t =
  (val Support.Show.contramap (module String) name)

include (Show : Support.Show.SHOW with type t := t)

let inspect_duplicates identifiers =
  let duplicates, set =
    List.fold_left
      (fun (duplicates, encountered_identifiers) addition ->
        if Set.mem addition encountered_identifiers then
          let duplicates' = addition :: duplicates in
          (duplicates', encountered_identifiers)
        else
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
