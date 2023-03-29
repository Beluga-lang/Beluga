open Support

(** {1 Transforms} *)

let rec without_field field_to_erase json =
  match json with
  | `Null
  | `Bool _
  | `Intlit _
  | `String _
  | `Float _
  | `Int _
  | `Variant (_, Option.None) ->
      json
  | `Tuple xs ->
      let xs' = List.map (without_field field_to_erase) xs in
      `Tuple xs'
  | `List xs ->
      let xs' = List.map (without_field field_to_erase) xs in
      `List xs'
  | `Assoc xs ->
      let xs' =
        List.filter_map
          (fun (field, data) ->
            if String.(field = field_to_erase) then Option.none
            else
              let data' = without_field field_to_erase data in
              Option.some (field, data'))
          xs
      in
      `Assoc xs'
  | `Variant (l, Option.Some x) ->
      let x' = without_field field_to_erase x in
      `Variant (l, Option.some x')

let without_locations json = without_field "location" json

(** {1 Support} *)

let[@inline] json_of_association e = `Assoc e

let[@inline] json_of_int i = `Int i

let[@inline] json_of_bool b = `Bool b

let[@inline] json_of_string s = `String s

let[@inline] json_of_list f l = `List (List.map f l)

let[@inline] json_of_list1 f l = json_of_list f (List1.to_list l)

let[@inline] json_of_list2 f l = json_of_list f (List2.to_list l)

let[@inline] json_of_variant ~name ~data =
  `List [ json_of_string name; json_of_association data ]

let[@inline] json_of_option v =
  Fun.(Option.map v >> Option.value ~default:`Null)
