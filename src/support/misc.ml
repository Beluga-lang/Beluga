(** Totally miscellaneous functions. *)

(** Converts a list of characters into an equivalent string. *)
let string_pack (cs : char list) : string =
  String.concat "" (List.map (String.make 1) cs)
