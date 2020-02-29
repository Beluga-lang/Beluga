(**
   An internal module with a type for (validated) option names
   @author Clare Jang
 *)

type t =
  | Names
    of string (* Major name *)
       * string list (* Other possible names *)

let to_list name =
  match name with
  | Names (n, ns) -> n :: ns

let to_string name =
  String.concat ", " (to_list name)
