(**
   An internal module with a type for (validated) option names
   @author Clare Jang
 *)

type t =
  { canonical: string
  ; aliases: string list
  }

let to_list { canonical; aliases } =
  canonical :: aliases

let to_string name =
  String.concat ", " (to_list name)
