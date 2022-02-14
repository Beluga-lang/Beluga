type t =
  { canonical : string
  ; aliases : string list
  }

val to_list : t -> string list

val to_string : t -> string
