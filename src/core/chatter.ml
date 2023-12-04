open Support

let level : int ref = ref 1

let print lvl f =
  if lvl <= !level
  then (f Format.std_formatter; Format.pp_print_flush Format.std_formatter ())
  else ()
