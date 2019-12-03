type get_input = string -> string option -> unit -> string option
type set_hints = (string -> (string * bool) option) -> unit
type t =
  { get_input : get_input
  ; set_hints : set_hints
  }

val create : Options.test_file option -> int option -> t
