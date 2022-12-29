open Beluga_syntax

(** [with_pp_to_file filename handler] calls [handler] with a pretty-printer
    to the file at [filename]. The contents of the file are replaced by the
    outputs printed it. *)
val with_pp_to_file : string -> (Format.formatter -> unit) -> unit

(** [read_test_case_inputs ~filename] reads test cases terminated by [;;]
    from the file at [filename]. Lines in the file comprised only of
    whitespaces or starting with [%] are ignored. *)
val read_test_case_inputs : filename:string -> (Location.t * string) list
