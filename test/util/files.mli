open Beluga_syntax

(** [read_test_case_inputs ~filename] reads test case inputs from the file at
    [filename].

    A test case is optionally preceeded by comments prefixed by [%], and must
    be terminated with [;;]. *)
val read_test_case_inputs : filename:string -> (Location.t * string) list
