(** The `stop and `go_on flag control what happens in the presence of errors.
    In particular, the `stop flag will cause Harpoon to exit as soon
    as an error in encountered instead of continuing to process
    commands which may not make sense anymore.
    This is especially important when running tests.
 *)
type interaction_mode = [ `stop | `go_on ]

(** Controls the behaviour of saving sessions back to the signature
    when they are completed. *)
type save_mode = [ `save_back | `no_save_back ]

type test_kind = [ `incomplete | `complete ]
type test_file = string * test_kind

type ('a, 'b) t =
  { path : 'a (* the path of the signature file to load, could be a cfg *)
  ; all_paths : 'b (* the list of paths resolved from the signature file to load *)
  ; test_file : test_file option (* the harpoon test file to load *)
  ; test_start : int option (* the first line from which the harpoon test file is considered as input *)
  ; test_stop : interaction_mode (* whether to stop a test if there's an error *)
  ; load_holes : bool (* whether begin immediately from holes in the file *)
  ; save_back : save_mode (* whether save finished theorems back to the file *)
  }

type parsed_t
type elaborated_t =
  (string, string list) t

val parse_arguments : string list -> parsed_t
val elaborate : parsed_t -> elaborated_t
