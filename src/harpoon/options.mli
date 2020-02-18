type test_kind = [ `incomplete | `complete ]
type test_file = string * test_kind

type ('a, 'b) t =
  { path : 'a (* the path of the signature file to load, could be a cfg *)
  ; all_paths : 'b (* the list of paths resolved from the signature file to load *)
  ; test_file : test_file option (* the harpoon test file to load *)
  ; test_start : int option (* the first line from which the harpoon test file is considered as input *)
  ; test_stop : [ `stop | `go_on ] (* whether to stop a test if there's an error *)
  ; load_holes : bool (* whether begin immediately from holes in the file *)
  ; save_back : bool (* whether save finished theorems back to the file *)
  }

type partial_t
type valid_t
type elaborated_t =
  (string, string list) t

val initial_t : partial_t

val parse_arguments : string list -> partial_t
val validate : partial_t -> valid_t
val elaborate : valid_t -> elaborated_t
