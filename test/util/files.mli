open Support
open Beluga_syntax

(** [read_test_case_inputs ~filename] reads test case inputs from the file at
    [filename].

    A test case is optionally preceeded by comments prefixed by [%], and must
    be terminated with [;;]. *)
val read_test_case_inputs :
  filename:String.t -> (Location.t * String.t) List.t

(** [find_compiler_tests directory] is the list of all Beluga signature files
    and configuration files in [directory]. The returned file paths are
    sorted alphabetically.

    Configuration files have file extension [".cfg"]. Beluga signature files
    have file extension [".bel"].

    - If a directory contains configuration files, then only those
      configuration files are returned for that directory and its
      subdirectories.
    - If a directory does not contain configuration files, then its Beluga
      signature files are returned, along with the compiler test files in its
      subdirectories. *)
val find_compiler_tests : directory:String.t -> String.t List.t
