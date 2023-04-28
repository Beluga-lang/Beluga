(** The [`stop] and [`go_on] flags control what happens in the presence of
    errors. In particular, the `stop flag will cause Harpoon to exit as soon
    as an error in encountered instead of continuing to process commands
    which may not make sense anymore. This is especially important when
    running tests. *)
type interaction_mode =
  [ `stop
  | `go_on
  ]

(** Controls the behaviour of saving sessions back to the signature when they
    are completed. *)
type save_mode =
  [ `save_back
  | `no_save_back
  ]

type test_kind =
  [ `incomplete
  | `complete
  ]

type test_file = private
  { filename : string
  ; kind : test_kind
  }

(** The command-line options specified to Harpoon. *)
type t = private
  { path : string
        (** The path of the signature file to load. It is expected to be
            either a [".bel"] or a [".cfg"] file. *)
  ; test_file : test_file option  (** The Harpoon test file to load. *)
  ; test_start : int option
        (** The first line from which the Harpoon test file is considered as
            input. *)
  ; test_stop : interaction_mode
        (** Whether to stop a test if there's an error. *)
  ; load_holes : bool
        (** Whether to begin immediately from holes in the file. *)
  ; save_back : save_mode
        (** Whether to save finished theorems back to the file. *)
  }

val parse_arguments : string list -> t
