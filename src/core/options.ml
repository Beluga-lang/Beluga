(** Centralized module for global flags.

    Think twice (no, make it thrice) about adding anything here.
 *)

module Testing = struct
  let print_external_syntax = ref false
end

module PrinterControl = struct
  type subst_style =
    [ `natural
    | `de_bruijn
    ]

  let implicit = ref false
  let subst_style : subst_style ref = ref `natural
end

module Subord = struct
  let dump = ref false
end

module Debug = struct
  let chatter_level = ref 1
end

module HTML = struct
  type css_file = [ `normal | `none | `file of string ]
  let generate = ref false
  let printing = ref false
  let filename = ref (Some "out.html")
  let css : css_file ref = ref `normal
end

module Monitor = struct
  (* TODO this should be refactored as a single variable holding an
     option containing the path to dump to. None signifies stdout.
     -je
   *)

  (** on: is true if we call the interpreter with argument: +t
      The result is to print the timings to stdout when signature
      reconstruction ends.
   *)
  let on = ref false

  (** onf: is true if we call the interpreter with argument: +tfile
      The result is to dump the timing to a file when signature
      reconstruction ends.
   *)
  let onf = ref false

  (** Decides whether either timing mode (stdout or file) is active *)
  let is_active () = !on || !onf
end
