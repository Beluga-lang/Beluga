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
