(** Centralized module for global flags.

    Think twice (no, make it thrice) about adding anything here. *)

module Subord = struct
  let dump = ref false
end

module Debug = struct
  let chatter_level = ref 1
end

module Html = struct
  let enabled = ref false
end
