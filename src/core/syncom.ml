(** Common syntax elements that are used in multiple stages of the
    Beluga syntax.
 *)

(** General snoc-lists. *)
module LF = struct
  type 'a ctx =                          (* Generic context declaration    *)
    | Empty                              (* C ::= Empty                    *)
    | Dec of 'a ctx * 'a                 (* | C, x:'a                      *)
end

module Harpoon = struct
  type invoke_kind =
    [ `ih
    | `lemma
    ]
end
