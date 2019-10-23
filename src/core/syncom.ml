(** Common syntax elements that are used in multiple stages of the
    Beluga syntax.
 *)

(** General snoc-lists. *)
module LF = struct
  type 'a ctx =                          (* Generic context declaration    *)
    | Empty                              (* C ::= Empty                    *)
    | Dec of 'a ctx * 'a                 (* | C, x:'a                      *)

  type svar_class = Ren | Subst

  type depend =
    | Maybe     (* implicit *)
    | No        (* explicit *)
    | Inductive (* used for induction *)
end

module Harpoon = struct
  type invoke_kind =
    [ `ih
    | `lemma
    ]

  type split_kind =
    [ `split
    | `invert
    ]

  type boxity =
    [ `boxed
    | `unboxed
    ]

  type level =
    [ `meta
    | `comp
    ]
end
