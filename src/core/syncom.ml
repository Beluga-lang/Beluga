(** Common syntax elements that are used in multiple stages of the
    Beluga syntax.
 *)

module Loc = Location

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

module Comp = struct
  type case_pragma = PragmaCase | PragmaNotCase

  type 'a generic_context_case =
    | EmptyContext of Loc.t
    | ExtendedBy of Loc.t * 'a

  type plicity =
    [ `implicit
    | `explicit
    ]

  type 'ctx_case generic_case_label =
    | NamedCase of Loc.t * Id.name
    | ContextCase of 'ctx_case
    | PVarCase of Loc.t * int option (* the number of the projection, if any *)

  type boxity =
    [ `boxed
    | `unboxed
    ]
end

module Harpoon = struct
  type defer_kind =
    [ `subgoal
    | `theorem
    ]

  type invoke_kind =
    [ `ih
    | `lemma
    ]

  type split_kind =
    [ `split
    | `invert
    | `impossible
    ]

  type level =
    [ `meta
    | `comp
    ]
end
