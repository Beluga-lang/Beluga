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
    | BVarCase of Loc.t
    | ContextCase of 'ctx_case
    | PVarCase of
        Loc.t
        * int (* schema element number (1-based) *)
        * int option (* the number of the projection, if any (1-based) *)

  type boxity =
    [ `boxed
    | `unboxed
    ]

 type 'a generic_order =
   | Arg of 'a                             (* O ::= x                    *)
   | Lex of 'a generic_order list                 (*     | {O1 .. On}           *)
   | Simul of 'a generic_order list               (*     | [O1 .. On]           *)
 (* Note: Simul is currently unused. It doesn't even have a parser. -je *)

 let rec map_order (f : 'a -> 'b) : 'a generic_order -> 'b generic_order =
   function
   | Arg x -> Arg (f x)
   | Lex xs -> Lex (List.map (map_order f) xs)
   | Simul xs -> Simul (List.map (map_order f) xs)
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
