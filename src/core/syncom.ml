(** Common syntax elements that are used in multiple stages of the
    Beluga syntax.
 *)

module Loc = Location

module Common = struct
  type plicity =
    [ `implicit
    | `explicit
    ]

  let is_explicit : plicity -> bool = function
    | `explicit -> true
    | _ -> false

  let is_implicit : plicity -> bool = function
    | `implicit -> true
    | _ -> false
end

(** General snoc-lists. *)
module LF = struct
  include Common

  type 'a ctx =                          (* Generic context declaration    *)
    | Empty                              (* C ::= Empty                    *)
    | Dec of 'a ctx * 'a                 (* | C, x:'a                      *)

  type svar_class = Ren | Subst

  type depend =
    | Maybe     (* implicit *)
    | No        (* explicit *)
    | Inductive (* used for induction *)

  module Depend = struct
    let equals d1 d2 = match d1, d2 with
      | Maybe, Maybe -> true
      | No, No -> true
      | Inductive, Inductive -> true
      | _ -> false

    let of_plicity : plicity -> depend = function
      | `implicit -> Maybe
      | `explicit -> No

    let to_plicity : depend -> plicity = function
      | Maybe -> `implicit
      | No -> `explicit
      | Inductive ->
         Error.violation
           "[Depend] [to_plicity] Inductive is impossible"

    (** Variant of to_plicity that does not fail on Inductive, instead
        sending it to `explicit.
     *)
    let to_plicity' : depend -> plicity = function
      | Inductive -> `explicit
      | d -> to_plicity d
  end
end

module Comp = struct
  include Common

  type unbox_modifier =
    [ `strengthened
    ]

  type case_pragma = PragmaCase | PragmaNotCase

  type context_case =
    | EmptyContext of Loc.t
    | ExtendedBy of Loc.t * int (* specifies a schema element *)

  type case_label =
    | NamedCase of Loc.t * Id.name
    | BVarCase of Loc.t
    | ContextCase of context_case
    | PVarCase of
        Loc.t
        * int (* schema element number (1-based) *)
        * int option (* the number of the projection, if any (1-based) *)

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
