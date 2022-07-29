(** Common syntax elements that are used in multiple stages of the
    Beluga syntax.
 *)
open Support

(** General snoc-lists. *)
module LF = struct
  type 'a ctx =                          (* Generic context declaration    *)
    | Empty                              (* C ::= Empty                    *)
    | Dec of 'a ctx * 'a                 (* | C, x:'a                      *)

  type svar_class = Ren | Subst
end

module Comp = struct
  type unbox_modifier =
    [ `strengthened
    ]

  type case_pragma = PragmaCase | PragmaNotCase

  type context_case =
    | EmptyContext of Location.t
    | ExtendedBy of Location.t * int (* specifies a schema element *)

  type case_label =
    | NamedCase of Location.t * Name.t
    | BVarCase of Location.t
    | ContextCase of context_case
    | PVarCase
      of Location.t
         * int (* schema element number (1-based) *)
         * int option (* the number of the projection, if any (1-based) *)

  type 'a generic_order =
    | Arg of 'a                                    (* O ::= x                    *)
    | Lex of 'a generic_order list                 (*     | {O1 .. On}           *)
    | Simul of 'a generic_order list               (*     | [O1 .. On]           *)
  (* Note: Simul is currently unused. It doesn't even have a parser. -je *)

  (** Type specified in an interactive use of `suffices` *)
  type 'a generic_suffices_typ =
    [ `exact of 'a (* user specified an exact type annotation *)
    | `infer of Location.t (* user specified `_` and expects the type to be known *)
    ]

  let map_suffices_typ (f : 'a -> 'b) : 'a generic_suffices_typ -> 'b generic_suffices_typ =
    function
    | `exact x -> `exact (f x)
    | `infer loc -> `infer loc

  let rec map_order (f : 'a -> 'b) : 'a generic_order -> 'b generic_order =
    function
    | Arg x -> Arg (f x)
    | Lex xs -> Lex (List.map (map_order f) xs)
    | Simul xs -> Simul (List.map (map_order f) xs)
end
