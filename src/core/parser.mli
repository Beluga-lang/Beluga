open Support

module Loc = Location
module Comp = Syntax.Ext.Comp
module LF = Syntax.Ext.LF

type input = (Loc.t * Token.t) LinkStream.t
type state

(** Constructs the initial state for a parser by providing an input stream. *)
val initial_state : input -> state

type error

exception Error of state * error

(***** Type of parse results. *****)

type 'a result

(* Eliminators for `result`: *)

(** Extracts the result of the parser, raising an exception if it failed. *)
val extract : state * 'a result -> 'a

(** Handles parse errors. *)
val handle : (error -> 'b) -> ('a -> 'b) -> 'a result -> 'b

val to_either : 'a result -> (error, 'a) Either.t

val print_error : Format.formatter -> error -> unit

(***** Parser type *****)

type 'a t

(** Type of located values, i.e. values paired with their location. *)
type 'a locd = Loc.t * 'a

(* Eliminator for parsers: *)
(** Runs a parser on a given state, resulting in a final state and a result. *)
val run : 'a t -> state -> state * 'a result

(** Require end of input after the given parser. *)
val only : 'a t -> 'a t

val span : 'a t -> 'a locd t

(***** Exported helpers operations *****)

(** Transforms a parse result with a function. *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** Flipped, operator form of `map`. *)
val ($>) : 'a t -> ('a -> 'b) -> 'b t

(** Runs the parser, but capturing failure. *)
val maybe : 'a t -> 'a option t

(** Alternation between parsers.

    Runs `p1`. If it fails, p2 is run if one of the following is true.
    - p1 failed without consuming any input.
    - p2 failed with backtracking enabled.

    Backtracking is enabled by the `trying` combinator.
 *)
val alt : 'a t -> 'a t -> 'a t

(***** Exported productions *****)

(** Parser for a full Beluga signature. *)
val sgn : Syntax.Ext.Sgn.decl list t

val name : Id.name t

(** Parser for a Harpoon command. *)
val interactive_harpoon_command : Syntax.Ext.Harpoon.command t
val interactive_harpoon_command_sequence : Syntax.Ext.Harpoon.command list t

val trust_order : Comp.total_dec t
val total_order : 'a Comp.generic_order t -> 'a Comp.generic_order t
val numeric_total_order : Syntax.Ext.Comp.numeric_order t
val optional_numeric_total_order : Syntax.Ext.Comp.numeric_order option t

(** Parser for computation type. *)
val cmp_typ : Comp.typ t

(** Parser for computation checkable expressions. *)
val cmp_exp_chk : Comp.exp_chk t

(** Parser for computation synthesizable expressions. *)
val cmp_exp_syn : Comp.exp_syn t

(** Parser for the next theorem name in Harpoon. *)
val next_theorem : [ `quit | `next of Id.name ] t

  (*
(* exports for debugging! *)
val cmp_kind : Comp.kind t
val cmp_exp_syn : Comp.exp_syn t
val clf_typ_rec_block : LF.typ_rec t
   *)
