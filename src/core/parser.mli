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

(* Eliminator for parsers: *)
(** Runs a parser on a given state, resulting in a final state and a result. *)
val run : 'a t -> state -> state * 'a result

(** Require end of input after the given parser. *)
val only : 'a t -> 'a t

(***** Exported productions *****)

(** Parser for a full Beluga signature. *)
val sgn : Syntax.Ext.Sgn.decl list t

(** Parser for a Harpoon command. *)
val harpoon_command : Syntax.Ext.Harpoon.command t

val numeric_total_order : Syntax.Ext.Comp.numeric_order t
val optional_numeric_total_order : Syntax.Ext.Comp.numeric_order option t

(** Parser for computation type. *)
val cmp_typ : Comp.typ t

(** Parser for computation checkable expressions. *)
val cmp_exp_chk : Comp.exp_chk t

(** Parser for computation synthesizable expressions. *)
val cmp_exp_syn : Comp.exp_syn t

  (*
(* exports for debugging! *)
val cmp_kind : Comp.kind t
val cmp_exp_syn : Comp.exp_syn t
val clf_typ_rec_block : LF.typ_rec t
   *)
