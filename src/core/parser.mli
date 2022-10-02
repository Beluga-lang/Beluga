open Support
open Syntax.Prs

type input = (Location.t * Token.t) LinkStream.t

type state

(** Constructs the initial state for a parser by providing an input stream. *)
val initial_state : input -> state

type error

exception
  Error of
    { state : state
    ; cause : error
    }

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

val span : 'a t -> (Location.t * 'a) t

(***** Exported helpers operations *****)

(** Transforms a parse result with a function. *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** Flipped, operator form of `map`. *)
val ( $> ) : 'a t -> ('a -> 'b) -> 'b t

(** Runs the parser, but capturing failure. *)
val maybe : 'a t -> 'a option t

(** Alternation between parsers.

    Runs `p1`. If it fails, p2 is run if one of the following is true.

    - p1 failed without consuming any input.
    - p2 failed with backtracking enabled.

    Backtracking is enabled by the `trying` combinator. *)
val alt : 'a t -> 'a t -> 'a t

val choice : 'a t List.t -> 'a t

val interactive_harpoon_command : Harpoon.Repl.Command.t t

val interactive_harpoon_command_sequence : Harpoon.Repl.Command.t List.t t

val next_theorem : [ `quit | `next of Identifier.t ] t

val lf_object : LF.Object.t t

val clf_object : CLF.Object.t t

val clf_context_object : CLF.Context_object.t t

val schema_object : Meta.Schema_object.t t

val meta_thing : Meta.Thing.t t

val meta_context : Meta.Context_object.t t

val comp_sort_object : Comp.Sort_object.t t

val comp_pattern_object : Comp.Pattern_object.t t

val comp_expression_object : Comp.Expression_object.t t

val comp_context : Comp.Context_object.t t

val sgn_decl : Signature.Declaration.t t

val sgn : Signature.t t

val trust_totality_declaration : Signature.Totality.Declaration.t t

val named_totality_declaration : Signature.Totality.Declaration.t t

val numeric_totality_declaration : Signature.Totality.Declaration.t t

val totality_declaration : Signature.Totality.Declaration.t t
