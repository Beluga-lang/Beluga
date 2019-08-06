open Syntax.Int

type hole_id

(** Converts a hole identifier to a string representation. *)
val string_of_hole_id : hole_id -> string

(* Isomorphic to `string option`. *)
type hole_name =
  | Anonymous
  | Named of string

val name_of_option : string option -> hole_name
val option_of_name : hole_name -> string option

(** A strategy for retrieving a hole. *)
type lookup_strategy

(** Gets a string representation of the given strategy. *)
val string_of_lookup_strategy : lookup_strategy -> string

(** An error that arises when lookup by a given strategy fails. *)
exception NoSuchHole of lookup_strategy

(** Parses a lookup strategy.
 * An integer gives the `by_id` strategy, whereas a non-integer gives
 * the `by_name` strategy
 * Returns None if the parsing fails. *)
val parse_lookup_strategy : string -> lookup_strategy option

(** Parses a lookup strategy, throwing an exception on failure. *)
val unsafe_parse_lookup_strategy : string -> lookup_strategy

(** Looks up a hole by its number.
  * Use strategies with `get`. *)
val by_id : hole_id -> lookup_strategy

(** Looks up a hole by its name.
  * Use strategies with `get`. *)
val by_name : string -> lookup_strategy

type lf_hole_info =
  { cPsi : LF.dctx
  ; lfGoal : LF.tclo
  }

type comp_hole_info =
  { cG : Comp.gctx
  ; compGoal : Comp.typ * LF.msub
  }

type hole_info =
  | LfHoleInfo of lf_hole_info
  | CompHoleInfo of comp_hole_info

type hole =
  { loc : Syntax.Loc.t
  ; name : hole_name
    (** "Context Delta", for metavariables. *)
  ; cD : LF.mctx
    (** information specific to the hole type. *)
  ; info : hole_info
  }

(** Decides whether this is an LF hole. *)
val is_lf_hole : hole -> bool

(** Decides whether this is a computational hole. *)
val is_comp_hole : hole -> bool

(** Decides whether a hole has a name (is not anonymous). *)
val hole_is_named : hole -> bool

(** Stringifies a hole name.
 * If the hole is anonymous, then its name is the empty string. *)
val string_of_name : hole_name -> string

(** Stringifies a hole name.
 * If the hole is anonymous, then use its hole id. *)
val string_of_name_or_id : hole_name * hole_id -> string

(** Checks whether the internal array of holes is empty. *)
val none : unit -> bool

(** Pretty-prints a single hole. *)
val print : Format.formatter -> (hole_id * hole) -> unit

(** Retrieves a single hole using the given strategy. *)
val get : lookup_strategy -> (hole_id * hole) option

(** Retrieves a single hole using the given strategy,
 * raising NoSuchHole if the hole does not exist. *)
val unsafe_get : lookup_strategy -> hole_id * hole

(** Finds the first hole satisfying the given predicate. *)
val find : (hole -> bool) -> (int * hole) option

(** Looks up a hole, retrieving the hole itself and its number. *)
val lookup : string -> (int * hole) option

(** Decides whether a location is contained within a location. *)
val loc_within : Syntax.Loc.t -> Syntax.Loc.t -> bool

(** Counts the number of holes. *)
val count : unit -> int

(** Removes all holes contained in the given location. *)
val destroy_holes_within : Syntax.Loc.t -> unit

(** Adds a new hole. *)
val add : hole -> hole_id

(** Clears the main hole array. *)
val clear : unit -> unit

(** Gets the current list of holes. *)
val list : unit -> (hole_id * hole) list
