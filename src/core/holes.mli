open Syntax.Int

type hole_id

val string_of_hole_id : hole_id -> string

(* Essentially the same as `string option`. *)
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
  
type hole =
  { loc : Syntax.Loc.t;
    name : hole_name;
    (** LF context (the D is for "delta") *)
    cD : LF.mctx;
    (** computation context (the G is for "gamma") *)
    cG : Comp.gctx;
    goal : Comp.typ * LF.msub;
  }

(** Decides whether a hole has a name (is not anonymous). *)
val hole_is_named : hole -> bool

(** Stringifies a hole name.
 * If the hole is anonymous, then its name is the empty string. *)
val string_of_name : hole_name -> string

(** Checks whether the internal array of holes is empty. *)
val none : unit -> bool

(** Pretty-prints a single hole. *)
val format_hole : hole_id -> hole -> string

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

(** Gets the number of the hole at the given location. *)
val at : Syntax.Loc.t -> (hole_id * hole) option

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
