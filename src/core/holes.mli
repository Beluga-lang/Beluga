open Syntax.Int

(* Define two opaque types to be used as indices for `hole_info`. *)

type lf_hole_info =
  { cPsi : LF.dctx
  ; lfGoal : LF.tclo
  ; mutable lfSolution : LF.nclo option
  }

type comp_hole_info =
  { cG : Comp.gctx
  ; compGoal : Comp.typ * LF.msub
  ; mutable compSolution : Comp.exp_chk option
  }

type _ hole_info =
  | LFInfo : lf_hole_info hole_info
  | CompInfo : comp_hole_info hole_info

(** A hole with a known kind of information. *)
type 'a hole =
  { loc : Syntax.Loc.t
  ; name : HoleId.name
    (** "Context Delta", for metavariables. *)
  ; cD : LF.mctx
    (** information specific to the hole type. *)
  ; info : 'a
  }

(** Existential wrapper for 'a hole with a singleton type. *)
type some_hole =
  | Exists : 'a hole_info * 'a hole -> some_hole

(** A strategy for retrieving a hole. *)
type lookup_strategy

(** Gets a string representation of the given strategy. *)
val string_of_lookup_strategy : lookup_strategy -> string

type error =
  | InvalidHoleIdentifier of string
  | NoSuchHole of lookup_strategy
  | NameShadowing of string * Loc.t
  | UnsolvedHole of HoleId.name * HoleId.t

(** An error that arises when lookup by a given strategy fails. *)
exception Error of Loc.t * error

(** Parses a lookup strategy.
 * An integer gives the `by_id` strategy, whereas a non-integer gives
 * the `by_name` strategy
 * Returns None if the parsing fails. *)
val parse_lookup_strategy : string -> lookup_strategy option

(** Parses a lookup strategy, throwing an exception on failure.
    The given location is used in the thrown exception.
 *)
val unsafe_parse_lookup_strategy : Loc.t -> string -> lookup_strategy

(** Looks up a hole by its number.
  * Use strategies with `get`. *)
val by_id : HoleId.t -> lookup_strategy

(** Looks up a hole by its name.
  * Use strategies with `get`. *)
val by_name : string -> lookup_strategy

type snapshot

(** Gets a snapshot of the current hole ids. *)
val get_snapshot : unit -> snapshot

(** Gets a list of holes added since the given snapshot.
    This can be used to whether an ad hoc expression contained any
    holes.
 *)
val holes_since : snapshot -> (HoleId.t * some_hole) list

(** Runs a function, and catches any new holes added as a result of
    running it.
 *)
val catch : (unit -> 'a) -> (HoleId.t * some_hole) list * 'a

(** Decides whether this is an LF hole. *)
val to_lf_hole : some_hole -> lf_hole_info hole option

(** Decides whether this is a computational hole. *)
val to_comp_hole : some_hole -> comp_hole_info hole option

(** Decides whether this hole is solved. *)
val is_solved : some_hole -> bool

(** Decides whether this hole is unsolved. *)
val is_unsolved : some_hole -> bool

(** Decides whether a hole has a name (is not anonymous). *)
val hole_is_named : some_hole -> bool

(** Checks whether the internal array of holes is empty. *)
val none : unit -> bool

(** Retrieves a single hole using the given strategy. *)
val get : lookup_strategy -> (HoleId.t * some_hole) option

(** Retrieves a single hole using the given strategy,
 * raising NoSuchHole if the hole does not exist. *)
val unsafe_get : lookup_strategy -> HoleId.t * some_hole

(** Looks up a hole, retrieving the hole itself and its number. *)
val lookup : string -> (HoleId.t * some_hole) option

(** Decides whether a location is contained within a location. *)
val loc_within : Syntax.Loc.t -> Syntax.Loc.t -> bool

(** Counts the number of holes. *)
val count : unit -> int

(** Removes all holes contained in the given location. *)
val destroy_holes_within : Syntax.Loc.t -> unit

(** Allocates a new hole ID. *)
val allocate : unit -> HoleId.t

(** Assigns the hole to the given ID. *)
val assign : HoleId.t -> some_hole -> unit

(** Clears the hole arrays. *)
val clear : unit -> unit

(** Gets the current list of holes. *)
val list : unit -> (HoleId.t * some_hole) list

(** Adds a Harpoon subgoal to the internal list. *)
val add_harpoon_subgoal : Comp.open_subgoal -> unit

(** Gets the list of Harpoon subgoals. *)
val get_harpoon_subgoals : unit -> Comp.open_subgoal list
