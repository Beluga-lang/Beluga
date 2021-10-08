(** Designates an interval delimited by locations.
    The second location is excluded.
    (i.e. The interval is closed on the left but open on the right.)
 *)
type t =
  { start : Loc.t;
    (** The location where the span starts. *)
    stop : Loc.t;
    (** The location where the span stops. (Exclusive.) *)
  }

(** Raised when attempting to unsafely construct a span from
locations that violate the invariant that the start location comes
before the stop location. *)
exception InvalidSpan

(** Constructs a span from a pair of locations.
    If the second location comes before the first, then the result is
    {!Stdlib.None}.
 *)
val of_pair : Loc.t -> Loc.t -> t option

(** Constructs a span from a pair of locations.
    If the second location comes before the first, then {!
    Mupc.Span.InvalidSpan } is raised.
    Use this rather than {! Mupc.Span.from_pair } if you're sure
    that the locations respect the invariant.
    (Or if you really like exceptions.)
 *)
val of_pair' : Loc.t -> Loc.t -> t

(** Constructs a string representation of a span. *)
val to_string : t -> string
