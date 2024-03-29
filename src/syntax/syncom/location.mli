(** Character position ranges in source files.

    A parser is typically responsible for constructing locations using
    positions generated by the lexer. *)

open Support

(** The type of range over character positions in a source file. *)
type t

(** {1 Constructors} *)

(** [ghost] is the null location used for AST nodes having no correspondence
    to a source file. *)
val ghost : t

(** [initial filename] is the location at the beginning of the file with name
    [filename]. *)
val initial : string -> t

(** [make ~filename ~start_position ~stop_position] is the non-ghost location
    starting at the character position [start_position] inclusively and
    ending at the character position [stop_position] exclusively in the file
    at [filename]. *)
val make :
     filename:string
  -> start_position:Position.t
  -> stop_position:Position.t
  -> t

(** [join l1 l2] is the smallest location that contains [l1] and [l2].

    It is assumed that [filename l1 = filename l2].

    Ghost locations are left and right identities of [join], meaning that:

    - If [is_ghost l1], then [join l1 l2 = l2].
    - If [is_ghost l2], then [join l1 l2 = l1]. *)
val join : t -> t -> t

(** [join_all init ls] is each location in [ls] joined together, additionally
    with [init]. *)
val join_all : t -> t List.t -> t

(** [join_all_contramap f init xs] is each location contramapped by [f] from
    [xs]. joined together, additionally with [init].

    If [xs = \[x1; x2; ...; xn\]], then
    [join_all_contramap f init xs = join_all init \[f x1; f x2; ...; f xn\]]. *)
val join_all_contramap : ('a -> t) -> t -> 'a List.t -> t

val join_all1 : t List1.t -> t

val join_all1_contramap : ('a -> t) -> 'a List1.t -> t

val join_all2_contramap : ('a -> t) -> 'a List2.t -> t

val start_position_as_location : t -> t

val stop_position_as_location : t -> t

val set_filename : string -> t -> t

val set_start : Position.t -> t -> t

val set_stop : Position.t -> t -> t

(** [set_start_line line location] is [location] with its start line set to
    [line]. The start position's beginning of line and offset are not
    modified, so the output location may be invalid. This should only be used
    with locations that do not point to files, like ghost locations. *)
val set_start_line : int -> t -> t

(** [set_stop_line line location] is like [set_start_line line location] but
    for the location's stop position. *)
val set_stop_line : int -> t -> t

(** {1 Destructors} *)

val filename : t -> string

val start_position : t -> Position.t

val stop_position : t -> Position.t

val start_offset : t -> int

val stop_offset : t -> int

val start_bol : t -> int

val stop_bol : t -> int

val start_line : t -> int

val stop_line : t -> int

val start_column : t -> int

val stop_column : t -> int

(** [spanned_offsets location] is
    [stop_offset location - start_offset location]. *)
val spanned_offsets : t -> int

(** {1 Predicates and Comparisons} *)

val is_ghost : t -> bool

module Ord_by_start : Ord.ORD with type t = t

val compare_start : t -> t -> int

module Ord_by_stop : Ord.ORD with type t = t

val compare_stop : t -> t -> int

(** {1 Printing} *)

(** Prints `<filename>, line <n>, column <n>'. Suitable for proper errors. *)
val print : Format.formatter -> t -> unit

val pp : Format.formatter -> t -> unit

(** Prints `line <n>, column <n>'. More suitable for debug prints. *)
val print_short : Format.formatter -> t -> unit

(** Prints `<n>.<n> - <n>.<n>' indicating start and stop positions. *)
val print_span_short : Format.formatter -> t -> unit

(** {1 Interoperability} *)

val make_from_lexing_positions :
     filename:string
  -> start_position:Lexing.position
  -> stop_position:Lexing.position
  -> t

val start_to_lexing_position : t -> Lexing.position

val stop_to_lexing_position : t -> Lexing.position

val to_lexing_positions : t -> Lexing.position * Lexing.position

(** {1 Instances} *)

(** Structural equality instance. *)
include Eq.EQ with type t := t

(** Lexicographical ordering instance by filename, start position and stop
    position in that sequence. *)
include Ord.ORD with type t := t
