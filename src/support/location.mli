(** Locations in source files. *)

(** {1 Positions} *)

(** The type of character position in a source file. *)
type pos

(** {2 Constructors} *)

val initial_pos : pos

(** {2 Destructors} *)

val position_line : pos -> int

val position_column : pos -> int

val position_bol : pos -> int

val position_offset : pos -> int

(** {1 Locations} *)

(** The type of range over character positions in a source file. *)
type t

(** {2 Constructors} *)

(** [ghost] is the null location used for AST nodes having no correspondence
    to a source file. *)
val ghost : t

(** [initial filename] is the location at the beginning of the file with name
    [filename]. *)
val initial : string -> t

val make :
     string
  -> start_position:Lexing.position
  -> stop_position:Lexing.position
  -> t

(** [join l1 l2] is the union of the ranges [l1] and [l2].

    It is assumed that [filename l1 = filename l2].

    - If [l1 = ghost], then [join l1 l2 = l2].
    - If [l2 = ghost], then [join l1 l2 = l1]. *)
val join : t -> t -> t

(** [join_all init ls] is the union of the locations in [ls] with [init]. *)
val join_all : t -> t List.t -> t

(** [join_all_contramap f init xs] is the union of the locations [init] and
    those contramapped by [f] from [xs].

    If [xs = \[x1; x2; ...; xn\]], then
    [join_all_contramap f init xs = join_all init \[f x1; f x2; ...; f xn\]]. *)
val join_all_contramap : ('a -> t) -> t -> 'a List.t -> t

val join_all1 : t List1.t -> t

val join_all1_contramap : ('a -> t) -> 'a List1.t -> t

val shift : int -> t -> t

val move_line : int -> t -> t

(** {2 Destructors} *)

val start_offset : t -> int

val stop_offset : t -> int

val start_bol : t -> int

val stop_bol : t -> int

val start_line : t -> int

val stop_line : t -> int

val start_column : t -> int

val stop_column : t -> int

val filename : t -> string

val start_position : t -> pos

val stop_position : t -> pos

(** {2 Predicates and Comparisons} *)

val is_ghost : t -> bool

val compare_start : t -> t -> int

(** {2 Printing} *)

(** Prints `<filename>, line <n>, column <n>'. Suitable for proper errors. *)
val print : Format.formatter -> t -> unit

val pp : Format.formatter -> t -> unit

(** Prints `line <n>, column <n>'. More suitable for debug prints. *)
val print_short : Format.formatter -> t -> unit

(** Prints `<n>.<n> - <n>.<n>' indicating start and stop positions. *)
val print_span_short : Format.formatter -> t -> unit
