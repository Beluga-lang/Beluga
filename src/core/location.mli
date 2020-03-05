type pos
val position_line : pos -> int
val position_column : pos -> int
val position_bol : pos -> int
val position_offset : pos -> int
val initial_pos : pos

type t
val initial : string -> t
val join : t -> t -> t
val is_ghost : t -> bool
val ghost : t
val shift : int -> t -> t
val move_line : int -> t -> t
val start_offset : t -> int
val stop_offset : t -> int
val start_bol : t -> int
val stop_bol : t -> int
val start_line : t -> int
val stop_line : t -> int
val start_column : t -> int
val stop_column : t -> int
val filename : t -> string

(** Prints `<filename>, line <n>, column <n>'. Suitable for proper errors. *)
val print : Format.formatter -> t -> unit

(** Prints `line <n>, column <n>'. More suitable for debug prints. *)
val print_short : Format.formatter -> t -> unit

(** Prints `<n>.<n> - <n>.<n>' indicating start and stop positions. *)
val print_span_short : Format.formatter -> t -> unit

val start_position : t -> pos
val stop_position : t -> pos

val compare_start : t -> t -> int
