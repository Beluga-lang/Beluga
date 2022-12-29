(** Character positions in source files.

    The definition for a character position depends on the source file's
    encoding. A lexer is typically responsible for constructing positions. *)

open Support

(** The type of character positions in a source file. *)
type t

(** {1 Constructors} *)

(** [make ~line ~beginning_of_line ~offset] is the source code position at a
    character distance [offset] from the initial position of a file. [line]
    is the number of the line (starting at 1) in which the character occurs.
    [beginning_of_line] is the character distance from the initial position
    of the file and the beginning of the line.

    The character distances have to be computed with respect to the file's
    encoding. UTF-8, the default encoding for Beluga signatures, is a
    variable-width encoding, so it is incorrect to always count a byte as a
    character. *)
val make : line:int -> beginning_of_line:int -> offset:int -> t

(** [initial] is the initial position of a character in a source file, with
    [line initial = 1], [beginning_of_line initial = 0] and
    [offset initial = 0]. *)
val initial : t

(** {1 Destructors} *)

(** [line position] is the line of [position]. The line count starts at [1]. *)
val line : t -> int

(** [column position] is the column of [position], computed from its
    beginning of line and actual offsets. The column count starts at [1]. *)
val column : t -> int

val beginning_of_line : t -> int

val offset : t -> int

(** {1 Instances} *)

(** Equality of positions by their offsets. *)
include Eq.EQ with type t := t

(** Total ordering of positions by their offsets. *)
include Ord.ORD with type t := t

(** {1 Interoperability} *)

(** [make_from_lexing_position lexing_position] is the character position
    derived from [lexing_position] using its [pos_lnum], [pos_bol] and
    [pos_cnum]. *)
val make_from_lexing_position : Lexing.position -> t

(** [to_lexing_position ?filename position] is the lexing position derived
    from [position] with [filename] as [pos_fname] if it is defined, and [""]
    otherwise. *)
val to_lexing_position : ?filename:string -> t -> Lexing.position
