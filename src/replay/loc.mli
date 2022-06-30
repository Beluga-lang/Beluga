open Support

(** A location inside an input stream. *)
type t =
  { line : int  (** The line that the parser is on. *)
  ; offset : int  (** The offset that the parser is on inside the file. *)
  ; bol : int  (** The offset at which the current line begins on. *)
  }

(** Computes what column the location refers to within its line. *)
val column : t -> int

(** Increases the location by analyzing the given character. If the character
    is a line break, then the line number is incremented and the
    beginning-of-line offset is set to the current offset. *)
val inc_by_char : char -> t -> t

(** The initial location. Used to kick-start parsers. Specifically, this
    location has {!line = 1 !}, {!offset = 1 !}, and {!bol = 1 !}. *)
val initial : t

(** {1 Instances} *)

(** Total ordering of locations by their offset. *)
include Ord.ORD with type t := t

include Show.SHOW with type t := t
