open Support

type t =
  { line : int  (** The position's line number. *)
  ; bol : int
        (** The position's beginning of line offset. This is the number of
            characters from the start of the file up to the beginning of the
            line. *)
  ; offset : int
        (** The position's offset. This is the number of characters from the
            start of the file up to the position. *)
  }

let[@inline] line position = position.line

let[@inline] column position = position.offset - position.bol + 1

let[@inline] beginning_of_line position = position.bol

let[@inline] offset position = position.offset

let make ~line ~beginning_of_line ~offset =
  { line; bol = beginning_of_line; offset }

let initial = make ~line:1 ~beginning_of_line:0 ~offset:0

let make_from_lexing_position position =
  let line = position.Lexing.pos_lnum
  and beginning_of_line = position.Lexing.pos_bol
  and offset = position.Lexing.pos_cnum in
  make ~line ~beginning_of_line ~offset

let to_lexing_position ?(filename = "") position =
  let pos_fname = filename
  and pos_lnum = line position
  and pos_bol = beginning_of_line position
  and pos_cnum = offset position in
  { Lexing.pos_fname; pos_lnum; pos_bol; pos_cnum }

include (
  Ord.Make (struct
    type nonrec t = t

    let compare p1 p2 = Int.compare p1.offset p2.offset
  end) :
    Ord.ORD with type t := t)
