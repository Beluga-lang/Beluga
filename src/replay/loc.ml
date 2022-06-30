open Support

(** A location inside an input stream. *)
type t =
  { line : int  (** The line that the parser is on. *)
  ; offset : int  (** The offset that the parser is on inside the file. *)
  ; bol : int  (** The offset at which the current line begins on. *)
  }

let offset l = l.offset

let column l = l.offset - l.bol

let inc_by_char c loc =
  { line = (if c = '\n' then loc.line + 1 else loc.line)
  ; offset = loc.offset + 1
  ; bol = (if c = '\n' then loc.offset + 1 else loc.bol)
  }

let initial = { line = 1; offset = 1; bol = 1 }

include ((val Ord.contramap (module Int) offset) : Ord.ORD with type t := t)

include (
  Show.Make (struct
    type nonrec t = t

    let pp ppf loc =
      Format.fprintf ppf "line %d, column %d" (loc.line + 1)
        (loc.offset - loc.bol + 1)
  end) :
    Show.SHOW with type t := t)
