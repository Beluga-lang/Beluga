(** A location inside an input stream.
*)
type t =
  { line : int;
    (** The line that the parser is on. *)
    offset : int;
    (** The offset that the parser is on inside the file. *)
    bol : int;
    (** The offset at which the current line begins on. *)
  }

let column (l : t) : int =
  l.offset - l.bol

let to_string (loc : t) : string =
  Printf.sprintf "line %d, column %d" (loc.line + 1) (loc.offset - loc.bol + 1)

let compare (l1 : t) (l2 : t) : int =
  Pervasives.compare l1.offset l2.offset

let inc_by_char (c : char) (loc : t) =
  { line = if c = '\n' then loc.line + 1 else loc.line;
    offset = loc.offset + 1;
    bol = if c = '\n' then loc.offset + 1 else loc.bol;
  }

let initial : t =
  { line = 1;
    offset = 1;
    bol = 1;
  }
