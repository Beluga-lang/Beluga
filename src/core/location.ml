open Support

type pos =
  { line : int
  ; bol : int
  ; offset : int
  }

let position_line p = p.line
let position_column p = p.offset - p.bol
let position_bol p = p.bol
let position_offset p = p.offset

let initial_pos = { line = 1; bol = 0; offset = 0 }

type t =
  { filename : string
  ; start : pos
  ; stop : pos
  ; ghost : bool
  }

(** Joins two locations, keeping the starting position of the former,
    and the stopping position of the latter.
    The ghost location is a unit of this operation.
 *)
let join l1 l2 =
  match () with
  | _ when l1.ghost -> l2
  | _ when l2.ghost -> l1
  | _ ->
     assert (Misc.String.equals l1.filename l2.filename);
     { filename = l1.filename
     ; start = l1.start
     ; stop = l2.stop
     ; ghost = false
     }

let is_ghost s = s.ghost

let start_offset s = s.start.offset
let stop_offset s = s.stop.offset
let start_bol s = s.start.bol
let stop_bol s = s.stop.bol
let start_line s = s.start.line
let stop_line s = s.stop.line
let filename s = s.filename

let column p = p.offset - p.bol
let start_column s = column s.start
let stop_column s = column s.stop

let initial filename =
  { start = initial_pos
  ; stop = initial_pos
  ; ghost = false
  ; filename
  }

let ghost = { (initial "_ghost") with ghost = true }

(** Shifts the column offset of the location *)
let shift n s : t =
  { s with
    start = s.stop;
    stop = { s.stop with offset = s.stop.offset + n }
  }

let move_line n s : t =
  { s with
    start = { s.start with line = s.start.line + n; bol = s.start.offset };
    stop = { s.stop with line = s.stop.line + n; bol = s.stop.offset }
  }

let print_short ppf l =
  let open Format in
  fprintf ppf "line %d, column %d" (start_line l) (start_column l)

let print_span_short ppf l =
  let open Format in
  fprintf ppf "%d.%d - %d.%d"
    (start_line l)
    (start_column l)
    (stop_line l)
    (stop_column l)

let print ppf l =
  let open Format in
  fprintf ppf "%s, %a" l.filename print_short l

let start_position s = s.start
let stop_position s = s.stop

let compare_start l1 l2 = compare l1.start.offset l2.start.offset
