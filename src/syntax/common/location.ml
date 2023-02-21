open Support

type t =
  { filename : string
  ; start : Position.t
  ; stop : Position.t
  ; ghost : bool
  }

let join l1 l2 =
  if l1.ghost then l2
  else if l2.ghost then l1
  else (
    assert (String.equal l1.filename l2.filename);
    let start = Position.min l1.start l2.start in
    let stop = Position.max l1.stop l2.stop in
    { filename = l1.filename; start; stop; ghost = false })

let join_all initial_location locations =
  List.fold_left join initial_location locations

let join_all_contramap get_location initial_location located_elements =
  List.fold_left
    (fun accumulated_location located_element ->
      join accumulated_location (get_location located_element))
    initial_location located_elements

let join_all1 locations = List1.fold_left Fun.id join locations

let join_all1_contramap get_location located_elements =
  List1.fold_left get_location
    (fun accumulated_location located_element ->
      join accumulated_location (get_location located_element))
    located_elements

let join_all2_contramap get_location located_elements =
  List2.fold_left get_location
    (fun accumulated_location located_element ->
      join accumulated_location (get_location located_element))
    (fun accumulated_location located_element ->
      join accumulated_location (get_location located_element))
    located_elements

let[@inline] is_ghost location = location.ghost

let[@inline] start_offset location = Position.offset location.start

let[@inline] stop_offset location = Position.offset location.stop

let[@inline] spanned_offsets location =
  stop_offset location - start_offset location

let[@inline] start_bol location = Position.beginning_of_line location.start

let[@inline] stop_bol location = Position.beginning_of_line location.stop

let[@inline] start_line location = Position.line location.start

let[@inline] stop_line location = Position.line location.stop

let[@inline] filename location = location.filename

let[@inline] start_column location = Position.column location.start

let[@inline] stop_column location = Position.column location.stop

let[@inline] make ~filename ~start_position ~stop_position =
  { filename; start = start_position; stop = stop_position; ghost = false }

let[@inline] initial filename =
  make ~filename ~start_position:Position.initial
    ~stop_position:Position.initial

let ghost = { (initial "_ghost") with ghost = true }

let make_from_lexing_positions ~filename ~start_position ~stop_position =
  let start_position' = Position.make_from_lexing_position start_position in
  let stop_position' = Position.make_from_lexing_position stop_position in
  make ~filename ~start_position:start_position'
    ~stop_position:stop_position'

let start_to_lexing_position location =
  if is_ghost location then Position.to_lexing_position location.start
  else Position.to_lexing_position ~filename:location.filename location.start

let stop_to_lexing_position location =
  if is_ghost location then Position.to_lexing_position location.stop
  else Position.to_lexing_position ~filename:location.filename location.stop

let to_lexing_positions location =
  if is_ghost location then
    ( Position.to_lexing_position location.start
    , Position.to_lexing_position location.stop )
  else
    ( Position.to_lexing_position ~filename:location.filename location.start
    , Position.to_lexing_position ~filename:location.filename location.stop
    )

let set_filename filename location = { location with filename }

let set_start start location = { location with start }

let set_stop stop location = { location with stop }

let start_position_as_location location = set_stop location.start location

let stop_position_as_location location = set_start location.stop location

let print_short ppf l =
  Format.fprintf ppf "line %d, column %d" (start_line l) (start_column l)

let print_span_short ppf l =
  Format.fprintf ppf "%d.%d - %d.%d" (start_line l) (start_column l)
    (stop_line l) (stop_column l)

let print ppf location =
  Format.fprintf ppf "File \"%s\",@ line %d,@ column %d" (filename location)
    (start_line location) (start_column location)

let pp = print

let start_position location = location.start

let stop_position location = location.stop

module Ord_by_start = (val Ord.contramap (module Position) start_position)

module Ord_by_stop = (val Ord.contramap (module Position) stop_position)

let compare_start = Ord_by_start.compare

let compare_stop = Ord_by_stop.compare

module Ord =
  (val Ord.sequence3
         (module String)
         (module Position)
         (module Position)
         filename start_position stop_position)

include (Ord : Support.Ord.ORD with type t := t)
