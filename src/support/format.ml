include Stdlib.Format

(** Polymorphic function that processes a format string. *)
type fmt = { fmt : 'a. ('a, formatter, unit) format -> 'a }

(** Converts something to a string using a formatting function. *)
let stringify p x = asprintf "%a" p x

(** Prints the given string followed by a space break hint. *)
let punctuation s ppf () = fprintf ppf "%s@ " s

(** Prints a semicolon followed by a space break hint. *)
let semicolon = punctuation ";"

(** Prints a comma followed by a space break hint. *)
let comma = punctuation ","

(* http://www.faqs.org/rfcs/rfc3629.html *)

exception Malformed_utf8_cluster

let utf_8_width =
  let width = Stdlib.Array.make 256 (-1) in
  for i = 0 to 127 do
    width.(i) <- 1
  done;
  for i = 192 to 223 do
    width.(i) <- 2
  done;
  for i = 224 to 239 do
    width.(i) <- 3
  done;
  for i = 240 to 247 do
    width.(i) <- 4
  done;
  fun c ->
    let w = width.(Stdlib.Char.code c) in
    if w > 0 then w else raise Malformed_utf8_cluster

(* Removing this creates a cyclic dependency somehow *)
module String = Stdlib.String

let pp_utf_8 ppf t =
  let string_length = Stdlib.String.length t in
  let i = ref 0 in
  let utf8_codepoint_length = ref 0 in
  (* Each iteration, [i] is increased, with a variable increment *)
  while !i < string_length do
    let c = t.[!i] in
    incr utf8_codepoint_length;
    i := !i + utf_8_width c
  done;
  assert (!i = string_length);
  pp_print_as ppf !utf8_codepoint_length t

let pp_utf_8_text ppf t =
  let total_string_length = Stdlib.String.length t in
  let left = ref 0 in
  let utf8_codepoint_cluster_length = ref 0 in
  let right = ref 0 in
  let flush () =
    pp_print_as ppf
      !utf8_codepoint_cluster_length
      (Stdlib.String.sub t !left (!right - !left));
    incr right (* [utf_8_width '\n' = utf_8_width ' ' = 1] *);
    left := !right;
    utf8_codepoint_cluster_length := 0
  in
  (* Each iteration, [right] is increased, with a variable increment *)
  while !right < total_string_length do
    match t.[!right] with
    | '\n' ->
        flush ();
        pp_force_newline ppf ()
    | ' ' ->
        flush ();
        pp_print_space ppf ()
    (* there is no specific support for '\t' as it is unclear what a right
       semantics would be *)
    | c ->
        incr utf8_codepoint_cluster_length;
        right := !right + utf_8_width c
  done;
  assert (!right = total_string_length);
  if !left <> total_string_length then flush ()
