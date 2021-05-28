(**
 * usage: lex_check FILE
 * synopsis: verifies that the Beluga EOI token appears at the actual
   end of the input, as measured by counting the Unicode code points
   in the file.
   Traditionally, this was done directly in the TEST script (by
   calling out to wc -m to count code points), but for portability
   reasons, this is now implemented in OCaml.
   Exit status:
     - 0: FILE passes the check
     - 1: FILE fails the check (diagnose the issue by using lex_dump)
     - 2: unhandled OCaml exception
 *)

open Support
open Beluga

(** From a token stream, finds to location of the EOI token. *)
let rec find_eoi (s : (Location.t * Token.t) Gen.t) : Location.t option =
  match s () with
  | None -> None
  | Some (l, Token.EOI) -> Some l
  | _ -> find_eoi s

let rec count n lexbuf =
  match Sedlexing.next lexbuf with
  | None -> n
  | Some _ -> count (n + 1) lexbuf

let passes_check (path : string) : bool =
  let input = Std.input_file ?bin:(Some true) path in
  let real_end = Sedlexing.Utf8.from_string input |> count 0 in
  Printf.printf "found end %d\n" real_end;
  let stream = GenMisc.of_string input in
  let out = Lexer.mk (Location.initial path) stream in
  match find_eoi out with
  | None -> false
  | Some l -> Location.start_offset l = real_end

let main () =
  match Array.to_list Sys.argv with
  | [_; path] ->
     if passes_check path then
       exit 0
     else
       exit 1
  | _ ->
     print_string "Invalid number of command-line arguments.\n";
     exit 1

let _ = main ()
