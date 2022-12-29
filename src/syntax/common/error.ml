open Support
open Debug.Fmt

let raise = raise

exception Violation of string

let violation msg =
  Debug.printf (fun p -> p.fmt "[violation] %s" msg);
  raise (Violation msg)

exception NotImplemented of Location.t option * string

let not_implemented loc msg = raise (NotImplemented (Option.some loc, msg))

let not_implemented' msg = raise (NotImplemented (Option.none, msg))

type print_result = string

let error_format_buffer = Buffer.create 1024

let error_format = Format.formatter_of_buffer error_format_buffer

let register_printer f =
  Printexc.register_printer (fun e ->
      try Option.some (f e) with
      | Match_failure _ -> Option.none)

let register_printer' f = Printexc.register_printer f

let print f =
  (* Print to stderr any uncaught exception resulting from applying f to
     error_format. Such an exception would be thrown when in the middle of
     printing an exception! *)
  Printexc.print f error_format;
  Format.pp_print_newline error_format ();
  Format.pp_print_flush error_format ();
  let str = Buffer.contents error_format_buffer in
  Buffer.reset error_format_buffer;
  str

let register_printing_function (extract : exn -> 'a option)
    (fmt_ppr : Format.formatter -> 'a -> unit) : unit =
  let open Fun in
  register_printer'
    (Option.map (fun e -> print (fun ppf -> fmt_ppr ppf e)) ++ extract)

let register_located_printing_function
    (extract : exn -> (Location.t * 'a) option)
    (fmt_ppr : Format.formatter -> 'a -> unit) : unit =
  let f (loc, e) =
    print (fun ppf ->
        Format.fprintf ppf "@[<v>%a:@,%a@]" Location.print loc fmt_ppr e)
  in
  let open Fun in
  register_printer' (Option.map f ++ extract)

let print_location loc =
  Format.fprintf error_format "%a:@," Location.print loc

let print_with_location loc f =
  print_location loc;
  print f

(* Since this printer is registered first, it will be executed only if all
   other printers fail. *)
let _ =
  Printexc.register_printer (fun _exn ->
      (* We unfortunately do not have direct access to the default printer
         that Printexc uses for exceptions, so we print the message we want
         as a side-effect and return None, which should in turn convince
         Printexc to resort to the default printer to actually print the
         exception. *)
      Format.fprintf Format.err_formatter
        "Uncaught exception.@ Please report this as a bug.@.";
      None)

let report_mismatch ppf title title_obj1 pp_obj1 obj1 title_obj2 pp_obj2 obj2
    =
  Format.fprintf ppf "@[<v>%s@," title;
  Format.fprintf ppf "    @[<v>%s:@,  %a@,%s:@,  %a@]@,@]" title_obj1 pp_obj1
    obj1 title_obj2 pp_obj2 obj2

(* The following is for coverage. Probably needs to be phased out. *)
let information = ref []

let reset_information () = information := []

let get_information () =
  Format.stringify
    (List.pp ~pp_sep:Format.pp_print_newline Format.pp_print_string)
    (List.rev !information)

let add_information message = information := message :: !information

(** Register some basic printers. *)
let () =
  register_printer (fun [@warning "-8"] (Sys_error msg) ->
      print (fun ppf -> Format.fprintf ppf "System error: %s" msg));

  register_printer (fun [@warning "-8"] (Violation msg) ->
      print (fun ppf ->
          Format.fprintf ppf
            "@[<v>Internal error (please report as a bug):@,@[%a@]@]"
            Format.pp_print_string msg));

  register_printer (fun [@warning "-8"] (NotImplemented (loc, msg)) ->
      print (fun ppf ->
          Option.when_some loc print_location;
          Format.fprintf ppf "@[<v>Not implemented.@,@[%a@]@]"
            Format.pp_print_string msg))

(* TODO: Use Sedlexing to read a file up to a given offset *)
(*=

type input_line =
  { text : string
  ; start_pos : int
  }

let lines_around ~(start_pos : Location.pos) ~(end_pos : Location.pos)
    ~(seek : int -> unit) ~(read_char : unit -> char option) :
    input_line list =
  seek (Location.position_bol start_pos);
  let lines = ref [] in
  let bol = ref (Location.position_bol start_pos) in
  let cur = ref (Location.position_bol start_pos) in
  let b = Buffer.create 80 in
  let add_line () =
    if !bol < !cur then (
      let text = Buffer.contents b in
      Buffer.clear b;
      lines := { text; start_pos = !bol } :: !lines;
      bol := !cur)
  in
  let rec loop () =
    if !bol >= Location.position_offset end_pos then ()
    else
      match read_char () with
      | None ->
        (* end of input *)
        add_line ()
      | Some c -> (
        incr cur;
        match c with
        | '\r' -> loop ()
        | '\n' ->
          add_line ();
          loop ()
        | _ ->
          Buffer.add_char b c;
          loop ())
  in
  loop ();
  List.rev !lines

(* Get lines from a file *)
let lines_around_from_file ~(start_pos : Location.pos) ~(end_pos : Location.pos)
    (filename : string) : input_line list =
  try
    let cin = open_in_bin filename in
    let read_char () =
      try Some (input_char cin) with End_of_file -> None
    in
    let lines =
      lines_around ~start_pos ~end_pos ~seek:(seek_in cin) ~read_char
    in
    close_in cin;
    lines
  with Sys_error _ -> []
*)

(*=
File "src/core/synprs_to_synext'.ml", line 4788, characters 37-47:
4788 |         { location; identifier; typ; expression } -> Obj.magic ()
                                            ^^^^^^^^^^
Error (warning 27 [unused-var-strict]): unused variable expression.

       { location; identifier; typ; expression } -> Obj.magic ()

*)
