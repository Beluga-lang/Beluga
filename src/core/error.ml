(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

exception Violation of string

exception NotImplemented

type print_result = string

let error_format_buffer = Buffer.create 200

let error_format = Format.formatter_of_buffer error_format_buffer

let register_printer f =
  Printexc.register_printer
    (fun e -> try Some (f e) with Match_failure _ -> None)

let print f =
  (* Print to stderr any uncaught exception resulting from applying f
     to error_format. Such an exception would be thrown when in the
     middle of printing an exception! *)
  Printexc.print f error_format;
  Format.pp_print_newline error_format ();
  Format.pp_print_flush error_format ();
  let str = Buffer.contents error_format_buffer in
  Buffer.reset error_format_buffer;
  str

let string_of_loc loc =
  if Syntax.Loc.is_ghost loc then "<unknown location>"
  else begin
    Parser.Grammar.Loc.print Format.str_formatter loc;
    Format.flush_str_formatter ()
  end

let print_with_location loc f =
  Format.fprintf error_format "%s:@." (string_of_loc loc);
  print f

let _ = register_printer
  (fun (Violation msg) ->
    print (fun ppf ->
      Format.pp_print_string ppf msg;
      Format.pp_print_newline ppf ();
      Format.pp_print_newline ppf ();
      Format.fprintf ppf "Beluga encountered an internal violation.@ \
                          Please report this as a bug."))

let _ = register_printer
  (fun NotImplemented ->
    print (fun ppf ->
      Format.fprintf ppf "Not implemented."))

let information = ref []

let getInformation () =
  match List.rev !information with
    | [] -> ""
    | information ->
      (List.fold_left (fun acc s -> acc ^ "\n" ^ s) "" information) ^ "\n"

let addInformation message =
  information := message :: !information
