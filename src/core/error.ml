module Options =
struct
  let print_loc = ref true
end

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

let print_with_location loc f =
  if !Options.print_loc then
    Format.fprintf error_format "%s:@." (Syntax.Loc.to_string loc);
  print f

(* Since this printer is registered first, it will be executed only if
   all other printers fail. *)
let _ = Printexc.register_printer
  (fun exc ->
    (* We unfortunately do not have direct access to the default
       printer that Printexc uses for exceptions, so we print the
       message we want as a side-effect and return None, which should
       in turn convince Printexc to resort to the default printer to
       actually print the exception. *)
    Format.fprintf Format.err_formatter
      "Uncaught exception.@ Please report this as a bug.@.";
    None)

let _ = register_printer
  (fun (Sys_error msg) ->
    print (fun ppf ->
      Format.fprintf ppf "System error: %s" msg))

let _ = register_printer
  (fun (Violation msg) ->
    print (fun ppf ->
      Format.fprintf ppf "Internal error (please report as a bug):@;%s" msg))

let _ = register_printer
  (fun NotImplemented ->
    print (fun ppf ->
      Format.fprintf ppf "Not implemented."))

let report_mismatch ppf title title_obj1 pp_obj1 obj1 title_obj2 pp_obj2 obj2 =
  Format.fprintf ppf "%s@." title;
  Format.fprintf ppf
    "    @[<v>%s: %a@;\
              %s: %a@]@."
    title_obj1 pp_obj1 obj1
    title_obj2 pp_obj2 obj2

(* The following is for coverage. Probably needs to be phased out. *)
let information = ref []

let getInformation () =
  match List.rev !information with
    | [] -> ""
    | information ->
      (List.fold_left (fun acc s -> acc ^ "\n" ^ s) "" information) ^ "\n"

let addInformation message =
  information := message :: !information
