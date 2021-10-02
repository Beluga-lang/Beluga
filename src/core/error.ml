open Support

module F = Fun

open Debug.Fmt

exception Violation of string
let violation msg =
  Debug.printf (fun p -> p.fmt "[violation] %s" msg);
  raise (Violation msg)

exception NotImplemented of Location.t option * string
let not_implemented loc msg = raise (NotImplemented (Some loc, msg))
let not_implemented' msg = raise (NotImplemented (None, msg))

type print_result = string

let error_format_buffer = Buffer.create 1024

let error_format = Format.formatter_of_buffer error_format_buffer

let register_printer f =
  Printexc.register_printer
    begin fun e ->
    try
      Some (f e)
    with
    | Match_failure _ -> None
    end

let register_printer' f = Printexc.register_printer f

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

let register_printing_function
      (extract : exn -> 'a option)
      (fmt_ppr : Format.formatter -> 'a -> unit)
    : unit =
  let open F in
  register_printer'
    (Maybe.map (fun e -> print (fun ppf -> fmt_ppr ppf e)) ++ extract)

let register_located_printing_function
      (extract : exn -> (Location.t * 'a) option)
      (fmt_ppr : Format.formatter -> 'a -> unit)
    : unit =
  let f (loc, e) =
    print
      begin fun ppf ->
      Format.fprintf ppf "@[<v>%a:@,%a@]"
      Location.print loc
        fmt_ppr e
      end
  in
  let open F in
  register_printer' (Maybe.map f ++ extract)

let print_location loc =
  Format.fprintf error_format "%a:@," Location.print loc

let print_with_location loc f =
  print_location loc;
  print f

(* Since this printer is registered first, it will be executed only if
   all other printers fail. *)
let _ =
  Printexc.register_printer
    begin fun exc ->
    (* We unfortunately do not have direct access to the default
       printer that Printexc uses for exceptions, so we print the
       message we want as a side-effect and return None, which should
       in turn convince Printexc to resort to the default printer to
       actually print the exception. *)
    Format.fprintf Format.err_formatter
      "Uncaught exception.@ Please report this as a bug.@.";
    None
    end

let report_mismatch ppf title title_obj1 pp_obj1 obj1 title_obj2 pp_obj2 obj2 =
  Format.fprintf ppf "@[<v>%s@," title;
  Format.fprintf ppf
    "    @[<v>%s:@,  %a@,\
              %s:@,  %a@]@,@]"
    title_obj1 pp_obj1 obj1
    title_obj2 pp_obj2 obj2

(* The following is for coverage. Probably needs to be phased out. *)
let information = ref []

let resetInformation () =
  information := []

let getInformation () =
  match List.rev !information with
  | [] -> ""
  | information ->
     List.fold_left (fun acc s -> acc ^ "\n" ^ s) "" information ^ "\n"

let addInformation message =
  information := message :: !information

(** Register some basic printers. *)
let _ =
  register_printer
    begin fun (Sys_error msg) ->
    print
      begin fun ppf ->
      Format.fprintf ppf "System error: %s"
        msg
      end
    end;

  register_printer
    begin fun (Violation msg) ->
    print
      begin fun ppf ->
      Format.fprintf ppf "@[<v>Internal error (please report as a bug):@,@[%a@]@]"
        Format.pp_print_string msg
      end
    end;

  register_printer
    begin fun (NotImplemented (loc, msg)) ->
    print
      begin fun ppf ->
      Maybe.when_some loc print_location;
      Format.fprintf ppf "@[<v>Not implemented.@,@[%a@]@]"
        Format.pp_print_string msg
      end
    end
