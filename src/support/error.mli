exception Violation of string

(** Raises a Violation exception with the given message. *)
val violation : string -> 'a

exception NotImplemented of Location.t option * string

(** Raises a NotImplemented exception at the given location, with the given message. *)
val not_implemented : Location.t -> string -> 'a

(** Raises a NotImplemented exception with the given message. *)
val not_implemented' : string -> 'a

(** Abstract dummy datatype to enforce that printing be done using the
    printing functions provided by this module. *)
type print_result

(** Wrapper around Printexc.register_printer.
    The given function should use partial pattern matching (ew) to
    signal that it doesn't know how to deal with other types of
    exceptions.
 *)
val register_printer : (exn -> print_result) -> unit

(** Wrapper around Printexc.register_printer.
    The given function should return None if it doesn't know how to
    handle a given exception.
 *)
val register_printer' : (exn -> print_result option) -> unit

(** Registers a printer for an exception using the a given exception
    selection function and exception formatter. *)
val register_printing_function : (exn -> 'a option)
                                 -> (Format.formatter -> 'a -> unit)
                                 -> unit

(** Registers a printer for an exception that carries a location using
    the given exception selection function and exception formatter. *)
val register_located_printing_function : (exn -> (Location.t * 'a) option)
                                         -> (Format.formatter -> 'a -> unit)
                                         -> unit

(** Use suplied formatter for printing errors. *)
val print : (Format.formatter -> unit) -> print_result

(** Use supplied formatter for printing errors decorated with location information. *)
val print_with_location : Location.t -> (Format.formatter -> unit) -> print_result

(** Helper function to construct an error message reporting a mismatch
    between something that was expected and what was actually
    encountered. e.g. a type mismatch or a context clash.

    example:
    report_mismatch ppf "Type mismatch." "Expected type" pp_ty1 ty1 "Inferred type" pp_ty2 ty2
*)
val report_mismatch : Format.formatter -> string
                      -> string -> (Format.formatter -> 'a -> unit) -> 'a
                      -> string -> (Format.formatter -> 'b -> unit) -> 'b
                      -> unit

val resetInformation : unit -> unit
val getInformation : unit -> string

val addInformation : string -> unit
