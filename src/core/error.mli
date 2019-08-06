module Options :
sig
  (** Whether to include locations in the output of errors or not.
      Omitting locations is useful when comparing outputs of two
      script runs, because locations and their formatting are
      dependent on the version of Camlp4, not Beluga. *)
  val print_loc : bool ref
end

exception Violation of string

exception NotImplemented

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

(** Use suplied formatter for printing errors. *)
val print : (Format.formatter -> unit) -> print_result

(** Use supplied formatter for printing errors decorated with location information. *)
val print_with_location : Syntax.Loc.t -> (Format.formatter -> unit) -> print_result

(** Helper function to construct an error message reporting a mismatch
    between something that was expected and what was actually
    encountered. e.g. a type mismatch or a context clash.

    example:
    report_mismatch ppf "Type mismatch." "Expected type" pp_ty1 ty1 "Inferred type" pp_ty2 ty2
*)
val report_mismatch :
  Format.formatter -> string ->
  string -> (Format.formatter -> 'a -> unit) -> 'a ->
  string -> (Format.formatter -> 'b -> unit) -> 'b ->
  unit

val resetInformation : unit -> unit
val getInformation   : unit -> string

val addInformation   : string -> unit
