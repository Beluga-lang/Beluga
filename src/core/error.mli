exception Violation of string

exception NotImplemented

(** Abstract dummy datatype to enforce that printing be done using the
    printing functions provided by this module. *)
type print_result

(** Wrapper around Printexc.register_printer. *)
val register_printer : (exn -> print_result) -> unit

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
  string -> (Format.formatter -> 'a -> unit) -> 'a ->
  unit

val getInformation : unit -> string

val addInformation : string -> unit
