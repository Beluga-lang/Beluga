exception Violation of string

exception NotImplemented

type print_result

(* Wrapper around Printexc.register_printer. *)
val register_printer : (exn -> print_result) -> unit

(* Use suplied formatter for printing errors. *)
val print : (Format.formatter -> unit) -> print_result

(* Use supplied formatter for printing errors decorated with location information. *)
val print_with_location : Syntax.Loc.t -> (Format.formatter -> unit) -> print_result

val getInformation : unit -> string

val addInformation : string -> unit
