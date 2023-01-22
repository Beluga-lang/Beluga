open Support

val raise : exn -> 'a

exception Violation of string

(** Raises a Violation exception with the given message. *)
val violation : string -> 'a

(** [located_exception locations cause] is a decorated exception having
    [cause] and [locations] for source file error-reporting. This exception
    is not exported from this module, so it may never be caught elsewhere.

    This sort of exception is used to signal to the user which part of their
    source code is problematic. *)
val located_exception : Location.t List1.t -> exn -> exn

(** [located_exception1 location cause] is a decorated exception having
    [cause] and locations [\[location\]] for source file error-reporting. *)
val located_exception1 : Location.t -> exn -> exn

(** [located_exception2 location1 location2 cause] is a decorated exception
    having [cause] and locations [\[location1; location2\]] for source file
    error-reporting. *)
val located_exception2 : Location.t -> Location.t -> exn -> exn

(** [raise_at locations cause] raises [located_exception locations cause]. *)
val raise_at : Location.t List1.t -> exn -> 'a

(** [raise_at1 location cause] raises [located_exception1 location cause]. *)
val raise_at1 : Location.t -> exn -> 'a

(** [raise_at2 location1 location2 cause] raises
    [located_exception2 location1 location2 cause]. *)
val raise_at2 : Location.t -> Location.t -> exn -> 'a

(** [composite_exception causes] is the composite exception having many
    related [causes]. This exception is not exported from this module, so it
    may never be caught elsewhere.

    This sort of exception is used to report multiple exception causes for
    the same problem. For instance, during disambiguation, we may have
    encountered a bound variable that is of the wrong type. This exception
    can be represented as the composite for an exception for the variable
    being bound and of an unexpected sort, and another exception for
    reporting the sort of bound variable it is. *)
val composite_exception : exn List2.t -> exn

(** [composite_exception2 cause1 cause2] is the composite exception having
    causes [\[cause1; cause2\]]. *)
val composite_exception2 : exn -> exn -> exn

(** [aggregate_exception exceptions] is the composite exception having many
    unrelated [exceptions]. This exception is not exported from this module,
    so it may never be caught elsewhere.

    This sort of exception is used to report multiple different exceptions.
    For instance, during the indexing of a signature, unrelated exceptions
    may arise in different compilation units. These unrelated exceptions can
    be raised as an aggregate exception. *)
val aggregate_exception : exn List2.t -> exn

(** [aggregate_exception2 exception1 exception2] is the aggregate exception
    having causes [\[exception1; exception2\]]. This exception is not
    exported from this module, so it may never be caught elsewhere. *)
val aggregate_exception2 : exn -> exn -> exn

(** [raise_not_implemented ?location message] raises an exception signalling
    that we've reached a segment of code that is not yet implemented. The
    optional [location] is used to additionally report to the user the part
    of their work that triggered this exception. *)
val raise_not_implemented : ?location:Location.t -> string -> 'a

(** [raise_unsupported_exception_printing exn] raises an exception signalling
    that a pretty-printer function for exceptions encountered an unsupported
    exception variant [exn]. This is used together with
    {!val:register_exception_printer}. *)
val raise_unsupported_exception_printing : exn -> 'a

(** [register_exception_printer pp_exn] registers the pretty-printing
    function [pp_exn] for printing some exceptions. If [pp_exn] does not
    support an exception variant [exn], then it should call
    [raise_unsupported_exception_printing exn].

    Example usage:

    {[
      let pp_exception ppf = function
        | My_exception _ -> Format.fprintf ppf _
        | exn -> Error.raise_unsupported_exception_printing exn

      let () = Error.register_exception_printer pp_exception
    ]} *)
val register_exception_printer : (Format.formatter -> exn -> unit) -> unit

(** Abstract dummy datatype to enforce that printing be done using the
    printing functions provided by this module. *)
type print_result

(** Wrapper around Printexc.register_printer. The given function should use
    partial pattern matching (ew) to signal that it doesn't know how to deal
    with other types of exceptions. *)
val register_printer : (exn -> print_result) -> unit

(** Wrapper around Printexc.register_printer. The given function should
    return None if it doesn't know how to handle a given exception. *)
val register_printer' : (exn -> print_result option) -> unit

(** Registers a printer for an exception using the a given exception
    selection function and exception formatter. *)
val register_printing_function :
  (exn -> 'a option) -> (Format.formatter -> 'a -> unit) -> unit

(** Registers a printer for an exception that carries a location using the
    given exception selection function and exception formatter. *)
val register_located_printing_function :
     (exn -> (Location.t * 'a) option)
  -> (Format.formatter -> 'a -> unit)
  -> unit

(** Use suplied formatter for printing errors. *)
val print : (Format.formatter -> unit) -> print_result

(** Use supplied formatter for printing errors decorated with location
    information. *)
val print_with_location :
  Location.t -> (Format.formatter -> unit) -> print_result

(** Helper function to construct an error message reporting a mismatch
    between something that was expected and what was actually encountered.
    e.g. a type mismatch or a context clash.

    example: report_mismatch ppf "Type mismatch." "Expected type" pp_ty1 ty1
    "Inferred type" pp_ty2 ty2 *)
val report_mismatch :
     Format.formatter
  -> string
  -> string
  -> (Format.formatter -> 'a -> unit)
  -> 'a
  -> string
  -> (Format.formatter -> 'b -> unit)
  -> 'b
  -> unit

val reset_information : unit -> unit

val get_information : unit -> string

val add_information : string -> unit
