(** Utilities for raising and catching exceptions. *)

open Support

(** [enable_colored_output ()] enables coloring functions in pretty-printing
    of exceptions. *)
val enable_colored_output : unit -> unit

(** [disable_colored_output ()] disables coloring functions in
    pretty-printing of exceptions. *)
val disable_colored_output : unit -> unit

(** [raise exn] raises [exn]. *)
val raise : exn -> 'a

(** [re_raise exn] raises [exn] with the backtrace of the latest caught
    exception. This should only be used if [exn] was caught in a [try-with]
    expression. *)
val re_raise : exn -> 'a

(** [raise_notrace exn] raises [exn] without producing a stack trace. This is
    more efficient for exceptions used for control flow. *)
val raise_notrace : exn -> 'a

(** [Violation message] is the exception signalling a programmer error, like
    an unmet pre-condition. This exception variant should not be exported,
    but it is incorrectly being used for backtracking with exceptions in the
    core library. *)
exception Violation of string

(** [raise_violation ?location message] raises a violation exception with the
    given [message] and [location]. *)
val raise_violation : ?location:Location.t -> string -> 'a

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

(** [raise_at1_opt location_opt cause] raises
    [located_exception1 location cause] if
    [location_opt = Option.Some location], or raises [cause] if
    [location_opt = Option.None]. *)
val raise_at1_opt : Location.t Option.t -> exn -> 'a

(** [located_exception_printer pp locations] is a printer for the exception
    printed by [pp] with location snippets for [locations] in order. *)
val located_exception_printer :
     (Format.formatter -> unit)
  -> Location.t List1.t
  -> Format.formatter
  -> unit

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

val raise_composite_exception : exn List2.t -> 'a

val raise_composite_exception2 : exn -> exn -> 'a

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

val raise_aggregate_exception : exn List2.t -> 'a

val raise_aggregate_exception2 : exn -> exn -> 'a

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
      let () =
        Error.register_exception_printer (function
          | My_exception (message : string) ->
              Format.dprintf "@[<v 0>My exception was raised:@ %s@]" message
          | exn -> Error.raise_unsupported_exception_printing exn)
    ]} *)
val register_exception_printer : (exn -> Format.formatter -> unit) -> unit

(** [find_printer exn] is the exception printer registered with
    {!register_exception_printer} that handles [exn]. If there is no such
    printer, then [raise_unsupported_exception_printing exn] is evaluated.

    [find_printer] is used when registering exception printers for exceptions
    that contain sub-exceptions, like located, aggregate or composite
    exceptions. *)
val find_printer : exn -> Format.formatter -> unit

(** Helper function to construct an error message reporting a mismatch
    between something that was expected and what was actually encountered.
    e.g. a type mismatch or a context clash.

    example: mismatch_reporter "Type mismatch." "Expected type" pp_ty1 ty1
    "Inferred type" pp_ty2 ty2 *)
val mismatch_reporter :
     string
  -> string
  -> (Format.formatter -> 'a -> unit)
  -> 'a
  -> string
  -> (Format.formatter -> 'b -> unit)
  -> 'b
  -> Format.formatter
  -> unit
