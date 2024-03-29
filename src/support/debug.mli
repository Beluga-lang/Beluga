(** Debug-print library with up to 31 separate categories of information.

    @author Joshua Dunfield
    @author Jacob Thomas Errington *)

(** Usage:

    - In each client module, create debug-printer functions by calling
      {!makeFunctions} or {!makeFunctions'}:

    {[
      let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [...])

      let (dprintf, dprint, dprnt) = Debug.makeFunctions' (Debug.toFlags [...])
    ]}

    where `...' is the category (or categories) specific to the module.

    Then,

    - [dprint] takes a thunk
    - [dprnt] (misspelled) takes a string
    - [dprintf] takes a callback receiving formatter, with which you can
      generate formatted output, including custom indentation.

    If debugging is turned off, [print] is more efficient whenever computing
    the string is at all nontrivial. This actually matters; running the test
    suite with debug mode enabled takes several times longer.

    All functions will add a newline after printing your text. *)

type flags

val enable : unit -> unit

val is_enabled : unit -> bool

val init : string option -> unit

val makeFunctions : flags -> ((unit -> string) -> unit) * (string -> unit)

(** This submodule defines a record containing a higher-rank polymorphic
    function. We need this record type so that we can pass a
    partially-applied [Format.fprintf] function to client modules. We
    introduce the submodule so that client modules can selectively open it if
    they want to use the format-string support provided by [Debug]; this will
    bring into scope only the [fmt] type and the [fmt] projection for the
    record.

    Clients can then write:

    {[
      let dprintf, _, _ = Debug.makeFunctions (Debug.toFlags [ 11 ])

      open Debug.Fmt

      let _ = dprintf (fun p -> p.fmt "%s %d" "hello" 4)
    ]} *)
module Fmt : sig
  type fmt = { fmt : 'a. ('a, Format.formatter, unit) format -> 'a }
end

type 'a io = 'a -> unit

val makeFunctions' : flags -> Fmt.fmt io io * (unit -> string) io * string io

val toFlags : int list -> flags

(** Tests if a given flag is set. *)
val flag : int -> bool

(** Runs the given function with debug printing indented by the given number
    of spaces. Pass in [dprintf] obtained by calling [makeFunctions'].

    Note that the vbox introduced to indent will NOT be closed if the given
    function raises an exception. This is a trade-off since the alternative
    would be to reraise the exception, which sadly destroys the backtrace. *)
val indented : Fmt.fmt io io -> int -> (unit -> 'a) -> 'a

val printf : Fmt.fmt io -> unit
