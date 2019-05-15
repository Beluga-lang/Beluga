(* File: Debug.sml
  Author: Joshua Dunfield
  Contents: Debug-print library with up to 31 separate categories of information.

  Usage:

   - show, showAll, showNone determine which categories will be printed.

   - In each client module, create debug-printer functions by calling `makeFunctions':

      let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [...])

    where `...' is the category (conceivably, categories) specific to the module.

   - `print' takes a thunk; `prnt' (misspelled) takes a string.
     If debugging is turned off, `print' is more efficient whenever
      computing the string is at all nontrivial.  This can actually matter, because
      the point of this module is really to allow you to leave debugging print statements
      everywhere, and it's easy to forget they're around.

     Both `print' and `prnt' add a newline.

  TODO: Add a third form that's like `printf', for those who enjoy such things.

  OLD TODO: Functorize.  Have one debug-functor for each category; the numbers
    then become debugging levels per category, allowing one to incrementally
    crank up verbosity for the module of interest.  Have a single module whose `show'
    is propagated to all debug-functors.
*)

type flags

val chatter : int ref
val pipeDebug : bool ref
val filename : string ref
val makeFunctions :
  flags ->
  ((unit -> string) -> unit) * (string -> unit)

(* In most cases, you should use `makeFunctions' rather than `print'/`prnt' directly *)
val print : flags -> (unit -> string) -> unit
val prnt : flags -> string -> unit
val toFlags : int list -> flags

val show : flags -> unit    (* Set the types of output to be printed *)
val showAll : unit -> unit
val showNone : unit -> unit

val indent : int -> unit
val outdent : int -> unit
val pushIndentationLevel : unit -> unit
val popIndentationLevel : unit -> unit
