include module type of Stdlib.Option

val eliminate : (unit -> 'b) -> ('a -> 'b) -> 'a option -> 'b

(** Gets the value from an option if it exists. Otherwise gives a default value. *)
val get_default : 'a -> 'a option -> 'a

(** Gets the value from an option if it exists. Otherwise raises the given exception. *)
val get' : exn -> 'a option -> 'a

(** Convert a boolean to an option.
    When used with other monadic operations, this is (a specialized)
    `guard` function from Haskell, which allows to abort a monadic
    computation on account of a boolean check.
 *)
val of_bool : bool -> unit option

val ( $ ) : 'a option -> ('a -> 'b option) -> 'b option

(** Named, flipped version of ($). *)
val flat_map : ('a -> 'b option) -> 'a option -> 'b option

val ( <|> ) : 'a option Lazy.t -> 'a option Lazy.t -> 'a option Lazy.t

(** Selects the first alternative that succeeds.
    Forces every thunk until one computes `Some x'.
 *)
val choice : 'a option Lazy.t list -> 'a option Lazy.t

(** Returns the first option that isn't None, if any. *)
val alt : 'a option -> 'a option -> 'a option

(** Maps a function that may fail over a list, and eagerly fails as
    soon as any individual call fails.
    Note that elements beyond the first failing one will not be
    processed.
 *)
val traverse : ('a -> 'b option) -> 'a list -> 'b list option

(** Maps a function that may fail over a list, and eagerly fails as
    soon as an individual call fails. The functions themselves may not
    compute interesting results.
 *)
val traverse_ : ('a -> unit option) -> 'a list -> unit option

(** Folds a list with a function that may fail, eagerly failing.
    Note that elements beyond the first failing one will not be
    processed.
 *)
val fold_left : ('b -> 'a -> 'b option) -> 'b -> 'a list -> 'b option

(** Transforms the contents of an option with a pure function. *)
val ( $> ) : 'a option -> ('a -> 'b) -> 'b option

(** Returns the second option only if the first is `Some _'.
    In a sense, this is the opposite of <|>.
 *)
val ( &> ) : 'a option -> 'b option -> 'b option

val void : 'a option -> unit option

(**
 * Removes all `None` options from the list.
 *
 * In fact, `cat_options` is implemented in terms of `filter_map`.
 *)
val cat_options : 'a option list -> 'a list

(** Specialized effectful eliminator for option types. *)
val when_some : 'a option -> ('a -> unit) -> unit

type 'a all_or_none =
  [ `all of 'a list
  | `mixed of 'a list
  | `none
  | `empty
  ]

val all_or_none : 'a option list -> 'a all_or_none

(**
 * Specialized eliminator for options to print them generally.
 *)
val print' : (Format.formatter -> unit -> unit) ->
             (Format.formatter -> 'a -> unit) ->
             Format.formatter ->
             'a option ->
             unit

(**
 * Prints an option by doing nothing if it is `None`; else it uses the given printer.
 *)
val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit

(**
 * Prints an option by showing `None` or `Some X` where X is generated
 * by the given formatting function.
 *)
val show : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit
