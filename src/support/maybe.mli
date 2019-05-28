exception NoValue (** Thrown when attempting to get a maybe when there's None. *)
val eliminate : (unit -> 'b) -> ('a -> 'b) -> 'a option -> 'b

val is_some : 'a option -> bool

val get' : exn -> 'a option -> 'a

val get : 'a option -> 'a

(** Convert a boolean to an option.
    When used with other monadic operations, this is (a specialized)
    `guard` function from Haskell, which allows to abort a monadic
    computation on account of a boolean check.
 *)
val of_bool : bool -> unit option

val map : ('a -> 'b) -> 'a option -> 'b option

val ( $ ) : 'a option -> ('a -> 'b option) -> 'b option
                                                
val pure : 'a -> 'a option

(** Maps a function that may fail over a list, and eagerly fails as
    soon as any individual call fails.
    Note that elements beyond the first failing one will not be
    processed.
 *)
val traverse : ('a -> 'b option) -> 'a list -> 'b list option

(** Folds a list with a function that may fail, eagerly failing.
    Note that elements beyond the first failing one will not be
    processed.
 *)
val fold_left : ('b -> 'a -> 'b option) -> 'b -> 'a list -> 'b option

val none : 'a option

val ( $> ) : 'a option -> ('a -> 'b) -> 'b option

val void : 'a option -> unit option

(**
 * Applies a transformation to a list that may fail, removing failed results.
 * Side-effects are guaranteed to run from left to right.
 * This is the same as composing `List.map` with `cat_options`, but
 * incurs only one traversal of the list.
 *)
val filter_map : ('a -> 'b option) -> 'a list -> 'b list

(**
 * Removes all `None` options from the list.
 *
 * In fact, `cat_options` is implemented in terms of `filter_map`.
 *)
val cat_options : 'a option list -> 'a list

(**
 * Prints an option by doing nothing if it is `None`; else it uses the given printer.
 *)
val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit
