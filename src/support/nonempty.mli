(** Nonempty list. *)
type 'a t

type 'a nonempty = 'a t

val uncons : 'a t -> 'a * 'a list
val head : 'a t -> 'a
val tail : 'a t -> 'a list

val unsnoc : 'a t -> 'a list * 'a
val last : 'a t -> 'a

(** Constructs a nonempty list given an element. *)
val from : 'a -> 'a list -> 'a t

(** Elimination principle for `Nonempty.t'. *)
val fold_right : ('a -> 'b) (* for the Sing case *) ->
                 ('a -> 'b -> 'b) (* for the Cons case *) ->
                 'a t ->
                 'b

(** Elimination principle for `Nonempty.t'. *)
val fold_left : ('a -> 'b) (* for the Sing case *) ->
                ('b -> 'a -> 'b) (* for the Cons cas *) ->
                'a t ->
                'b

(** [destructure f l] is [f h t], where [h] and [t] are the head and tail of [l]
    respectively.
*)
val destructure : ('a -> 'a list -> 'b) -> 'a t -> 'b

(** Counts the number of elements in the nonempty list. *)
val length : 'a t -> int

(** Converts a list to a nonempty list. *)
val of_list : 'a list -> 'a t option

(** Converts a nonempty list to a list. *)
val to_list : 'a t -> 'a list

(** Maps a function over the nonempty list. *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** Runs an effectful function over the nonempty list. *)
val iter : ('a -> unit) -> 'a t -> unit

val for_all : ('a -> bool) -> 'a t -> bool

(** Collapses a nonempty sequence to a single element, provided all
    elements are (structurally) equal. *)
val all_equal : 'a t -> 'a option

(** Finds the leftmost minimal element of the sequence according to
    the given decision procedure for the strict less-than relation on
    'a.
 *)
val minimum_by : ('a -> 'a -> bool) -> 'a t -> 'a

(** Finds the leftmost minimal element of the sequence according to
    the default ordering for the type 'a.
 *)
val minimum : 'a t -> 'a

(** Finds the leftmost maximal element of the sequence according to
    the default ordering for the type 'a. *)
val maximum : 'a t -> 'a

(** Groups elements of a list according to a key computed from the
    element. The input list need not be sorted.
    (The algorithm inserts every element of the list into a hashtable
    in order to construct the grouping.)
    Each group is guaranteed to be nonempty.
 *)
val group_by : ('a -> 'key) -> 'a list -> ('key * 'a t) list

val print : ?pp_sep:(Format.formatter -> unit -> unit) ->
            (Format.formatter -> 'a -> unit) ->
            Format.formatter ->
            'a t ->
            unit

module Syntax : sig
  val ($>) : 'a t -> ('a -> 'b) -> 'b t
end
