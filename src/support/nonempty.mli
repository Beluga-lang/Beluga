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

(** Counts the number of elements in the nonempty list. *)
val length : 'a t -> int

(** Converts a list to a nonempty list. *)
val of_list : 'a list -> 'a t option

(** Converts a nonempty list to a list. *)
val to_list : 'a t -> 'a list

(** Maps a function over the nonempty list. *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** Collapses a nonempty sequence to a single element, provided all
    elements are (structurally) equal. *)
val all_equal : 'a t -> 'a option

val print : ?pp_sep:(Format.formatter -> unit -> unit) ->
            (Format.formatter -> 'a -> unit) ->
            Format.formatter ->
            'a t ->
            unit

module Syntax : sig
  val ($>) : 'a t -> ('a -> 'b) -> 'b t
end
