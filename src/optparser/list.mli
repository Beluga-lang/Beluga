include module type of Stdlib.List

(** [take_circularly k \[x1; x2; ...; xn\]] is the list of the first [k]
    elements taken fron the sequence
    [\[x1; x2; ...; xn; x1; x2; ...; xn; x1; ...\]]. If [k < 0], then [\[\]]
    is returned.

    @raise Invalid_argument if the input list is empty. *)
val take_circularly : int -> 'a t -> 'a t

(** [maximum_element max default xs] is the maximum element in [xs] by
    comparison using [maximum], or [default] if [xs] is empty. *)
val maximum_element : ('a -> 'a -> 'a) -> 'a -> 'a list -> 'a
