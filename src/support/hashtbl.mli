include module type of Stdlib.Hashtbl

(** [map f m] maps the values in [m] by [f].
    This involves converting [m] to a {!Seq}, mapping the values by [m], then
    constructing the new hashtable from the resulting sequence.
*)
val map : ('a -> 'b) -> ('k, 'a) t -> ('k, 'b) t

(** [group_by k l] groups the values in [l] by the keys assigned by [k] into a
    hashtable.
*)
val group_by : ('a -> 'k) -> 'a list -> ('k, 'a list) t
