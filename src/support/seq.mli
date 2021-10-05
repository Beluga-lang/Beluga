include module type of Stdlib.Seq

(** [to_list s] converts [s] to a list. The sequence traversal happens
    immediately and will not terminate on infinite sequences.
*)
val to_list : 'a t -> 'a list
