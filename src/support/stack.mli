include module type of Stdlib.Stack

val popping : 'a t -> ('a option -> 'b) -> 'b

(** [to_list s] converts [s] into a list, where the top element of [s] is the
    last element of the output list.
*)
val to_list : 'a t -> 'a list

(** [to_list_rev s] converts [s] into a list, where the top element of [s] is
    the first element of the list.
*)
val to_list_rev : 'a t -> 'a list
