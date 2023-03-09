include module type of Stdlib.Seq

(** [of_gen g] is the sequence obtained by sequentially invoking the
    effectful function [g] to produce the next element [x] when
    [g () = Option.Some x].

    If it is ever the case that [g () = Option.None], then the resultant
    sequence has finite length. *)
val of_gen : (unit -> 'a option) -> 'a t

(** [of_list l] is the sequence obtained from the list [l]. *)
val of_list : 'a list -> 'a t

(** [to_list s] converts [s] to a list. The sequence traversal happens
    immediately and will not terminate on infinite sequences. *)
val to_list : 'a t -> 'a list
