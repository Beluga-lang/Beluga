include module type of DynArray

(** [append_list dst l] effectfully appends all the elements of [l] to [dst]. *)
val append_list : 'a t -> 'a list -> unit

(** [head d] is [Some h] with [h] being the first element of [d] if [d] is
    non-empty, and [None] otherwise. *)
val head : 'a t -> 'a option

(** [get_opt d i] is [Some (get d i)] if [d] has an element at index [i], and
    [None] otherwise. *)
val get_opt : 'a t -> int -> 'a option

(** [rfind_opt_idx d p] is [Some (i, l)] where [l] is the last element in [d]
    that satisfies [p] and [i] is the index of [l] in [d], and [None]
    otherwise. *)
val rfind_opt_idx : 'a t -> ('a -> bool) -> (int * 'a) option
