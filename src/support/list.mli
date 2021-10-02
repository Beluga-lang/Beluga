include module type of Stdlib.List

(** [last l] is the last element in the list.
    @raise Invalid_argument if the list is empty.
*)
val last : 'a list -> 'a

(** [pairs [x_1; x_2; ...; x_n]] is
    [[(x_1, x_2); (x_2, x_3); ...; (x_n-1, x_n)]], the list of all successive
    pairs in [[x_1; x_2; ...; x_n]].
    The output list has one element less than the input list.
*)
val pairs : 'a list -> ('a * 'a) list

(** [null l] is true if and only if [l = []].
*)
val null : 'a list -> bool

(** [nonempty l] is true if and only if [l <> []].
*)
val nonempty : 'a list -> bool

(** [filter_rev p l] returns all the elements of the list [l] that satisfy the
    predicate [f]. The order of the elements in the input list is reversed.
*)
val filter_rev : ('a -> bool) -> 'a list -> 'a list

(** [for_each l f] is [map f l].
*)
val for_each : 'a list -> ('a -> 'b) -> 'b list

(** [for_each_ l f] is [iter f l]
*)
val for_each_ : 'a list -> ('a -> unit) -> unit

(** [uncons l] is [Some (hd l, tl l)] if [l <> []] and [None] otherwise.
*)
val uncons : 'a list -> ('a * 'a list) option

(** [concat_map f [x1; x2; ...; xn]] is [f x1 @ f x2 @ ... @ f xn].
    It is the "bind" monadic operation for lists.
    It is more efficient than separately mapping and concatenating lists.
*)
val concat_map : ('a -> 'b list) -> 'a list -> 'b list

(** [concat_mapi f [x0; x1; ...; xn]] is [f 0 x0 @ f 1 x1 @ ... @ f n xn].
*)
val concat_mapi : (int -> 'a -> 'b list) -> 'a list -> 'b list

(** [index_of p l] is the index of the first element in [l] that satisfies the
    predicate [p]. Returns [None] if no such element was found.
*)
val index_of : ('a -> bool) -> 'a list -> int option

(** [equals eq [a1; ...; an] [b1; ..; bm]] holds when the two input lists have
    the same length, and for each pair of elements [ai], [bi] at the same
    position we have [eq ai bi].
    Note: the [eq] function may be called even if the lists have different
    lengths. If you know your equality function is costly, you may want to
    check {!compare_lengths} first.
*)
val equals : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool

(** [hd_opt l] is [Some (hd l)] if [l <> []] and [None] otherwise.
*)
val hd_opt : 'a list -> 'a option

(** [index [x0; x1; ...; xn]] is [[(0, x0); (1, x1); ...; (n, xn)]].
*)
val index : 'a list -> (int * 'a) list

(** [mapi2 f [x0; x1; ...; xn] [y0; y1; ...; yn]] is
    [[f 0 x0 y0; f 1 x1 y1; ...; f n xn yn]].
    @raise Invalid_argument if the two lists are determined to not have the same
    length.
*)
val mapi2 : (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

(** [drop k l] is [l] without its first [k] elements. If [l] has fewer than
    [k] elements, then [[]] is returned.
*)
val drop : int -> 'a list -> 'a list
