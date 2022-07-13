include module type of Stdlib.List

(** [last l] is the last element in the list.

    @raise Invalid_argument if the list is empty. *)
val last : 'a list -> 'a

(** [pairs \[x_1; x_2; ...; x_n\]] is
    [\[(x_1, x_2); (x_2, x_3); ...; (x_n-1, x_n)\]], the list of all
    successive pairs in [\[x_1; x_2; ...; x_n\]]. The output list has one
    element less than the input list. *)
val pairs : 'a list -> ('a * 'a) list

(** [null l] is true if and only if [l = \[\]]. *)
val null : 'a list -> bool

(** [nonempty l] is true if and only if [l <> \[\]]. *)
val nonempty : 'a list -> bool

(** [filter_rev p l] returns all the elements of the list [l] that satisfy
    the predicate [f]. The order of the elements in the input list is
    reversed. *)
val filter_rev : ('a -> bool) -> 'a list -> 'a list

(** [find_map f l] applies [f] to the elements of [l] in order, and returns
    the first result of the form [Option.Some v], or [Option.None] if none
    exist. *)
val find_map : ('a -> 'b option) -> 'a list -> 'b option

(** [uncons l] is [Option.Some (hd l, tl l)] if [l <> \[\]] and [Option.None]
    otherwise. *)
val uncons : 'a list -> ('a * 'a list) option

(** [concat_map f \[x1; x2; ...; xn\]] is [f x1 @ f x2 @ ... @ f xn]. It is
    the "bind" monadic operation for lists. It is more efficient than
    separately mapping and concatenating lists. *)
val concat_map : ('a -> 'b list) -> 'a list -> 'b list

(** [concat_mapi f \[x0; x1; ...; xn\]] is [f 0 x0 @ f 1 x1 @ ... @ f n xn]. *)
val concat_mapi : (int -> 'a -> 'b list) -> 'a list -> 'b list

(** [index_of p l] is the index of the first element in [l] that satisfies
    the predicate [p]. Returns [Option.None] if no such element was found. *)
val index_of : ('a -> bool) -> 'a list -> int option

(** [equal eq \[a1; ...; an\] \[b1; ..; bm\]] holds when the two input lists
    have the same length, and for each pair of elements [ai], [bi] at the
    same position we have [eq ai bi]. Note: the [eq] function may be called
    even if the lists have different lengths. If you know your equality
    function is costly, you may want to check {!compare_lengths} first. *)
val equal : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool

(** [hd_opt l] is [Option.Some (hd l)] if [l <> \[\]] and [Option.None]
    otherwise. *)
val hd_opt : 'a list -> 'a option

(** [index \[x0; x1; ...; xn\]] is [\[(0, x0); (1, x1); ...; (n, xn)\]]. *)
val index : 'a list -> (int * 'a) list

(** Same as {!fold_left2} but for three lists. *)
val fold_left3 :
  ('b -> 'a1 -> 'a2 -> 'a3 -> 'b) -> 'b -> 'a1 t -> 'a2 t -> 'a3 t -> 'b

(** Same as {!fold_left3} but for four lists. *)
val fold_left4 :
     ('b -> 'a1 -> 'a2 -> 'a3 -> 'a4 -> 'b)
  -> 'b
  -> 'a1 t
  -> 'a2 t
  -> 'a3 t
  -> 'a4 t
  -> 'b

(** [mapi2 f \[x0; x1; ...; xn\] \[y0; y1; ...; yn\]] is
    [\[f 0 x0 y0; f 1 x1 y1; ...; f n xn yn\]].

    @raise Invalid_argument
      if the two lists are determined to not have the same length. *)
val mapi2 : (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

(** [drop k l] is [l] without its first [k] elements. If [l] has fewer than
    [k] elements, then [\[\]] is returned. *)
val drop : int -> 'a list -> 'a list

(** [ap \[x1; x2; ...; xn\] \[f1; f2; ...; fn\]] is
    [\[f1 x1; f2 x2; ...; fn xn\]].

    @raise Invalid_argument
      if the two lists are determined to have different lengths. *)
val ap : 'a list -> ('a -> 'b) list -> 'b list

(** [ap_one x \[f1; f2; ...; fn\]] is [\[f1 x; f2 x; ...; fn x\]]. *)
val ap_one : 'a -> ('a -> 'b) list -> 'b list

(** Transform a list of pairs into a pair of lists:
    [split \[(a1, b1); ...; (an, bn)\]] is
    [(\[a1; ...; an\], \[b1; ...; bn\])]. *)
val split : ('a * 'b) list -> 'a list * 'b list

(** Transform a pair of lists into a list of pairs:
    [combine \[a1; ...; an\] \[b1; ...; bn\]] is
    [\[(a1, b1); ...; (an, bn)\]].

    @raise Invalid_argument if the two lists have different lengths. *)
val combine : 'a list -> 'b list -> ('a * 'b) list

(** [take k \[x1; x2; ...; xn\]] is
    [(\[x1; x2; ...; xk\], \[x(k+1); x(k+2); ...; xn\])].

    - If [k <= 0], then [take k \[x1; x2; ...; xn\]] is
      [(\[\], \[x1; x2; ...; xn\])].
    - If [k >= n], then [take k \[x1; x2; ...; xn\]] is
      [(\[x1; x2; ...; xn\], \[\])]. *)
val take : int -> 'a list -> 'a list * 'a list

(** [compare cmp \[a1; ...; an\] \[b1; ...; bm\]] performs a lexicographic
    comparison of the two input lists, using the same ['a -> 'a -> int]
    interface as {!Stdlib.compare}:

    - [a1 :: l1] is smaller than [a2 :: l2] (negative result) if [a1] is
      smaller than [a2], or if they are equal (0 result) and [l1] is smaller
      than [l2]
    - the empty list [\[\]] is strictly smaller than non-empty lists Note:
      the [cmp] function will be called even if the lists have different
      lengths. *)
val compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int

(** {1 Printing} *)

(** [pp ?pp_sep pp_v ppf l] prints the items of the list [l] using [pp_v] to
    print each item and calling [pp_sep] between items on the formatter
    [ppf]. *)
val pp :
     ?pp_sep:(Format.formatter -> unit -> unit)
  -> (Format.formatter -> 'a -> unit)
  -> Format.formatter
  -> 'a t
  -> unit

(** [show ?pp_sep pp_v l] shows as a string the items of the list [l] using
    [pp_v] to show each item and calling [pp_sep] between items. *)
val show :
     ?pp_sep:(Format.formatter -> unit -> unit)
  -> (Format.formatter -> 'a -> unit)
  -> 'a t
  -> string

(** {1 Instances} *)

module MakeEq (E : Eq.EQ) : Eq.EQ with type t = E.t t

(** Functor building an implementation of {!Ord} given a totally ordered
    type. The ordering between two lists of totally ordered types is as
    follows with respect to [compare l r]:

    - [compare l r < 0] if the first non-equal comparison has the element in
      [l] be less than the element in [r], or [r] starts with [l].
    - [compare l r > 0] if the first non-equal comparison has the element in
      [l] be greater than the element in [r], or [l] starts with [r].
    - [compare l r = 0] if all elements in [l] and [r] are pairwise equal. *)
module MakeOrd (O : Ord.ORD) : Ord.ORD with type t = O.t t

module MakeShow (S : Show.SHOW) : Show.SHOW with type t = S.t t
