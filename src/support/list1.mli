(** The type of lists of length at least [1]. *)
type 'a t = private T of 'a * 'a list

(** {1 Constructors} *)

(** [from h t] is the non-empty list obtained by prepending [h] onto the list
    [t]. *)
val from : 'a -> 'a list -> 'a t

(** [singleton e] is the non-empty list with the single element [e] in it. *)
val singleton : 'a -> 'a t

(** [cons e l] is the non-empty list obtained by prepending [e] onto [l]. *)
val cons : 'a -> 'a t -> 'a t

(** [rev l] is [l] in reverse order. *)
val rev : 'a t -> 'a t

(** {1 Destructors} *)

(** [uncons l] is [(head l, tail l)]. *)
val uncons : 'a t -> 'a * 'a list

(** [head l] is the first element in [l]. *)
val head : 'a t -> 'a

(** [tail l] is the list of elements that succeed the head of [l]. *)
val tail : 'a t -> 'a list

(** [unsnoc (a_1, \[a_2; ...; a_(n-1); a_n\])] is
    [(\[a_1; a_2; ...; a_(n-1)\], a_n)], with [a_n] being the last element in
    the non-empty list, and [\[a_1; a_2; ...; a_(n-1)\]] being the list of
    elements that precede [a_n] in order. *)
val unsnoc : 'a t -> 'a list * 'a

(** [last l] is the last element in [l]. *)
val last : 'a t -> 'a

(** [length l] the number of elements in [l]. *)
val length : 'a t -> int

(** [append l1 l2] is the concatenation of [l1] and [l2]. *)
val append : 'a t -> 'a t -> 'a t

(** [flatten l] is the concatenation of the lists in [l]. *)
val flatten : 'a t t -> 'a t

(** {1 Comparison} *)

(** [compare l1 l2] is equivalent to [compare (length l1) (length l2)],
    except that the computation stops after reaching the end of the shortest
    list. *)
val compare_lengths : 'a t -> 'b t -> int

(** [compare_length_with l n] is equivalent to [compare (length l) n],
    except that the computation stops after at most [n] iterations on [l]. *)
val compare_length_with : 'a t -> int -> int

(** [equal eq (a1, \[a2; ...; an\]) (b1, \[b2; ...; bm\])] holds when the two
    input lists have the same length, and for each pair of elements [ai],
    [bi] at the same position we have [eq ai bi].

    Note: the [eq] function may be called even if the lists have different
    lengths. If you know your equality function is costly, you may want to
    check {!List1.compare_lengths} first. *)
val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

(** [compare cmp (a1, \[a2; ...; an\]) (b1, \[b2; ...; bm\])] performs a
    lexicographic comparison of the two input lists, using the same
    ['a -> 'a -> int] interface as {!Stdlib.compare}:

    - [cons a1 l1] is smaller than [cons a2 l2] (negative result) if [a1] is
      smaller than [a2], or if they are equal (0 result) and [l1] is smaller
      than [l2]
    - [singleton a] is smaller than [singleton b] if [a] is smaller than [b]

    Note: the [cmp] function will be called even if the lists have different
    lengths. *)
val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

(** {1 Iterators} *)

(** [iter f (a1, \[a2; ...; an\])] applies function [f] in turn to
    [\[a1; ...; an\]]. It is equivalent to
    [begin f a1; f a2; ...; f an; () end]. *)
val iter : ('a -> unit) -> 'a t -> unit

(** [map f (a1, \[a2; ...; an\])] is [(f a1, \[f a2; ...; f an\])]. *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** [fold_right sing cons (a1, \[a2; ...; an\])] is
    [cons a1 (cons a2 (... (sing an) ...))]. *)
val fold_right : ('a -> 'b) -> ('a -> 'b -> 'b) -> 'a t -> 'b

(** [fold_left sing cons (a1, \[a2; ...; an\])] is
    [cons (... (cons (sing a1) a2) ....) an]. *)
val fold_left : ('a -> 'b) -> ('b -> 'a -> 'b) -> 'a t -> 'b

(** [filter_map f l] applies [f] to every element of [l], filters out the
    [Option.None] elements and returns the list of the arguments of the
    [Option.Some] elements. *)
val filter_map : ('a -> 'b option) -> 'a t -> 'b list

(** [concat_map f l] is [concat (map f l)]. *)
val concat_map : ('a -> 'b t) -> 'a t -> 'b t

(** Collapses a non-empty sequence to a single element, provided all elements
    are (structurally) equal. *)
val all_equal : 'a t -> 'a option

(** Maps a function that may fail over a non-empty list, and eagerly fails as
    soon as any individual call fails. Note that elements beyond the first
    failing one will not be processed. *)
val traverse : ('a -> 'b option) -> 'a t -> 'b t option

(** {1 Iterators on two lists} *)

(** [map2 f (a1, \[a2; ...; an\]) (b1, \[b2; ...; bn\])] is
    [(f a1 b1, \[f a2 b2; ...; f an bn\])].

    @raise Invalid_argument
      if the two lists are determined to have different lengths. *)
val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

(** {1 List scanning} *)

(** [for_all p (a1, \[a2; ...; an\])] checks if all elements of the non-empty
    list satisfy the predicate [p]. That is, it returns
    [(p a1) && (p a2) && ... && (p an)]. *)
val for_all : ('a -> bool) -> 'a t -> bool

(** [exists p (a1, \[a2; ...; an\])] checks if any element of the non-empty
    list satisfies the predicate [p]. That is, it returns
    [(p a1) || (p a2) || ... || (p an)]. *)
val exists : ('a -> bool) -> 'a t -> bool

(** {1 List searching} *)

(** [find_opt p l] is the first element in [l] satisfying the predicate [p].
    Returns [Option.None] if there is no such element. *)
val find_opt : ('a -> bool) -> 'a t -> 'a option

(** [find_map f l] applies [f] to the elements of [l] in order, and returns
    the first result of the form [Option.Some v], or [Option.None] if none
    exist. *)
val find_map : ('a -> 'b option) -> 'a t -> 'b option

(** Finds the leftmost minimal element of the sequence according to the given
    decision procedure for the strict less-than relation on ['a]. *)
val minimum_by : ('a -> 'a -> bool) -> 'a t -> 'a

(** Finds the leftmost maximal element of the sequence according to the given
    decision procedure for the strict greater-than relation on ['a]. *)
val maximum_by : ('a -> 'a -> bool) -> 'a t -> 'a

(** Finds the leftmost minimal element of the sequence according to the
    default ordering for the type 'a. *)
val minimum : 'a t -> 'a

(** Finds the leftmost maximal element of the sequence according to the
    default ordering for the type 'a. *)
val maximum : 'a t -> 'a

(** [partition f l] returns a pair of lists [(l1, l2)], where [l1] is the
    list of all the elements of [l] that satisfy the predicate [f], and [l2]
    is the list of all the elements of [l] that do not satisfy [f]. The order
    of elements in the input list is preserved. At least one of [l1] and [l2]
    is non-empty. *)
val partition : ('a -> bool) -> 'a t -> 'a list * 'a list

(** Groups elements of a list according to a key computed from the element.
    The input list need not be sorted. (The algorithm inserts every element
    of the list into a hashtable in order to construct the grouping.) Each
    group is guaranteed to be non-empty. *)
val group_by : ('a -> 'key) -> 'a list -> ('key * 'a t) list

(** {1 Non-empty lists of pairs}*)

(** Transform a non-empty list of pairs into a pair of non-empty lists:
    [split ((a1, b1), \[(a2, b2); ...; (an, bn)\])] is
    [(a1, \[a2; ...; an\]), (b1, \[b2; ...; bn\])]. *)
val split : ('a * 'b) t -> 'a t * 'b t

(** Transform a pair of lists into a list of pairs:
    [combine (a1, \[a2; ...; an\]) (b1, \[b2; ...; bn\])] is
    [((a1, b1), \[(a2, b2); ...; (an, bn)\])].

    @raise Invalid_argument if the two lists have different lengths. *)
val combine : 'a t -> 'b t -> ('a * 'b) t

(** {1 Apply} *)

(** [ap (x1, \[x2; ...; xn\]) (f1, \[f2; ...; fn\])] is
    [(f1 x1, \[f2 x2; ...; fn xn\])].

    @raise Invalid_argument
      if the two lists are determined to have different lengths. *)
val ap : 'a t -> ('a -> 'b) t -> 'b t

(** [ap_one x (f1, \[f2; ...; fn\])] is [(f1 x, \[f2 x; ...; fn x\])]. *)
val ap_one : 'a -> ('a -> 'b) t -> 'b t

(** {1 Printing} *)

(** [pp ?pp_sep pp_v ppf l] prints the items of the non-empty list [l] using
    [pp_v] to print each item and calling [pp_sep] between items on the
    formatter [ppf]. *)
val pp :
     ?pp_sep:(Format.formatter -> unit -> unit)
  -> (Format.formatter -> 'a -> unit)
  -> Format.formatter
  -> 'a t
  -> unit

(** [show ?pp_sep pp_v l] shows as a string the items of the non-empty list
    [l] using [pp_v] to show each item and calling [pp_sep] between items. *)
val show :
     ?pp_sep:(Format.formatter -> unit -> unit)
  -> (Format.formatter -> 'a -> unit)
  -> 'a t
  -> string

(** {1 Interoperability} *)

(** Converts a list to a non-empty list. *)
val of_list : 'a list -> 'a t option

(** Converts a non-empty list to a list. *)
val to_list : 'a t -> 'a list

(** {1 Instances} *)

module MakeEq (E : Eq.EQ) : Eq.EQ with type t = E.t t

module MakeOrd (O : Ord.ORD) : Ord.ORD with type t = O.t t

module MakeShow (S : Show.SHOW) : Show.SHOW with type t = S.t t
