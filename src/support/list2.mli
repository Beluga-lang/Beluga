(** The type of lists of length at least [2]. *)
type 'a t = private T of 'a * 'a * 'a list

(** {1 Constructors} *)

(** [from x1 x2 xs] is the list obtained by prepending [x2], then [x1] onto
    the list [xs]. *)
val from : 'a -> 'a -> 'a list -> 'a t

(** [from1 x xs] is the list obtained by prepending [x] onto the list [xs]. *)
val from1 : 'a -> 'a List1.t -> 'a t

(** [pair x1 x2] is the list with the elements [x1] and [x2] in it. *)
val pair : 'a -> 'a -> 'a t

(** [cons x xs] is the list obtained by prepending [x] onto [xs]. *)
val cons : 'a -> 'a t -> 'a t

(** [rev l] is [l] in reverse order. *)
val rev : 'a t -> 'a t

(** {1 Destructors} *)

(** [last l] is the last element in [l]. *)
val last : 'a t -> 'a

(** [length l] the number of elements in [l]. *)
val length : 'a t -> int

(** {1 Comparison} *)

(** [compare l1 l2] is equivalent to [compare (length l1) (length l2)],
    except that the computation stops after reaching the end of the shortest
    list. *)
val compare_lengths : 'a t -> 'b t -> int

(** [equal eq (a1, a2, \[a3; ...; an\]) (b1, b2, \[b3; ...; bm\])] holds when
    the two input lists have the same length, and for each pair of elements
    [ai], [bi] at the same position we have [eq ai bi].

    Note: the [eq] function may be called even if the lists have different
    lengths. If you know your equality function is costly, you may want to
    check {!List2.compare_lengths} first. *)
val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

(** [compare cmp (a1, a2, \[a3; ...; an\]) (b1, b2, \[b3; ...; bm\])]
    performs a lexicographic comparison of the two input lists, using the
    same ['a -> 'a -> int] interface as {!Stdlib.compare}:

    - [cons a1 l1] is smaller than [cons a2 l2] (negative result) if [a1] is
      smaller than [a2], or if they are equal (0 result) and [l1] is smaller
      than [l2]
    - [pair a1 a2] is smaller than [pair b1 b2] if [a1] is smaller than [b1],
      or if [a1 = b1] and [a2] is smaller than [b2]

    Note: the [cmp] function will be called even if the lists have different
    lengths. *)
val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

(** {1 Iterators} *)

(** [iter f (a1, a2, \[a3; ...; an\])] applies function [f] in turn to
    [\[a1; ...; an\]]. It is equivalent to
    [begin f a1; f a2; ...; f an; () end]. *)
val iter : ('a -> unit) -> 'a t -> unit

(** [iter2 f (a1, a2, \[a3; ...; an\]) (b1, b2, \[b3; ...; bn\])] applies
    function [f] in turn, pairwise, to [\[a1; ...; an\]] and
    [\[b1; ...; bn\]]. It is equivalent to
    [begin f a1 b1; f a2 b2; ...; f an bn; () end].

    @raise Invalid_argument
      if the two lists are determined to have different lengths. *)
val iter2 : ('a -> 'b -> unit) -> 'a t -> 'b t -> unit

(** [map f (a1, a2, \[a3; ...; an\])] is [(f a1, f a2, \[f a3; ...; f an\])]. *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** [mapi f (a0, a1, \[a2; ...; an\])] is
    [(f 0 a0, f 1 a1, \[f 2 a2; ...; f n an\])]. *)
val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t

(** [map2 f (a1, a2, \[a3; ...; an\]) (b1, b2, \[b3; ...; bn\])] is
    [(f a1 b1, f a2 b2, \[f a3 b3; ...; f an bn\])].

    @raise Invalid_argument
      if the two lists are determined to have different lengths. *)
val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

(** [mapi2 f (a0, a1, \[a2; ...; an\]) (b0, b1, \[b2; ...; bn\])] is
    [(f 0 a0 b0, f 1 a1 b1, \[f 2 a2 b2; ...; f n an bn\])].

    @raise Invalid_argument
      if the two lists are determined to have different lengths. *)
val mapi2 : (int -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

(** [fold_right fst snd cons (a1, a2, \[a3; ...; an\])] is
    [cons a1 (cons a2 (... (snd a(n-1) (fst an)) ...))]. *)
val fold_right :
  ('a -> 'b) -> ('a -> 'b -> 'c) -> ('a -> 'c -> 'c) -> 'a t -> 'c

(** [fold_left fst snd cons (a1, a2, \[a3; ...; an\])] is
    [cons (... (cons (snd (fst a1) a2) a3) ....) an]. *)
val fold_left :
  ('a -> 'b) -> ('b -> 'a -> 'c) -> ('c -> 'a -> 'c) -> 'a t -> 'c

(** [fold_left2 fst snd cons (a1, a2, \[a3; ...; an\]) (b1, b2, \[b3; ...; bn\])]
    is [cons (... (cons (snd (fst a1 b1) a2 b2) a3 b3) ....) an bn].

    @raise Invalid_argument
      if the two lists are determined to have different lengths. *)
val fold_left2 :
     ('a -> 'b -> 'c)
  -> ('c -> 'a -> 'b -> 'd)
  -> ('d -> 'a -> 'b -> 'd)
  -> 'a t
  -> 'b t
  -> 'd

(** Same as {!fold_left2} but for three lists. *)
val fold_left3 :
     ('a1 -> 'a2 -> 'a3 -> 'b)
  -> ('b -> 'a1 -> 'a2 -> 'a3 -> 'c)
  -> ('c -> 'a1 -> 'a2 -> 'a3 -> 'c)
  -> 'a1 t
  -> 'a2 t
  -> 'a3 t
  -> 'c

(** Same as {!fold_left3} but for four lists. *)
val fold_left4 :
     ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'b)
  -> ('b -> 'a1 -> 'a2 -> 'a3 -> 'a4 -> 'c)
  -> ('c -> 'a1 -> 'a2 -> 'a3 -> 'a4 -> 'c)
  -> 'a1 t
  -> 'a2 t
  -> 'a3 t
  -> 'a4 t
  -> 'c

(** [filter_map f l] applies [f] to every element of [l], filters out the
    [Option.None] elements and returns the list of the arguments of the
    [Option.Some] elements. *)
val filter_map : ('a -> 'b option) -> 'a t -> 'b list

(** Maps a function that may fail over a list, and eagerly fails as soon as
    any individual call fails. Note that elements beyond the first failing
    one will not be processed. *)
val traverse : ('a -> 'b option) -> 'a t -> 'b t option

(** {1 List scanning} *)

(** [for_all p (a1, a2, \[a3; ...; an\])] checks if all elements of the list
    satisfy the predicate [p]. That is, it returns
    [(p a1) && (p a2) && ... && (p an)]. *)
val for_all : ('a -> bool) -> 'a t -> bool

(** [for_all2 p (a1, a2, \[a3; ...; an\]) (b1, b2, \[b3; ...; bn\])] checks
    if, pairwise, all elements of the lists satisfy the predicate [p]. That
    is, it returns [(p a1 b1) && (p a2 b2) && ... && (p an bn)].

    @raise Invalid_argument
      if the two lists are determined to have different lengths. *)
val for_all2 : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool

(** [exists p (a1, a2, \[a3; ...; an\])] checks if any element of the list
    satisfies the predicate [p]. That is, it returns
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

(** [partition f l] returns a pair of lists [(l1, l2)], where [l1] is the
    list of all the elements of [l] that satisfy the predicate [f], and [l2]
    is the list of all the elements of [l] that do not satisfy [f]. The order
    of elements in the input list is preserved. At least one of [l1] and [l2]
    is non-empty. *)
val partition : ('a -> bool) -> 'a t -> 'a list * 'a list

(** {1 Lists of pairs}*)

(** Transform a list of pairs into a pair of lists:
    [split ((a1, b1), (a2, b2), \[(a3, b3); ...; (an, bn)\])] is
    [(a1, a2, \[a3; ...; an\]), (b1, b2, \[b3; ...; bn\])]. *)
val split : ('a * 'b) t -> 'a t * 'b t

(** Transform a pair of lists into a list of pairs:
    [combine (a1, a2, \[a3; ...; an\]) (b1, b2, \[b3; ...; bn\])] is
    [((a1, b1), (a2, b2), \[(a3, b3); ...; (an, bn)\])].

    @raise Invalid_argument if the two lists have different lengths. *)
val combine : 'a t -> 'b t -> ('a * 'b) t

(** {1 Apply} *)

(** [ap (x1, x2, \[x3; ...; xn\]) (f1, f2, \[f3; ...; fn\])] is
    [(f1 x1, f2 x2, \[f3 x3; ...; fn xn\])].

    @raise Invalid_argument
      if the two lists are determined to have different lengths. *)
val ap : 'a t -> ('a -> 'b) t -> 'b t

(** [ap_one x (f1, f2, \[f3; ...; fn\])] is
    [(f1 x, f2 x, \[f3 x; ...; fn x\])]. *)
val ap_one : 'a -> ('a -> 'b) t -> 'b t

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

(** {1 Interoperability} *)

(** Converts a list to a [T]. *)
val of_list : 'a list -> 'a t option

(** Converts a [T] to a list. *)
val to_list : 'a t -> 'a list

(** Converts a [List1.T] to a [T]. *)
val of_list1 : 'a List1.t -> 'a t option

(** Converts a [T] to a [List1.T]. *)
val to_list1 : 'a t -> 'a List1.t

(** {1 Instances} *)

module MakeEq (E : Eq.EQ) : Eq.EQ with type t = E.t t

module MakeOrd (O : Ord.ORD) : Ord.ORD with type t = O.t t

module MakeShow (S : Show.SHOW) : Show.SHOW with type t = S.t t
