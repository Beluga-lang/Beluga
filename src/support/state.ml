module type STATE = sig
  type state

  type 'a t = state -> state * 'a

  val get : state t

  val put : state -> unit t

  val modify : (state -> state) -> unit t

  val run : 'a t -> state -> state * 'a

  val eval : 'a t -> state -> 'a

  val exec : 'a t -> state -> state

  val traverse_tuple2 :
    ('a1 -> 'b1 t) -> ('a2 -> 'b2 t) -> 'a1 * 'a2 -> ('b1 * 'b2) t

  val traverse_tuple3 :
       ('a1 -> 'b1 t)
    -> ('a2 -> 'b2 t)
    -> ('a3 -> 'b3 t)
    -> 'a1 * 'a2 * 'a3
    -> ('b1 * 'b2 * 'b3) t

  val traverse_list : ('a -> 'b t) -> 'a List.t -> 'b List.t t

  val traverse_list1 : ('a -> 'b t) -> 'a List1.t -> 'b List1.t t

  val traverse_list2 : ('a -> 'b t) -> 'a List2.t -> 'b List2.t t

  val traverse_list_void : ('a -> _ t) -> 'a List.t -> Unit.t t

  val traverse_list1_void : ('a -> _ t) -> 'a List1.t -> Unit.t t

  val traverse_list2_void : ('a -> _ t) -> 'a List2.t -> Unit.t t

  val traverse_reverse_list : ('a -> 'b t) -> 'a List.t -> 'b List.t t

  val traverse_reverse_list1 : ('a -> 'b t) -> 'a List1.t -> 'b List1.t t

  val traverse_reverse_list2 : ('a -> 'b t) -> 'a List2.t -> 'b List2.t t

  val traverse_reverse_list_void : ('a -> _ t) -> 'a List.t -> Unit.t t

  val traverse_reverse_list1_void : ('a -> _ t) -> 'a List1.t -> Unit.t t

  val traverse_reverse_list2_void : ('a -> _ t) -> 'a List2.t -> Unit.t t

  val traverse_option : ('a -> 'b t) -> 'a Option.t -> 'b Option.t t

  val traverse_option_void : ('a -> _ t) -> 'a Option.t -> Unit.t t

  val seq_list : 'a t List.t -> 'a List.t t

  val seq_list1 : 'a t List1.t -> 'a List1.t t

  val seq_list_void : unit t list -> unit t

  include Monad.MONAD with type 'a t := 'a t

  include Functor.FUNCTOR with type 'a t := 'a t

  include Apply.APPLY with type 'a t := 'a t
end

module Make (S : sig
  type t
end) : STATE with type state = S.t = struct
  type state = S.t

  let[@inline] run m init = m init

  module M = Monad.Make (struct
    (** The type of state transformers. *)
    type 'a t = state -> state * 'a

    let[@inline] return a state = (state, a)

    let[@inline] bind f v state =
      let state', a = run v state in
      f a state'
  end)

  include M
  include Functor.Make (M)
  include Apply.Make (M)

  let[@inline] [@specialise] get state = (state, state)

  let[@inline] [@specialise] put state' _m = (state', ())

  let[@inline] [@specialise] modify f =
    let* s = get in
    let s' = f s in
    put s'

  let[@inline] [@specialise] eval m init =
    let _final, n = run m init in
    n

  let[@inline] [@specialise] exec m init =
    let final, _n = run m init in
    final

  let[@specialise] traverse_tuple2 f1 f2 (a1, a2) =
    let* b1 = f1 a1 in
    let* b2 = f2 a2 in
    return (b1, b2)

  let[@specialise] traverse_tuple3 f1 f2 f3 (a1, a2, a3) =
    let* b1 = f1 a1 in
    let* b2 = f2 a2 in
    let* b3 = f3 a3 in
    return (b1, b2, b3)

  let[@specialise] rec traverse_list f l =
    match l with
    | [] -> return []
    | x :: xs ->
        let* y = f x in
        let* ys = traverse_list f xs in
        return (y :: ys)

  let[@specialise] traverse_list1 f l =
    let* y = f (List1.head l) in
    let* ys = traverse_list f (List1.tail l) in
    return (List1.from y ys)

  let[@specialise] traverse_list2 f l =
    let* y1 = f (List2.first l) in
    let* y2 = f (List2.second l) in
    let* ys = traverse_list f (List2.tail l) in
    return (List2.from y1 y2 ys)

  let[@specialise] rec traverse_list_void f l =
    match l with
    | [] -> return ()
    | x :: xs ->
        let* _ = f x in
        traverse_list_void f xs

  let[@specialise] traverse_list1_void f l =
    let* _ = f (List1.head l) in
    traverse_list_void f (List1.tail l)

  let[@specialise] traverse_list2_void f l =
    let* _ = f (List2.first l) in
    let* _ = f (List2.second l) in
    traverse_list_void f (List2.tail l)

  let[@specialise] rec traverse_reverse_list f l =
    match l with
    | [] -> return []
    | x :: xs ->
        let* ys = traverse_reverse_list f xs in
        let* y = f x in
        return (y :: ys)

  let[@specialise] traverse_reverse_list1 f l =
    let* ys = traverse_reverse_list f (List1.tail l) in
    let* y = f (List1.head l) in
    return (List1.from y ys)

  let[@specialise] traverse_reverse_list2 f l =
    let* ys = traverse_reverse_list f (List2.tail l) in
    let* y2 = f (List2.second l) in
    let* y1 = f (List2.first l) in
    return (List2.from y1 y2 ys)

  let[@specialise] rec traverse_reverse_list_void f l =
    match l with
    | [] -> return ()
    | x :: xs ->
        let* _ = traverse_reverse_list_void f xs in
        let* _ = f x in
        return ()

  let[@specialise] traverse_reverse_list1_void f l =
    let* _ = traverse_reverse_list_void f (List1.tail l) in
    let* _ = f (List1.head l) in
    return ()

  let[@specialise] traverse_reverse_list2_void f l =
    let* _ = traverse_list_void f (List2.tail l) in
    let* _ = f (List2.second l) in
    let* _ = f (List2.first l) in
    return ()

  let[@specialise] traverse_option f o =
    match o with
    | Option.Some x ->
        let* y = f x in
        return (Option.some y)
    | Option.None -> return Option.none

  let[@specialise] traverse_option_void f o =
    match o with
    | Option.Some x ->
        let* _ = f x in
        return ()
    | Option.None -> return ()

  let[@specialise] rec seq_list l =
    match l with
    | [] -> return []
    | x :: xs ->
        let* y = x in
        let* ys = seq_list xs in
        return (y :: ys)

  let[@specialise] seq_list1 l =
    let* y = List1.head l in
    let* ys = seq_list (List1.tail l) in
    return (List1.from y ys)

  let[@specialise] rec seq_list_void xs =
    match xs with
    | [] -> return ()
    | x :: xs ->
        let* () = x in
        seq_list_void xs
end
