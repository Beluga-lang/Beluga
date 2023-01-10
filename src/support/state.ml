module type STATE = sig
  type state

  include Monad.MONAD with type 'a t = state -> state * 'a

  val get : state t

  val put : state -> unit t

  val modify : (state -> state) -> unit t

  val run : 'a t -> state -> state * 'a

  val eval : 'a t -> state -> 'a

  val exec : 'a t -> state -> state

  val locally : (state -> state) -> 'a t -> 'a t

  val scoped : set:Unit.t t -> unset:Unit.t t -> 'a t -> 'a t

  val try_catch : 'a t -> on_exn:(exn -> 'a t) -> 'a t

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

  let[@inline] get state = (state, state)

  let[@inline] put state' _m = (state', ())

  let[@inline] modify f =
    let* s = get in
    let s' = f s in
    put s'

  let[@inline] eval m init =
    let _final, n = run m init in
    n

  let[@inline] exec m init =
    let final, _n = run m init in
    final

  let[@inline] locally f m s =
    let a = eval m (f s) in
    (s, a)

  let[@inline] scoped ~set ~unset m =
    let* () = set in
    let* a = m in
    let* () = unset in
    return a

  let[@inline] try_catch m ~on_exn state =
    try run m state with
    | exn -> run (on_exn exn) state

  let rec traverse_list f l =
    match l with
    | [] -> return []
    | x :: xs ->
        let* y = f x in
        let* ys = traverse_list f xs in
        return (y :: ys)

  let traverse_list1 f l =
    let* y = f (List1.head l) in
    let* ys = traverse_list f (List1.tail l) in
    return (List1.from y ys)

  let traverse_list2 f l =
    let* y1 = f (List2.first l) in
    let* y2 = f (List2.second l) in
    let* ys = traverse_list f (List2.tail l) in
    return (List2.from y1 y2 ys)

  let rec traverse_list_void f l =
    match l with
    | [] -> return ()
    | x :: xs ->
        let* _ = f x in
        traverse_list_void f xs

  let traverse_list1_void f l =
    let* _ = f (List1.head l) in
    traverse_list_void f (List1.tail l)

  let traverse_list2_void f l =
    let* _ = f (List2.first l) in
    let* _ = f (List2.second l) in
    traverse_list_void f (List2.tail l)

  let rec traverse_reverse_list f l =
    match l with
    | [] -> return []
    | x :: xs ->
        let* ys = traverse_reverse_list f xs in
        let* y = f x in
        return (y :: ys)

  let traverse_reverse_list1 f l =
    let* ys = traverse_reverse_list f (List1.tail l) in
    let* y = f (List1.head l) in
    return (List1.from y ys)

  let traverse_reverse_list2 f l =
    let* ys = traverse_reverse_list f (List2.tail l) in
    let* y2 = f (List2.second l) in
    let* y1 = f (List2.first l) in
    return (List2.from y1 y2 ys)

  let rec traverse_reverse_list_void f l =
    match l with
    | [] -> return ()
    | x :: xs ->
        let* _ = traverse_reverse_list_void f xs in
        let* _ = f x in
        return ()

  let traverse_reverse_list1_void f l =
    let* _ = traverse_reverse_list_void f (List1.tail l) in
    let* _ = f (List1.head l) in
    return ()

  let traverse_reverse_list2_void f l =
    let* _ = traverse_list_void f (List2.tail l) in
    let* _ = f (List2.second l) in
    let* _ = f (List2.first l) in
    return ()

  let traverse_option f o =
    match o with
    | Option.Some x ->
        let* y = f x in
        return (Option.some y)
    | Option.None -> return Option.none

  let traverse_option_void f o =
    match o with
    | Option.Some x ->
        let* _ = f x in
        return ()
    | Option.None -> return ()
end
