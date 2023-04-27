module type IMPERATIVE_STATE = sig
  type state

  val traverse_tuple2 :
       state
    -> (state -> 'a1 -> 'b1)
    -> (state -> 'a2 -> 'b2)
    -> 'a1 * 'a2
    -> 'b1 * 'b2

  val traverse_tuple3 :
       state
    -> (state -> 'a1 -> 'b1)
    -> (state -> 'a2 -> 'b2)
    -> (state -> 'a3 -> 'b3)
    -> 'a1 * 'a2 * 'a3
    -> 'b1 * 'b2 * 'b3

  val traverse_list : state -> (state -> 'a -> 'b) -> 'a List.t -> 'b List.t

  val traverse_list1 :
    state -> (state -> 'a -> 'b) -> 'a List1.t -> 'b List1.t

  val traverse_list2 :
    state -> (state -> 'a -> 'b) -> 'a List2.t -> 'b List2.t

  val iter_list : state -> (state -> 'a -> Unit.t) -> 'a List.t -> Unit.t

  val iter_list1 : state -> (state -> 'a -> Unit.t) -> 'a List1.t -> Unit.t

  val iter_list2 : state -> (state -> 'a -> Unit.t) -> 'a List2.t -> Unit.t

  val traverse_reverse_list :
    state -> (state -> 'a -> 'b) -> 'a List.t -> 'b List.t

  val traverse_reverse_list1 :
    state -> (state -> 'a -> 'b) -> 'a List1.t -> 'b List1.t

  val traverse_reverse_list2 :
    state -> (state -> 'a -> 'b) -> 'a List2.t -> 'b List2.t

  val iter_rev_list : state -> (state -> 'a -> Unit.t) -> 'a List.t -> Unit.t

  val iter_rev_list1 :
    state -> (state -> 'a -> Unit.t) -> 'a List1.t -> Unit.t

  val iter_rev_list2 :
    state -> (state -> 'a -> Unit.t) -> 'a List2.t -> Unit.t

  val traverse_option :
    state -> (state -> 'a -> 'b) -> 'a Option.t -> 'b Option.t

  val iter_option : state -> (state -> 'a -> Unit.t) -> 'a Option.t -> Unit.t

  val seq_list : state -> (state -> 'a) List.t -> 'a List.t

  val seq_list1 : state -> (state -> 'a) List1.t -> 'a List1.t

  val iter_seq : state -> (state -> Unit.t) list -> unit
end

module Make (State : sig
  type state
end) : IMPERATIVE_STATE with type state = State.state = struct
  include State

  let traverse_tuple2 state f1 f2 (a1, a2) =
    let b1 = f1 state a1 in
    let b2 = f2 state a2 in
    (b1, b2)

  let traverse_tuple3 state f1 f2 f3 (a1, a2, a3) =
    let b1 = f1 state a1 in
    let b2 = f2 state a2 in
    let b3 = f3 state a3 in
    (b1, b2, b3)

  let rec traverse_list state f l =
    match l with
    | [] -> []
    | x :: xs ->
        let y = f state x in
        let ys = traverse_list state f xs in
        y :: ys

  let traverse_list1 state f l =
    let y = f state (List1.head l) in
    let ys = traverse_list state f (List1.tail l) in
    List1.from y ys

  let traverse_list2 state f l =
    let y1 = f state (List2.first l) in
    let y2 = f state (List2.second l) in
    let ys = traverse_list state f (List2.tail l) in
    List2.from y1 y2 ys

  let rec iter_list state f l =
    match l with
    | [] -> ()
    | x :: xs ->
        f state x;
        iter_list state f xs

  let iter_list1 state f l =
    f state (List1.head l);
    iter_list state f (List1.tail l)

  let iter_list2 state f l =
    f state (List2.first l);
    f state (List2.second l);
    iter_list state f (List2.tail l)

  let rec traverse_reverse_list state f l =
    match l with
    | [] -> []
    | x :: xs ->
        let ys = traverse_reverse_list state f xs in
        let y = f state x in
        y :: ys

  let traverse_reverse_list1 state f l =
    let ys = traverse_reverse_list state f (List1.tail l) in
    let y = f state (List1.head l) in
    List1.from y ys

  let traverse_reverse_list2 state f l =
    let ys = traverse_reverse_list state f (List2.tail l) in
    let y2 = f state (List2.second l) in
    let y1 = f state (List2.first l) in
    List2.from y1 y2 ys

  let rec iter_rev_list state f l =
    match l with
    | [] -> ()
    | x :: xs ->
        iter_rev_list state f xs;
        f state x

  let iter_rev_list1 state f l =
    iter_rev_list state f (List1.tail l);
    f state (List1.head l)

  let iter_rev_list2 state f l =
    iter_list state f (List2.tail l);
    f state (List2.second l);
    f state (List2.first l)

  let traverse_option state f o =
    match o with
    | Option.Some x ->
        let y = f state x in
        Option.some y
    | Option.None -> Option.none

  let iter_option state f o =
    match o with
    | Option.Some x -> f state x
    | Option.None -> ()

  let rec seq_list state l =
    match l with
    | [] -> []
    | x :: xs ->
        let y = x state in
        let ys = seq_list state xs in
        y :: ys

  let seq_list1 state l =
    let y = List1.head l state in
    let ys = seq_list state (List1.tail l) in
    List1.from y ys

  let rec iter_seq state xs =
    match xs with
    | [] -> ()
    | x :: xs ->
        x state;
        iter_seq state xs
end
