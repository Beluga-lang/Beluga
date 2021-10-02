(** Totally miscellaneous functions. *)

include Equality

(** Runs a function ignoring all exceptions.
    In general this is a terrible idea, but it is sometimes necessary
    when performing cleanup that may fail while in an exception
    handler.
 *)
let noexcept f = try f () with _ -> ()

(** An exception to be raised in unimplemented features.
 * Code that raises this exception should never be committed.
 *)
exception NotImplemented of string

let not_implemented (msg : string) : 'a = raise (NotImplemented msg)

(** Enumerates a list using a state transformer to generate indices.
    The initial seed {!s!} contains the initial state and the function
    {!f!} transforms this state to compute a new state and an index.
    These indices are sequentially zipped with the given list to
    produce an indexed list, and the final state is returned.
 *)
let rec enumerate_with_state (s : 's) (f : 's -> ('s * 'i)) (l : 'a list) : 's * ('i * 'a) list =
  match l with
  | [] -> (s, [])
  | (x :: xs) ->
     let (s', i) = f s in
     let y = (i, x) in
     let (s_final, ys) = enumerate_with_state s' f xs in
     (s_final, y :: ys)

(** Enumerates a list by pairing each element with its index. *)
let enumerate (l : 'a list) : (int * 'a) list =
  enumerate_with_state 0 (fun s -> (s + 1, s)) l |> snd

(** Forms the tuple of its two inputs. *)
let tuple (x : 'a) (y : 'b) : 'a * 'b =
  (x, y)

(** Creates a constant function that raises the given exception.
    Useful when eliminating option-types.
 *)
let throw (e : exn) : 'b -> 'a =
  fun _ -> raise e

let on f : ('b -> 'b -> 'c) -> 'a -> 'a -> 'c =
  fun g x y -> g (f x) (f y)

type void = { impossible: 'a. 'a }

module DynArray = struct
  include DynArray

  (** [append_list dst l] effectfully appends all the elements of [l] to [dst].
  *)
  let rec append_list d = function
    | [] -> ()
    | x :: xs -> add d x; append_list d xs
  
  (** [head d] is [Some h] with [h] being the first element of [d] if [d] is
    non-empty, and [None] otherwise.
  *)
  let head = function
    | d when empty d -> None
    | d -> Some (get d 0)
  
  (** [get_opt d i] is [Some (get d i)] if [d] has an element at index [i], and
      [None] otherwise.
  *)
  let get_opt d i =
    try
      Some (get d i)
    with
    | Invalid_arg _ -> None
  
  (** [rfind_opt_idx d p] is [Some (i, l)] where [l] is the last element in [d]
      that satisfies [p] and [i] is the index of [l] in [d], and [None] otherwise.
  *)
  let rfind_opt_idx d p =
    let rec go = function
      | -1 -> None
      | k ->
         let x = get d k in
         if p x then
           Some (k, x)
         else
           go (k-1)
    in
    go (length d - 1)
end

module Function = struct
  let (++) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c =
    fun f g x -> f (g x)

  let flip (f : 'a -> 'b -> 'c) : 'b -> 'a -> 'c =
    fun y x -> f x y

  let sequence (l : ('a -> 'b) list) (x : 'a) =
    List.map (fun f -> f x) l

  let rec until (f : unit -> bool) : unit =
    if f ()
    then until f
    else ()

  (** A convenient way to execute an effect in the middle of a
      composition pipeline.
      ... |> through (fun x -> print_string x) |> ...
   *)
  let through (f : 'a -> unit) : 'a -> 'a =
    fun x -> f x; x

  (** A convenient way to execute an effect *after* running a
      function, without needing a use a let-expression to store the result
      of the function.
   *)
  let after (f : unit -> unit) : 'a -> 'a =
    fun x -> f (); x

  let curry f x y = f (x, y)
  let uncurry f (x, y) = f x y
end

module Seq = struct
  include Seq

  let rec to_list s =
    match s () with
    | Seq.Nil -> []
    | Seq.Cons (x, s) -> x :: to_list s
end

module Hashtbl = struct
  include Hashtbl

  (** Constructs a new hashtable by mapping the given function over the values.
      This is somewhat inefficient as the hastable is converted into a
      sequence, mapped, and converted back, but it should run in
      linear time in one pass due to the lazy nature of Seq.t.
   *)
  let map (f : 'a -> 'b) : ('k, 'a) Hashtbl.t -> ('k, 'b) Hashtbl.t =
    fun h ->
    to_seq h
    |> Seq.map (fun (k, x) -> (k, f x))
    |> of_seq

  (** Constructs a hashtable from a list by using a function to send
      each element to a key.
   *)
  let group_by (p : 'a -> 'k) (l : 'a list) : ('k, 'a list) Hashtbl.t =
    let h = Hashtbl.create 32 in
    let () =
      let insert k x =
        let d =
          match Hashtbl.find_opt h k with
          | None -> DynArray.make 32
          | Some d -> d
        in
        DynArray.add d x;
        Hashtbl.replace h k d
      in
      List.for_each_ l (fun x -> insert (p x) x)
    in
    map DynArray.to_list h
end

module Char = struct
  let equals (c1 : char) (c2 : char) = Stdlib.(=) c1 c2
end

module Stack = struct
  include Stack

  let top_opt s =
    try Some (Stack.top s)
    with Stack.Empty -> None

  let pop_opt s =
    try Some (Stack.pop s)
    with Stack.Empty -> None

  (** Pops an item from a stack and runs the given function on it.
      If the function raises an exception, the item is placed back onto
      the stack.
      The given function must not modify the stack.
   *)
  let popping s f =
    let x = top_opt s in
    let y = f x in
    let _ = pop_opt s in
    y

  (** Converts the stack into a list.
      The top element of the stack is the *last* element of the list.
   *)
  let to_list s =
    fold (fun l x -> x :: l) [] s

  (** Converts the stack into a list.
      The top element of the stack is the *first* element of the
      list. *)
  let to_list_rev s =
    fold (fun k x -> fun l -> k (x :: l)) (fun x -> x) s []
end
