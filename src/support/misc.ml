(** Totally miscellaneous functions. *)

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

module S = String

module String = struct
  (** Unpacks a string into a list of characters. *)
  let unpack (s : string) : char list =
    let n = String.length s in
    let rec go i = match () with
      | () when i < n -> String.get s i :: go (i + 1)
      | () -> []
    in
    go 0

  (** Converts a list of characters into an equivalent string. *)
  let pack (cs : char list) : string =
    String.concat "" (List.map (String.make 1) cs)

  let drop n s : string = String.sub s n (String.length s - n)
end

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

(** Forms a constant function returning the given value.
    Warning: since OCaml is an eager language, the expression `const x`
    will fully evaluate `x` before forming the constant function.
    Therefore, if evaluation of `x` produces side-effects, they will
    be performed at the time that the constant function is _formed_
    rather than when it is _run_.
 *)
let const (x : 'b) : 'a -> 'b =
  fun _ -> x

(** Creates a constant function that raises the given exception.
    Useful when eliminating option-types.
 *)
let throw (e : exn) : 'b -> 'a =
  fun _ -> raise e

let on f : ('b -> 'b -> 'c) -> 'a -> 'a -> 'c =
  fun g x y -> g (f x) (f y)

module List = struct
  include List

  (** Gets the last element of a list.
      Raises `invalid_arg` if the list is empty.
   *)
  let rec last (l : 'a list) : 'a = match l with
    | [] -> invalid_arg
    | [x] -> x
    | _ :: xs -> last xs

  (** Computes the list of all successive pairs in a given
      list.contents.
      `pairs [x_1; x_2; ... x_n]
      = `[(x_1, x_2); (x_2, x_3); ...; (x_n-1, x_n)]`
      The output list will have one less element than the input list.
   *)
  let rec pairs l =
    match l with
    | [] | [_] -> []
    | x1 :: x2 :: xs -> (x1, x2) :: pairs (x2 :: xs)

  (** Decides if a list is empty. *)
  let null = function
    | [] -> true
    | _ -> false

  let nonempty l = not (null l)

  let filter_rev p l =
    let rec go acc = function
      | [] -> acc
      | x :: xs -> go (if p x then x :: acc else acc) xs
    in
    go [] l

  let for_each l f = List.map f l

  let for_each_ l f = List.iter f l

  let uncons : 'a list -> ('a * 'a list) option = function
    | [] -> None
    | x :: xs -> Some (x, xs)

  (** The "bind" monadic operation for lists.
      More efficient that separately mapping and concatenating.
   *)
  let rec concat_map (f : 'a -> 'b list) : 'a list -> 'b list = function
    | [] -> []
    | x :: xs -> f x @ concat_map f xs

  (** Finds the index of the element satisfying the predicate. *)
  let index_of (p : 'a -> bool) (l : 'a list) : int option =
    let rec go k = function
      | [] -> None
      | x :: _ when p x -> Some k
      | _ :: xs -> go (k + 1) xs
    in
    go 0 l
end

let id (x : 'a) : 'a = x

type void = { impossible: 'a. 'a }

module DynArray = struct
  include DynArray

  let rec append_list d = function
    | [] -> ()
    | x :: xs -> DynArray.add d x; append_list d xs

  let head = function
    | d when DynArray.empty d -> None
    | d -> Some (DynArray.get d 0)

  let get_opt d i =
    try
      Some (DynArray.get d i)
    with
    | DynArray.Invalid_arg _ -> None

  (** Finds the *last* element in the array satisfying p, and returns also its index. *)
  let rfind_opt_idx (type a) (d : a DynArray.t) (p : a -> bool) : (int * a) option =
    let rec go = function
      | -1 -> None
      | k ->
         let x = DynArray.get d k in
         if p x then
           Some (k, x)
         else
           go (k-1)
    in
    go (DynArray.length d - 1)
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
