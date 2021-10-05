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
      that satisfies [p] and [i] is the index of [l] in [d], and [None]
      otherwise.
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
