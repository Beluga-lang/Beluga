(** Totally miscellaneous functions. *)

(** An exception to be raised in unimplemented features.
 * Code that raises this exception should never be committed.
 *)
exception NotImplemented of string

let not_implemented (msg : string) : 'a = raise (NotImplemented msg)

(** Unpacks a string into a list of characters. *)
let string_unpack (s : string) : char list =
  let n = String.length s in
  let rec go i = match () with
    | () when i < n -> String.get s i :: go (i + 1)
    | () -> []
  in
  go 0

(** Converts a list of characters into an equivalent string. *)
let string_pack (cs : char list) : string =
  String.concat "" (List.map (String.make 1) cs)

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


module List = struct
  let rec last (l : 'a list) : 'a = match l with
    | [] -> invalid_arg
    | [x] -> x
    | x :: xs -> last xs
end

let id (x : 'a) : 'a = x

type void = { impossible: 'a. 'a }
