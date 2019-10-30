(** Totally miscellaneous functions. *)

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

module List = struct
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
end

let id (x : 'a) : 'a = x

type void = { impossible: 'a. 'a }

module Gen = struct
  let of_string s =
    let n = ref 0 in
    let n_max = S.length s in
    fun () ->
    if !n < n_max
    then
      let c = S.get s !n in
      let _ = incr n in
      Some c
    else
      None

  let of_in_channel_lines chan =
    fun () ->
    try
      Some (input_line chan)
    with
    | _ -> None

  let of_in_channel ?(buffer_size = 1024) chan =
    let bs = Bytes.create buffer_size in
    let count = ref 0 in
    let i = ref 0 in
    let more () = count := input chan bs 0 buffer_size; i := 0 in
    let next () =
      let c = Bytes.get bs !i in
      incr i;
      Some c
    in
    more ();
    fun () ->
    match () with
    | _ when !count = 0 -> None
    | _ when i < count -> next ()
    | _ when i = count ->
       more ();
       if !count = 0 then
         None
       else
         next ()
    | () -> failwith "impossible"

  let drop_lines g ln : unit =
    let rec go n =
      if n <= 0
      then ()
      else
        begin
          ignore (g ());
          go (n - 1)
        end
    in
    go ln

  (** Not portable. Will not work with windows line endings. *)
  let line_generator ?(buffer_size = 2048) (g : char Gen.t) : string Gen.t =
    let bs = Bytes.create buffer_size in
    let finished = ref false in
    function
    | _ when !finished -> None
    | _ ->
       let got_nl = ref false in
       let i = ref 0 in
       while not !got_nl do
         let c = g () in
         match c with
         | None ->
            got_nl := true;
            finished := true
         | Some c ->
            Bytes.set bs !i c;
            incr i;
            got_nl := c = '\n'
       done;
       Some (Bytes.sub_string bs 0 !i)

  let sequence (gs : 'a Gen.t list) : 'a Gen.t =
    let rgs = ref gs in
    let rec go () =
      match !rgs with
      | [] -> None
      | g :: gs ->
         match g () with
         | None -> rgs := gs; go ()
         | e -> e
    in
    go
end
