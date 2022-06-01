open Support

type 'a t' =
  | Nil
  | Cons of 'a * 'a t

and 'a t = int * 'a t' Lazy.t

let of_gen (g : unit -> 'a option) : 'a t =
  let rec go n =
    n,
    lazy
      begin match g () with
      | None -> Nil
      | Some x -> Cons (x, go (n + 1))
      end
  in
  go 0

let of_stream (s : 'a Stream.t) : 'a t =
  let rec go n =
    n,
    lazy
      begin match
        try
          Some (Stream.next s)
        with
        | Stream.Failure -> None
      with
      | None -> Nil
      | Some x -> Cons (x, go (n + 1))
      end
  in
  go 0

let rec iter f s =
  match Pair.snd s with
  | lazy Nil -> ()
  | lazy (Cons (x, s)) ->
     f x;
     iter f s

let position s = Pair.fst s

let observe s =
  match Pair.snd s with
  | lazy Nil -> None
  | lazy (Cons (x, s)) -> Some (x, s)
