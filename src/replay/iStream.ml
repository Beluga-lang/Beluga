open Support

type 'a t =
  { next : unit -> ('a * 'a t) option }

type 'a istream = 'a t

let rec map (f : 'a -> 'b) (s : 'a t) =
  { next =
      fun () ->
      Maybe.map (Pair.bimap f (map f)) (s.next ())
  }

let empty : 'a t =
  { next = fun () -> None }

(** Put a given element on the front of a stream. *)
let cons (x : unit -> 'a) (s : 'a t) =
  { next = fun () -> Some (x (), s) }

(*
(** Prepends the list of items to the front of the stream.
The list is prepended in reverse order, so the last item of the list
becomes the new head of the stream. *)
let rec prepend_tl (xs : 'a list) (s : 'a t) : 'a t =
  match xs with
  | [] -> s
  | (x :: xs) -> prepend_tl xs (cons x s)
 *)

let rec of_channel'
          (buf : Bytes.t) (pos : int)
          (len : int) (chan : in_channel) :
          char t =
  let next () : (char * char t) option =
    (* if we've yielded all the chars in our buffer, we need to read
    more chars from the channel *)
    if pos = len then
      begin
        let len' = input chan buf 0 (Bytes.length buf) in
        (* if input returns 0 bytes, we've reached EOF *)
        if len' = 0 then
          None
        else
          let c = Bytes.get buf 0 in
          Some (c, of_channel' buf 1 len' chan)
      end
    (* otherwise just yield the next char and bump up our pointer *)
    else
      begin
        let c = Bytes.get buf pos in
        Some (c, of_channel' buf (pos + 1) len chan)
      end
  in
  { next = next }

let of_channel (chan : in_channel) : char t =
  of_channel' (Bytes.create 1024) 0 0 chan

(** Read from a stream so long as items satisfy a given predicate.
The returned list contains all the leading elements of the stream
that satisfy the predicate.
If the second component of the pair is non-empty then it contains
the rest of the stream as well as the first item that failed to
satisfy the predicate. *)
let take_while (p : 'a -> bool) (s : 'a t) :
      'a list * ('a * 'a t) option =
  let rec go (acc : 'a list) (s : 'a t) :
        'a list * ('a * 'a t) option =
    (* try to pull the next item from the stream *)
    match s.next () with
    (* if the stream is empty, we're done *)
    | None -> (acc, None)
    | Some (c, s) ->
       (* otherwise, check the predicate and prepend the item to the
       list if it passes *)
       if p c then
         go (c :: acc) s
       (* otherwise, we need to put the character back onto the
       stream and finish *)
       else
         (acc, Some (c, s))
  in
  go [] s |> Pair.lmap List.rev

let take_while_str (p : char -> bool) (s : char t) :
      string * (char * char t) option =
  take_while p s |> Pair.lmap String.pack

module AsBasicStream = struct
  type 'a t = 'a istream

  let rec unfold (f : 's -> ('a * 's) option) (s : 's) : 'a t =
    { next =
        fun () ->
        f s |> Maybe.map (Pair.rmap (unfold f))
    }

  let observe (s : 'a t) : ('a * 'a t) option = s.next ()
end
