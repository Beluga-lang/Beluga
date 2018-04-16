(** A head-strict stream is non-empty and its head is a value. *)
type 'a t =
  { head : 'a;
    tail : unit -> 'a t Maybe.t;
  }

(** Constructs a head-strict stream. *)
let rec unfold (seed : 's) (next : 's -> ('a * 's) Maybe.t) : 'a t Maybe.t =
  let open Maybe in
  next seed $>
    fun (x, seed) ->
    { head = x;
      tail = fun () -> unfold seed next;
    }

(** Converts an istream (fully lazy stream) into a head-strict stream.
Since the istream might be empty, the return type is in an
Maybe.t. *)
module OfBasicStream (S : Types.BasicStream) = struct
  let f (s : 'a S.t) : 'a t Maybe.t =
    unfold s (fun s -> S.observe s)
end
     
(** Prepend an element to a head-strict stream. *)
let cons (x : 'a) (s : unit -> 'a t Maybe.t) : 'a t =
  { head = x;
    tail = s;
  }
