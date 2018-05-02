(** A head-strict stream is non-empty and its head is a value. *)
type 'a t =
  { head : 'a;
    tail : unit -> 'a t option;
  }

(** Constructs a head-strict stream. *)
let rec unfold (seed : 's) (next : 's -> ('a * 's) option) : 'a t option =
  let open Maybe in
  next seed $>
    fun (x, seed) ->
    { head = x;
      tail = fun () -> unfold seed next;
    }

(** Converts any basic stream into a head-strict stream.
    Since the basic stream might be empty, the return type is in an
    {!Pervasives.option}.
 *)
module OfBasicStream (S : Types.BasicStream) = struct
  let f (s : 'a S.t) : 'a t option =
    unfold s (fun s -> S.observe s)
end
     
(** Prepend an element to a head-strict stream. *)
let cons (x : 'a) (s : unit -> 'a t option) : 'a t =
  { head = x;
    tail = s;
  }
