open Support

(** A head-strict stream is non-empty and its head is a value. *)
type 'a t =
  { head : 'a;
    tail : 'a t option Lazy.t;
  }

(** Constructs a head-strict stream. *)
let rec unfold (seed : 's) (next : 's -> ('a * 's) option) : 'a t option =
  let open Option in
  next seed $>
    fun (x, seed) ->
    { head = x;
      tail = lazy (unfold seed next);
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
let cons (x : 'a) (s : 'a t option Lazy.t) : 'a t =
  { head = x;
    tail = s;
  }
