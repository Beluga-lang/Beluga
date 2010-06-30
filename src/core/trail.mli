(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

(** Trailing Abstract Operations

    @author Joshua Dunfield
    @author Brigitte Pientka
    @author Roberto Virga
*)



module type TRAIL = sig
  type 'a t

  val trail   : unit -> 'a t

  val suspend : 'a t -> ('a -> 'b) -> 'b t
  val resume  : 'b t -> 'a t -> ('b -> 'a) -> unit

  val reset   : 'a t -> unit
  val mark    : 'a t -> unit
  val unwind  : 'a t -> ('a -> unit) -> unit
  val log     : 'a t -> 'a -> unit
end



module EmptyTrail : TRAIL

module StdTrail   : TRAIL
