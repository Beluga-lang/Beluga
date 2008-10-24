(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Trailing Abstract Operations

    @author Roberto Virga
*)



module type TRAIL = sig
  type 'a trail

  val trail   : unit -> 'a trail

  val suspend : 'a trail * ('a -> 'b) -> 'b trail
  val resume  : 'b trail * 'a trail  * ('b -> 'a) -> unit

  val reset   : 'a trail -> unit
  val mark    : 'a trail -> unit
  val unwind  : 'a trail * ('a -> unit) -> unit
  val log     : 'a trail * 'a -> unit
end



module EmptyTrail : TRAIL = struct

  type 'a trail = unit

  let trail () = ()

  let suspend ((), copy) = ()

  let resume ((), (), reset) = ()

  let reset () = ()

  let mark () = ()

  let unwind ((), undo) = ()

  let log ((), action) = ()

end



module Trail : TRAIL = struct

    type 'a trail_desc =
      | Cons of 'a * 'a trail_desc
      | Mark of 'a trail_desc
      | Nil

    type 'a trail = 'a trail_desc ref

    let rec trail () = ref Nil

    let rec reset trail =
      trail := Nil

    let rec suspend (trail, copy) =
      let rec suspend' trail = match trail with
        | Nil                  -> Nil
        | Mark trail           -> suspend' trail
        | Cons (action, trail) ->
            Cons (copy action, suspend' trail) in
      let ftrail = suspend' !trail
      in
        ref ftrail

    let rec resume (ftrail, trail, reset) =
      let rec resume' trail = match trail with
        | Nil                    -> Nil
        | Mark ftrail            -> resume' ftrail
        | Cons (faction, ftrail) ->
            Cons (reset faction, resume' ftrail) in
      let trail' = resume' !ftrail
      in
        trail := trail'


    let rec mark trail = trail := Mark !trail

    let rec unwind (trail, undo) =
      let rec unwind' trail = match trail with
        | Nil                  -> Nil
        | Mark trail           -> trail
        | Cons (action, trail) ->
              undo action
            ; unwind' trail
      in
        trail := unwind' !trail

    let rec log (trail, action) = trail := Cons (action, !trail)

end
