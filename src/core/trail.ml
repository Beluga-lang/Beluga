(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Trailing Abstract Operations

    @author Roberto Virga
*)

module Trail = struct

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
