(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

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



module EmptyTrail : TRAIL = struct

  type 'a t = unit

  let trail   ()           = ()

  let suspend () _copy     = ()

  let resume  () () _reset = ()

  let reset   ()           = ()

  let mark    ()           = ()

  let unwind  () _undo     = ()

  let log     () _action   = ()

end



module StdTrail : TRAIL = struct

    type 'a desc =
      | Cons of 'a * 'a desc
      | Mark of 'a desc
      | Nil

    type 'a t = 'a desc ref

    let trail () = ref Nil

    let reset trail = trail := Nil

    let suspend trail copy =
      let rec suspend' trail = match trail with
        | Nil                  -> Nil
        | Mark trail           -> suspend' trail
        | Cons (action, trail) ->
            Cons (copy action, suspend' trail) in
      let ftrail = suspend' !trail
      in
        ref ftrail

    let resume ftrail trail reset =
      let rec resume' trail = match trail with
        | Nil                    -> Nil
        | Mark ftrail            -> resume' ftrail
        | Cons (faction, ftrail) ->
            Cons (reset faction, resume' ftrail) in
      let trail' = resume' !ftrail
      in
        trail := trail'


    let mark trail = trail := Mark !trail

    let unwind trail undo =
      let rec unwind' trail = match trail with
        | Nil                  -> Nil
        | Mark trail           -> trail
        | Cons (action, trail) ->
              undo action
            ; unwind' trail
      in
        trail := unwind' !trail

    let log trail action = trail := Cons (action, !trail)

end
