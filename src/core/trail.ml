(** Trailing Abstract Operations

    @author Joshua Dunfield
    @author Brigitte Pientka
    @author Roberto Virga
    Modified: Costin Badescu
*)

module type TRAIL = sig
  type 'a t

  val trail : unit -> 'a t
  val reset : 'a t -> unit
  val mark : 'a t -> unit
  val unwind : 'a t -> ('a -> unit) -> unit
  val log : 'a t -> 'a -> unit
end

module EmptyTrail : TRAIL = struct
  type 'a t = unit

  let trail () = ()
  let reset () = ()
  let mark () = ()
  let unwind () _ = ()
  let log () _ = ()
end

module StdTrail : TRAIL = struct
  type 'a event = Mark | Event of 'a

  type 'a t = 'a event Stack.t

  let trail () = Stack.create ()
  let log trail action = Stack.push (Event action) trail
  let reset trail = Stack.clear trail
  let mark trail = Stack.push (Mark) trail
  let rec unwind trail undo =
    if not (Stack.is_empty trail)
    then
      begin match Stack.pop trail with
      | Mark -> ()
      | Event action ->
         undo action;
         unwind trail undo
      end
end
