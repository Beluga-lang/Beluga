(** An ad hoc disjoint union of two types. *)
type ('e, 'a) t =
  | Left of 'e
  | Right of 'a

(** Eliminator for disjoint unions. *)
val eliminate : ('e -> 'c) -> ('a -> 'c) -> ('e, 'a) t -> 'c

(** Checks whether the union holds the right-hand type. *)
val is_right : ('e, 'a) t -> bool

(** Checks whether the union holds the left-hand type. *)
val is_left : ('e, 'a) t -> bool

(** Right injection into the union. *)
val pure : 'a -> ('e, 'a) t

(** Left injection into the union. *)
val left : 'e -> ('e, 'a) t

(** Transforms the right-hand type in the union, if any. *)
val rmap : ('a -> 'b) -> ('e, 'a) t -> ('e, 'b) t

(** Transforms the left-hand type in the union, if any. *)
val lmap : ('e1 -> 'e2) -> ('e1, 'a) t -> ('e2, 'a) t

(** Transforms both sides of the union. *)
val bimap : ('e1 -> 'e2) -> ('a -> 'b) -> ('e1, 'a) t -> ('e2, 'b) t

(** Forgets the right-hand side of the union. *)
val rvoid : ('e, 'a) t -> ('e, unit) t

(** Forgets the left-hand side of the union. *)
val lvoid : ('e, 'a) t -> (unit, 'a) t

(** Forgets both sides of the union. *)
val void : ('e, 'a) t -> (unit, unit) t

(** Promotes a function that constructs a union into a function that
    transforms a union.

    {!Either.bind} and {!Either.pure} witness that {!Either.t} is a
    monad if the left-hand type is fixed.
 *)
val bind : ('a -> ('e, 'b) t) -> ('e, 'a) t -> ('e, 'b) t

(** Eliminates the union into a {!Stdlib.option}, forgetting the value in
the left-hand side. *)
val forget : ('e, 'a) t -> 'a option

(** Converts a {!Stdlib.option} into a union with a unit left-hand
    side.
 *)
val of_option : 'a option -> (unit, 'a) t

(** Converts a {!Stdlib.option} into a union with a left-hand side
    constructed from a thunk in case the {!Stdlib.option}
    contained {!Option.None}.
 *)
val of_option' : (unit -> 'e) -> 'a option -> ('e, 'a) t

(** Converts a union into an option, forgetting the left side, if
    any.
 *)
val to_option : ('e, 'a) t -> 'a option

(** Infix form of {!Either.bind}. *)
val ( $ ) : ('e, 'a) t -> ('a -> ('e, 'b) t) -> ('e, 'b) t

(** Infix form of {!Either.rmap}. *)
val ( $> ) : ('e, 'a) t -> ('a -> 'b) -> ('e, 'b) t

(** Traps exceptions thrown by evaluating a function into a union.
    You can delay handling the exceptions until the union is eliminated
    by using the following trick.
    Suppose `e : (exn, a) t`. Then,
    > eliminate
       (fun ex ->
         try raise ex
         with
         | Whatever -> do_something_to_handle_Whatever
       )
       (fun x -> success x)

    The benefit of using `trap` is that you can be selective about
    which code gets its exceptions caught.
 *)
val trap : (unit -> 'a) -> (exn, 'a) t
