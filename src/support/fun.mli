include module type of Stdlib.Fun

(** [f ++ g] is the function composition of [f] and [g], such that [(f ++ g) x]
    is [f (g x)].
*)
val (++) : ('b -> 'c) -> ('a -> 'b) -> ('a -> 'c)

(** [flip f x y] is [f y x].
*)
val flip : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)

(** [until f] repeatedly calls the effectful function [f] until [f ()] is
    [false].
    If [f] always returns [true], then [until f] will not terminate.
*)
val until : (unit -> bool) -> unit

(** [through f x] applies the effectful function [f] on [x] and returns [x].
    @example [... |> through (fun x -> print_string x) |> ...]
*)
val through : ('a -> unit) -> 'a -> 'a

(** [after f x] calls the effectful function [f] and returns [x].
    This effectively calls [f] after executing a function pipeline.
    @example [... |> through (fun x -> print_string "Success") |> ...]
*)
val after : (unit -> unit) -> 'a -> 'a

(** Converts an uncurried function to a curried function.
*)
val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c

(** Converts a curried function to a function on pairs.
*)
val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
