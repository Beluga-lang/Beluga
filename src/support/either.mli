type ('e, 'a) t =
  | Left of 'e
  | Right of 'a

val eliminate : ('e -> 'c) -> ('a -> 'c) -> ('e, 'a) t -> 'c

val is_right : ('e, 'a) t -> bool

val is_left : ('e, 'a) t -> bool

val pure : 'a -> ('e, 'a) t

val left : 'e -> ('e, 'a) t

val rmap : ('a -> 'b) -> ('e, 'a) t -> ('e, 'b) t

val lmap : ('e1 -> 'e2) -> ('e1, 'a) t -> ('e2, 'a) t

val bimap : ('e1 -> 'e2) -> ('a -> 'b) -> ('e1, 'a) t -> ('e2, 'b) t

val rvoid : ('e, 'a) t -> ('e, unit) t

val lvoid : ('e, 'a) t -> (unit, 'a) t

val void : ('e, 'a) t -> (unit, unit) t

val bind : ('a -> ('e, 'b) t) -> ('e, 'a) t -> ('e, 'b) t

val forget : ('e, 'a) t -> 'a Maybe.t

val either_of_maybe : 'a Maybe.t -> (unit, 'a) t

val ( $ ) : ('e, 'a) t -> ('a -> ('e, 'b) t) -> ('e, 'b) t

val ( $> ) : ('e, 'a) t -> ('a -> 'b) -> ('e, 'b) t
