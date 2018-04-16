type 'a t =
  | Nothing
  | Just of 'a
  
val eliminate : (unit -> 'b) -> ('a -> 'b) -> 'a t -> 'b

val is_some : 'a t -> bool

val map : ('a -> 'b) -> 'a t -> 'b t

val ( $ ) : 'a t -> ('a -> 'b t) -> 'b t
                                                
val pure : 'a -> 'a t

val ( $> ) : 'a t -> ('a -> 'b) -> 'b t

val void : 'a t -> unit t
