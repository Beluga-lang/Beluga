val eliminate : (unit -> 'b) -> ('a -> 'b) -> 'a option -> 'b

val is_some : 'a option -> bool

val map : ('a -> 'b) -> 'a option -> 'b option

val ( $ ) : 'a option -> ('a -> 'b option) -> 'b option
                                                
val pure : 'a -> 'a option

val none : 'a option

val ( $> ) : 'a option -> ('a -> 'b) -> 'b option

val void : 'a option -> unit option
