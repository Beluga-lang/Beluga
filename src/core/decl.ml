type t = int
let (<) = (<)

let decl_counter = ref 0
let next () = incr decl_counter; !decl_counter
let reset () = decl_counter := 0
