(* Not Trailing Abstract Operations *)
(* Author: Roberto Virga *)

module Notrail = struct

  type 'a trail = unit

  let trail () = ()

  let suspend ((), copy) = ()
  let resume ((),(), reset) = ()
  
  let reset () = ()

  let mark () = ()

  let unwind ((), undo) = ()

  let log ((), action) = ()
end (* module struct NoTrail *)
