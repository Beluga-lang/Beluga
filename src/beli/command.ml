
(* the type of commands  *)
type command = { cmd : string ;
                 run : string list -> unit ;
                 help : string }


(* registered commands *)
let _reg : command list ref = ref []


let register _cmd _f _help = ()

let is_command _cmd = `Input ""

let do_command _cmd = ()


(* The built in commands *)

(* ... *)
