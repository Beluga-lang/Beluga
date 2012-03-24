(*
 *  monitor.mli
 *
 *  Made by (Kirchner DIMITRI)
 *  Login   <dimitri@logic-3.CS.McGill.CA>
 *
 *  Started on  Thu May  7 15:01:24 2009 Kirchner DIMITRI
 *  Last update Thu May  7 15:01:24 2009 Kirchner DIMITRI
 *)

val on : bool ref
val onf : bool ref

val timer : string * (unit -> 'a) -> 'a
val print_timer : unit -> unit
