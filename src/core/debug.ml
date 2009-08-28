(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(*
 * For interface, see debug.mli
 *)

type flags = int

let r_flags : flags ref = ref 0

let show flags =
    r_flags := flags

let rec toFlags = function
  | [] -> 0
  | x::xs ->
       if x > 30 then
         raise (Invalid_argument "toFlags argument out of bounds")
       else 
         (toFlags xs) lor (1 lsl x)

let showAll () =
    show (lnot 0)

let showNone () =
    show (toFlags [])

let print flags f =
    if flags land !r_flags == 0 then 
        ()
    else
        (print_string (f() ^ "\n")
       ; flush_all())

let prnt flags s =
    print flags (fun () -> s)

let makeFunctions flags =
  (print flags, prnt flags)
