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

let level = ref 0

let indent n = level := !level + n
let outdent n = level := !level - n

let indentLevelStack = ref ([] : int list)
let pushIndentationLevel () = (indentLevelStack := !level :: !indentLevelStack)
let popIndentationLevel () =
  let poppedLevel :: rest = !indentLevelStack in
    indentLevelStack := rest;
    level := poppedLevel

let print_level_spaces() =
  let rec p n = if n < 1 then () else (print_string " "; p (n - 1))
  in
     p (!level)

let rec print_noticing_newlines s x len =
  if x >= len then ()
  else
    let ch = String.get s x in
     (if ch = '\n' then
        (print_string "\n";
         print_level_spaces())
      else
        print_char ch);
      print_noticing_newlines s (x + 1) len
        

let print flags f =
    if flags land !r_flags == 0 then 
        ()
    else
        (print_level_spaces();
         let s = f() in
           print_noticing_newlines s 0 (String.length s);
           print_string "\n";
           flush_all())

let prnt flags s =
    print flags (fun () -> s)

let makeFunctions flags =
  (print flags, prnt flags)

