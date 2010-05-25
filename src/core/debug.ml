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

let flagsToString flags =
  let rec seq n =
    if n > 30 then ""
    else (if flags land (1 lsl n) <> 0 then string_of_int n ^ ";" else "")
       ^ seq (n + 1)
  in
    if flags = lnot 0 then "[all]"
    else if flags = 0 then "[none]"
    else "[" ^ seq 0 ^ "]"

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
         let s = try f()
                 with
                   | Match_failure stuff -> (print_string ("*** Match_failure exception raised inside function passed to dprint ***\n*** Goodbye. ***" ^ flagsToString flags ^ "\n");
                                             exit 200)
                   | exn -> (print_string ("*** WARNING: EXCEPTION RAISED INSIDE FUNCTION PASSED TO dprint *** " ^ flagsToString flags ^ "\n");
                             flush_all();
                             raise exn) in
           print_noticing_newlines s 0 (String.length s);
           print_string "\n";
           flush_all())

let prnt flags s =
    print flags (fun () -> s)

let makeFunctions flags =
  (print flags, prnt flags)

