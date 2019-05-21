(*
 * For interface, see debug.mli
 *)

let chatter : int ref =  ref 1

let pipeDebug = ref false

let filename = ref "debug"

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

let print_level_spaces f () = for _ = 1 to !level do f " " done

let rec print_noticing_newlines f s x len =
  if x >= len then ()
  else
    let ch = String.get s x in
     (if ch = '\n' then
        (f "\n";
         print_level_spaces f ())
      else
        f (String.make 1 ch));
      print_noticing_newlines f s (x + 1) len

let print' f =
  let finalize, out =
    if !pipeDebug then
      let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 (!filename ^ ".out") in
      let out = output_string oc in
      (fun () -> close_out oc), out
    else
      Misc.const (), prerr_string
  in
  let s =
    try
      f ()
    with
      exn ->
      out
        ( "*** Exception raised inside function passed to dprint:\n"
          ^ Printexc.to_string exn ^ "\n\n"
          ^ Printexc.get_backtrace()
        );
      flush_all ();
      raise exn
  in
  print_noticing_newlines out s 0 (String.length s);
  out "\n";
  finalize ();
  flush_all ()

let print flags f =
  if flags land !r_flags = 0 then () else print' f

let prnt flags s =
  print flags (fun () -> s)

let makeFunctions flags =
  (print flags, prnt flags)

