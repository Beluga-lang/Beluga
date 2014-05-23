(*
 * For interface, see debug.mli
 *)

let chatter : int ref =  ref 1

let pipeDebug = ref true

let debugFilename = "debug.out"

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

let print_level_spaces f () =
  let rec p n = if n < 1 then () else (f " "; p (n - 1))
  in
     p (!level)

let rec print_noticing_newlines f s x len =
  if x >= len then ()
  else
    let ch = String.get s x in
     (if ch = '\n' then
        (f "\n";
         print_level_spaces f ())
      else
        f (Char.escaped ch));
      print_noticing_newlines f s (x + 1) len


let print flags f =
  if (flags land !r_flags) = 0 then
    ()
  else begin
    if !pipeDebug then begin
      let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "debug.out" in
      let out = output_string oc in
      (print_level_spaces out ();
      let s = try f()
      with
        | Match_failure (file, line, column) -> (out ("*** Match_failure("
                ^ file ^ ", " ^ string_of_int line ^ ", " ^ string_of_int column ^ ")"
                ^ " exception raised inside function passed to dprint ***\n*** Goodbye. ***" ^ flagsToString flags ^ "\n");
                                  exit 200)
        | exn -> (out ("*** WARNING: EXCEPTION RAISED INSIDE FUNCTION PASSED TO dprint *** " ^ flagsToString flags ^ "\n");
                  flush_all();
                  raise exn) in
      let _ = print_noticing_newlines out s 0 (String.length s) in
      let _ = out "\n" in
      close_out oc;
      flush_all()) 
    end else begin
      let out = print_string in
      (print_level_spaces out ();
      let s = try f()
      with
        | Match_failure (file, line, column) -> (out ("*** Match_failure("
                ^ file ^ ", " ^ string_of_int line ^ ", " ^ string_of_int column ^ ")"
                ^ " exception raised inside function passed to dprint ***\n*** Goodbye. ***" ^ flagsToString flags ^ "\n");
                                  exit 200)
        | exn -> (out ("*** WARNING: EXCEPTION RAISED INSIDE FUNCTION PASSED TO dprint *** " ^ flagsToString flags ^ "\n");
                  flush_all();
                  raise exn) in
      print_noticing_newlines out s 0 (String.length s);
      out "\n";
      flush_all()) 
      end
    end

let prnt flags s =
  print flags (fun () -> s)

let makeFunctions flags =
  (print flags, prnt flags)

