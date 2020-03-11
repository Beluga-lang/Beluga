open Support.Equality
module Maybe = Support.Maybe

exception NotInitialized

type flags = int

type 'a io = 'a -> unit

module Fmt = Support.Fmt
open Fmt

let r_flags : flags ref = ref 0

let enable () =
  Printexc.record_backtrace true;
  r_flags := lnot 0

let out : Format.formatter option ref = ref None

(** Tests if a given flag is set. *)
let flag (n : int) : bool = 1 = !r_flags land (1 lsl n)

let rec toFlags = function
  | [] -> 0
  | x::xs ->
       if x > 30 then
         raise (Invalid_argument "toFlags argument out of bounds")
       else
         (toFlags xs) lor (1 lsl x)

let init_formatter ppf : unit =
  out := Some ppf;
  Format.fprintf ppf "@[<v>"

let init (filename : string option) : unit =
  match !out with
  | Some _ -> ()
  | None ->
     let oc =
       match filename with
       | Some name ->
          open_out name
       | None ->
          stderr
     in
     init_formatter (Format.formatter_of_out_channel oc)

let print' f =
  let ppf = Maybe.get' NotInitialized !out in
  begin
    let fmt x = Format.fprintf ppf x in
    try
      f { fmt }
    with
      exn ->
      Format.fprintf ppf
        "*** @[<v>Exception raised inside function passed to dprint:@,\
         %s@,%s@]"
          (Printexc.to_string exn)
          (Printexc.get_backtrace ());
      flush_all ();
      raise exn
  end;
  Format.fprintf ppf "@,@?";
  flush_all ()

let printf flags (f : fmt -> unit) : unit =
  if flags land !r_flags = 0 then () else print' f

let print flags f =
  printf flags (fun p -> p.fmt "%s" (f ()))

let prnt flags s =
  print flags (fun () -> s)

let makeFunctions flags =
  (print flags, prnt flags)

let makeFunctions' flags =
  (printf flags, print flags, prnt flags)

let printf f = printf 1 f

let indented dprintf n f =
  dprintf
    (fun p ->
      (* generate the format string with the right number of spaces.
         I suspect this is more performant than calling `p.fmt " "` n
         times.
       *)
      let rec mkfmt fmt n =
        match n with
        | 0 -> fmt ^^ "@[<v>"
        | _ -> mkfmt (" " ^^ fmt) (n - 1)
      in
      let fmt = mkfmt "" n in
      p.fmt fmt);
  let x = f () in
  dprintf (fun p -> p.fmt "@]");
  x
