exception NotInitialized

type flags = int

type 'a io = 'a -> unit

module Fmt = struct
  type fmt =
    { fmt : 'a. ('a, Format.formatter, unit) format -> 'a }
end

open Fmt

let chatter : int ref =  ref 1

let r_flags : flags ref = ref 0

let enable () =
  r_flags := lnot 0

let out : Format.formatter option ref = ref None

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
    let g fmt = Format.fprintf ppf fmt in
    try
      f { fmt = g }
    with
      exn ->
      Format.fprintf ppf
        "*** Exception raised inside function passed to dprint:\n%s\n\n%s"
          (Printexc.to_string exn)
          (Printexc.get_backtrace ());
      flush_all ();
      raise exn
  end;
  Format.fprintf ppf "@.";
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
