open Equality

exception Debug_not_initialized

type flags = int

type 'a io = 'a -> unit

module Fmt = Format
open Fmt

let r_flags : flags ref = ref 0 (* Boolean flags as a bit sequence. *)

let enable () =
  Printexc.record_backtrace true;
  r_flags := lnot 0 (* All bits set to [1] *)

let is_enabled () = !r_flags <> 0

let out : Format.formatter option ref = ref Option.none

(** Tests if a given flag is set. *)
let flag (n : int) : bool = 1 = !r_flags land (1 lsl n)

let rec toFlags = function
  | [] -> 0
  | x :: xs ->
      if x > 30 then
        raise
          (Invalid_argument
             (Format.asprintf "[%s] argument out of bounds" __FUNCTION__))
      else toFlags xs lor (1 lsl x)

let init_formatter ppf = out := Option.some ppf

let init filename =
  match !out with
  | Option.Some _ -> ()
  | Option.None ->
      let out_channel =
        match filename with
        | Option.Some name -> open_out name
        | Option.None -> stderr
      in
      init_formatter (Format.formatter_of_out_channel out_channel)

let print' f =
  let ppf = Option.get' Debug_not_initialized !out in
  let fmt x = Format.fprintf ppf (x ^^ "@\n") in
  (try f { fmt } with
  | exn ->
      Format.fprintf ppf
        "*** @[<v>Exception raised inside function passed to dprint:@,\
         %s@,\
         %s@]"
        (Printexc.to_string exn)
        (Printexc.get_backtrace ());
      flush_all ();
      raise exn);
  Format.fprintf ppf "@,@?";
  flush_all ()

let printf flags f = if Bool.not (flags land !r_flags = 0) then print' f

let print flags f = printf flags (fun p -> p.fmt "%s" (f ()))

let prnt flags s = printf flags (fun p -> p.fmt "%s" s)

let makeFunctions flags = (print flags, prnt flags)

let makeFunctions' flags = (printf flags, print flags, prnt flags)

let printf f = printf 1 f

(** [make_margin n] is a string of spaces of length [n]. *)
let make_margin n = String.init n (fun _index -> ' ')

let indented dprintf n =
  let margin = make_margin n in
  fun f ->
    dprintf (fun p -> p.fmt "%s@[<v>" margin);
    let x = f () in
    dprintf (fun p -> p.fmt "@]");
    x
