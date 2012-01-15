(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

module type SIG = sig
  type error

  val error_location : error -> Syntax.Loc.t
  val report_error : Format.formatter -> error -> unit
end

exception Violation of string

exception NotImplemented

let information = ref []

let getInformation () =
  match List.rev !information with
    | [] -> ""
    | information ->
        (List.fold_left (fun acc s -> acc ^ "\n" ^ s) "" information) ^ "\n"

let addInformation message =
  information := message :: !information
