(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



(** A location, to be paired with a token during lexical analysis.
    Used for localized error reporting, etc. *)
module Loc : Camlp4.Sig.Loc
  with type t = Core.Syntax.Loc.t

(** Token functionality, parameterized on a concrete location and
    token representation. *)
module Token : Camlp4.Sig.Token
  with module Loc = Loc
  and  type t     = Token.t


(** Located errors specific to the lexical analysis phase. *)
module Error : Camlp4.Sig.Error


(** Create a function mapping an initial location (needed for the file
    name) and a stream of characters to a stream of located tokens. *)
val mk : unit -> (Loc.t -> char Stream.t -> (Token.t * Loc.t) Stream.t)
