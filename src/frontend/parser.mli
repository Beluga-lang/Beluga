(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



open Core.Common
open Core.Syntax



module Grammar : Camlp4.Sig.Grammar.Static
  with module Loc   = Lexer.Loc
  and  module Token = Lexer.Token


(** Grammar entry for an entire LF Signature *)
val p_sgn_eoi : Ext.sgn_decl list Grammar.Entry.t

(** Parse a stream and return a signature *)
val parse_stream :
     ?name:string
  -> input:char Stream.t
  -> 'a Grammar.Entry.t
  -> (exn, 'a) either

(** Parse a string and return a signature *)
val parse_string :
     ?name:string
  -> input:string
  -> 'a Grammar.Entry.t
  -> (exn, 'a) either

(** Parse a channel and return a signature *)
val parse_channel :
  ?name:string
  -> input:in_channel
  -> 'a Grammar.Entry.t
  -> (exn, 'a) either

(** Parse a file and return a signature *)
val parse_file   :
     name:string
  -> 'a Grammar.Entry.t
  -> (exn, 'a) either
