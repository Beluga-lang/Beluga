(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



open Core.Syntax



module Grammar : Camlp4.Sig.Grammar.Static
  with module Loc   = Lexer.Loc
  and  module Token = Lexer.Token



(** Parse a stream and return a signature *)
val parse_stream :
     ?name:string
  -> input:char Stream.t
  -> 'a Grammar.Entry.t
  -> 'a

(** Parse a string and return a signature *)
val parse_string :
     ?name:string
  -> input:string
  -> 'a Grammar.Entry.t
  -> 'a

(** Parse a file and return a signature *)
val parse_file   :
     file_name:string
  -> 'a Grammar.Entry.t
  -> 'a
