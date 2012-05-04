open Ast


module Grammar : Camlp4.Sig.Grammar.Static
  with module Loc   = Slexer.Loc
  and  module Token = Slexer.Token


(** Grammar entry for an entire LF Signature *)
val section_eoi : Ast.section list Grammar.Entry.t

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

(** Parse a channel and return a signature *)
val parse_channel :
  ?name:string
  -> input:in_channel
  -> 'a Grammar.Entry.t
  -> 'a

(** Parse a file and return a signature *)
val parse_file   :
     name:string
  -> 'a Grammar.Entry.t
  -> 'a



