open Syntax

module Grammar : Camlp4.Sig.Grammar.Static
  with module Loc   = Lexer.Loc
  and  module Token = Lexer.Token

(***** Exported grammar productions *****)

(** Grammar entry for an entire LF Signature *)
val sgn : Ext.Sgn.sgn Grammar.Entry.t

(** Grammar entry for a computation type. *)
val cmp_typ : Ext.Comp.typ Grammar.Entry.t

(** Grammar entry for a Harpoon command. *)
val harpoon_command : Ext.Harpoon.command Grammar.Entry.t

(** Grammar entry for a checkable computation expression. *)
val cmp_exp_chk : Ext.Comp.exp_chk Grammar.Entry.t

(***** Parsing functions *****)

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
