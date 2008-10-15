(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



open Core.Syntax



val parse_stream : ?name:string -> input:char Stream.t -> Ext.sgn_decl list

val parse_string : ?name:string -> input:string        -> Ext.sgn_decl list

val parse_file   :  name:string ->                        Ext.sgn_decl list
