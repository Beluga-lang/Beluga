(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax.Int

val enableCoverage : bool ref

val covers  : LF.mctx
           -> LF.mctx
           -> Comp.ctyp_decl LF.ctx
           -> Comp.branch list
           -> (LF.typ * LF.dctx)
           -> unit

exception NoCover
