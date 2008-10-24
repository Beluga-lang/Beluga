(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   @author Darin Morrison
*)


val whnf     : Syntax.Int.nclo -> Syntax.Int.nclo 
val whnfTyp  : Syntax.Int.tclo -> Syntax.Int.tclo 
val norm     : Syntax.Int.nclo -> Syntax.Int.normal

val conv       : Syntax.Int.nclo -> Syntax.Int.nclo -> bool
val convTyp    : Syntax.Int.tclo -> Syntax.Int.tclo -> bool
val convTypRec : Syntax.Int.trec_clo -> Syntax.Int.trec_clo -> bool
val convSub    : Syntax.Int.sub -> Syntax.Int.sub -> bool
