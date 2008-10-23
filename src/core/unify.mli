(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   @author Darin Morrison
*)

  type unifTrail

  (* trailing of variable instantiation *)

  val reset       : unit -> unit
  val mark   : unit -> unit
  val unwind : unit -> unit

  val instantiateMVar : Syntax.Int.normal option ref * Syntax.Int.normal * Syntax.Int.constrnt list -> unit
  val instantiatePVar : Syntax.Int.head option ref * Syntax.Int.head * Syntax.Int.constrnt list -> unit

  val resetAwakenCnstrs : unit -> unit
  val nextCnstr : unit -> Syntax.Int.constrnt option
  val addConstraint : Syntax.Int.constrnt list ref * Syntax.Int.constrnt -> unit
  val solveConstraint : Syntax.Int.constrnt -> unit


  (* unification *)
  val intersection : Syntax.Int.psi_hat * (Syntax.Int.sub * Syntax.Int.sub) * Syntax.Int.dctx -> (Syntax.Int.sub * Syntax.Int.dctx)

  exception Unify of string

  val unify : Syntax.Int.psi_hat * Syntax.Int.nclo * Syntax.Int.nclo -> unit (* raises Unify *)
