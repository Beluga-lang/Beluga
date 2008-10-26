(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)

type ('a, 'b) either =
  | InL of 'a
  | InR of 'b
