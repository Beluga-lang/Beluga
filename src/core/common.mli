(* -*- indent-tabs-mode: nil; -*- *)

type ('a, 'b) either =
  | InL of 'a
  | InR of 'b
