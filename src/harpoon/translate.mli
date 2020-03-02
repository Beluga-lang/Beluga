open Support
open Beluga
open Syntax.Int

type error =
  | IncompleteProof

exception Error of error

(** Translates a theorem.
    Theorems proven already by a program are returned as-is, but
    theorems proven with a Harpoon proof are translated.
 *)
val theorem : Comp.thm -> Comp.typ -> Comp.exp_chk

(** Traps exceptions raised by this module. *)
val trap : (unit -> 'a) -> (error, 'a) Either.t

(** Formats an error. *)
val fmt_ppr_error : Format.formatter -> error -> unit
