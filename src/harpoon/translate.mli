open Support
open Beluga
open Syntax.Int

type error =
  | IncompleteProof

exception Error of error

type result = (error, Comp.exp_chk) Either.t

(** Translates a theorem given by a Store entry. *)
val entry : Store.Cid.Comp.Entry.t -> (error, Comp.exp_chk) Either.t

(** Translates a theorem.
    Theorems proven already by a program are returned as-is, but
    theorems proven with a Harpoon proof are translated.
 *)
val theorem : Comp.thm -> Comp.typ -> Comp.exp_chk

(** Traps exceptions raised by this module. *)
val trap : (unit -> 'a) -> (error, 'a) Either.t

(** Formats an error. *)
val fmt_ppr_error : Format.formatter -> error -> unit

(** Formats a translation result. *)
val fmt_ppr_result : Format.formatter -> result -> unit
