(** Pretty-printing for the external syntax. *)

open Synext'

(** Pretty-printing for LF kinds, types and terms. *)
module LF : sig
  open LF

  val pp_kind : Format.formatter -> Kind.t -> Unit.t

  val pp_typ : Format.formatter -> Typ.t -> Unit.t

  val pp_term : Format.formatter -> Term.t -> Unit.t
end

(** Pretty-printing for contextual LF objects. *)
module CLF : sig
  open CLF

  val pp_typ : Format.formatter -> Typ.t -> Unit.t

  val pp_term : Format.formatter -> Term.t -> Unit.t

  val pp_substitution : Format.formatter -> Substitution.t -> Unit.t

  val pp_context : Format.formatter -> Context.t -> Unit.t

  val pp_typ_pattern : Format.formatter -> Typ.Pattern.t -> Unit.t

  val pp_term_pattern : Format.formatter -> Term.Pattern.t -> Unit.t

  val pp_substitution_pattern :
    Format.formatter -> Substitution.Pattern.t -> Unit.t

  val pp_context_pattern : Format.formatter -> Context.Pattern.t -> Unit.t
end
