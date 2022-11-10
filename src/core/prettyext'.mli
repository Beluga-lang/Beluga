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

  val pp_term_pattern : Format.formatter -> Term.Pattern.t -> Unit.t

  val pp_substitution_pattern :
    Format.formatter -> Substitution.Pattern.t -> Unit.t

  val pp_context_pattern : Format.formatter -> Context.Pattern.t -> Unit.t
end

(** Pretty-printing for meta-level syntax. *)
module Meta : sig
  open Meta

  val pp_typ : Format.formatter -> Typ.t -> Unit.t

  val pp_object : Format.formatter -> Object.t -> Unit.t

  val pp_context : Format.formatter -> Context.t -> Unit.t

  val pp_pattern : Format.formatter -> Pattern.t -> Unit.t

  val pp_schema : Format.formatter -> Schema.t -> Unit.t
end

(** Pretty-printing for computation-level syntax. *)
module Comp : sig
  open Comp

  val pp_kind : Format.formatter -> Kind.t -> Unit.t

  val pp_typ : Format.formatter -> Typ.t -> Unit.t

  val pp_expression : Format.formatter -> Expression.t -> Unit.t

  val pp_pattern : Format.formatter -> Pattern.t -> Unit.t

  val pp_context : Format.formatter -> Context.t -> Unit.t
end
