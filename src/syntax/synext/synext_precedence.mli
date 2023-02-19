open Support
open Common
open Synext_definition

module type BASE_PRECEDENCE = sig
  type precedence

  module Ord : Ord.ORD with type t = precedence
end

module type PRECEDENCE_STATE = sig
  include State.STATE

  val lookup_operator_precedence : Qualified_identifier.t -> Int.t Option.t t
end

module Make_precedences (S : PRECEDENCE_STATE) : sig
  include State.STATE with type state = S.state

  (** {1 Precedence of LF Syntax} *)

  module Lf_precedence : BASE_PRECEDENCE

  val precedence_of_lf_kind : lf_kind -> Lf_precedence.precedence t

  val precedence_of_lf_typ : lf_typ -> Lf_precedence.precedence t

  val precedence_of_lf_term : lf_term -> Lf_precedence.precedence t

  (** {1 Precedence of Contextual LF Syntax} *)

  module Clf_precedence : BASE_PRECEDENCE

  val precedence_of_clf_typ : clf_typ -> Clf_precedence.precedence t

  val precedence_of_clf_term : clf_term -> Clf_precedence.precedence t

  val precedence_of_clf_term_pattern :
    clf_term_pattern -> Clf_precedence.precedence t

  (** {1 Precedence of Meta-Level Syntax} *)

  module Schema_precedence : BASE_PRECEDENCE

  val precedence_of_schema : schema -> Schema_precedence.precedence t

  (** {1 Precedence of Computation-Level Syntax} *)

  module Comp_sort_precedence : BASE_PRECEDENCE

  val precedence_of_comp_kind :
    comp_kind -> Comp_sort_precedence.precedence t

  val precedence_of_comp_typ : comp_typ -> Comp_sort_precedence.precedence t

  module Comp_expression_precedence : BASE_PRECEDENCE

  val precedence_of_comp_expression :
    comp_expression -> Comp_expression_precedence.precedence t

  module Comp_pattern_precedence : BASE_PRECEDENCE

  val precedence_of_comp_pattern :
    comp_pattern -> Comp_pattern_precedence.precedence t
end
