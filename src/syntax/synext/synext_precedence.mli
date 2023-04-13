open Support
open Common
open Synext_definition

module type BASE_PRECEDENCE = sig
  type precedence

  module Ord : Ord.ORD with type t = precedence
end

module type PRECEDENCE_STATE = sig
  include Imperative_state.IMPERATIVE_STATE

  val lookup_operator_precedence :
    state -> Qualified_identifier.t -> Int.t Option.t
end

module Make_precedences (S : PRECEDENCE_STATE) : sig
  include Imperative_state.IMPERATIVE_STATE with type state = S.state

  (** {1 Precedence of LF Syntax} *)

  module Lf_precedence : BASE_PRECEDENCE

  val precedence_of_lf_kind : state -> lf_kind -> Lf_precedence.precedence

  val precedence_of_lf_typ : state -> lf_typ -> Lf_precedence.precedence

  val precedence_of_lf_term : state -> lf_term -> Lf_precedence.precedence

  (** {1 Precedence of Contextual LF Syntax} *)

  module Clf_precedence : BASE_PRECEDENCE

  val precedence_of_clf_typ : state -> clf_typ -> Clf_precedence.precedence

  val precedence_of_clf_term : state -> clf_term -> Clf_precedence.precedence

  val precedence_of_clf_term_pattern :
    state -> clf_term_pattern -> Clf_precedence.precedence

  (** {1 Precedence of Meta-Level Syntax} *)

  module Schema_precedence : BASE_PRECEDENCE

  val precedence_of_schema : state -> schema -> Schema_precedence.precedence

  (** {1 Precedence of Computation-Level Syntax} *)

  module Comp_sort_precedence : BASE_PRECEDENCE

  val precedence_of_comp_kind :
    state -> comp_kind -> Comp_sort_precedence.precedence

  val precedence_of_comp_typ :
    state -> comp_typ -> Comp_sort_precedence.precedence

  module Comp_expression_precedence : BASE_PRECEDENCE

  val precedence_of_comp_expression :
    state -> comp_expression -> Comp_expression_precedence.precedence

  module Comp_pattern_precedence : BASE_PRECEDENCE

  val precedence_of_comp_pattern :
    state -> comp_pattern -> Comp_pattern_precedence.precedence
end
