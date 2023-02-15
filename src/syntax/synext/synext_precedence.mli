open Support
open Synext_definition

(** {1 Precedence of LF Syntax} *)

module Lf_precedence : Ord.ORD

val precedence_of_lf_kind : lf_kind -> Lf_precedence.t

val precedence_of_lf_typ : lf_typ -> Lf_precedence.t

val precedence_of_lf_term : lf_term -> Lf_precedence.t

(** {1 Precedence of Contextual LF Syntax} *)

module Clf_precedence : Ord.ORD

val precedence_of_clf_typ : clf_typ -> Clf_precedence.t

val precedence_of_clf_term : clf_term -> Clf_precedence.t

val precedence_of_clf_term_pattern : clf_term_pattern -> Clf_precedence.t

(** {1 Precedence of Meta-Level Syntax} *)

module Meta_precedence : Ord.ORD

val precedence_of_schema : schema -> Meta_precedence.t

(** {1 Precedence of Computation-Level Syntax} *)

module Comp_precedence : Ord.ORD

val precedence_of_comp_kind : comp_kind -> Comp_precedence.t

val precedence_of_comp_typ : comp_typ -> Comp_precedence.t

val precedence_of_comp_expression : comp_expression -> Comp_precedence.t

val precedence_of_comp_pattern : comp_pattern -> Comp_precedence.t
