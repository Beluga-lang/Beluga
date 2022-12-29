(** Annotations for parameters and variables generating induction hypotheses. *)

open Support

(** The type of annotation for inductive or not inductive parameters.

    An inductive parameter generates induction hypotheses when split on. *)
type t = private
  | Inductive  (** The annotation for inductive parameters. *)
  | Not_inductive  (** The annotation for non-inductive parameters. *)

(** {1 Constructors} *)

(** [not_inductive] is [Not_inductive]. *)
val not_inductive : t

(** [inductive] is [Inductive]. *)
val inductive : t

(** {1 Predicates and comparisons} *)

(** [max ind1 ind2] is [Inductive] if at least one of [ind1] and [ind2] is
    [Inductive]. Otherwise, [Not_inductive] is returned. *)
val max : t -> t -> t

(** [min ind1 ind2] is [Not_inductive] if at least one of [ind1] and [ind2]
    is [Not_inductive]. Otherwise, [Inductive] is returned. *)
val min : t -> t -> t

(** [is_not_inductive ind] is [true] if and only if [ind] is [Not_inductive]. *)
val is_not_inductive : t -> bool

(** [is_inductive ind] is [true] if and only if [ind] is [Inductive]. *)
val is_inductive : t -> bool

(** {1 Instances} *)

include Eq.EQ with type t := t
