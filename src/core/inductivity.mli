(** The type of annotation for inductive or not inductive parameters.

    An inductive parameter generates induction hypotheses when split on. *)
type t = private
  | Inductive  (** The annotation for inductive parameters. *)
  | NotInductive  (** The annotation for non-inductive parameters. *)

(** {1 Constructors} *)

(** [not_inductive] is [NotInductive]. *)
val not_inductive : t

(** [inductive] is [Inductive]. *)
val inductive : t

(** {1 Predicates and comparisons} *)

(** [max ind1 ind2] is [Inductive] if at least one of [ind1] and [ind2] is
    [Inductive]. Otherwise, [NotInductive] is returned. *)
val max : t -> t -> t

(** [is_not_inductive ind] is [true] if and only if [ind] is [NotInductive]. *)
val is_not_inductive : t -> bool

(** [is_inductive ind] is [true] if and only if [ind] is [Inductive]. *)
val is_inductive : t -> bool
