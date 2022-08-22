open Support

(** The type of description for infix, prefix and postfix operators. *)
type t

(** {1 Destructors} *)

(** [arity operator] is the number of arguments [operator] is expected to be
    applied with.

    - If [fixity operator = Fixity.Prefix], then [arity operator >= 0].
    - If [fixity operator = Fixity.Infix], then [arity operator = 2].
    - If [fixity operator = Fixity.Postfix], then [arity operator = 1]. *)
val arity : t -> Int.t

(** [precedence operator] is the user-defined value for parsing the order of
    operations when operands and arguments are juxtaposed.

    If [precedence o1 < precedence o2], then [o2] precedes [o1] such that
    [a o1 b o2 c] is parsed as [a o1 (b o2 c)], where [a], [b] and [c] are
    operands. *)
val precedence : t -> Int.t

(** [fixity operator] is the fixity of [operator]. *)
val fixity : t -> Fixity.t

(** [associativity operator] is the associativity of [operator].

    - If [fixity operator = Fixity.Prefix], then
      [associativity operator = Associativity.Right_associative].
    - If [fixity operator = Fixity.Postfix], then
      [associativity operator = Associativity.Left_associative]. *)
val associativity : t -> Associativity.t

(** {1 Constructors} *)

val make_prefix : arity:Int.t -> precedence:Int.t -> t

val make_infix : associativity:Associativity.t -> precedence:Int.t -> t

val make_postfix : precedence:Int.t -> t