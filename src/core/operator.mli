open Support

type t

(** {1 Destructors} *)

val arity : t -> Int.t

val precedence : t -> Int.t

val fixity : t -> Fixity.t

val associativity : t -> Associativity.t

(** {1 Constructors} *)

val make_prefix :
  identifier:QualifiedIdentifier.t -> arity:Int.t -> precedence:Int.t -> t

val make_infix :
     identifier:QualifiedIdentifier.t
  -> associativity:Associativity.t
  -> precedence:Int.t
  -> t

val make_postfix : identifier:QualifiedIdentifier.t -> precedence:Int.t -> t
