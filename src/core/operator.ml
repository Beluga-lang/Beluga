open Support

type t =
  | Prefix of
      { arity : Int.t
      ; precedence : Int.t
      }
  | Infix of
      { precedence : Int.t
      ; associativity : Associativity.t
      }
  | Postfix of { precedence : Int.t }

let[@inline] arity = function
  | Prefix { arity; _ } -> arity
  | Infix _ -> 2
  | Postfix _ -> 1

let[@inline] precedence = function
  | Prefix { precedence; _ }
  | Infix { precedence; _ }
  | Postfix { precedence; _ } -> precedence

let[@inline] fixity = function
  | Prefix _ -> Fixity.prefix
  | Infix _ -> Fixity.infix
  | Postfix _ -> Fixity.postfix

let[@inline] associativity = function
  | Infix { associativity; _ } -> associativity
  | Prefix _ -> Associativity.right_associative
  | Postfix _ -> Associativity.left_associative

let make_prefix ~arity ~precedence =
  assert (arity >= 0);
  Prefix { arity; precedence }

let make_infix ~associativity ~precedence =
  Infix { precedence; associativity }

let make_postfix ~precedence = Postfix { precedence }

include (
  Eq.Make (struct
    type nonrec t = t

    let equal = Stdlib.( = )
  end) :
    Eq.EQ with type t := t)
