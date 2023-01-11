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
  | Postfix { precedence; _ } ->
      precedence

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

let is_prefix operator =
  match operator with
  | Prefix _ -> true
  | _ -> false

let is_infix operator =
  match operator with
  | Infix _ -> true
  | _ -> false

let is_postfix operator =
  match operator with
  | Postfix _ -> true
  | _ -> false

let is_nullary = Fun.(arity >> Int.( = ) 0)

let is_unary = Fun.(arity >> Int.( = ) 1)

let is_binary = Fun.(arity >> Int.( = ) 2)

let is_left_associative =
  Fun.(associativity >> Associativity.is_left_associative)

let is_right_associative =
  Fun.(associativity >> Associativity.is_right_associative)

let is_non_associative =
  Fun.(associativity >> Associativity.is_non_associative)

include (
  Eq.Make (struct
    type nonrec t = t

    let equal = Stdlib.( = )
  end) :
    Eq.EQ with type t := t)
