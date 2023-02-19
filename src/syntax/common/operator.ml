open Support

type t =
  | Prefix of { precedence : Int.t }
  | Infix of
      { precedence : Int.t
      ; associativity : Associativity.t
      }
  | Postfix of { precedence : Int.t }

let[@inline] arity = function
  | Infix _ -> 2
  | Prefix _
  | Postfix _ ->
      1

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

let make_prefix ~precedence = Prefix { precedence }

let make_infix ~associativity ~precedence =
  Infix { precedence; associativity }

let make_postfix ~precedence = Postfix { precedence }

let is_prefix = function
  | Prefix _ -> true
  | Infix _
  | Postfix _ ->
      false

let is_infix = function
  | Infix _ -> true
  | Prefix _
  | Postfix _ ->
      false

let is_postfix = function
  | Postfix _ -> true
  | Prefix _
  | Infix _ ->
      false

let is_unary = function
  | Infix _ -> false
  | Prefix _
  | Postfix _ ->
      true

let is_binary = function
  | Infix _ -> true
  | Prefix _
  | Postfix _ ->
      false

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
