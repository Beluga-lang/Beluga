(* MinML abstract syntax
 * Based on the course project of COMP 302, Winter 2010, Joshua Dunfield
 *
 * Shen Chen Xu
 *)

signature MINML = sig
  (* Variables *)
  type name = string
              
  (* Primitive operations *)
  datatype primop = Equals | LessThan | Plus | Minus | Times | Negate

  (* Expression *)
  (* Binders are grouped with their scope, e.g. Fn of (name * exp) *)
  datatype exp =
           Int of int                         (* 0 | 1 | 2 | ... *)
         | Bool of bool                       (* true | false *)
         | If of exp * exp * exp              (* if e then e1 else e2 *)
         | Primop of primop * exp list        (* e1 <op> e2  or  <op> e *)
         | Tuple of exp list                  (* (e1, ..., eN) *)
         | Fn of (name * exp)                 (* fn x => e *)
         | Rec of (name * Type.tp * exp)      (* rec f => e  ---Recursive expression *)
         | Let of (dec list * exp)            (* let decs in e end *)
         | Apply of exp * exp                 (* e1 e2 *)
         | Var of name                        (* x *)
         | Anno of exp * Type.tp              (* e : t *)

         | Case of exp * (pattern * exp) list (* CASE e of p => b | ... *)
         | Valcon of name * exp               (* value constructors that take arguments *)
         | Valcon0 of string                  (* nullary value constructors *)

       and dec =
           Val of exp * name                  (* val x = e *)
         | Valtuple of exp * (name list)      (* val (x1,...,xN) = e *)
         | Datatype of (name * (name * Type.tp list) list)
       (* Datatype name with a list of clause, each clause consists of a value constructor
        * and a list of argument types
        *)

       and pattern =
           Varpat of name
         | Intpat of int
         | Boolpat of bool
         | Tuplepat of pattern list
         | Valconpat of (name * pattern)
         | Valcon0pat of name                 (* nullary value constructor pattern *)

  type tp = Type.tp
            
  (* given a primop and some arguments, apply it *)
  val evalOp : primop * exp list -> exp option

end;  (* signature MINML *)


structure MinML :> MINML = struct
  
  type name = string
              
  datatype primop = Equals | LessThan | Plus | Minus | Times | Negate
                                                               
  datatype exp =
           Int of int                         (* 0 | 1 | 2 | ... *)
         | Bool of bool                       (* true | false *)
         | If of exp * exp * exp              (* if e then e1 else e2 *)
         | Primop of primop * exp list        (* e1 <op> e2  or  <op> e *)
         | Tuple of exp list                  (* (e1, ..., eN) *)
         | Fn of (name * exp)                 (* fn x => e *)
         | Rec of (name * Type.tp * exp)      (* rec f => e  ---Recursive expression *)
         | Let of (dec list * exp)            (* let decs in e end *)
         | Apply of exp * exp                 (* e1 e2 *)
         | Var of name                        (* x *)
         | Anno of exp * Type.tp              (* e : t *)

         | Case of exp * (pattern * exp) list (* CASE e of p => b | ... *)
         | Valcon of name * exp               (* value constructors that take arguments *)
         | Valcon0 of string                  (* nullary value constructors *)

       and dec =
           Val of exp * name                  (* val x = e *)
         | Valtuple of exp * (name list)      (* val (x1,...,xN) = e *)
         | Datatype of (name * (name * Type.tp list) list)
       (* type name with a list of clause, each clause consists of a value constructor
        * and a list of argument types
        *)

       and pattern =
           Varpat of name
         | Intpat of int
         | Boolpat of bool
         | Tuplepat of pattern list
         | Valconpat of (name * pattern)
         | Valcon0pat of name                 (* nullary value constructors *)

  type tp = Type.tp

  fun fromString (f, f') =
      (Option.valOf (Real.fromString f), Option.valOf(Real.fromString f'))


  (* Evaluation of primops on evaluated arguments (i.e., values).
   *
   * evalOp' doesn't coerce its arguments.
   *)
  fun evalOp (Equals, [Int i, Int i']) = SOME (Bool (i = i'))
    | evalOp (Equals, [Bool b, Bool b']) = SOME (Bool (b = b'))
    | evalOp (LessThan, [Int i, Int i']) = SOME (Bool (i < i'))
    | evalOp (Plus, [Int i, Int i']) = SOME (Int (i + i'))
    | evalOp (Minus, [Int i, Int i']) = SOME (Int (i - i'))
    | evalOp (Times, [Int i, Int i']) = SOME (Int (i * i'))
    | evalOp (Negate, [Int i]) = SOME (Int (~i))
    | evalOp (Negate, [Bool b]) = SOME (Bool (not b))
    | evalOp _ = NONE

end  (* structure MinML *)
