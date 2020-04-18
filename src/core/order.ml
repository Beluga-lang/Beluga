open Support

module Comp = Syntax.Ext.Comp
module I = Syntax.Int.Comp

let rec of_numeric_order : Comp.numeric_order -> I.order =
  function
  | Comp.Arg n -> I.Arg n
  | Comp.Lex xs -> I.Lex (List.map of_numeric_order xs)
  | Comp.Simul xs -> I.Simul (List.map of_numeric_order xs)


(* Mutual dependencies in call patterns:                            *)
(* A call pattern   (a1 P1) .. (ai Pi) .. (an Pn)   expresses       *)
(* that the proof of ai can refer to                                *)
(*   ih a1 .. ai, as long as the arguments are strictly smaller     *)
(* and to                                                           *)
(*   ih a(i+1) .. an as long as the arguments are smaller or equal  *)
(* then the ones of ai.                                             *)

type mutual =                   (* Mutual dependencies        *)
  | Empty                       (* C ::= .                    *)
  | LE of Id.cid_prog * mutual  (*     |  <= (a) C            *)
  | LT of Id.cid_prog * mutual  (*     |  > (a) C             *)

type dec =                             (* Termination declaration    *)
  | Dec of I.order * mutual            (* Dec ::= (O, C)            *)

(** Converts the order to a list of argument positions
    If the order is too complicated, returns None.
 *)
let list_of_order : I.order -> int list option =
  function
  | I.Arg x -> Some [x]
  | I.Lex xs ->
     let f =
       function
       | I.Arg x -> Some x
       | _ -> None (* We don't support nested lexicographic orders. *)
     in
     Maybe.traverse f xs
