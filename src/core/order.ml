module Comp = Syntax.Ext.Comp

type order =	       	                (* Orders                     *)
    Arg of int			(* O ::= x                    *)
  | Lex of order list                 (*     | {O1 .. On}           *)
  | Simul of order list               (*     | [O1 .. On]           *)

let rec of_numeric_order (o : Comp.numeric_order) : order =
  match o with
  | Comp.Arg n -> Arg n
  | Comp.Lex xs -> Lex (List.map of_numeric_order xs)
  | Comp.Simul xs -> Simul (List.map of_numeric_order xs)


(* Mutual dependencies in call patterns:                            *)
(* A call pattern   (a1 P1) .. (ai Pi) .. (an Pn)   expresses       *)
(* that the proof of ai can refer to                                *)
(*   ih a1 .. ai, as long as the arguments are strictly smaller     *)
(* and to                                                           *)
(*   ih a(i+1) .. an as long as the arguments are smaller or equal  *)
(* then the ones of ai.                                             *)

type mutual =		                (* Mutual dependencies        *)
    Empty				(* C ::= .                    *)
  | LE of Id.cid_prog * mutual	(*     |  <= (a) C            *)
  | LT of Id.cid_prog * mutual	(*     |  > (a) C             *)

type dec =                           (* Termination declaration    *)
    Dec of order * mutual            (* Dec ::= (O, C)            *)

(** Converts the order to a list of argument positions
    If the order is too complicated, returns None.
 *)
let list_of_order : order -> int list option = function
  | Arg x -> Some [x]
  | Lex xs ->
     let f = function
       | Arg x -> Some x
       | _ -> None (* We don't support nested lexicographic orders. *)
     in
     Maybe.traverse f xs
