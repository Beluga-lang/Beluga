
  type order =	       	                (* Orders                     *)
      Arg of int			(* O ::= x                    *)
    | Lex of order list                 (*     | {O1 .. On}           *)
    | Simul of order list               (*     | [O1 .. On]           *)

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

