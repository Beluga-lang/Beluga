(* Printing expressions *)
signature PRINT =
sig
  (* print an expression *)
  val expToString : MinML.exp -> string
  val typeToString : MinML.tp -> string
end

(*--------------------------------------------------*)
structure Print :> PRINT =
struct

  open Lib
  structure M = MinML
  type exp = M.exp

  fun paren lvl oplvl string =
      if oplvl < lvl then "(" ^ string ^ ")"
      else string

  fun po_prec M.Equals = 4
    | po_prec M.LessThan = 4
    | po_prec M.Plus = 5
    | po_prec M.Minus = 5
    | po_prec M.Times = 6
    | po_prec M.Negate = 8

  fun po M.Equals = "="
    | po M.LessThan = "<"
    | po M.Plus = "+"
    | po M.Minus = "-"
    | po M.Times = "*"
    | po M.Negate = "~"

  and expstr lvl e =
      let val f = expstr
      in case e of
           M.Int i => Int.toString i
         | M.Bool true => "true"
         | M.Bool false => "false"
         | M.If (ec, et, ef) =>
           paren lvl 2 ("if " ^ f 3 ec ^ " then " ^ f 3 et ^ " else " ^ f 3 ef)
         | M.Primop (p, []) => "(bad primop)"
         | M.Primop (p, [e]) => paren lvl 8 (po p ^ f 8 e)
         | M.Primop (p, e::es) =>
           paren lvl (po_prec p) (foldl (fn (a, b) => b ^ " " ^ po p ^ " " ^ f (po_prec p) a) (f (po_prec p) e) es)
         | M.Tuple es => "(" ^ separate ", " (f 1) es ^ ")"
         | M.Fn (x, e) =>
           paren lvl 3 ("fn " ^ x ^  " => " ^ f 1 e)
         | M.Rec (ff, ftype, e) =>
           paren lvl 3 ("rec " ^ ff ^  " : " ^ typeToString ftype ^ " => " ^ f 1 e)
         | M.Let (decs, e) =>
           "let " ^ separate "\n    " decToString decs ^ " in " ^ f 0 e ^ " end"
         | M.Apply (e1, e2) =>
           paren lvl 7 ((f 7 e1) ^ " " ^ (f 8 e2))
         | M.Var v => v
         | M.Anno (e, t) => paren lvl 1 (f 2 e ^ " : " ^ typeToString t)

         | M.Case (p, cs) => "case " ^ f lvl p ^ " of " ^ clauseToString cs
         | M.Valcon (name, e) => name ^ " " ^ f lvl e
         | M.Valcon0 x => x
      end

  and clauseToString [] = ""
    | clauseToString [(p, e)] = patternToString 0 p ^ " => " ^ expToString e
    | clauseToString (c :: cs) = clauseToString [c] ^ " | " ^ clauseToString cs

  and patternToString lvl p =
      let val f = patternToString
      in case p of
           M.Varpat x => x
         | M.Intpat i => Int.toString i
         | M.Boolpat true => "true"
         | M.Boolpat false => "false"
         | M.Tuplepat ps => "(" ^ (separate ", " (f 1) ps) ^ ")"
         | M.Valconpat (x, y) => x ^" " ^ patternToString lvl y
         | M.Valcon0pat x => x
      end

  and expToString e = expstr 0 e

  and decToString e = let
    val f = expToString
  in
    case e of
      M.Val (r as M.Rec (ff, ftype, M.Fn(x, body)), gg) =>
      if ff = gg then
        "fun " ^ ff ^ " : " ^ typeToString ftype ^ " " ^ x ^  " = " ^ f body
      else "val " ^ gg ^ " = " ^ f r

    | M.Val (e1, x) =>
      "val " ^ x ^ " = " ^ f e1

    | M.Valtuple (e1, xs) =>
      "val (" ^ separate ", " (fn name => name) xs ^ ") = " ^ f e1
    | M.Datatype (name, clauses) =>
      "datatype " ^ name ^ " = ..."
  end

  and typeToString t = Type.toString (* expToString *) t
end;  (* structure Print *)
