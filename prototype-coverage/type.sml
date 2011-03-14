signature TYPE = sig

  datatype tp =
           Int
         | Bool
         | Arrow of tp * tp
         | Product of tp list
         | Tycon of string     (* user defined types *)
         | Awesome

  val eq : tp * tp -> bool

  val toString : tp -> string

end

structure Type :> TYPE = struct

  datatype tp =
           Int
         | Bool
         | Arrow of tp * tp
         | Product of tp list
         | Tycon of string
         | Awesome

  open Lib

  fun eq (Arrow(domain1, range1), Arrow(domain2, range2)) =
      eq(domain1, domain2) andalso eq(range1, range2)
    | eq (Product ts1, Product ts2) =
      length ts1 = length ts2 andalso List.all eq (ListPair.zip (ts1, ts2))
    | eq (Int, Int) = true
    | eq (Bool, Bool) = true
    | eq (Tycon n1, Tycon n2) = (n1 = n2)
    | eq (Awesome, _) = true
    | eq (_, Awesome) = true
    | eq (_, _) = false

  fun paren lvl oplvl string =
      if oplvl < lvl then "(" ^ string ^ ")"
      else string

  fun toS lvl tp =
      case tp of
        Int => "int"
      | Bool => "bool"
      | Arrow (domain, range) =>
        paren lvl 1 (toS 2 domain ^ " -> " ^ toS 1 range)
      | Product [] => "unit"
      | Product tps => paren lvl 2 (separate " * " (toS 3) tps)
      | Tycon name => name
      | Awesome => "awesome"

  fun toString tp = toS 0 tp
end (* structure Type *)
