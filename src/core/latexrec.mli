module Index :
sig
  val annotatedProofs : (Id.name, Annotated.Comp.exp_chk) Hashtbl.t
end

module Printer :
sig
  val printRecLatex : string -> string -> unit
end