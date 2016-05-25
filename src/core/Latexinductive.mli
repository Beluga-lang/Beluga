open Syntax.Int

module Convert : 
sig
  val typToClause : Comp.typ -> clause
end

module Printer :
sig
  val clauseToLatex : clause -> string
  val printCompTypesLatex : string -> unit 
end