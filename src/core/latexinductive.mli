open Syntax.Int

type goal =
  | Atom of Comp.typ
  | Impl of goal * goal
  | All of LF.ctyp_decl * goal

type conjunction =
  | True
  | Conjunct of conjunction * goal

type clause =
  { tHead : Comp.typ
  ; eVars : LF.mctx
  ; subGoals : conjunction }

module Convert : 
sig
  val typToClause : Comp.typ -> clause
end

module Printer :
sig
  val clauseToLatex : clause -> Id.name list -> string
  val printCompTypesLatex : string -> string -> unit 
end