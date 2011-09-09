(**
   @author Renaud Germain
*)

open Syntax
open Id
open Error

(* val recSgnDecl : Ext.Sgn.decl -> Int.Sgn.decl
  val recSgnDecls : Ext.Sgn.decl list -> Int.Sgn.decl list
*)

val recSgnDecl : Ext.Sgn.decl -> unit

val recSgnDecls : Ext.Sgn.decl list -> unit

(**
   @author Marie-Andree B.Langlois
*)

(*val makeTerminals : terminal list -> string list
val checkString : string -> string list -> bool
val alts : Loc.t -> string -> string list -> 'a -> alternative -> Ext.LF.typ
val sgnAlts : Loc.t -> string -> string list -> string list -> alternative list -> Ext.Sgn.decl list
val sgnTypes : string list -> string list -> production list -> Ext.Sgn.decl list
val typ_or_sym : Loc.t -> string -> judge list -> string list -> Ext.LF.kind 
val typ_or_sym_list : judge list -> string list -> string list
val sgnJudge : 'a -> jName -> jsyntax -> string list -> string list * Ext.Sgn.decl
val valts : Loc.t -> string list -> vAlternative -> Ext.LF.spine
val judges : string list -> rules list -> Ext.Sgn.decl list
val recSectionDecl :   string list -> string list -> Syntax.section list -> Syntax.Ext.Sgn.decl list 
val recSectionDeclGram : Parser.Grammar.Loc.t -> Syntax.section list -> string list *)
val sectionDecls :  Syntax.section list -> Syntax.Ext.Sgn.decl list
