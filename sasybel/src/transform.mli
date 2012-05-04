(**
   @author Marie-Andree B.Langlois
*)

open Core
open Syntax
open Id
open Error
(*
val makeTerminals : Ast.terminal list -> string list
val checkString : string -> string list -> bool
val alts : Parser.Grammar.Loc.t -> string -> string list -> string list -> string list -> string list -> Ast.alternative -> Syntax.Ext.LF.typ
val sgnAlts : Parser.Grammar.Loc.t -> string -> string list -> string list -> string list -> string list -> Ast.alternative list -> Syntax.Ext.Sgn.decl list
val sgnTypes : string list -> string list -> production list -> Ext.Sgn.decl list
val typ_or_sym : Loc.t -> string -> judge list -> string list -> Ext.LF.kind 
val typ_or_sym_list : judge list -> string list -> string list
val sgnJudge : 'a -> jName -> jsyntax -> string list -> string list * Ext.Sgn.decl
val valts : Loc.t -> string list -> vAlternative -> Ext.LF.spine
val judges : string list -> rules list -> Ext.Sgn.decl list
val recSectionDecl :   string list -> string list -> Syntax.section list -> Syntax.Ext.Sgn.decl list 
val recSectionDeclGram : Parser.Grammar.Loc.t -> Syntax.section list -> string list *)
val sectionDecls : Ast.section list -> Syntax.Ext.Sgn.decl list
