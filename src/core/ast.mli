(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

(**
   @author Marie-Andree B.Langlois
*)

(** Syntax for the LF *)

open Id
open Syntax


type section =
  | Terminals_decl of Loc.t * terminal list
  | Grammar of Loc.t * production
  | Judgement of Loc.t * jName * jsyntax * assptn option * rules list
  | Theorems of Loc.t * tName * statement * proof list

and file = section list 

and aName = 
  | AName of string

and jName =
  | JName of string

and cName =
  | CName of string

and rName =
  | RName of string

and pName =
  | PName of string

and vName =
  | VName of string

and tName =
  | TName of string

and terminal =
  | Terminal of Loc.t * string

and production = 
  | Production of Loc.t * typ * alternative list
 (* | ContextProd of Loc.t * typ * alternative list*)

and typ = 
  | Typ of Loc.t * string
  | Ctx of Loc.t * string

and alternative =                       
  | AltAtomic of Loc.t * string * alternative option     (* z, suc nat *)
  | AltLam of Loc.t * aName * alternative option (* * alternative binding*)(* * typ * alternative list *)    (* lam \x. e[x] *)  
  | AltFn of Loc.t * typ * typ_or_alt * alternative option                             (* tau -> tau *)
  | AltLet of Loc.t * alternative * alternative * alternative
  | AltBin of Loc.t * alternative                             (* e[x] *)      (* let N x. M[x] *)
  | AltOft of Loc.t * alternative * alternative           (* x : Tau *)
  | AltCtx of Loc.t * typ * alternative list              (* for contexts Gamma, x : tau, AltOft list to be more specific *)
  | AltPar     (* to be removed when manage to ignore  () *)

and typ_or_alt =
  | Ty of typ
  | La of alternative list
                                             
and jsyntax =
  | JSyntax of Loc.t * context option * judge list 

and judge =
  | Judge of Loc.t * string 

and symbol = 
  | Sign of Loc.t * string

and context =
  | Context of cName * alternative list

and assptn = 
  | Assptn of cName

(* should the diference between premise and conclusion be done here? *)
and rules =
  | Rule of Loc.t * premise list * rName * premise              (* RName *)

(* premises and conclustion are Jsyntax with alternatives instead of typs and the typs in the alternatives have varible names *)
(* how to see if the same variable names are used in each premise *)

(* the name option is to name the premises in the proofs, none is when defining the rules VName *)
and premise =
  | Premisse of Loc.t * pName option * pContext option *  vAlternative (* list *)

and pJudge =
  | PJudge of Loc.t * vAlternative

and vAlternative =
  | VAltAtomic of Loc.t * string * vAlternative option      (* z, suc nat *)
  | VAltLam of Loc.t * aName * vAlternative (* * vName * vAlternative list*)
  | VAltFn of Loc.t * vName * typ_or_valt * vAlternative option
  | VAltBin of Loc.t * vAlternative
  | VAltLet of Loc.t * vAlternative                              
  | VAltOft of Loc.t * vAlternative * vName                   (* x : tau *)
  | VAltCtx of Loc.t * cName * vAlternative list              (* for contexts Gamma, x : tau, AltOft list to be more specific *)  
  | VAltPar of Loc.t * vAlternative * vAlternative option

and typ_or_valt =
  | VTy of typ
  | VLa of vAlternative list

and pContext =
  | PContext of vAlternative list

and tpremise =
  | TPremisse of Loc.t * pName option * pContext option *  vAlternative 

and statement = 
  | ForAllExist of Loc.t * tpremise list * premise      
  | Exist of Loc.t  * premise

and proof = 
  | Proof of Loc.t * tpremise * vName * argument list      (* a proof in SASyLF is an induction statement and a list of arguments; dt: e value by induction on ds ... arguments *)
  | PRule of Loc.t * tpremise * proof * vName list
  | Induction of Loc.t * name
  | InductionHyp of Loc.t
  | CaseAn of Loc.t * tpremise * vName list * argument list
  | PTheorem of Loc.t * tName 
  | URule of Loc.t * tpremise * rName * vName list option

and argument = 
  | Argument of Loc.t * rules * proof list 
  | Arg of Loc.t * vAlternative * proof list

type kind_or_typ =
  | Kind of Ext.LF.kind
  | Typp  of Ext.LF.typ
 





