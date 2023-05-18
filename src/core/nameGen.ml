open Beluga_syntax
module LF = Synint.LF
module Comp = Synint.Comp

let mvar_string tA =
  match Store.Cid.Typ.gen_mvar_name tA with
  | None -> "X"
  | Some g -> g ()

let pvar_string tA =
  match Store.Cid.Typ.gen_var_name tA with
  | None -> "p"
  | Some g -> g ()

let bvar_string tA =
  match Store.Cid.Typ.gen_var_name tA with
  | None -> "x"
  | Some g -> g ()

let mvar (tA : LF.typ) : Name.t =
  Name.mk_some_string (mvar_string tA)

let pvar (tA : LF.typ) : Name.t =
  Name.mk_some_string ("#" ^ pvar_string tA)

let bvar (tA : LF.typ) : Name.t =
  Name.mk_some_string (bvar_string tA)

let rec var_string = function
  | Comp.TypBox (_, mT) -> (
    match mT with
    | LF.CTyp _ ->
      Error.raise_violation "[NameGen.var] computational CTyp impossible"
    | LF.ClTyp (cU, _) -> (
      match cU with
      | LF.MTyp tA | LF.PTyp tA -> bvar_string tA
      | LF.STyp _ -> "s"))
  | Comp.TypPiBox (_, _, tau) | Comp.TypArr (_, _, tau) | Comp.TypClo (tau, _)
    -> var_string tau
  | _ -> "x"

let var tau = Name.mk_some_string (var_string tau)

let renumber (ctx : Name.t list) name =
  match Name.max_usage ctx (Name.base_name name) with
  | `unused -> Name.modify_number (Fun.const None) name
  | `used k -> Name.modify_number (Fun.const (Name.inc_hint_cnt k)) name
