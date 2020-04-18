open Support

module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

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

let mvar (tA : LF.typ) : Id.name =
  Id.(mk_name (SomeString (mvar_string tA)))

let pvar (tA : LF.typ) : Id.name =
  Id.(mk_name (SomeString ("#" ^ pvar_string tA)))

let bvar (tA : LF.typ) : Id.name =
  Id.(mk_name (SomeString (bvar_string tA)))

let rec var_string =
  function
  | Comp.TypBox (_, mT) ->
     begin match mT with
     | LF.CTyp _ ->
        Error.violation
          "[NameGen.var] computational CTyp impossible"
     | LF.ClTyp (cU, _) ->
        match cU with
        | LF.MTyp tA | LF.PTyp tA -> bvar_string tA
        | LF.STyp _ -> "s"
     end
  | Comp.TypPiBox (_, _, tau) | Comp.TypArr (_, _, tau) | Comp.TypClo (tau, _) ->
     var_string tau
  | _ -> "x"

let var tau = Id.(mk_name (SomeString (var_string tau)))

let renumber (ctx : Id.name list) name =
  match Id.max_usage ctx (Id.base_name name) with
  | `unused -> Id.modify_number (Misc.const None) name
  | `used k -> Id.modify_number (Misc.const (Id.inc_hint_cnt k)) name
