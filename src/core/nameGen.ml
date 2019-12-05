(** Contextual name generator.
    This name generator will use programmer-supplied naming hints
    (falling back to good old X, Y, Z) but adjust the numeric counter
    on the name so it is the smallest allowed in a given context.
 *)

open Support

module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

(** Generate a raw metavariable name for a given LF type.
    Uses programmer-supplied name hints with a fallback.
 *)
let mvar (tA : LF.typ) : Id.name =
  match Store.Cid.Typ.gen_mvar_name tA with
  | None -> Id.(mk_name (SomeString "X"))
  | Some g -> Id.(mk_name (SomeString (g ())))

let renumber (ctx : Id.name list) name =
  match Id.max_usage ctx (Id.base_name name) with
  | `unused -> Id.modify_number (Misc.const None) name
  | `used k -> Id.modify_number (Misc.const (Id.inc_hint_cnt k)) name
