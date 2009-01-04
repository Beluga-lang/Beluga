(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

type name     = {
  string_of_name : string
}

type cid_typ    = int

type cid_term   = int

type cid_schema = int

type cid_prog   = int

type offset     = int

type var        = int


let mk_name = function
    (* If no {!name} is given, create a new unique {!name}.  This
    prevents the problem that when a {!Store.Typ.entry} or
    {!Store.Term.entry} is looked up, we never have to compare a
    {!string option}.  This prevents the case where two entries appear
    to refer to the same name because {!None} = {!None}. *)
  | None    -> { string_of_name = (Gensym.VarData.gensym ()) }
  | Some "" -> { string_of_name = (Gensym.VarData.gensym ()) }
  | Some x  -> { string_of_name = x                          }
