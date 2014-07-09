type name     = {
  modules : string list;
  string_of_name : string ;
  was_generated : bool ;
}

type cid_typ    = (string list, int)

type cid_term   = (string list, int)

type cid_schema = (string list, int)

type cid_coercion = (string list, int)

type cid_comp_typ = (string list, int)

type cid_comp_cotyp = (string list, int)

type cid_comp_const = (string list, int)

type cid_comp_dest = (string list, int)

type cid_prog   = (string list, int)

type offset     = int

type var        = int

type name_guide =
  | NoName
  | MVarName of (unit -> string) option
  | SVarName of (unit -> string) option
  | PVarName of (unit -> string) option
  | BVarName of (unit -> string) option
  | SomeName of name
  | SomeString of string

let mk_name ?(modules=[]) : name_guide -> name = function
    (* If no {!name} is given, create a new unique {!name}.
       This prevents the problem that when a {!Store.Typ.entry} or {!Store.Term.entry} is
       looked up, we never have to compare a {!string option}.
       This prevents the case where two entries appear to refer to the same name
       because {!None} = {!None}. *)
  | MVarName (Some vGen)  ->
        { modules = modules; string_of_name = vGen() ; was_generated = true}

  | MVarName None  ->
      { modules = modules; string_of_name = Gensym.MVarData.gensym() ; was_generated = true }

  | PVarName (Some vGen)  ->
        { modules = modules; string_of_name = vGen() ; was_generated = true }

  | PVarName None  ->
      { modules = modules; string_of_name = "#" ^ Gensym.VarData.gensym() ; was_generated = true }

  | SVarName None ->
      { modules = modules; string_of_name = Gensym.MVarData.gensym() ; was_generated = true}
      
  | SVarName (Some vGen) ->
        { modules = modules; string_of_name = vGen() ; was_generated = true }

  | BVarName (Some vGen)   ->
        { modules = modules; string_of_name = vGen() ; was_generated = true}

  | SomeName x  -> x

  | SomeString x -> 
        { modules = modules; string_of_name = x ; was_generated = false }

  | _     -> { modules = modules; string_of_name = (Gensym.VarData.gensym ())  ; was_generated = true }
