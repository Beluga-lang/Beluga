type name     = {
  modules : string list;
  string_of_name : string ;
  was_generated : bool ;
}

type module_id = int

type cid_typ    = module_id * int

type cid_term   = module_id * int

type cid_schema = module_id * int

type cid_coercion = module_id * int

type cid_comp_typ = module_id * int

type cid_comp_cotyp = module_id * int

type cid_comp_const = module_id * int

type cid_comp_dest = module_id * int

type cid_prog   = module_id * int

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
