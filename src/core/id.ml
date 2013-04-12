type name     = {
  string_of_name : string
}

type cid_typ    = int

type cid_term   = int

type cid_schema = int

type cid_coercion = int

type cid_comp_typ = int

type cid_comp_cotyp = int

type cid_comp_const = int

type cid_comp_dest = int

type cid_prog   = int

type offset     = int

type var        = int

type name_guide =
  | NoName
  | MVarName of (unit -> string) option
  | PVarName of (unit -> string) option
  | BVarName of (unit -> string) option
  | SomeName of name
  | SomeString of string


let mk_name = function
    (* If no {!name} is given, create a new unique {!name}.
       This prevents the problem that when a {!Store.Typ.entry} or {!Store.Term.entry} is
       looked up, we never have to compare a {!string option}.
       This prevents the case where two entries appear to refer to the same name
       because {!None} = {!None}. *)
  | MVarName (Some vGen)  ->
      { string_of_name = vGen() }

  | MVarName None  ->
      { string_of_name = Gensym.MVarData.gensym() }

  | PVarName (Some vGen)  ->
      { string_of_name = "#" ^ vGen() }

  | PVarName None  ->
      { string_of_name = "#" ^ Gensym.VarData.gensym() }


  | BVarName (Some vGen)   ->
        { string_of_name = vGen() }

  | SomeName x  -> x

  | SomeString x     ->
        { string_of_name = x }

  | _     -> { string_of_name = (Gensym.VarData.gensym ()) }
