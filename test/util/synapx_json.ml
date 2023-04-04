open Support
open Beluga
open Beluga_syntax
open Base_json

let json_of_location location =
  if Location.is_ghost location then `Null
  else
    json_of_association
      [ ("filename", json_of_string (Location.filename location))
      ; ("start_line", json_of_int (Location.start_line location))
      ; ("start_column", json_of_int (Location.start_column location))
      ; ("stop_line", json_of_int (Location.stop_line location))
      ; ("stop_column", json_of_int (Location.stop_column location))
      ]

let[@inline] json_of_plicity = function
  | Plicity.Explicit -> json_of_string "explicit"
  | Plicity.Implicit -> json_of_string "implicit"

let json_of_name name =
  json_of_association
    [ ("modules", json_of_list json_of_string (Name.get_module name))
    ; ("name", json_of_string (Name.base_name name))
    ; ("location", json_of_location (Name.location name))
    ]

let rec lf_tuple_to_list1 = function
  | Synapx.LF.Last tM -> List1.singleton tM
  | Synapx.LF.Cons (tM, rest) -> List1.cons tM (lf_tuple_to_list1 rest)

let rec lf_spine_to_list = function
  | Synapx.LF.Nil -> []
  | Synapx.LF.App (tM, spine) -> tM :: lf_spine_to_list spine

let rec meta_spine_to_list = function
  | Synapx.Comp.MetaNil -> []
  | Synapx.Comp.MetaApp (cA, mspine) -> cA :: meta_spine_to_list mspine

let rec lf_typ_rec_to_list1 = function
  | Synapx.LF.SigmaLast (name_opt, typ) -> List1.singleton (name_opt, typ)
  | Synapx.LF.SigmaElem (name, typ, rest) ->
      List1.cons (Option.some name, typ) (lf_typ_rec_to_list1 rest)

let json_of_lf_ctx json_of_element cPsi =
  json_of_list json_of_element (Context.to_list cPsi)

let json_of_lf_svar_class = function
  | Synapx.LF.Ren -> json_of_string "renaming"
  | Synapx.LF.Subst -> json_of_string "substitution"

let rec json_of_lf_kind = function
  | Synapx.LF.Typ -> json_of_variant ~name:"Synapx.LF.Typ" ~data:[]
  | Synapx.LF.PiKind ((declaration, plicity), tK) ->
      json_of_variant ~name:"Synapx.LF.PiKind"
        ~data:
          [ ("declaration", json_of_lf_typ_decl declaration)
          ; ("plicity", json_of_plicity plicity)
          ; ("body", json_of_lf_kind tK)
          ]

and json_of_lf_typ_decl = function
  | Synapx.LF.TypDecl (name, tA) ->
      json_of_variant ~name:"Synapx.LF.TypDecl"
        ~data:[ ("name", json_of_name name); ("typ", json_of_lf_typ tA) ]
  | Synapx.LF.TypDeclOpt name ->
      json_of_variant ~name:"Synapx.LF.TypDeclOpt"
        ~data:[ ("name", json_of_name name) ]

and json_of_lf_cltyp = function
  | Synapx.LF.MTyp tA ->
      json_of_variant ~name:"Synapx.LF.MTyp"
        ~data:[ ("typ", json_of_lf_typ tA) ]
  | Synapx.LF.PTyp tA ->
      json_of_variant ~name:"Synapx.LF.PTyp"
        ~data:[ ("typ", json_of_lf_typ tA) ]
  | Synapx.LF.STyp (svar_class, cPsi) ->
      json_of_variant ~name:"Synapx.LF.STyp"
        ~data:
          [ ("substitution_class", json_of_lf_svar_class svar_class)
          ; ("closure", json_of_lf_dctx cPsi)
          ]

and json_of_lf_ctyp = function
  | Synapx.LF.ClTyp (tp, cPsi) ->
      json_of_variant ~name:"Synapx.LF.ClTyp"
        ~data:
          [ ("context", json_of_lf_dctx cPsi); ("typ", json_of_lf_cltyp tp) ]
  | Synapx.LF.CTyp cid ->
      json_of_variant ~name:"Synapx.LF.CTyp"
        ~data:[ ("schema_cid", json_of_int cid) ]

and json_of_lf_ctyp_decl = function
  | Synapx.LF.Decl (name, cA, plicity) ->
      json_of_variant ~name:"Synapx.LF.Decl"
        ~data:
          [ ("identifier", json_of_name name)
          ; ("typ", json_of_lf_ctyp cA)
          ; ("plicity", json_of_plicity plicity)
          ]
  | Synapx.LF.DeclOpt name ->
      json_of_variant ~name:"Synapx.LF.DeclOpt"
        ~data:[ ("identifier", json_of_name name) ]

and json_of_lf_typ = function
  | Synapx.LF.Atom (location, cid, spine) ->
      json_of_variant ~name:"Synapx.LF.Atom"
        ~data:
          [ ("location", json_of_location location)
          ; ("cid_typ", json_of_int cid)
          ; ("spine", json_of_lf_spine spine)
          ]
  | Synapx.LF.PiTyp ((declaration, plicity), tA) ->
      json_of_variant ~name:"Synapx.LF.PiTyp"
        ~data:
          [ ("declaration", json_of_lf_typ_decl declaration)
          ; ("plicity", json_of_plicity plicity)
          ; ("body", json_of_lf_typ tA)
          ]
  | Synapx.LF.Sigma trec ->
      json_of_variant ~name:"Synapx.LF.Sigma"
        ~data:[ ("typ", json_of_lf_typ_rec trec) ]

and json_of_lf_typ_rec trec =
  json_of_list1
    (fun (name_opt, typ) ->
      json_of_association
        [ ("name", json_of_option json_of_name name_opt)
        ; ("typ", json_of_lf_typ typ)
        ])
    (lf_typ_rec_to_list1 trec)

and json_of_lf_tuple tuple =
  json_of_list1 json_of_lf_normal (lf_tuple_to_list1 tuple)

and json_of_lf_normal = function
  | Synapx.LF.Lam (location, var, tM) ->
      json_of_variant ~name:"Synapx.LF.Lam"
        ~data:
          [ ("location", json_of_location location)
          ; ("parameter_identifier", json_of_name var)
          ; ("body", json_of_lf_normal tM)
          ]
  | Synapx.LF.Root (location, head, spine) ->
      json_of_variant ~name:"Synapx.LF.Root"
        ~data:
          [ ("location", json_of_location location)
          ; ("head", json_of_lf_head head)
          ; ("spine", json_of_lf_spine spine)
          ]
  | Synapx.LF.LFHole (location, label_opt) ->
      json_of_variant ~name:"Synapx.LF.LFHole"
        ~data:
          [ ("location", json_of_location location)
          ; ("label", json_of_option json_of_string label_opt)
          ]
  | Synapx.LF.Tuple (location, tuple) ->
      json_of_variant ~name:"Synapx.LF.Tuple"
        ~data:
          [ ("location", json_of_location location)
          ; ("elements", json_of_lf_tuple tuple)
          ]
  | Synapx.LF.Ann (location, tM, tA) ->
      json_of_variant ~name:"Synapx.LF.Ann"
        ~data:
          [ ("location", json_of_location location)
          ; ("term", json_of_lf_normal tM)
          ; ("typ", json_of_lf_typ tA)
          ]

and json_of_lf_head = function
  | Synapx.LF.BVar offset ->
      json_of_variant ~name:"Synapx.LF.BVar"
        ~data:[ ("offset", json_of_int offset) ]
  | Synapx.LF.Const cid ->
      json_of_variant ~name:"Synapx.LF.Const"
        ~data:[ ("cid_term", json_of_int cid) ]
  | Synapx.LF.MVar (u, s) ->
      json_of_variant ~name:"Synapx.LF.MVar"
        ~data:
          [ ("u", json_of_lf_cvar u)
          ; ("s", json_of_option json_of_lf_sub s)
          ]
  | Synapx.LF.Proj (head, j) ->
      json_of_variant ~name:"Synapx.LF.Proj"
        ~data:
          [ ("head", json_of_lf_head head)
          ; ("projection", json_of_lf_proj j)
          ]
  | Synapx.LF.Hole -> json_of_variant ~name:"Synapx.LF.Hole" ~data:[]
  | Synapx.LF.PVar (p, s) ->
      json_of_variant ~name:"Synapx.LF.PVar"
        ~data:
          [ ("p", json_of_lf_cvar p)
          ; ("s", json_of_option json_of_lf_sub s)
          ]
  | Synapx.LF.FVar name ->
      json_of_variant ~name:"Synapx.LF.FVar"
        ~data:[ ("name", json_of_name name) ]
  | Synapx.LF.FMVar (name, s) ->
      json_of_variant ~name:"Synapx.LF.FMVar"
        ~data:
          [ ("name", json_of_name name)
          ; ("s", json_of_option json_of_lf_sub s)
          ]
  | Synapx.LF.FPVar (name, s) ->
      json_of_variant ~name:"Synapx.LF.FPVar"
        ~data:
          [ ("name", json_of_name name)
          ; ("s", json_of_option json_of_lf_sub s)
          ]

and json_of_lf_proj = function
  | Synapx.LF.ByPos j -> json_of_int j
  | Synapx.LF.ByName x -> json_of_name x

and json_of_lf_spine spine =
  json_of_list json_of_lf_normal (lf_spine_to_list spine)

and json_of_lf_sub = function
  | Synapx.LF.EmptySub -> json_of_variant ~name:"Synapx.LF.EmptySub" ~data:[]
  | Synapx.LF.Id -> json_of_variant ~name:"Synapx.LF.Id" ~data:[]
  | Synapx.LF.Dot (ft, s) ->
      json_of_variant ~name:"Synapx.LF.Dot"
        ~data:
          [ ("term", json_of_lf_front ft)
          ; ("substitution", json_of_lf_sub s)
          ]
  | Synapx.LF.SVar (i, sigma) ->
      json_of_variant ~name:"Synapx.LF.SVar"
        ~data:
          [ ("variable", json_of_lf_cvar i)
          ; ("closure", json_of_option json_of_lf_sub sigma)
          ]
  | Synapx.LF.FSVar (s, sigma) ->
      json_of_variant ~name:"Synapx.LF.FSVar"
        ~data:
          [ ("name", json_of_name s)
          ; ("closure", json_of_option json_of_lf_sub sigma)
          ]

and json_of_lf_front = function
  | Synapx.LF.Head h ->
      json_of_variant ~name:"Synapx.LF.Head"
        ~data:[ ("head", json_of_lf_head h) ]
  | Synapx.LF.Obj tM ->
      json_of_variant ~name:"Synapx.LF.Obj"
        ~data:[ ("obj", json_of_lf_normal tM) ]

and json_of_lf_cvar = function
  | Synapx.LF.Offset offset ->
      json_of_variant ~name:"Synapx.LF.Offset"
        ~data:[ ("offset", json_of_int offset) ]
  | Synapx.LF.MInst (_cM, _cA) ->
      Format.fprintf Format.err_formatter
        "Warning: Unsupported [Synapx.LF.MInst] in JSON conversion";
      json_of_variant ~name:"Synapx.LF.MInst"
        ~data:
          [ ("term", json_of_string "<unsupported>")
          ; ("typ", json_of_string "<unsupported>")
          ]

and json_of_lf_dctx = function
  | Synapx.LF.Null -> json_of_variant ~name:"Synapx.LF.Null" ~data:[]
  | Synapx.LF.CtxVar g ->
      json_of_variant ~name:"Synapx.LF.CtxVar"
        ~data:[ ("variable", json_of_lf_ctx_var g) ]
  | Synapx.LF.DDec (cPsi, declaration) ->
      json_of_variant ~name:"Synapx.LF.DDec"
        ~data:
          [ ("context", json_of_lf_dctx cPsi)
          ; ("declaration", json_of_lf_typ_decl declaration)
          ]
  | Synapx.LF.CtxHole -> json_of_variant ~name:"Synapx.LF.CtxHole" ~data:[]

and json_of_lf_ctx_var = function
  | Synapx.LF.CtxName n ->
      json_of_variant ~name:"Synapx.LF.CtxName"
        ~data:[ ("name", json_of_name n) ]
  | Synapx.LF.CtxOffset offset ->
      json_of_variant ~name:"Synapx.LF.CtxOffset"
        ~data:[ ("offset", json_of_int offset) ]

and json_of_lf_mctx cD = json_of_lf_ctx json_of_lf_ctyp_decl cD

and json_of_lf_sch_elem = function
  | Synapx.LF.SchElem (some, trec) ->
      json_of_variant ~name:"Synapx.LF.SchElem"
        ~data:
          [ ("some", json_of_lf_ctx json_of_lf_typ_decl some)
          ; ("block", json_of_lf_typ_rec trec)
          ]

and json_of_lf_schema = function
  | Synapx.LF.Schema schemas ->
      json_of_variant ~name:"Synapx.LF.Schema"
        ~data:[ ("schemas", json_of_list json_of_lf_sch_elem schemas) ]

and json_of_lf_psi_hat (cvar_opt, offset) =
  json_of_variant ~name:"Synapx.LF.psi_hat"
    ~data:
      [ ("context_variable", json_of_option json_of_lf_ctx_var cvar_opt)
      ; ("offset", json_of_int offset)
      ]

let rec json_of_comp_unbox_modifier = function
  | `Strengthened -> json_of_string "strengthened"

and json_of_comp_case_pragma = function
  | Synapx.Comp.PragmaCase -> json_of_bool true
  | Synapx.Comp.PragmaNotCase -> json_of_bool false

and json_of_comp_context_case = function
  | Synapx.Comp.EmptyContext location ->
      json_of_variant ~name:"Synapx.Comp.EmptyContext"
        ~data:[ ("location", json_of_location location) ]
  | Synapx.Comp.ExtendedBy (location, i) ->
      json_of_variant ~name:"Synapx.Comp.ExtendedBy"
        ~data:
          [ ("location", json_of_location location); ("i", json_of_int i) ]

and json_of_comp_case_label = function
  | Synapx.Comp.NamedCase (location, name) ->
      json_of_variant ~name:"Synapx.Comp.NamedCase"
        ~data:
          [ ("location", json_of_location location)
          ; ("name", json_of_name name)
          ]
  | Syncom.Comp.BVarCase location ->
      json_of_variant ~name:"Synapx.Comp.BVarCase"
        ~data:[ ("location", json_of_location location) ]
  | Syncom.Comp.ContextCase case ->
      json_of_variant ~name:"Synapx.Comp.ContextCase"
        ~data:[ ("case", json_of_comp_context_case case) ]
  | Syncom.Comp.PVarCase (location, schema_element, projection_opt) ->
      json_of_variant ~name:"Synapx.Comp.PVarCase"
        ~data:
          [ ("location", json_of_location location)
          ; ("schema_element", json_of_int schema_element)
          ; ("projection", json_of_option json_of_int projection_opt)
          ]

and json_of_comp_generic_order json_of_argument = function
  | Synapx.Comp.Arg argument ->
      json_of_variant ~name:"Synapx.Comp.Arg"
        ~data:[ ("argument", json_of_argument argument) ]
  | Synapx.Comp.Lex orders ->
      json_of_variant ~name:"Synapx.Comp.Lex"
        ~data:
          [ ( "orders"
            , json_of_list
                (json_of_comp_generic_order json_of_argument)
                orders )
          ]
  | Synapx.Comp.Simul orders ->
      json_of_variant ~name:"Synapx.Comp.Simul"
        ~data:
          [ ( "orders"
            , json_of_list
                (json_of_comp_generic_order json_of_argument)
                orders )
          ]

and json_of_comp_generic_suffices_typ json_of_typ = function
  | `exact tA ->
      json_of_variant ~name:"Synapx.Comp.exact"
        ~data:[ ("typ", json_of_typ tA) ]
  | `infer location ->
      json_of_variant ~name:"Synapx.Comp.infer"
        ~data:[ ("location", json_of_location location) ]

let rec json_of_comp_kind = function
  | Synapx.Comp.Ctype location ->
      json_of_variant ~name:"Synapx.Comp.Ctype"
        ~data:[ ("location", json_of_location location) ]
  | Synapx.Comp.PiKind (location, declaration, body) ->
      json_of_variant ~name:"Synapx.Comp.PiKind"
        ~data:
          [ ("location", json_of_location location)
          ; ("declaration", json_of_lf_ctyp_decl declaration)
          ; ("body", json_of_comp_kind body)
          ]

and json_of_comp_meta_typ (location, cA) =
  json_of_variant ~name:"Synapx.Comp.meta_typ"
    ~data:
      [ ("location", json_of_location location)
      ; ("typ", json_of_lf_ctyp cA)
      ]

and json_of_comp_mfront = function
  | Synapx.Comp.ClObj (cPsi, s) ->
      json_of_variant ~name:"Synapx.Comp.ClObj"
        ~data:
          [ ("context", json_of_lf_dctx cPsi)
          ; ("substitution", json_of_lf_sub s)
          ]
  | Synapx.Comp.CObj cPsi ->
      json_of_variant ~name:"Synapx.Comp.CObj"
        ~data:[ ("context", json_of_lf_dctx cPsi) ]

and json_of_comp_meta_obj (location, mft) =
  json_of_variant ~name:"Synapx.Comp.meta_obj"
    ~data:
      [ ("location", json_of_location location)
      ; ("obj", json_of_comp_mfront mft)
      ]

and json_of_comp_meta_spine meta_spine =
  json_of_list json_of_comp_meta_obj (meta_spine_to_list meta_spine)

and json_of_comp_typ = function
  | Synapx.Comp.TypBase (location, cid, mspine) ->
      json_of_variant ~name:"Synapx.Comp.TypBase"
        ~data:
          [ ("location", json_of_location location)
          ; ("cid_comp_typ", json_of_int cid)
          ; ("spine", json_of_comp_meta_spine mspine)
          ]
  | Synapx.Comp.TypCobase (location, cid, mspine) ->
      json_of_variant ~name:"Synapx.Comp.TypCobase"
        ~data:
          [ ("location", json_of_location location)
          ; ("cid_comp_cotyp", json_of_int cid)
          ; ("spine", json_of_comp_meta_spine mspine)
          ]
  | Synapx.Comp.TypDef (location, cid, mspine) ->
      json_of_variant ~name:"Synapx.Comp.TypDef"
        ~data:
          [ ("location", json_of_location location)
          ; ("cid_comp_typdef", json_of_int cid)
          ; ("spine", json_of_comp_meta_spine mspine)
          ]
  | Synapx.Comp.TypBox (location, cA) ->
      json_of_variant ~name:"Synapx.Comp.TypBox"
        ~data:
          [ ("location", json_of_location location)
          ; ("boxed_typ", json_of_comp_meta_typ cA)
          ]
  | Synapx.Comp.TypArr (location, tau1, tau2) ->
      json_of_variant ~name:"Synapx.Comp.TypArr"
        ~data:
          [ ("location", json_of_location location)
          ; ("domain", json_of_comp_typ tau1)
          ; ("range", json_of_comp_typ tau2)
          ]
  | Synapx.Comp.TypCross (location, taus) ->
      json_of_variant ~name:"Synapx.Comp.TypCross"
        ~data:
          [ ("location", json_of_location location)
          ; ("typs", json_of_list2 json_of_comp_typ taus)
          ]
  | Synapx.Comp.TypPiBox (location, decl, tau) ->
      json_of_variant ~name:"Synapx.Comp.TypPiBox"
        ~data:
          [ ("location", json_of_location location)
          ; ("declaration", json_of_lf_ctyp_decl decl)
          ; ("body", json_of_comp_typ tau)
          ]
  | Synapx.Comp.TypInd tau ->
      json_of_variant ~name:"Synapx.Comp.TypInd"
        ~data:[ ("typ", json_of_comp_typ tau) ]

and json_of_comp_exp = function
  | Synapx.Comp.Fn (location, var, body) ->
      json_of_variant ~name:"Synapx.Comp.Fn"
        ~data:
          [ ("location", json_of_location location)
          ; ("parameter", json_of_name var)
          ; ("body", json_of_comp_exp body)
          ]
  | Synapx.Comp.Fun (location, branches) ->
      json_of_variant ~name:"Synapx.Comp.Fun"
        ~data:
          [ ("location", json_of_location location)
          ; ("branches", json_of_comp_fun_branches branches)
          ]
  | Synapx.Comp.MLam (location, var, body) ->
      json_of_variant ~name:"Synapx.Comp.MLam"
        ~data:
          [ ("location", json_of_location location)
          ; ("parameter", json_of_name var)
          ; ("body", json_of_comp_exp body)
          ]
  | Synapx.Comp.Tuple (location, es) ->
      json_of_variant ~name:"Synapx.Comp.Tuple"
        ~data:
          [ ("location", json_of_location location)
          ; ("elements", json_of_list2 json_of_comp_exp es)
          ]
  | Synapx.Comp.LetTuple (location, scrutinee, (xs, body)) ->
      json_of_variant ~name:"Synapx.Comp.LetTuple"
        ~data:
          [ ("location", json_of_location location)
          ; ("scrutinee", json_of_comp_exp scrutinee)
          ; ("variables", json_of_list2 json_of_name xs)
          ; ("body", json_of_comp_exp body)
          ]
  | Synapx.Comp.Let (location, scrutinee, (x, body)) ->
      json_of_variant ~name:"Synapx.Comp.Let"
        ~data:
          [ ("location", json_of_location location)
          ; ("scrutinee", json_of_comp_exp scrutinee)
          ; ("variable", json_of_name x)
          ; ("body", json_of_comp_exp body)
          ]
  | Synapx.Comp.Box (location, cM) ->
      json_of_variant ~name:"Synapx.Comp.Box"
        ~data:
          [ ("location", json_of_location location)
          ; ("boxed_meta_object", json_of_comp_meta_obj cM)
          ]
  | Synapx.Comp.Case (location, check_coverage, scrutinee, branches) ->
      json_of_variant ~name:"Synapx.Comp.Case"
        ~data:
          [ ("location", json_of_location location)
          ; ("check_coverage", json_of_comp_case_pragma check_coverage)
          ; ("scrutinee", json_of_comp_exp scrutinee)
          ; ("branches", json_of_list json_of_comp_branch branches)
          ]
  | Synapx.Comp.Impossible (location, scrutinee) ->
      json_of_variant ~name:"Synapx.Comp.Impossible"
        ~data:
          [ ("location", json_of_location location)
          ; ("scrutinee", json_of_comp_exp scrutinee)
          ]
  | Synapx.Comp.Hole (location, label_opt) ->
      json_of_variant ~name:"Synapx.Comp.Hole"
        ~data:
          [ ("location", json_of_location location)
          ; ("label", json_of_option json_of_string label_opt)
          ]
  | Synapx.Comp.BoxHole location ->
      json_of_variant ~name:"Synapx.Comp.BoxHole"
        ~data:[ ("location", json_of_location location) ]
  | Synapx.Comp.Var (location, offset) ->
      json_of_variant ~name:"Synapx.Comp.Var"
        ~data:
          [ ("location", json_of_location location)
          ; ("offset", json_of_int offset)
          ]
  | Synapx.Comp.DataConst (location, cid) ->
      json_of_variant ~name:"Synapx.Comp.DataConst"
        ~data:
          [ ("location", json_of_location location)
          ; ("cid_comp_const", json_of_int cid)
          ]
  | Synapx.Comp.Obs (location, destructee, cid) ->
      json_of_variant ~name:"Synapx.Comp.Obs"
        ~data:
          [ ("location", json_of_location location)
          ; ("destructee", json_of_comp_exp destructee)
          ; ("cid_comp_dest", json_of_int cid)
          ]
  | Synapx.Comp.Const (location, cid) ->
      json_of_variant ~name:"Synapx.Comp.Const"
        ~data:
          [ ("location", json_of_location location)
          ; ("cid_prog", json_of_int cid)
          ]
  | Synapx.Comp.Apply (location, applicand, argument) ->
      json_of_variant ~name:"Synapx.Comp.Apply"
        ~data:
          [ ("location", json_of_location location)
          ; ("applicand", json_of_comp_exp applicand)
          ; ("argument", json_of_comp_exp argument)
          ]
  | Synapx.Comp.Ann (location, e, tau) ->
      json_of_variant ~name:"Synapx.Comp.Ann"
        ~data:
          [ ("location", json_of_location location)
          ; ("expression", json_of_comp_exp e)
          ; ("typ", json_of_comp_typ tau)
          ]

and json_of_comp_pattern = function
  | Synapx.Comp.PatMetaObj (location, cM) ->
      json_of_variant ~name:"Synapx.Comp.PatMetaObj"
        ~data:
          [ ("location", json_of_location location)
          ; ("meta_object", json_of_comp_meta_obj cM)
          ]
  | Synapx.Comp.PatConst (location, cid, pat_spine) ->
      json_of_variant ~name:"Synapx.Comp.PatConst"
        ~data:
          [ ("location", json_of_location location)
          ; ("cid_comp_const", json_of_int cid)
          ; ("spine", json_of_comp_pattern_spine pat_spine)
          ]
  | Synapx.Comp.PatFVar (location, name) ->
      json_of_variant ~name:"Synapx.Comp.PatFVar"
        ~data:
          [ ("location", json_of_location location)
          ; ("name", json_of_name name)
          ]
  | Synapx.Comp.PatVar (location, name, offset) ->
      json_of_variant ~name:"Synapx.Comp.PatVar"
        ~data:
          [ ("location", json_of_location location)
          ; ("name", json_of_name name)
          ; ("offset", json_of_int offset)
          ]
  | Synapx.Comp.PatTuple (location, pats) ->
      json_of_variant ~name:"Synapx.Comp.PatTuple"
        ~data:
          [ ("location", json_of_location location)
          ; ("patterns", json_of_list2 json_of_comp_pattern pats)
          ]
  | Synapx.Comp.PatAnn (location, pat, tau) ->
      json_of_variant ~name:"Synapx.Comp.PatAnn"
        ~data:
          [ ("location", json_of_location location)
          ; ("pattern", json_of_comp_pattern pat)
          ; ("typ", json_of_comp_typ tau)
          ]

and json_of_comp_pattern_spine = function
  | Synapx.Comp.PatNil location ->
      json_of_variant ~name:"Synapx.Comp.PatNil"
        ~data:[ ("location", json_of_location location) ]
  | Synapx.Comp.PatApp (location, pat, pat_spine) ->
      json_of_variant ~name:"Synapx.Comp.PatApp"
        ~data:
          [ ("location", json_of_location location)
          ; ("pattern", json_of_comp_pattern pat)
          ; ("spine", json_of_comp_pattern_spine pat_spine)
          ]
  | Synapx.Comp.PatObs (location, cid, pat_spine) ->
      json_of_variant ~name:"Synapx.Comp.PatObs"
        ~data:
          [ ("location", json_of_location location)
          ; ("cid_comp_dest", json_of_int cid)
          ; ("spine", json_of_comp_pattern_spine pat_spine)
          ]

and json_of_comp_branch = function
  | Synapx.Comp.Branch (location, cD, pat, body) ->
      json_of_variant ~name:"Synapx.Comp.Branch"
        ~data:
          [ ("location", json_of_location location)
          ; ("meta_context", json_of_lf_mctx cD)
          ; ("pattern", json_of_comp_pattern pat)
          ; ("body", json_of_comp_exp body)
          ]

and json_of_comp_fun_branches = function
  | Synapx.Comp.NilFBranch location ->
      json_of_variant ~name:"Synapx.Comp.Branch"
        ~data:[ ("location", json_of_location location) ]
  | Synapx.Comp.ConsFBranch (location, (pat_spine, body), fun_branches) ->
      json_of_variant ~name:"Synapx.Comp.Branch"
        ~data:
          [ ("location", json_of_location location)
          ; ("pattern_spine", json_of_comp_pattern_spine pat_spine)
          ; ("body", json_of_comp_exp body)
          ; ("branches", json_of_comp_fun_branches fun_branches)
          ]

and json_of_comp_ctyp_decl = function
  | Synapx.Comp.CTypDecl (var, tau) ->
      json_of_variant ~name:"Synapx.Comp.CTypDecl"
        ~data:
          [ ("variable", json_of_name var); ("typ", json_of_comp_typ tau) ]

and json_of_comp_gctx cG = json_of_lf_ctx json_of_comp_ctyp_decl cG

and json_of_comp_hypotheses { Synapx.Comp.cD; cG } =
  json_of_variant ~name:"Synapx.Comp.hypotheses"
    ~data:
      [ ("meta_context", json_of_lf_mctx cD)
      ; ("comp_context", json_of_comp_gctx cG)
      ]

and json_of_comp_proof = function
  | Synapx.Comp.Incomplete (location, label_opt) ->
      json_of_variant ~name:"Synapx.Comp.Incomplete"
        ~data:
          [ ("location", json_of_location location)
          ; ("label", json_of_option json_of_string label_opt)
          ]
  | Synapx.Comp.Command (location, command, proof) ->
      json_of_variant ~name:"Synapx.Comp.Command"
        ~data:
          [ ("location", json_of_location location)
          ; ("command", json_of_comp_command command)
          ; ("proof", json_of_comp_proof proof)
          ]
  | Synapx.Comp.Directive (location, directive) ->
      json_of_variant ~name:"Synapx.Comp.Directive"
        ~data:
          [ ("location", json_of_location location)
          ; ("directive", json_of_comp_directive directive)
          ]

and json_of_comp_command = function
  | Synapx.Comp.By (location, expression, assignee) ->
      json_of_variant ~name:"Synapx.Comp.By"
        ~data:
          [ ("location", json_of_location location)
          ; ("expression", json_of_comp_exp expression)
          ; ("assignee", json_of_name assignee)
          ]
  | Synapx.Comp.Unbox (location, expression, assignee, modifier_opt) ->
      json_of_variant ~name:"Synapx.Comp.Unbox"
        ~data:
          [ ("location", json_of_location location)
          ; ("expression", json_of_comp_exp expression)
          ; ("assignee", json_of_name assignee)
          ; ( "modifier"
            , json_of_option
                (function
                  | `Strengthened -> json_of_string "strengthened")
                modifier_opt )
          ]

and json_of_comp_directive = function
  | Synapx.Comp.Intros (location, hypothetical) ->
      json_of_variant ~name:"Synapx.Comp.Intros"
        ~data:
          [ ("location", json_of_location location)
          ; ("hypothetical", json_of_comp_hypothetical hypothetical)
          ]
  | Synapx.Comp.Solve (location, solution) ->
      json_of_variant ~name:"Synapx.Comp.Solve"
        ~data:
          [ ("location", json_of_location location)
          ; ("solution", json_of_comp_exp solution)
          ]
  | Synapx.Comp.Split (location, scrutinee, branches) ->
      json_of_variant ~name:"Synapx.Comp.Split"
        ~data:
          [ ("location", json_of_location location)
          ; ("scrutinee", json_of_comp_exp scrutinee)
          ; ("branches", json_of_list json_of_comp_split_branch branches)
          ]
  | Synapx.Comp.Suffices (location, scrutinee, args) ->
      json_of_variant ~name:"Synapx.Comp.Suffices"
        ~data:
          [ ("location", json_of_location location)
          ; ("scrutinee", json_of_comp_exp scrutinee)
          ; ("arguments", json_of_list json_of_comp_suffices_arg args)
          ]

and json_of_comp_suffices_arg (location, tau, proof) =
  json_of_variant ~name:"Synapx.Comp.suffices_arg"
    ~data:
      [ ("location", json_of_location location)
      ; ("typ", json_of_comp_typ tau)
      ; ("proof", json_of_comp_proof proof)
      ]

and json_of_comp_split_branch
    { Synapx.Comp.case_label; branch_body; split_branch_loc } =
  json_of_variant ~name:"Synapx.Comp.split_branch"
    ~data:
      [ ("location", json_of_location split_branch_loc)
      ; ("case_label", json_of_comp_case_label case_label)
      ; ("body", json_of_comp_hypothetical branch_body)
      ]

and json_of_comp_hypothetical
    { Synapx.Comp.hypotheses; proof; hypothetical_loc } =
  json_of_variant ~name:"Synapx.Comp.hypothetical"
    ~data:
      [ ("location", json_of_location hypothetical_loc)
      ; ("hypotheses", json_of_comp_hypotheses hypotheses)
      ; ("proof", json_of_comp_proof proof)
      ]

and json_of_comp_thm = function
  | Synapx.Comp.Program e ->
      json_of_variant ~name:"Synapx.Comp.Program"
        ~data:[ ("program", json_of_comp_exp e) ]
  | Synapx.Comp.Proof p ->
      json_of_variant ~name:"Synapx.Comp.Proof"
        ~data:[ ("proof", json_of_comp_proof p) ]
