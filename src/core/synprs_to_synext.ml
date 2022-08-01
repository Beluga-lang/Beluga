open Support

module LF = struct
  let rec elaborate_kind kind =
    match kind with
    | Synprs.LF.Typ { location } -> Synext.LF.Typ location
    | Synprs.LF.ArrKind { location; domain; range } ->
      let domain' = elaborate_typ domain
      and range' = elaborate_kind range in
      Synext.LF.ArrKind (location, domain', range')
    | Synprs.LF.PiKind { location; parameter_name; parameter_type; range } ->
      let parameter_type' = elaborate_typ parameter_type
      and range' = elaborate_kind range in
      Synext.LF.PiKind
        ( location
        , Synext.LF.TypDecl (parameter_name, parameter_type')
        , range' )

  and elaborate_typ typ =
    match typ with
    | Synprs.LF.Atom { location; head; spine } ->
      let spine' =
        List.fold_right
          (fun (location, element) acc ->
            let element' = elaborate_term element in
            Synext.LF.App (location, element', acc))
          spine Synext.LF.Nil
      in
      Synext.LF.Atom (location, head, spine')
    | Synprs.LF.ArrTyp { location; domain; range } ->
      let domain' = elaborate_typ domain
      and range' = elaborate_typ range in
      Synext.LF.ArrTyp (location, domain', range')
    | Synprs.LF.PiTyp { location; parameter_name; parameter_type; range } ->
      let parameter_type' = elaborate_typ parameter_type
      and range' = elaborate_typ range in
      Synext.LF.PiTyp
        ( location
        , Synext.LF.TypDecl (parameter_name, parameter_type')
        , range' )
    | Synprs.LF.Sigma { location; block } ->
      let block = elaborate_typ_rec block in
      Synext.LF.Sigma (location, block)
    | Synprs.LF.AtomTerm { location; term } ->
      let term' = elaborate_term term in
      Synext.LF.AtomTerm (location, term')

  and elaborate_term term =
    match term with
    | Synprs.LF.Lam { location; parameter_name; body } ->
      let body' = elaborate_term body in
      Synext.LF.Lam (location, parameter_name, body')
    | Synprs.LF.Root { location; head; spine } ->
      let head' = elaborate_head head
      and spine' =
        List.fold_right
          (fun (location, term) acc ->
            let term' = elaborate_term term in
            Synext.LF.App (location, term', acc))
          spine Synext.LF.Nil
      in
      Synext.LF.Root (location, head', spine')
    | Synprs.LF.Tuple { location; tuple } ->
      let tuple' =
        List1.fold_right
          (fun last ->
            let last' = elaborate_term last in
            Synext.LF.Last last')
          (fun term acc ->
            let term' = elaborate_term term in
            Synext.LF.Cons (term', acc))
          tuple
      in
      Synext.LF.Tuple (location, tuple')
    | Synprs.LF.LFHole { location; label } ->
      Synext.LF.LFHole (location, label)
    | Synprs.LF.Ann { location; term; typ } ->
      let term' = elaborate_term term
      and typ' = elaborate_typ typ in
      Synext.LF.Ann (location, term', typ')
    | Synprs.LF.TList { location; terms } ->
      let terms' = List.map elaborate_term terms in
      Synext.LF.TList (location, terms')
    | Synprs.LF.NTyp { location; typ } ->
      let typ' = elaborate_typ typ in
      Synext.LF.NTyp (location, typ')

  and elaborate_typ_rec sigma =
    match sigma with
    | Synprs.LF.SigmaLast (name_opt, typ) ->
      let typ' = elaborate_typ typ in
      Synext.LF.SigmaLast (name_opt, typ')
    | Synprs.LF.SigmaElem (name, typ, rest) ->
      let typ' = elaborate_typ typ
      and rest' = elaborate_typ_rec rest in
      Synext.LF.SigmaElem (name, typ', rest')

  and elaborate_head head =
    match head with
    | Synprs.LF.Name (location, name, sub_opt) ->
      let sub_opt' = Option.map elaborate_sub sub_opt in
      Synext.LF.Name (location, name, sub_opt')
    | Synprs.LF.Hole location -> Synext.LF.Hole location
    | Synprs.LF.PVar (location, name, sub_opt) ->
      let sub_opt' = Option.map elaborate_sub sub_opt in
      Synext.LF.PVar (location, name, sub_opt')
    | Synprs.LF.Proj (location, head, Synprs.LF.ByPos k) ->
      let head' = elaborate_head head in
      Synext.LF.Proj (location, head', Synext.LF.ByPos k)
    | Synprs.LF.Proj (location, head, Synprs.LF.ByName name) ->
      let head' = elaborate_head head in
      Synext.LF.Proj (location, head', Synext.LF.ByName name)

  and elaborate_sub sub =
    let start, terms = sub in
    let start' = elaborate_sub_start start
    and terms' = List.map elaborate_term terms in
    (start', terms')

  and elaborate_sub_start start =
    match start with
    | Synprs.LF.EmptySub location -> Synext.LF.EmptySub location
    | Synprs.LF.Id location -> Synext.LF.Id location
    | Synprs.LF.SVar (location, name, sub_opt) ->
      let sub_opt' = Option.map elaborate_sub sub_opt in
      Synext.LF.SVar (location, name, sub_opt')
end

module Comp = struct
  let elaborate_kind kind = Error.not_implemented' "[Comp.elaborate_kind]"

  let elaborate_typ typ = Error.not_implemented' "[Comp.elaborate_typ]"

  let elaborate_exp exp = Error.not_implemented' "[Comp.elaborate_exp]"

  let elaborate_pattern pattern =
    Error.not_implemented' "[Comp.elaborate_pattern]"
end

module Harpoon = struct
  let elaborate_command command =
    Error.not_implemented' "[Harpoon.elaborate_command]"
end

module Sgn = struct
  let elaborate_sgn sgn = Error.not_implemented' "[Sgn.elaborate_sgn]"
end
