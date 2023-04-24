open Syncom
open Synext_definition

let explicit_arguments_lf_kind =
  let rec explicit_arguments_lf_kind_tl kind acc =
    match kind with
    | LF.Kind.Arrow { range; _ } ->
        explicit_arguments_lf_kind_tl range (1 + acc)
    | LF.Kind.Pi { body; plicity = Plicity.Explicit; _ } ->
        explicit_arguments_lf_kind_tl body (1 + acc)
    | LF.Kind.Pi { body; plicity = Plicity.Implicit; _ } ->
        explicit_arguments_lf_kind_tl body acc
    | _ -> acc
  in
  fun kind -> explicit_arguments_lf_kind_tl kind 0

let explicit_arguments_lf_typ =
  let rec explicit_arguments_lf_typ_tl typ acc =
    match typ with
    | LF.Typ.Arrow { range; _ } ->
        explicit_arguments_lf_typ_tl range (1 + acc)
    | LF.Typ.Pi { body; plicity = Plicity.Explicit; _ } ->
        explicit_arguments_lf_typ_tl body (1 + acc)
    | LF.Typ.Pi { body; plicity = Plicity.Implicit; _ } ->
        explicit_arguments_lf_typ_tl body acc
    | _ -> acc
  in
  fun typ -> explicit_arguments_lf_typ_tl typ 0

let explicit_arguments_comp_kind =
  let rec explicit_arguments_comp_kind_tl kind acc =
    match kind with
    | Comp.Kind.Arrow { range; _ } ->
        explicit_arguments_comp_kind_tl range (1 + acc)
    | Comp.Kind.Pi { body; plicity = Plicity.Explicit; _ } ->
        explicit_arguments_comp_kind_tl body (1 + acc)
    | Comp.Kind.Pi { body; plicity = Plicity.Implicit; _ } ->
        explicit_arguments_comp_kind_tl body acc
    | _ -> acc
  in
  fun kind -> explicit_arguments_comp_kind_tl kind 0

let explicit_arguments_comp_typ =
  let rec explicit_arguments_comp_typ_tl typ acc =
    match typ with
    | Comp.Typ.Arrow { range; _ } ->
        explicit_arguments_comp_typ_tl range (1 + acc)
    | Comp.Typ.Pi { body; plicity = Plicity.Explicit; _ } ->
        explicit_arguments_comp_typ_tl body (1 + acc)
    | Comp.Typ.Pi { body; plicity = Plicity.Implicit; _ } ->
        explicit_arguments_comp_typ_tl body acc
    | _ -> acc
  in
  fun typ -> explicit_arguments_comp_typ_tl typ 0
