open Support
open Beluga

module LF = struct
  module rec Kind : sig
    include module type of Synext'.LF.Kind

    (** [equal x y] is [true] if and only if kinds [x] and [y] are
        structurally equal, without regards for locations. *)
    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.LF.Kind

    let equal x y =
      match (x, y) with
      | Typ _, Typ _ -> true
      | ( Arrow { domain = d1; range = r1; _ }
        , Arrow { domain = d2; range = r2; _ } ) ->
        Typ.equal d1 d2 && Kind.equal r1 r2
      | ( Pi { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Pi { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Typ.equal t1 t2 && Kind.equal b1 b2
      | _ -> false
  end

  and Typ : sig
    include module type of Synext'.LF.Typ

    (** [equal x y] is [true] if and only if types [x] and [y] are
        structurally equal, without regards for locations. *)
    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.LF.Typ

    let equal x y =
      match (x, y) with
      | ( Constant { identifier = i1; quoted = q1; _ }
        , Constant { identifier = i2; quoted = q2; _ } ) ->
        QualifiedIdentifier.equal i1 i2 && Bool.equal q1 q2
      | ( Application { applicand = f1; arguments = as1; _ }
        , Application { applicand = f2; arguments = as2; _ } ) ->
        Typ.equal f1 f2 && List.equal Term.equal as1 as2
      | ( Arrow { domain = d1; range = r1; orientation = o1; _ }
        , Arrow { domain = d2; range = r2; orientation = o2; _ } ) ->
        o1 = o2 && Typ.equal d1 d2 && Typ.equal r1 r2
      | ( Pi { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Pi { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Typ.equal t1 t2 && Typ.equal b1 b2
      | _ -> false
  end

  and Term : sig
    include module type of Synext'.LF.Term

    (** [equal x y] is [true] if and only if terms [x] and [y] are
        structurally equal, without regards for locations. *)
    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.LF.Term

    let equal x y =
      match (x, y) with
      | Variable { identifier = i1; _ }, Variable { identifier = i2; _ } ->
        Identifier.equal i1 i2
      | ( Constant { identifier = i1; quoted = q1; _ }
        , Constant { identifier = i2; quoted = q2; _ } ) ->
        QualifiedIdentifier.equal i1 i2 && Bool.equal q1 q2
      | ( Application { applicand = f1; arguments = as1; _ }
        , Application { applicand = f2; arguments = as2; _ } ) ->
        Term.equal f1 f2 && List.equal Term.equal as1 as2
      | ( Abstraction
            { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Abstraction
            { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Option.equal Typ.equal t1 t2
        && Term.equal b1 b2
      | Wildcard _, Wildcard _ -> true
      | ( TypeAnnotated { term = u1; typ = t1; _ }
        , TypeAnnotated { term = u2; typ = t2; _ } ) ->
        Term.equal u1 u2 && Typ.equal t1 t2
      | _ -> false
  end
end

module CLF = struct
  module rec Typ : sig
    include module type of Synext'.CLF.Typ

    (** [equal x y] is [true] if and only if types [x] and [y] are
        structurally equal, without regards for locations. *)
    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.CLF.Typ

    let equal x y =
      match (x, y) with
      | ( Constant { identifier = i1; quoted = q1; _ }
        , Constant { identifier = i2; quoted = q2; _ } ) ->
        QualifiedIdentifier.equal i1 i2 && Bool.equal q1 q2
      | ( Application { applicand = f1; arguments = as1; _ }
        , Application { applicand = f2; arguments = as2; _ } ) ->
        Typ.equal f1 f2 && List.equal Term.equal as1 as2
      | ( Arrow { domain = d1; range = r1; orientation = o1; _ }
        , Arrow { domain = d2; range = r2; orientation = o2; _ } ) ->
        o1 = o2 && Typ.equal d1 d2 && Typ.equal r1 r2
      | ( Pi { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Pi { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Typ.equal t1 t2 && Typ.equal b1 b2
      | Block { elements = e1; _ }, Block { elements = e2; _ } -> (
        match (e1, e2) with
        | `Unnamed t1, `Unnamed t2 -> Typ.equal t1 t2
        | `Record ts1, `Record ts2 ->
          List1.equal (Pair.equal Identifier.equal Typ.equal) ts1 ts2
        | _ -> false)
      | _ -> false
  end

  and Term : sig
    include module type of Synext'.CLF.Term

    (** [equal x y] is [true] if and only if terms [x] and [y] are
        structurally equal, without regards for locations. *)
    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.CLF.Term

    let equal x y =
      match (x, y) with
      | Variable { identifier = i1; _ }, Variable { identifier = i2; _ } ->
        Identifier.equal i1 i2
      | ( Constant { identifier = i1; quoted = q1; _ }
        , Constant { identifier = i2; quoted = q2; _ } ) ->
        QualifiedIdentifier.equal i1 i2 && Bool.equal q1 q2
      | ( Application { applicand = f1; arguments = as1; _ }
        , Application { applicand = f2; arguments = as2; _ } ) ->
        Term.equal f1 f2 && List.equal Term.equal as1 as2
      | ( Substitution { term = t1; substitution = s1; _ }
        , Substitution { term = t2; substitution = s2; _ } ) ->
        Term.equal t1 t2 && Substitution.equal s1 s2
      | ( Abstraction
            { parameter_identifier = i1; parameter_type = t1; body = b1; _ }
        , Abstraction
            { parameter_identifier = i2; parameter_type = t2; body = b2; _ }
        ) ->
        Option.equal Identifier.equal i1 i2
        && Option.equal Typ.equal t1 t2
        && Term.equal b1 b2
      | Hole { variant = v1; _ }, Hole { variant = v2; _ } -> (
        match (v1, v2) with
        | `Underscore, `Underscore | `Unlabelled, `Unlabelled -> true
        | `Labelled l1, `Labelled l2 -> Identifier.equal l1 l2
        | _ -> false)
      | Tuple { terms = ts1; _ }, Tuple { terms = ts2; _ } ->
        List1.equal Term.equal ts1 ts2
      | ( Projection { term = t1; projection = p1; _ }
        , Projection { term = t2; projection = p2; _ } ) -> (
        Term.equal t1 t2
        &&
        match (p1, p2) with
        | `By_identifier i1, `By_identifier i2 -> Identifier.equal i1 i2
        | `By_position i1, `By_position i2 -> Int.equal i1 i2
        | _ -> false)
      | ( TypeAnnotated { term = u1; typ = t1; _ }
        , TypeAnnotated { term = u2; typ = t2; _ } ) ->
        Term.equal u1 u2 && Typ.equal t1 t2
      | _ -> false
  end

  and Substitution : sig
    include module type of Synext'.CLF.Substitution

    (** [equal x y] is [true] if and only if terms [x] and [y] are
        structurally equal, without regards for locations. *)
    val equal : t -> t -> Bool.t
  end = struct
    include Synext'.CLF.Substitution

    let rec head_equal x y =
      match (x, y) with
      | Substitution.Head.None, Substitution.Head.None
      | Substitution.Head.Identity _, Substitution.Head.Identity _ -> true
      | ( Substitution.Head.Substitution_variable
            { identifier = i1; closure = o1; _ }
        , Substitution.Head.Substitution_variable
            { identifier = i2; closure = o2; _ } ) ->
        Identifier.equal i1 i2 && Option.equal equal o1 o2
      | _ -> false

    and equal x y =
      match (x, y) with
      | ( { Substitution.head = h1; terms = ts1; _ }
        , { Substitution.head = h2; terms = ts2; _ } ) ->
        head_equal h1 h2 && List.equal Term.equal ts1 ts2
  end
end
