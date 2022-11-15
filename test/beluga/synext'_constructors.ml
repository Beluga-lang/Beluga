open Support
open Beluga

let location = Location.ghost

let id n = Identifier.make ~location n

let qid ?m n =
  QualifiedIdentifier.make ~location
    ?modules:(Option.map (List.map id) m)
    (id n)

(** Abbreviated constructors for LF kinds, types and terms, with mocked
    locations and operators. These are strictly used for testing. *)
module LF = struct
  open Synext'.LF

  let id = id

  let qid = qid

  (* {1 LF kind constructors} *)

  let typ = Kind.Typ { location }

  let ( ==> ) domain range = Kind.Arrow { location; domain; range }

  let k_pi ?x ~t body =
    Kind.Pi
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  (** {1 LF type constructors} *)

  let t_c ?(quoted = false) ?m identifier =
    Typ.Constant
      { location
      ; identifier = qid ?m identifier
      ; operator = Obj.magic ()
      ; quoted
      }

  let t_app applicand arguments =
    Typ.Application
      { location; applicand; arguments = List1.unsafe_of_list arguments }

  let ( => ) domain range =
    Typ.Arrow { location; domain; range; orientation = `Forward }

  let ( <= ) range domain =
    Typ.Arrow { location; domain; range; orientation = `Backward }

  let t_pi ?x ~t body =
    Typ.Pi
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  (* {1 LF term constructors} *)

  let v identifier = Term.Variable { location; identifier = id identifier }

  let c ?(quoted = false) ?m identifier =
    Term.Constant
      { location
      ; identifier = qid ?m identifier
      ; operator = Obj.magic ()
      ; quoted
      }

  let app applicand arguments =
    Term.Application
      { location; applicand; arguments = List1.unsafe_of_list arguments }

  let lam ?x ?t body =
    Term.Abstraction
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  let hole = Term.Wildcard { location }

  let ( &: ) term typ = Term.TypeAnnotated { location; term; typ }
end

(** Abbreviated constructors for contextual LF types, terms, substitutions,
    contexts and patterns, with mocked locations and operators. These are
    strictly used for testing. *)
module CLF = struct
  open Synext'.CLF

  let id = id

  let qid = qid

  (* {1 Contextual LF type constructors} *)

  let t_c ?(quoted = false) ?m identifier =
    Typ.Constant
      { location
      ; identifier = qid ?m identifier
      ; operator = Obj.magic ()
      ; quoted
      }

  let t_app applicand arguments =
    Typ.Application
      { location; applicand; arguments = List1.unsafe_of_list arguments }

  let ( => ) domain range =
    Typ.Arrow { location; domain; range; orientation = `Forward }

  let ( <= ) range domain =
    Typ.Arrow { location; domain; range; orientation = `Backward }

  let t_pi ?x ~t body =
    Typ.Pi
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  let t_block_s t = Typ.Block { location; elements = `Unnamed t }

  let t_block ts =
    Typ.Block
      { location; elements = `Record (List1.map (Pair.map_left id) ts) }

  (* {1 Contextual LF term constructors} *)

  let v identifier = Term.Variable { location; identifier = id identifier }

  let c ?(quoted = false) ?m identifier =
    Term.Constant
      { location
      ; identifier = qid ?m identifier
      ; operator = Obj.magic ()
      ; quoted
      }

  let app applicand arguments =
    Term.Application
      { location; applicand; arguments = List1.unsafe_of_list arguments }

  let lam ?x ?t body =
    Term.Abstraction
      { location
      ; parameter_identifier = Option.map id x
      ; parameter_type = t
      ; body
      }

  let hole = Term.Hole { location; variant = `Underscore }

  let u_hole = Term.Hole { location; variant = `Unlabelled }

  let l_hole l = Term.Hole { location; variant = `Labelled (id l) }

  let ( &: ) term typ = Term.TypeAnnotated { location; term; typ }

  let rec substitution (head, terms) =
    let head' =
      match head with
      | `None -> Substitution.Head.None { location }
      | `Id -> Substitution.Head.Identity { location }
      | `SVar i ->
        Substitution.Head.Substitution_variable
          { location; identifier = id i; closure = Option.none }
      | `SClo (i, closure) ->
        let closure' = substitution closure in
        Substitution.Head.Substitution_variable
          { location; identifier = id i; closure = Option.some closure' }
    in
    { Substitution.head = head'; terms; location }

  let sub term sub =
    Term.Substitution { location; term; substitution = substitution sub }

  let tuple terms = Term.Tuple { location; terms }

  let proj_i term i =
    Term.Projection { location; term; projection = `By_position i }

  let proj_x term x =
    Term.Projection { location; term; projection = `By_identifier (id x) }

  let ctx (head, bindings) =
    let head' =
      match head with
      | `None -> Context.Head.None { location }
      | `Hole -> Context.Head.Hole { location }
      | `CVar identifier ->
        Context.Head.Context_variable
          { location; identifier = id identifier }
    and bindings' =
      List.map (fun (i, typ_opt) -> (id i, typ_opt)) bindings
    in
    { Context.head = head'; bindings = bindings'; location }
end

module Meta = struct
  open Synext'.Meta

  (** {1 Meta-Type Constructors} *)

  let t_schema schema = Typ.Context_schema { location; schema }

  let t_type context typ =
    Typ.Contextual_typ { location; context = CLF.ctx context; typ }

  let t_ptype context typ =
    Typ.Parameter_typ { location; context = CLF.ctx context; typ }

  let t_subst domain range =
    Typ.Plain_substitution_typ
      { location; domain = CLF.ctx domain; range = CLF.ctx range }

  let t_rsubst domain range =
    Typ.Renaming_substitution_typ
      { location; domain = CLF.ctx domain; range = CLF.ctx range }

  (** {1 Meta-Object Constructors} *)

  let o_ctx context = Object.Context { location; context = CLF.ctx context }

  let o_term context term =
    Object.Contextual_term { location; context = CLF.ctx context; term }

  let o_subst domain range =
    Object.Plain_substitution
      { location; domain = CLF.ctx domain; range = CLF.substitution range }

  let o_rsubst domain range =
    Object.Renaming_substitution
      { location; domain = CLF.ctx domain; range = CLF.substitution range }

  (** {1 Meta-Pattern Constructors} *)

  let p_ctx context = Pattern.Context { location; context }

  let p_term context term =
    Pattern.Contextual_term { location; context; term }

  let p_subst domain range =
    Pattern.Plain_substitution { location; domain; range }

  let p_rsubst domain range =
    Pattern.Renaming_substitution { location; domain; range }

  (** {1 Meta-Context Constructors} *)

  let mctx bindings = { Context.location; bindings }

  (** {1 Context Schema Constructors} *)

  let s_c ?m identifier =
    Schema.Constant { location; identifier = qid ?m identifier }

  let s_alt schemas = Schema.Alternation { location; schemas }

  let s_elem ?some block =
    let some' =
      Option.map
        (fun some -> List1.map (fun (i, typ) -> (id i, typ)) some)
        some
    and block' =
      match block with
      | `Unnamed t -> `Unnamed t
      | `Record bindings ->
        let bindings' = List1.map (fun (i, typ) -> (id i, typ)) bindings in
        `Record bindings'
    in
    Schema.Element { location; some = some'; block = block' }
end
