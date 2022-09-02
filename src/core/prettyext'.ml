(** Pretty-printing for the external syntax. *)

[@@@warning "+A-4-44-66"]

open Support
open Synext'

(** {1 Handling Parentheses}

    Parentheses are re-introduced during pretty-printing using the precedence
    ordering specified in the parser. Operator associativities also need to
    be considered to avoid adding extraneous parentheses. *)

let parenthesize pp ppf = Format.fprintf ppf "@[<2>(%a)@]" pp

let[@inline] parenthesize_argument_of_lesser_precedence precedence
    ~parent_precedence pp ppf argument =
  if precedence argument < parent_precedence then
    parenthesize pp ppf argument
  else pp ppf argument

let[@inline] parenthesize_argument_of_lesser_than_or_equal_precedence
    precedence ~parent_precedence pp ppf argument =
  if precedence argument <= parent_precedence then
    parenthesize pp ppf argument
  else pp ppf argument

let parenthesize_left_argument_left_associative_operator =
  parenthesize_argument_of_lesser_precedence

let parenthesize_right_argument_left_associative_operator =
  parenthesize_argument_of_lesser_than_or_equal_precedence

let parenthesize_left_argument_right_associative_operator =
  parenthesize_argument_of_lesser_than_or_equal_precedence

let parenthesize_right_argument_right_associative_operator =
  parenthesize_argument_of_lesser_precedence

let parenthesize_argument_non_associative_operator =
  parenthesize_argument_of_lesser_than_or_equal_precedence

let parenthesize_argument_prefix_operator =
  parenthesize_argument_of_lesser_than_or_equal_precedence

let parenthesize_argument_postfix_operator =
  parenthesize_argument_of_lesser_precedence

(** {1 Printing LF Kinds, Types and Terms} *)
module LF = struct
  open LF

  let precedence_kind kind =
    match kind with
    | Kind.Pi _ -> 10
    | Kind.Arrow _ -> 30
    | Kind.Typ _ -> 50

  let precedence_typ typ =
    match typ with
    | Typ.Pi _ -> 10
    | Typ.ForwardArrow _ | Typ.BackwardArrow _ -> 30
    | Typ.Application { applicand = Typ.Constant { quoted = false; _ }; _ }
    (* User-defined operator application *) -> 39
    | Typ.Application _ -> 40
    | Typ.Constant _ -> 50

  let precedence_term term =
    match term with
    | Term.Abstraction _ -> 10
    | Term.TypeAnnotated _ -> 20
    | Term.Application { applicand = Term.Constant { quoted = false; _ }; _ }
    (* User-defined operator application *) -> 39
    | Term.Application _ -> 40
    | Term.Wildcard _ | Term.Variable _ | Term.Constant _ -> 60

  let rec pp_kind ppf kind =
    let parent_precedence = precedence_kind kind in
    match kind with
    | Kind.Typ _ -> Format.fprintf ppf "type"
    | Kind.Arrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]"
        (parenthesize_left_argument_right_associative_operator precedence_typ
           ~parent_precedence pp_typ)
        domain pp_kind range
    | Kind.Pi { parameter_identifier = Option.None; parameter_type; body; _ }
      ->
      Format.fprintf ppf "@[<2>{@ _@ :@ %a@ }@ %a@]" pp_typ parameter_type
        pp_kind body
    | Kind.Pi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_kind body

  and pp_typ ppf typ =
    let parent_precedence = precedence_typ typ in
    match typ with
    | Typ.Constant { identifier; quoted = true; operator; _ }
      when Operator.is_nullary operator ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
    | Typ.Constant { identifier; quoted = false; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_typ applicand
    | Typ.Application
        { applicand =
            Typ.Constant { identifier; operator; quoted = false; _ }
        ; arguments
        ; _
        }
    (* User-defined type constant application *) -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
             (parenthesize_argument_prefix_operator precedence_term
                ~parent_precedence pp_term))
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        pp_infix_operator_application ~parent_precedence identifier operator
          ~left_argument ~right_argument ppf ()
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]"
          (pp_postfix_operator_argument ~parent_precedence operator)
          argument QualifiedIdentifier.pp identifier)
    | Typ.Application { applicand; arguments; _ }
    (* Arbitrary type application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator precedence_typ
           ~parent_precedence pp_typ)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator precedence_term
              ~parent_precedence pp_term))
        arguments
    | Typ.ForwardArrow { domain; range; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows *)
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]"
        (match domain with
        | Typ.BackwardArrow _ -> parenthesize pp_typ
        | _ ->
          parenthesize_left_argument_right_associative_operator
            precedence_typ ~parent_precedence pp_typ)
        domain
        (match range with
        | Typ.BackwardArrow _ -> parenthesize pp_typ
        | _ ->
          parenthesize_right_argument_right_associative_operator
            precedence_typ ~parent_precedence pp_typ)
        range
    | Typ.BackwardArrow { range; domain; _ } ->
      (* Backward arrows are left-associative and of equal precedence with
         forward arrows *)
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]"
        (match range with
        | Typ.ForwardArrow _ -> parenthesize pp_typ
        | _ ->
          parenthesize_left_argument_left_associative_operator precedence_typ
            ~parent_precedence pp_typ)
        range
        (match domain with
        | Typ.ForwardArrow _ -> parenthesize pp_typ
        | _ ->
          parenthesize_right_argument_left_associative_operator
            precedence_typ ~parent_precedence pp_typ)
        domain
    | Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
      (* Pis are weak prefix operators *)
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]"
        (fun ppf -> function
          | Option.Some parameter_identifier ->
            Identifier.pp ppf parameter_identifier
          | Option.None -> Format.fprintf ppf "_")
        parameter_identifier pp_typ parameter_type pp_typ body

  and pp_term ppf term =
    let parent_precedence = precedence_term term in
    match term with
    | Term.Variable { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Term.Constant { identifier; quoted = true; operator; _ }
      when Operator.is_nullary operator ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
    | Term.Constant { identifier; quoted = false; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_term applicand
    | Term.Application
        { applicand =
            Term.Constant { identifier; operator; quoted = false; _ }
        ; arguments
        ; _
        }
    (* User-defined term constant application *) -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
             (parenthesize_argument_prefix_operator precedence_term
                ~parent_precedence pp_term))
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        pp_infix_operator_application ~parent_precedence identifier operator
          ~left_argument ~right_argument ppf ()
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]"
          (pp_postfix_operator_argument ~parent_precedence operator)
          argument QualifiedIdentifier.pp identifier)
    | Term.Application { applicand; arguments; _ }
    (* Arbitrary term application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator precedence_term
           ~parent_precedence pp_term)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator precedence_term
              ~parent_precedence pp_term))
        arguments
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type pp_term
        body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
        parameter_identifier pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_term body
    | Term.Wildcard _ -> Format.fprintf ppf "_"
    | Term.TypeAnnotated { term; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a@ :@ %a@]"
        (parenthesize_left_argument_left_associative_operator precedence_term
           ~parent_precedence pp_term)
        term pp_typ typ

  and pp_infix_operator_application ~parent_precedence operator_identifier
      operator ~left_argument ~right_argument ppf () =
    match Operator.associativity operator with
    | Associativity.Left_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_left_associative_operator_left_argument ~parent_precedence
           operator)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_left_associative_operator_right_argument ~parent_precedence
           operator)
        right_argument
    | Associativity.Right_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_right_associative_operator_left_argument ~parent_precedence
           operator)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_right_associative_operator_right_argument
           ~parent_precedence operator)
        right_argument
    | Associativity.Non_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_non_associative_operator_left_argument ~parent_precedence
           operator)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_non_associative_operator_right_argument ~parent_precedence
           operator)
        right_argument

  and pp_infix_left_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.is_right_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf left_argument
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.precedence left_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term ppf left_argument
    | _ ->
      parenthesize_left_argument_left_associative_operator precedence_term
        ~parent_precedence pp_term ppf left_argument

  and pp_infix_left_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.is_right_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf right_argument
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.precedence right_argument_operator
           > Operator.precedence applicand_operator ->
      pp_term ppf right_argument
    | _ ->
      parenthesize_right_argument_left_associative_operator precedence_term
        ~parent_precedence pp_term ppf right_argument

  and pp_infix_right_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.is_left_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf left_argument
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.precedence left_argument_operator
           > Operator.precedence applicand_operator ->
      pp_term ppf left_argument
    | _ ->
      parenthesize_left_argument_right_associative_operator precedence_term
        ~parent_precedence pp_term ppf left_argument

  and pp_infix_right_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.is_left_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf right_argument
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.precedence right_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term ppf right_argument
    | Term.Abstraction _ -> pp_term ppf right_argument
    | _ ->
      parenthesize_right_argument_right_associative_operator precedence_term
        ~parent_precedence pp_term ppf right_argument

  and pp_infix_non_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.precedence left_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term ppf left_argument
    | _ ->
      parenthesize_argument_non_associative_operator precedence_term
        ~parent_precedence pp_term ppf left_argument

  and pp_infix_non_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.precedence right_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term ppf right_argument
    | Term.Abstraction _ -> pp_term ppf right_argument
    | _ ->
      parenthesize_argument_non_associative_operator precedence_term
        ~parent_precedence pp_term ppf right_argument

  and pp_postfix_operator_argument ~parent_precedence applicand_operator ppf
      argument =
    match argument with
    | Term.Application
        { applicand = Term.Constant { operator = argument_operator; _ }; _ }
      when Operator.is_postfix argument_operator -> pp_term ppf argument
    | Term.Application
        { applicand = Term.Constant { operator = argument_operator; _ }; _ }
      when Operator.precedence argument_operator
           > Operator.precedence applicand_operator -> pp_term ppf argument
    | _ ->
      parenthesize_argument_postfix_operator precedence_term
        ~parent_precedence pp_term ppf argument
end

(** {1 Printing Contextual LF Types, Terms, Type Patterns and Term Patterns} *)
module CLF = struct
  open CLF

  let precedence_typ typ =
    match typ with
    | Typ.Pi _ -> 10
    | Typ.ForwardArrow _ | Typ.BackwardArrow _ -> 30
    | Typ.Block _ -> 40
    | Typ.Application { applicand = Typ.Constant { quoted = false; _ }; _ }
    (* User-defined operator application *) -> 49
    | Typ.Application _ -> 50
    | Typ.Constant _ -> 80

  let precedence_term term =
    match term with
    | Term.Abstraction _ -> 10
    | Term.TypeAnnotated _ -> 20
    | Term.Application { applicand = Term.Constant { quoted = false; _ }; _ }
    (* User-defined operator application *) -> 49
    | Term.Application _ -> 50
    | Term.Substitution _ -> 60
    | Term.Projection _ -> 70
    | Term.Variable _ | Term.Constant _ | Term.Hole _ | Term.Tuple _ -> 80

  let precedence_typ_pattern typ_pattern =
    match typ_pattern with
    | Typ.Pattern.Block _ -> 40
    | Typ.Pattern.Application
        { applicand = Typ.Pattern.Constant { quoted = false; _ }; _ }
    (* User-defined operator application *) -> 49
    | Typ.Pattern.Application _ -> 50
    | Typ.Pattern.Constant _ -> 80

  let precedence_term_pattern term_pattern =
    match term_pattern with
    | Term.Pattern.Abstraction _ -> 10
    | Term.Pattern.TypeAnnotated _ -> 20
    | Term.Pattern.Application
        { applicand = Term.Pattern.Constant { quoted = false; _ }; _ }
    (* User-defined operator application *) -> 49
    | Term.Pattern.Application _ -> 50
    | Term.Pattern.Substitution _ -> 60
    | Term.Pattern.Projection _ -> 70
    | Term.Pattern.Variable _
    | Term.Pattern.Constant _
    | Term.Pattern.Wildcard _
    | Term.Pattern.Tuple _ -> 80

  let rec pp_typ ppf typ =
    let parent_precedence = precedence_typ typ in
    match typ with
    | Typ.Constant { identifier; quoted = true; operator; _ }
      when Operator.is_nullary operator ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
    | Typ.Constant { identifier; quoted = false; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_typ applicand
    | Typ.Application
        { applicand =
            Typ.Constant { identifier; operator; quoted = false; _ }
        ; arguments
        ; _
        }
    (* User-defined type constant application *) -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
             (parenthesize_argument_prefix_operator precedence_term
                ~parent_precedence pp_term))
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        pp_infix_operator_application ~parent_precedence identifier operator
          ~left_argument ~right_argument ppf ()
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]"
          (pp_postfix_operator_argument ~parent_precedence operator)
          argument QualifiedIdentifier.pp identifier)
    | Typ.Application { applicand; arguments; _ }
    (* Arbitrary type application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator precedence_typ
           ~parent_precedence pp_typ)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator precedence_term
              ~parent_precedence pp_term))
        arguments
    | Typ.ForwardArrow { domain; range; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows *)
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]"
        (match domain with
        | Typ.BackwardArrow _ -> parenthesize pp_typ
        | _ ->
          parenthesize_left_argument_right_associative_operator
            precedence_typ ~parent_precedence pp_typ)
        domain
        (match range with
        | Typ.BackwardArrow _ -> parenthesize pp_typ
        | _ ->
          parenthesize_right_argument_right_associative_operator
            precedence_typ ~parent_precedence pp_typ)
        range
    | Typ.BackwardArrow { range; domain; _ } ->
      (* Backward arrows are left-associative and of equal precedence with
         forward arrows *)
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]"
        (match range with
        | Typ.ForwardArrow _ -> parenthesize pp_typ
        | _ ->
          parenthesize_left_argument_left_associative_operator precedence_typ
            ~parent_precedence pp_typ)
        range
        (match domain with
        | Typ.ForwardArrow _ -> parenthesize pp_typ
        | _ ->
          parenthesize_right_argument_left_associative_operator
            precedence_typ ~parent_precedence pp_typ)
        domain
    | Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
      (* Pis are weak prefix operators *)
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]"
        (fun ppf -> function
          | Option.Some parameter_identifier ->
            Identifier.pp ppf parameter_identifier
          | Option.None -> Format.fprintf ppf "_")
        parameter_identifier pp_typ parameter_type pp_typ body
    | Typ.Block { elements = (Option.None, typ), []; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]" pp_typ typ
    | Typ.Block { elements = (Option.None, _typ), _nt1 :: _nts; _ } ->
      raise
      @@ Invalid_argument
           "[pp_typ_pattern] missing identifier for first type in block"
    | Typ.Block { elements = (Option.Some i1, t1), nts; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]"
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           (fun ppf (i, t) ->
             Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t))
        ((i1, t1) :: nts)

  and pp_term ppf term =
    let parent_precedence = precedence_term term in
    match term with
    | Term.Variable { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Term.Constant { identifier; quoted = true; operator; _ }
      when Operator.is_nullary operator ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
    | Term.Constant { identifier; quoted = false; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_term applicand
    | Term.Application
        { applicand =
            Term.Constant { identifier; operator; quoted = false; _ }
        ; arguments
        ; _
        }
    (* User-defined term constant application *) -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
             (parenthesize_argument_prefix_operator precedence_term
                ~parent_precedence pp_term))
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        pp_infix_operator_application ~parent_precedence identifier operator
          ~left_argument ~right_argument ppf ()
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]"
          (pp_postfix_operator_argument ~parent_precedence operator)
          argument QualifiedIdentifier.pp identifier)
    | Term.Application { applicand; arguments; _ }
    (* Arbitrary term application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator precedence_term
           ~parent_precedence pp_term)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator precedence_term
              ~parent_precedence pp_term))
        arguments
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type pp_term
        body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
        parameter_identifier pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_term body
    | Term.Hole { variant = `Underscore; _ } -> Format.fprintf ppf "_"
    | Term.Hole { variant = `Unlabelled; _ } -> Format.fprintf ppf "?"
    | Term.Hole { variant = `Labelled label; _ } ->
      Format.fprintf ppf "?%s" label
    | Term.Substitution { term; substitution; _ } ->
      Format.fprintf ppf "@[<2>%a%a@]"
        (parenthesize_left_argument_left_associative_operator precedence_term
           ~parent_precedence pp_term)
        term pp_substitution substitution
    | Term.Tuple { terms; _ } ->
      Format.fprintf ppf "@[<2><%a>@]"
        (List1.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,") pp_term)
        terms
    | Term.Projection { term; projection = `By_position i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%d@]"
        (parenthesize_left_argument_left_associative_operator precedence_term
           ~parent_precedence pp_term)
        term i
    | Term.Projection { term; projection = `By_identifier i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%a@]"
        (parenthesize_left_argument_left_associative_operator precedence_term
           ~parent_precedence pp_term)
        term Identifier.pp i
    | Term.TypeAnnotated { term; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a@ :@ %a@]"
        (parenthesize_left_argument_left_associative_operator precedence_term
           ~parent_precedence pp_term)
        term pp_typ typ

  and pp_substitution ppf substitution =
    match substitution with
    | Substitution.{ head = Substitution.Head.None; terms = []; _ } ->
      Format.fprintf ppf "[]"
    | Substitution.{ head = Substitution.Head.Identity _; terms = []; _ } ->
      Format.fprintf ppf "[..]"
    | Substitution.{ head = Substitution.Head.None; terms; _ } ->
      Format.fprintf ppf "@[<2>[%a]@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
        terms
    | Substitution.{ head = Substitution.Head.Identity _; terms; _ } ->
      Format.fprintf ppf "@[<2>[..,@ %a]@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
        terms
    | Substitution.
        { head =
            Substitution.Head.Substitution_variable
              { identifier; closure = Option.None; _ }
        ; terms = []
        ; _
        } -> Format.fprintf ppf "@[<2>[%a]@]" Identifier.pp identifier
    | Substitution.
        { head =
            Substitution.Head.Substitution_variable
              { identifier; closure = Option.Some closure; _ }
        ; terms = []
        ; _
        } ->
      Format.fprintf ppf "@[<2>[%a[%a]]@]" Identifier.pp identifier
        pp_substitution closure
    | Substitution.
        { head =
            Substitution.Head.Substitution_variable
              { identifier; closure = Option.None; _ }
        ; terms
        ; _
        } ->
      Format.fprintf ppf "@[<2>[%a,@ %a]@]" Identifier.pp identifier
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
        terms
    | Substitution.
        { head =
            Substitution.Head.Substitution_variable
              { identifier; closure = Option.Some closure; _ }
        ; terms
        ; _
        } ->
      Format.fprintf ppf "@[<2>[%a[%a],@ %a]@]" Identifier.pp identifier
        pp_substitution closure
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
        terms

  and pp_context ppf context =
    match context with
    | Context.{ head = Context.Head.None; typings = []; _ } -> ()
    | Context.{ head = Context.Head.Hole _; typings = []; _ } ->
      Format.fprintf ppf "_"
    | Context.
        { head = Context.Head.Context_variable { identifier; _ }
        ; typings = []
        ; _
        } -> Format.fprintf ppf "%a" Identifier.pp identifier
    | Context.{ head = Context.Head.None; typings; _ } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           (fun ppf -> function
             | i, Option.Some t ->
               Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t
             | i, Option.None -> Identifier.pp ppf i))
        typings
    | Context.{ head = Context.Head.Hole _; typings; _ } ->
      Format.fprintf ppf "@[<2>_,@ %a@]"
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           (fun ppf -> function
             | i, Option.Some t ->
               Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t
             | i, Option.None -> Identifier.pp ppf i))
        typings
    | Context.
        { head = Context.Head.Context_variable { identifier; _ }
        ; typings
        ; _
        } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           (fun ppf -> function
             | i, Option.Some t ->
               Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t
             | i, Option.None -> Identifier.pp ppf i))
        typings

  and pp_infix_operator_application ~parent_precedence operator_identifier
      operator ~left_argument ~right_argument ppf () =
    match Operator.associativity operator with
    | Associativity.Left_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_left_associative_operator_left_argument ~parent_precedence
           operator)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_left_associative_operator_right_argument ~parent_precedence
           operator)
        right_argument
    | Associativity.Right_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_right_associative_operator_left_argument ~parent_precedence
           operator)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_right_associative_operator_right_argument
           ~parent_precedence operator)
        right_argument
    | Associativity.Non_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_non_associative_operator_left_argument ~parent_precedence
           operator)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_non_associative_operator_right_argument ~parent_precedence
           operator)
        right_argument

  and pp_infix_left_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.is_right_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf left_argument
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.precedence left_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term ppf left_argument
    | _ ->
      parenthesize_left_argument_left_associative_operator precedence_term
        ~parent_precedence pp_term ppf left_argument

  and pp_infix_left_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.is_right_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf right_argument
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.precedence right_argument_operator
           > Operator.precedence applicand_operator ->
      pp_term ppf right_argument
    | _ ->
      parenthesize_right_argument_left_associative_operator precedence_term
        ~parent_precedence pp_term ppf right_argument

  and pp_infix_right_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.is_left_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf left_argument
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.precedence left_argument_operator
           > Operator.precedence applicand_operator ->
      pp_term ppf left_argument
    | _ ->
      parenthesize_left_argument_right_associative_operator precedence_term
        ~parent_precedence pp_term ppf left_argument

  and pp_infix_right_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.is_left_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf right_argument
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.precedence right_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term ppf right_argument
    | Term.Abstraction _ -> pp_term ppf right_argument
    | _ ->
      parenthesize_right_argument_right_associative_operator precedence_term
        ~parent_precedence pp_term ppf right_argument

  and pp_infix_non_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand = Term.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.precedence left_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term ppf left_argument
    | _ ->
      parenthesize_argument_non_associative_operator precedence_term
        ~parent_precedence pp_term ppf left_argument

  and pp_infix_non_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand = Term.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.precedence right_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term ppf right_argument
    | Term.Abstraction _ -> pp_term ppf right_argument
    | _ ->
      parenthesize_argument_non_associative_operator precedence_term
        ~parent_precedence pp_term ppf right_argument

  and pp_postfix_operator_argument ~parent_precedence applicand_operator ppf
      argument =
    match argument with
    | Term.Application
        { applicand = Term.Constant { operator = argument_operator; _ }; _ }
      when Operator.is_postfix argument_operator -> pp_term ppf argument
    | Term.Application
        { applicand = Term.Constant { operator = argument_operator; _ }; _ }
      when Operator.precedence argument_operator
           > Operator.precedence applicand_operator -> pp_term ppf argument
    | _ ->
      parenthesize_argument_postfix_operator precedence_term
        ~parent_precedence pp_term ppf argument

  let rec pp_typ_pattern ppf typ =
    let parent_precedence = precedence_typ_pattern typ in
    match typ with
    | Typ.Pattern.Constant { identifier; quoted = true; operator; _ }
      when Operator.is_nullary operator ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Pattern.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
    | Typ.Pattern.Constant { identifier; quoted = false; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Pattern.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_typ_pattern applicand
    | Typ.Pattern.Application
        { applicand =
            Typ.Pattern.Constant { identifier; operator; quoted = false; _ }
        ; arguments
        ; _
        }
    (* User-defined type constant application *) -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
             (parenthesize_argument_prefix_operator precedence_term_pattern
                ~parent_precedence pp_term_pattern))
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        pp_infix_operator_application ~parent_precedence identifier operator
          ~left_argument ~right_argument ppf ()
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]"
          (pp_postfix_operator_argument ~parent_precedence operator)
          argument QualifiedIdentifier.pp identifier)
    | Typ.Pattern.Application { applicand; arguments; _ }
    (* Arbitrary type application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator precedence_typ_pattern
           ~parent_precedence pp_typ_pattern)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator precedence_term_pattern
              ~parent_precedence pp_term_pattern))
        arguments
    | Typ.Pattern.Block { elements = (Option.None, typ), []; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]" pp_typ_pattern typ
    | Typ.Pattern.Block { elements = (Option.None, _typ), _nt1 :: _nts; _ }
      ->
      raise
      @@ Invalid_argument
           "[pp_typ_pattern] missing identifier for first type in block"
    | Typ.Pattern.Block { elements = (Option.Some i1, t1), nts; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]"
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           (fun ppf (i, t) ->
             Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ_pattern t))
        ((i1, t1) :: nts)

  and pp_term_pattern ppf term =
    let parent_precedence = precedence_term_pattern term in
    match term with
    | Term.Pattern.Variable { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Term.Pattern.Constant { identifier; quoted = true; operator; _ }
      when Operator.is_nullary operator ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Pattern.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
    | Term.Pattern.Constant { identifier; quoted = false; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Pattern.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_term_pattern applicand
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { identifier; operator; quoted = false; _ }
        ; arguments
        ; _
        }
    (* User-defined term constant application *) -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
             (parenthesize_argument_prefix_operator precedence_term_pattern
                ~parent_precedence pp_term_pattern))
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        pp_infix_operator_application ~parent_precedence identifier operator
          ~left_argument ~right_argument ppf ()
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]"
          (pp_postfix_operator_argument ~parent_precedence operator)
          argument QualifiedIdentifier.pp identifier)
    | Term.Pattern.Application { applicand; arguments; _ }
    (* Arbitrary term application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator precedence_term_pattern
           ~parent_precedence pp_term_pattern)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator precedence_term_pattern
              ~parent_precedence pp_term_pattern))
        arguments
    | Term.Pattern.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term_pattern body
    | Term.Pattern.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type
        pp_term_pattern body
    | Term.Pattern.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
        parameter_identifier pp_term_pattern body
    | Term.Pattern.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      (* Lambdas are weak prefix operators *)
      Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_term_pattern body
    | Term.Pattern.Wildcard _ -> Format.fprintf ppf "_"
    | Term.Pattern.Substitution { term; substitution; _ } ->
      Format.fprintf ppf "@[<2>%a%a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_term_pattern ~parent_precedence pp_term_pattern)
        term pp_substitution substitution
    | Term.Pattern.Tuple { terms; _ } ->
      Format.fprintf ppf "@[<2><%a>@]"
        (List1.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,")
           pp_term_pattern)
        terms
    | Term.Pattern.Projection { term; projection = `By_position i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%d@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_term_pattern ~parent_precedence pp_term_pattern)
        term i
    | Term.Pattern.Projection { term; projection = `By_identifier i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_term_pattern ~parent_precedence pp_term_pattern)
        term Identifier.pp i
    | Term.Pattern.TypeAnnotated { term; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a@ :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           precedence_term_pattern ~parent_precedence pp_term_pattern)
        term pp_typ typ

  and pp_infix_operator_application ~parent_precedence operator_identifier
      operator ~left_argument ~right_argument ppf () =
    match Operator.associativity operator with
    | Associativity.Left_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_left_associative_operator_left_argument ~parent_precedence
           operator)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_left_associative_operator_right_argument ~parent_precedence
           operator)
        right_argument
    | Associativity.Right_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_right_associative_operator_left_argument ~parent_precedence
           operator)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_right_associative_operator_right_argument
           ~parent_precedence operator)
        right_argument
    | Associativity.Non_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_non_associative_operator_left_argument ~parent_precedence
           operator)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_non_associative_operator_right_argument ~parent_precedence
           operator)
        right_argument

  and pp_infix_left_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.is_right_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term_pattern) ppf left_argument
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.precedence left_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term_pattern ppf left_argument
    | _ ->
      parenthesize_left_argument_left_associative_operator
        precedence_term_pattern ~parent_precedence pp_term_pattern ppf
        left_argument

  and pp_infix_left_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.is_right_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term_pattern) ppf right_argument
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.precedence right_argument_operator
           > Operator.precedence applicand_operator ->
      pp_term_pattern ppf right_argument
    | _ ->
      parenthesize_right_argument_left_associative_operator
        precedence_term_pattern ~parent_precedence pp_term_pattern ppf
        right_argument

  and pp_infix_right_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.is_left_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term_pattern) ppf left_argument
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.precedence left_argument_operator
           > Operator.precedence applicand_operator ->
      pp_term_pattern ppf left_argument
    | _ ->
      parenthesize_left_argument_right_associative_operator
        precedence_term_pattern ~parent_precedence pp_term_pattern ppf
        left_argument

  and pp_infix_right_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.is_left_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term_pattern) ppf right_argument
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.precedence right_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term_pattern ppf right_argument
    | Term.Pattern.Abstraction _ -> pp_term_pattern ppf right_argument
    | _ ->
      parenthesize_right_argument_right_associative_operator
        precedence_term_pattern ~parent_precedence pp_term_pattern ppf
        right_argument

  and pp_infix_non_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = left_argument_operator; _ }
        ; _
        }
      when Operator.precedence left_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term_pattern ppf left_argument
    | _ ->
      parenthesize_argument_non_associative_operator precedence_term_pattern
        ~parent_precedence pp_term_pattern ppf left_argument

  and pp_infix_non_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = right_argument_operator; _ }
        ; _
        }
      when Operator.precedence right_argument_operator
           >= Operator.precedence applicand_operator ->
      pp_term_pattern ppf right_argument
    | Term.Pattern.Abstraction _ -> pp_term_pattern ppf right_argument
    | _ ->
      parenthesize_argument_non_associative_operator precedence_term_pattern
        ~parent_precedence pp_term_pattern ppf right_argument

  and pp_postfix_operator_argument ~parent_precedence applicand_operator ppf
      argument =
    match argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = argument_operator; _ }
        ; _
        }
      when Operator.is_postfix argument_operator ->
      pp_term_pattern ppf argument
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant { operator = argument_operator; _ }
        ; _
        }
      when Operator.precedence argument_operator
           > Operator.precedence applicand_operator ->
      pp_term_pattern ppf argument
    | _ ->
      parenthesize_argument_postfix_operator precedence_term_pattern
        ~parent_precedence pp_term_pattern ppf argument
end
