(** Pretty-printing for the external syntax. *)

open Support
open Synext'

(** {1 Handling Parentheses}

    Parentheses are re-introduced during pretty-printing using the precedence
    ordering specified in the parser. Operator associativities also need to
    be considered to avoid adding extraneous parentheses. *)

let parenthesize pp ppf = Format.fprintf ppf "@[<2>(%a)@]" pp

module Make_parenthesizer (Precedence : Ord.ORD) = struct
  let[@inline] parenthesize_argument_of_lesser_precedence precedence
      ~parent_precedence pp ppf argument =
    if Precedence.(precedence argument < parent_precedence) then
      parenthesize pp ppf argument
    else pp ppf argument

  let[@inline] parenthesize_argument_of_lesser_than_or_equal_precedence
      precedence ~parent_precedence pp ppf argument =
    if Precedence.(precedence argument <= parent_precedence) then
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
end

(** {1 Printing LF Kinds, Types and Terms} *)
module LF = struct
  open LF

  module Precedence : sig
    type t

    val of_kind : Kind.t -> t

    val of_typ : Typ.t -> t

    val of_term : Term.t -> t

    include Ord.ORD with type t := t
  end = struct
    type t =
      | Static of Int.t
      | User_defined of Int.t

    let application_precedence = 4

    let of_kind kind =
      match kind with
      | Kind.Pi _ -> Static 1
      | Kind.Arrow _ -> Static 3
      | Kind.Typ _ -> Static 5

    let of_typ typ =
      match typ with
      | Typ.Pi _ -> Static 1
      | Typ.Arrow _ -> Static 3
      | Typ.Application { applicand = Typ.Constant { operator; _ }; _ }
        when Operator.is_prefix operator
             (* Juxtapositions are of higher precedence than user-defined
                operators *) -> Static application_precedence
      | Typ.Application
          { applicand = Typ.Constant { operator; quoted = false; _ }; _ }
      (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
      | Typ.Application _ -> Static application_precedence
      | Typ.Constant _ -> Static 5

    let of_term term =
      match term with
      | Term.Abstraction _ -> Static 1
      | Term.TypeAnnotated _ -> Static 2
      | Term.Application { applicand = Term.Constant { operator; _ }; _ }
        when Operator.is_prefix operator
             (* Juxtapositions are of higher precedence than user-defined
                operators *) -> Static application_precedence
      | Term.Application
          { applicand = Term.Constant { operator; quoted = false; _ }; _ }
      (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
      | Term.Application _ -> Static application_precedence
      | Term.Wildcard _ | Term.Variable _ | Term.Constant _ -> Static 6

    include (
      Ord.Make (struct
        type nonrec t = t

        let compare x y =
          match (x, y) with
          | Static x, Static y -> Int.compare x y
          | User_defined x, User_defined y -> Int.compare x y
          | User_defined _, Static y ->
            Int.compare ((2 * application_precedence) - 1) (2 * y)
          | Static x, User_defined _ ->
            Int.compare (2 * x) ((2 * application_precedence) - 1)
      end) :
        Ord.ORD with type t := t)
  end

  include Make_parenthesizer (Precedence)

  let rec pp_kind ppf kind =
    let parent_precedence = Precedence.of_kind kind in
    match kind with
    | Kind.Typ _ -> Format.fprintf ppf "type"
    | Kind.Arrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]"
        (parenthesize_left_argument_right_associative_operator
           Precedence.of_typ ~parent_precedence pp_typ)
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
    let parent_precedence = Precedence.of_typ typ in
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
             (parenthesize_argument_prefix_operator Precedence.of_term
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
          (pp_postfix_operator_argument ~parent_precedence)
          argument QualifiedIdentifier.pp identifier)
    | Typ.Application { applicand; arguments; _ }
    (* Arbitrary type application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator Precedence.of_typ
           ~parent_precedence pp_typ)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator Precedence.of_term
              ~parent_precedence pp_term))
        arguments
    | Typ.Arrow { domain; range; orientation = `Forward; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows *)
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]"
        (match domain with
        | Typ.Arrow { orientation = `Backward; _ } -> parenthesize pp_typ
        | _ ->
          parenthesize_left_argument_right_associative_operator
            Precedence.of_typ ~parent_precedence pp_typ)
        domain
        (match range with
        | Typ.Arrow { orientation = `Backward; _ } -> parenthesize pp_typ
        | _ ->
          parenthesize_right_argument_right_associative_operator
            Precedence.of_typ ~parent_precedence pp_typ)
        range
    | Typ.Arrow { range; domain; orientation = `Backward; _ } ->
      (* Backward arrows are left-associative and of equal precedence with
         forward arrows *)
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]"
        (match range with
        | Typ.Arrow { orientation = `Forward; _ } -> parenthesize pp_typ
        | _ ->
          parenthesize_left_argument_left_associative_operator
            Precedence.of_typ ~parent_precedence pp_typ)
        range
        (match domain with
        | Typ.Arrow { orientation = `Forward; _ } -> parenthesize pp_typ
        | _ ->
          parenthesize_right_argument_left_associative_operator
            Precedence.of_typ ~parent_precedence pp_typ)
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
    let parent_precedence = Precedence.of_term term in
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
             (parenthesize_argument_prefix_operator Precedence.of_term
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
          (pp_postfix_operator_argument ~parent_precedence)
          argument QualifiedIdentifier.pp identifier)
    | Term.Application { applicand; arguments; _ }
    (* Arbitrary term application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator Precedence.of_term
           ~parent_precedence pp_term)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator Precedence.of_term
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
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term ~parent_precedence pp_term)
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
        (pp_infix_non_associative_operator_left_argument ~parent_precedence)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_non_associative_operator_right_argument ~parent_precedence)
        right_argument

  and pp_infix_left_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand =
            Term.Constant
              { operator = left_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_right_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf left_argument
    | _ ->
      parenthesize_left_argument_left_associative_operator Precedence.of_term
        ~parent_precedence pp_term ppf left_argument

  and pp_infix_left_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand =
            Term.Constant
              { operator = right_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_right_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf right_argument
    | _ ->
      parenthesize_right_argument_left_associative_operator
        Precedence.of_term ~parent_precedence pp_term ppf right_argument

  and pp_infix_right_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand =
            Term.Constant
              { operator = left_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_left_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf left_argument
    | _ ->
      parenthesize_left_argument_right_associative_operator
        Precedence.of_term ~parent_precedence pp_term ppf left_argument

  and pp_infix_right_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand =
            Term.Constant
              { operator = right_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_left_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf right_argument
    | Term.Abstraction _ -> pp_term ppf right_argument
    | _ ->
      parenthesize_right_argument_right_associative_operator
        Precedence.of_term ~parent_precedence pp_term ppf right_argument

  and pp_infix_non_associative_operator_left_argument ~parent_precedence ppf
      left_argument =
    parenthesize_argument_non_associative_operator Precedence.of_term
      ~parent_precedence pp_term ppf left_argument

  and pp_infix_non_associative_operator_right_argument ~parent_precedence ppf
      right_argument =
    match right_argument with
    | Term.Abstraction _ -> pp_term ppf right_argument
    | _ ->
      parenthesize_argument_non_associative_operator Precedence.of_term
        ~parent_precedence pp_term ppf right_argument

  and pp_postfix_operator_argument ~parent_precedence ppf argument =
    match argument with
    | Term.Application
        { applicand =
            Term.Constant { operator = argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_postfix argument_operator -> pp_term ppf argument
    | _ ->
      parenthesize_argument_postfix_operator Precedence.of_term
        ~parent_precedence pp_term ppf argument
end

(** {1 Printing Contextual LF Types, Terms, Type Patterns and Term Patterns} *)
module CLF = struct
  open CLF

  module Precedence : sig
    type t

    val of_typ : Typ.t -> t

    val of_term : Term.t -> t

    val of_term_pattern : Term.Pattern.t -> t

    include Ord.ORD with type t := t
  end = struct
    type t =
      | Static of Int.t
      | User_defined of Int.t

    let application_precedence = 5

    let of_typ typ =
      match typ with
      | Typ.Pi _ -> Static 1
      | Typ.Arrow _ -> Static 3
      | Typ.Block _ -> Static 4
      | Typ.Application { applicand = Typ.Constant { operator; _ }; _ }
        when Operator.is_prefix operator
             (* Juxtapositions are of higher precedence than user-defined
                operators *) -> Static application_precedence
      | Typ.Application
          { applicand = Typ.Constant { operator; quoted = false; _ }; _ }
      (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
      | Typ.Application _ -> Static application_precedence
      | Typ.Constant _ -> Static 8

    let of_term term =
      match term with
      | Term.Abstraction _ -> Static 1
      | Term.TypeAnnotated _ -> Static 2
      | Term.Application { applicand = Term.Constant { operator; _ }; _ }
        when Operator.is_prefix operator
             (* Juxtapositions are of higher precedence than user-defined
                operators *) -> Static application_precedence
      | Term.Application
          { applicand = Term.Constant { operator; quoted = false; _ }; _ }
      (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
      | Term.Application _ -> Static application_precedence
      | Term.Substitution _ -> Static 6
      | Term.Projection _ -> Static 7
      | Term.Variable _ | Term.Constant _ | Term.Hole _ | Term.Tuple _ ->
        Static 8

    let of_term_pattern term =
      match term with
      | Term.Pattern.Abstraction _ -> Static 1
      | Term.Pattern.TypeAnnotated _ -> Static 2
      | Term.Pattern.Application
          { applicand = Term.Pattern.Constant { operator; _ }; _ }
        when Operator.is_prefix operator
             (* Juxtapositions are of higher precedence than user-defined
                operators *) -> Static application_precedence
      | Term.Pattern.Application
          { applicand = Term.Pattern.Constant { operator; quoted = false; _ }
          ; _
          }
      (* User-defined operator application *) ->
        User_defined (Operator.precedence operator)
      | Term.Pattern.Application _ -> Static application_precedence
      | Term.Pattern.Substitution _ -> Static 6
      | Term.Pattern.Projection _ -> Static 7
      | Term.Pattern.Wildcard _
      | Term.Pattern.Variable _
      | Term.Pattern.Constant _
      | Term.Pattern.Tuple _ -> Static 8

    include (
      Ord.Make (struct
        type nonrec t = t

        let compare x y =
          match (x, y) with
          | Static x, Static y -> Int.compare x y
          | User_defined x, User_defined y -> Int.compare x y
          | User_defined _, Static y ->
            Int.compare ((2 * application_precedence) - 1) (2 * y)
          | Static x, User_defined _ ->
            Int.compare (2 * x) ((2 * application_precedence) - 1)
      end) :
        Ord.ORD with type t := t)
  end

  include Make_parenthesizer (Precedence)

  let rec pp_typ ppf typ =
    let parent_precedence = Precedence.of_typ typ in
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
             (parenthesize_argument_prefix_operator Precedence.of_term
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
          (pp_postfix_operator_argument ~parent_precedence)
          argument QualifiedIdentifier.pp identifier)
    | Typ.Application { applicand; arguments; _ }
    (* Arbitrary type application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator Precedence.of_typ
           ~parent_precedence pp_typ)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator Precedence.of_term
              ~parent_precedence pp_term))
        arguments
    | Typ.Arrow { domain; range; orientation = `Forward; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows *)
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]"
        (match domain with
        | Typ.Arrow { orientation = `Backward; _ } -> parenthesize pp_typ
        | _ ->
          parenthesize_left_argument_right_associative_operator
            Precedence.of_typ ~parent_precedence pp_typ)
        domain
        (match range with
        | Typ.Arrow { orientation = `Backward; _ } -> parenthesize pp_typ
        | _ ->
          parenthesize_right_argument_right_associative_operator
            Precedence.of_typ ~parent_precedence pp_typ)
        range
    | Typ.Arrow { range; domain; orientation = `Backward; _ } ->
      (* Backward arrows are left-associative and of equal precedence with
         forward arrows *)
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]"
        (match range with
        | Typ.Arrow { orientation = `Forward; _ } -> parenthesize pp_typ
        | _ ->
          parenthesize_left_argument_left_associative_operator
            Precedence.of_typ ~parent_precedence pp_typ)
        range
        (match domain with
        | Typ.Arrow { orientation = `Forward; _ } -> parenthesize pp_typ
        | _ ->
          parenthesize_right_argument_left_associative_operator
            Precedence.of_typ ~parent_precedence pp_typ)
        domain
    | Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
      (* Pis are weak prefix operators *)
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]"
        (fun ppf -> function
          | Option.Some parameter_identifier ->
            Identifier.pp ppf parameter_identifier
          | Option.None -> Format.fprintf ppf "_")
        parameter_identifier pp_typ parameter_type pp_typ body
    | Typ.Block { elements = `Unnamed typ; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]" pp_typ typ
    | Typ.Block { elements = `Record nts; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]"
        (List1.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           (fun ppf (i, t) ->
             Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t))
        nts

  and pp_term ppf term =
    let parent_precedence = Precedence.of_term term in
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
             (parenthesize_argument_prefix_operator Precedence.of_term
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
          (pp_postfix_operator_argument ~parent_precedence)
          argument QualifiedIdentifier.pp identifier)
    | Term.Application { applicand; arguments; _ }
    (* Arbitrary term application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator Precedence.of_term
           ~parent_precedence pp_term)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator Precedence.of_term
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
      Format.fprintf ppf "?%a" Identifier.pp label
    | Term.Substitution { term; substitution; _ } ->
      Format.fprintf ppf "@[<2>%a[%a]@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term ~parent_precedence pp_term)
        term pp_substitution substitution
    | Term.Tuple { terms; _ } ->
      Format.fprintf ppf "@[<2><%a>@]"
        (List1.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,") pp_term)
        terms
    | Term.Projection { term; projection = `By_position i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%d@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term ~parent_precedence pp_term)
        term i
    | Term.Projection { term; projection = `By_identifier i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%a@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term ~parent_precedence pp_term)
        term Identifier.pp i
    | Term.TypeAnnotated { term; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a@ :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term ~parent_precedence pp_term)
        term pp_typ typ

  and pp_substitution ppf substitution =
    match substitution with
    | { Substitution.head = Substitution.Head.None _; terms = []; _ } ->
      Format.fprintf ppf "^"
    | { Substitution.head = Substitution.Head.Identity _; terms = []; _ } ->
      Format.fprintf ppf ".."
    | { Substitution.head = Substitution.Head.None _; terms; _ } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
        terms
    | { Substitution.head = Substitution.Head.Identity _; terms; _ } ->
      Format.fprintf ppf "@[<2>..,@ %a@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
        terms
    | { Substitution.head =
          Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } -> Format.fprintf ppf "@[<2>%a@]" Identifier.pp identifier
    | { Substitution.head =
          Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a[%a]@]" Identifier.pp identifier
        pp_substitution closure
    | { Substitution.head =
          Substitution.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
        terms
    | { Substitution.head =
          Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a[%a],@ %a@]" Identifier.pp identifier
        pp_substitution closure
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
        terms

  and pp_context ppf context =
    let pp_typing ppf typing =
      match typing with
      | identifier, Option.None ->
        Format.fprintf ppf "%a" Identifier.pp identifier
      | identifier, Option.Some typ ->
        Format.fprintf ppf "%a@ :@ %a" Identifier.pp identifier pp_typ typ
    in
    match context with
    | { Context.head = Context.Head.None _; bindings = []; _ } ->
      Format.fprintf ppf "^"
    | { Context.head = Context.Head.Hole _; bindings = []; _ } ->
      Format.fprintf ppf "_"
    | { Context.head = Context.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } -> Format.fprintf ppf "%a" Identifier.pp identifier
    | { Context.head = Context.Head.None _; bindings; _ } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_typing)
        bindings
    | { Context.head = Context.Head.Hole _; bindings; _ } ->
      Format.fprintf ppf "@[<2>_,@ %a@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_typing)
        bindings
    | { Context.head = Context.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_typing)
        bindings

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
        (pp_infix_non_associative_operator_left_argument ~parent_precedence)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_non_associative_operator_right_argument ~parent_precedence)
        right_argument

  and pp_infix_left_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand =
            Term.Constant
              { operator = left_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_right_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf left_argument
    | _ ->
      parenthesize_left_argument_left_associative_operator Precedence.of_term
        ~parent_precedence pp_term ppf left_argument

  and pp_infix_left_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand =
            Term.Constant
              { operator = right_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_right_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf right_argument
    | _ ->
      parenthesize_right_argument_left_associative_operator
        Precedence.of_term ~parent_precedence pp_term ppf right_argument

  and pp_infix_right_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Application
        { applicand =
            Term.Constant
              { operator = left_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_left_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf left_argument
    | _ ->
      parenthesize_left_argument_right_associative_operator
        Precedence.of_term ~parent_precedence pp_term ppf left_argument

  and pp_infix_right_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Application
        { applicand =
            Term.Constant
              { operator = right_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_left_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term) ppf right_argument
    | Term.Abstraction _ -> pp_term ppf right_argument
    | _ ->
      parenthesize_right_argument_right_associative_operator
        Precedence.of_term ~parent_precedence pp_term ppf right_argument

  and pp_infix_non_associative_operator_left_argument ~parent_precedence ppf
      left_argument =
    parenthesize_argument_non_associative_operator Precedence.of_term
      ~parent_precedence pp_term ppf left_argument

  and pp_infix_non_associative_operator_right_argument ~parent_precedence ppf
      right_argument =
    match right_argument with
    | Term.Abstraction _ -> pp_term ppf right_argument
    | _ ->
      parenthesize_argument_non_associative_operator Precedence.of_term
        ~parent_precedence pp_term ppf right_argument

  and pp_postfix_operator_argument ~parent_precedence ppf argument =
    match argument with
    | Term.Application
        { applicand =
            Term.Constant { operator = argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_postfix argument_operator -> pp_term ppf argument
    | _ ->
      parenthesize_argument_postfix_operator Precedence.of_term
        ~parent_precedence pp_term ppf argument

  let rec pp_term_pattern ppf term =
    let parent_precedence = Precedence.of_term_pattern term in
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
             (parenthesize_argument_prefix_operator
                Precedence.of_term_pattern ~parent_precedence pp_term_pattern))
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
          (pp_postfix_operator_argument ~parent_precedence)
          argument QualifiedIdentifier.pp identifier)
    | Term.Pattern.Application { applicand; arguments; _ }
    (* Arbitrary term application *) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_argument_prefix_operator Precedence.of_term_pattern
           ~parent_precedence pp_term_pattern)
        applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           (parenthesize_argument_prefix_operator Precedence.of_term_pattern
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
      Format.fprintf ppf "@[<2>%a[%a]@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term_pattern ~parent_precedence pp_term_pattern)
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
           Precedence.of_term_pattern ~parent_precedence pp_term_pattern)
        term i
    | Term.Pattern.Projection { term; projection = `By_identifier i; _ } ->
      (* Projections are left-associative *)
      Format.fprintf ppf "@[<2>%a.%a@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term_pattern ~parent_precedence pp_term_pattern)
        term Identifier.pp i
    | Term.Pattern.TypeAnnotated { term; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a@ :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term_pattern ~parent_precedence pp_term_pattern)
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
        (pp_infix_non_associative_operator_left_argument ~parent_precedence)
        left_argument QualifiedIdentifier.pp operator_identifier
        (pp_infix_non_associative_operator_right_argument ~parent_precedence)
        right_argument

  and pp_infix_left_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant
              { operator = left_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_right_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term_pattern) ppf left_argument
    | _ ->
      parenthesize_left_argument_left_associative_operator
        Precedence.of_term_pattern ~parent_precedence pp_term_pattern ppf
        left_argument

  and pp_infix_left_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant
              { operator = right_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_right_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term_pattern) ppf right_argument
    | _ ->
      parenthesize_right_argument_left_associative_operator
        Precedence.of_term_pattern ~parent_precedence pp_term_pattern ppf
        right_argument

  and pp_infix_right_associative_operator_left_argument ~parent_precedence
      applicand_operator ppf left_argument =
    match left_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant
              { operator = left_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_left_associative left_argument_operator
           && Operator.precedence left_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term_pattern) ppf left_argument
    | _ ->
      parenthesize_left_argument_right_associative_operator
        Precedence.of_term_pattern ~parent_precedence pp_term_pattern ppf
        left_argument

  and pp_infix_right_associative_operator_right_argument ~parent_precedence
      applicand_operator ppf right_argument =
    match right_argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant
              { operator = right_argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_left_associative right_argument_operator
           && Operator.precedence right_argument_operator
              = Operator.precedence applicand_operator ->
      (parenthesize pp_term_pattern) ppf right_argument
    | Term.Pattern.Abstraction _ -> pp_term_pattern ppf right_argument
    | _ ->
      parenthesize_right_argument_right_associative_operator
        Precedence.of_term_pattern ~parent_precedence pp_term_pattern ppf
        right_argument

  and pp_infix_non_associative_operator_left_argument ~parent_precedence ppf
      left_argument =
    parenthesize_argument_non_associative_operator Precedence.of_term_pattern
      ~parent_precedence pp_term_pattern ppf left_argument

  and pp_infix_non_associative_operator_right_argument ~parent_precedence ppf
      right_argument =
    match right_argument with
    | Term.Pattern.Abstraction _ -> pp_term_pattern ppf right_argument
    | _ ->
      parenthesize_argument_non_associative_operator
        Precedence.of_term_pattern ~parent_precedence pp_term_pattern ppf
        right_argument

  and pp_postfix_operator_argument ~parent_precedence ppf argument =
    match argument with
    | Term.Pattern.Application
        { applicand =
            Term.Pattern.Constant
              { operator = argument_operator; quoted = false; _ }
        ; _
        }
      when Operator.is_postfix argument_operator ->
      pp_term_pattern ppf argument
    | _ ->
      parenthesize_argument_postfix_operator Precedence.of_term_pattern
        ~parent_precedence pp_term_pattern ppf argument

  and pp_substitution_pattern ppf substitution_pattern =
    match substitution_pattern with
    | { Substitution.Pattern.head = Substitution.Pattern.Head.None _
      ; terms = []
      ; _
      } -> Format.fprintf ppf "^"
    | { Substitution.Pattern.head = Substitution.Pattern.Head.Identity _
      ; terms = []
      ; _
      } -> Format.fprintf ppf ".."
    | { Substitution.Pattern.head = Substitution.Pattern.Head.None _
      ; terms
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           pp_term_pattern)
        terms
    | { Substitution.Pattern.head = Substitution.Pattern.Head.Identity _
      ; terms
      ; _
      } ->
      Format.fprintf ppf "@[<2>..,@ %a@]"
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           pp_term_pattern)
        terms
    | { Substitution.Pattern.head =
          Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms = []
      ; _
      } -> Format.fprintf ppf "@[<2>%a@]" Identifier.pp identifier
    | { Substitution.Pattern.head =
          Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms = []
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a[%a]@]" Identifier.pp identifier
        pp_substitution closure
    | { Substitution.Pattern.head =
          Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.None; _ }
      ; terms
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           pp_term_pattern)
        terms
    | { Substitution.Pattern.head =
          Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a[%a],@ %a@]" Identifier.pp identifier
        pp_substitution closure
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           pp_term_pattern)
        terms

  and pp_context_pattern ppf context_pattern =
    let pp_typing ppf (i, t) =
      Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t
    in
    match context_pattern with
    | { Context.Pattern.head = Context.Pattern.Head.None _
      ; bindings = []
      ; _
      } -> Format.fprintf ppf "^"
    | { Context.Pattern.head = Context.Pattern.Head.Hole _
      ; bindings = []
      ; _
      } -> Format.fprintf ppf "_"
    | { Context.Pattern.head =
          Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } -> Format.fprintf ppf "%a" Identifier.pp identifier
    | { Context.Pattern.head = Context.Pattern.Head.None _; bindings; _ } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_typing)
        bindings
    | { Context.Pattern.head = Context.Pattern.Head.Hole _; bindings; _ } ->
      Format.fprintf ppf "@[<2>_,@ %a@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_typing)
        bindings
    | { Context.Pattern.head =
          Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_typing)
        bindings
end
