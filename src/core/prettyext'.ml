(** Pretty-printing for the external syntax. *)

open Support
open Synext'

(** {1 Handling Parentheses}

    Parentheses are re-introduced during pretty-printing using the precedence
    ordering specified in the parser. Operator associativities also need to
    be considered to avoid adding extraneous parentheses. *)

(** [parenthesize pp] is [pp] with the addition of parentheses. *)
let parenthesize pp ppf = Format.fprintf ppf "@[<2>(%a)@]" pp

(** A parenthesizing formatter is a pretty-printer for at term that performs
    an additional check to determine whether to parenthesize the term or not.
    This check is performed by computing the precedence of the term and
    comparing it with the precedence of the parent node in the AST. *)
type ('precedence, 'term) parenthesizing_formatter =
     ('term -> 'precedence)
  -> parent_precedence:'precedence
  -> (Format.formatter -> 'term -> Unit.t)
  -> Format.formatter
  -> 'term
  -> Unit.t

(** Functor for parenthesizing helper formatters. *)
module Make_parenthesizer (Precedence : Ord.ORD) : sig
  (** [parenthesize_term_of_lesser_precedence] is a parenthesizing formatter
      that adds parentheses to the term if it has a strictly lesser
      precedence than the precedence of its parent node in the AST. *)
  val parenthesize_term_of_lesser_precedence :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_term_of_lesser_than_or_equal_precedence] is a
      parenthesizing formatter that adds parentheses to the term if it has a
      lesser than or equal precedence with the precedence of its parent node
      in the AST. *)
  val parenthesize_term_of_lesser_than_or_equal_precedence :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_left_argument_left_associative_operator] is a
      parenthesizing formatter for a term appearing as a left argument to an
      infix left-associative operator. *)
  val parenthesize_left_argument_left_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_right_argument_left_associative_operator] is a
      parenthesizing formatter for a term appearing as a right argument to an
      infix left-associative operator. *)
  val parenthesize_right_argument_left_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_left_argument_right_associative_operator] is a
      parenthesizing formatter for a term appearing as a left argument to an
      infix right-associative operator. *)
  val parenthesize_left_argument_right_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_right_argument_right_associative_operator] is a
      parenthesizing formatter for a term appearing as a right argument to an
      infix right-associative operator. *)
  val parenthesize_right_argument_right_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_argument_non_associative_operator] is a parenthesizing
      formatter for a term appearing as an argument to an infix
      non-associative operator. *)
  val parenthesize_argument_non_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_argument_prefix_operator] is a parenthesizing formatter
      for a term appearing as an argument to a prefix operator. *)
  val parenthesize_argument_prefix_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_argument_postfix_operator] is a parenthesizing formatter
      for a term appearing as an argument to a postifx operator. *)
  val parenthesize_argument_postfix_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** {[
        pp_application ~guard_operator ~guard_operator_application
          ~precedence_of_applicand ~precedence_of_argument ~pp_applicand
          ~pp_argument ~parent_precedence ppf (applicand, arguments)
      ]}

      pretty-prints the application of [applicand] with [arguments] as a
      juxtaposition of terms delimited by whitespaces, with minimal
      parentheses.

      This pretty-printer supports applicands having a type different from
      that of its arguments. This allows for pretty-printing of LF type-level
      applications, which have LF types as applicands and LF terms as
      arguments.

      - [~guard_operator applicand] is [`Operator operator] if [applicand] is
        an unquoted operator, and [`Term] otherwise.
      - [~guard_operator_application argument] is
        [`Operator_application operator] if [argument] is the application of
        an unquoted operator, and [`Term] otherwise.
      - [~precedence_of_applicand applicand] is the precedence of
        [applicand].
      - [~precedence_of_argument argument] is the precedence of [argument].
      - [~pp_applicand] is a pretty-printer for the applicand.
      - [~pp_argument] is a pretty-printer for an argument in the
        application.
      - [~parent_precedence] is the precedence of the AST node parent to
        [applicand] and [arguments], meaning that it is the precedence of the
        application. *)
  val pp_application :
       guard_operator:('applicand -> [ `Term | `Operator of Operator.t ])
    -> guard_operator_application:
         ('argument -> [ `Term | `Operator_application of Operator.t ])
    -> precedence_of_applicand:('applicand -> Precedence.t)
    -> precedence_of_argument:('argument -> Precedence.t)
    -> pp_applicand:(Format.formatter -> 'applicand -> Unit.t)
    -> pp_argument:(Format.formatter -> 'argument -> Unit.t)
    -> parent_precedence:Precedence.t
    -> Format.formatter
    -> 'applicand * 'argument List1.t
    -> Unit.t
end = struct
  type precedence = Precedence.t

  let[@inline] parenthesize_term_of_lesser_precedence precedence
      ~parent_precedence pp ppf argument =
    if Precedence.(precedence argument < parent_precedence) then
      parenthesize pp ppf argument
    else pp ppf argument

  let[@inline] parenthesize_term_of_lesser_than_or_equal_precedence
      precedence ~parent_precedence pp ppf argument =
    if Precedence.(precedence argument <= parent_precedence) then
      parenthesize pp ppf argument
    else pp ppf argument

  let parenthesize_left_argument_left_associative_operator =
    parenthesize_term_of_lesser_precedence

  let parenthesize_right_argument_left_associative_operator =
    parenthesize_term_of_lesser_than_or_equal_precedence

  let parenthesize_left_argument_right_associative_operator =
    parenthesize_term_of_lesser_than_or_equal_precedence

  let parenthesize_right_argument_right_associative_operator =
    parenthesize_term_of_lesser_precedence

  let parenthesize_argument_non_associative_operator =
    parenthesize_term_of_lesser_than_or_equal_precedence

  let parenthesize_argument_prefix_operator =
    parenthesize_term_of_lesser_than_or_equal_precedence

  let parenthesize_argument_postfix_operator =
    parenthesize_term_of_lesser_precedence

  let rec pp_application ~guard_operator ~guard_operator_application
      ~precedence_of_applicand ~precedence_of_argument ~pp_applicand
      ~pp_argument ~parent_precedence ppf (applicand, arguments) =
    match guard_operator applicand with
    | `Term ->
      (* The applicand is not an unquoted operator, so the application is in
         prefix notation. *)
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_term_of_lesser_than_or_equal_precedence
           precedence_of_applicand ~parent_precedence pp_applicand)
        applicand
        (List1.pp ~pp_sep:Format.pp_print_space
           (parenthesize_term_of_lesser_than_or_equal_precedence
              precedence_of_argument ~parent_precedence pp_argument))
        arguments
    | `Operator operator ->
      (* The applicand is an unquoted operator, so pretty-printing must
         handle the operator fixity, associativity and precedence. *)
      pp_operator_application ~guard_operator_application
        ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
        applicand operator arguments ppf

  and pp_operator_application ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand operator arguments ppf =
    match Operator.fixity operator with
    | Fixity.Prefix ->
      pp_prefix_operator_application ~precedence_of_argument ~pp_applicand
        ~pp_argument ~parent_precedence applicand arguments ppf
    | Fixity.Infix ->
      assert (
        List1.compare_length_with arguments 2
        = 0 (* The arguments list must have exactly two elements *));
      let[@warning "-8"] (List1.T (left_argument, [ right_argument ])) =
        arguments
      in
      pp_infix_operator_application ~guard_operator_application
        ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
        applicand operator ~left_argument ~right_argument ppf
    | Fixity.Postfix ->
      assert (
        List1.compare_length_with arguments 1
        = 0 (* The arguments list must have exactly one element *));
      let[@warning "-8"] (List1.T (argument, [])) = arguments in
      pp_postfix_operator_application ~guard_operator_application
        ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
        applicand argument ppf

  and pp_prefix_operator_application ~precedence_of_argument ~pp_applicand
      ~pp_argument ~parent_precedence applicand arguments ppf =
    Format.fprintf ppf "@[<2>%a@ %a@]" pp_applicand applicand
      (List1.pp ~pp_sep:Format.pp_print_space
         (parenthesize_argument_prefix_operator precedence_of_argument
            ~parent_precedence pp_argument))
      arguments

  and pp_postfix_operator_application ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand argument ppf =
    Format.fprintf ppf "@[<2>%a@ %a@]"
      (pp_postfix_operator_argument ~guard_operator_application
         ~precedence_of_argument ~pp_argument ~parent_precedence)
      argument pp_applicand applicand

  and pp_infix_operator_application ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand operator ~left_argument ~right_argument ppf =
    match Operator.associativity operator with
    | Associativity.Left_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_left_associative_operator_left_argument
           ~guard_operator_application ~precedence_of_argument ~pp_argument
           ~parent_precedence operator)
        left_argument pp_applicand applicand
        (pp_infix_left_associative_operator_right_argument
           ~guard_operator_application ~precedence_of_argument ~pp_argument
           ~parent_precedence operator)
        right_argument
    | Associativity.Right_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_right_associative_operator_left_argument
           ~guard_operator_application ~precedence_of_argument ~pp_argument
           ~parent_precedence operator)
        left_argument pp_applicand applicand
        (pp_infix_right_associative_operator_right_argument
           ~guard_operator_application ~precedence_of_argument ~pp_argument
           ~parent_precedence operator)
        right_argument
    | Associativity.Non_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_non_associative_operator_left_argument
           ~precedence_of_argument ~pp_argument ~parent_precedence)
        left_argument pp_applicand applicand
        (pp_infix_non_associative_operator_right_argument
           ~precedence_of_argument ~pp_argument ~parent_precedence)
        right_argument

  and pp_infix_left_associative_operator_left_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator ppf left_argument =
    match guard_operator_application left_argument with
    | `Term ->
      parenthesize_left_argument_left_associative_operator
        precedence_of_argument ~parent_precedence pp_argument ppf
        left_argument
    | `Operator_application left_argument_operator ->
      if
        Operator.is_right_associative left_argument_operator
        && Operator.precedence left_argument_operator
           = Operator.precedence applicand_operator
      then (parenthesize pp_argument) ppf left_argument
        (* The applications of left and right-associative operators of the
           same precedence must be parenthesized, otherwise the expression is
           ambiguous. *)
      else
        parenthesize_left_argument_left_associative_operator
          precedence_of_argument ~parent_precedence pp_argument ppf
          left_argument

  and pp_infix_left_associative_operator_right_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator ppf right_argument =
    match guard_operator_application right_argument with
    | `Term ->
      parenthesize_right_argument_left_associative_operator
        precedence_of_argument ~parent_precedence pp_argument ppf
        right_argument
    | `Operator_application right_argument_operator ->
      if
        Operator.is_right_associative right_argument_operator
        && Operator.precedence right_argument_operator
           = Operator.precedence applicand_operator
      then (parenthesize pp_argument) ppf right_argument
        (* The applications of left and right-associative operators of the
           same precedence must be parenthesized, otherwise the expression is
           ambiguous. *)
      else
        parenthesize_right_argument_left_associative_operator
          precedence_of_argument ~parent_precedence pp_argument ppf
          right_argument

  and pp_infix_right_associative_operator_left_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator ppf left_argument =
    match guard_operator_application left_argument with
    | `Term ->
      parenthesize_left_argument_right_associative_operator
        precedence_of_argument ~parent_precedence pp_argument ppf
        left_argument
    | `Operator_application left_argument_operator ->
      if
        Operator.is_left_associative left_argument_operator
        && Operator.precedence left_argument_operator
           = Operator.precedence applicand_operator
      then (parenthesize pp_argument) ppf left_argument
        (* The applications of left and right-associative operators of the
           same precedence must be parenthesized, otherwise the expression is
           ambiguous. *)
      else
        parenthesize_left_argument_right_associative_operator
          precedence_of_argument ~parent_precedence pp_argument ppf
          left_argument

  and pp_infix_right_associative_operator_right_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator ppf right_argument =
    match guard_operator_application right_argument with
    | `Term ->
      parenthesize_right_argument_right_associative_operator
        precedence_of_argument ~parent_precedence pp_argument ppf
        right_argument
    | `Operator_application right_argument_operator ->
      if
        Operator.is_left_associative right_argument_operator
        && Operator.precedence right_argument_operator
           = Operator.precedence applicand_operator
      then (parenthesize pp_argument) ppf right_argument
        (* The applications of left and right-associative operators of the
           same precedence must be parenthesized, otherwise the expression is
           ambiguous. *)
      else
        parenthesize_right_argument_right_associative_operator
          precedence_of_argument ~parent_precedence pp_argument ppf
          right_argument

  and pp_infix_non_associative_operator_left_argument ~precedence_of_argument
      ~pp_argument ~parent_precedence ppf left_argument =
    parenthesize_argument_non_associative_operator precedence_of_argument
      ~parent_precedence pp_argument ppf left_argument

  and pp_infix_non_associative_operator_right_argument
      ~precedence_of_argument ~pp_argument ~parent_precedence ppf
      right_argument =
    parenthesize_argument_non_associative_operator precedence_of_argument
      ~parent_precedence pp_argument ppf right_argument

  and pp_postfix_operator_argument ~guard_operator_application
      ~precedence_of_argument ~pp_argument ~parent_precedence ppf argument =
    match guard_operator_application argument with
    | `Term ->
      parenthesize_argument_postfix_operator precedence_of_argument
        ~parent_precedence pp_argument ppf argument
    | `Operator_application operator ->
      if Operator.is_postfix operator then pp_argument ppf argument
      else
        parenthesize_argument_postfix_operator precedence_of_argument
          ~parent_precedence pp_argument ppf argument
end

(** {1 Printing LF Kinds, Types and Terms} *)
module LF = struct
  open LF

  (** Precedence computations on LF kinds, types and terms.

      The values used as precedence levels are defined based on the recursive
      descent parsers in {!Parser}. *)
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
            if application_precedence <= y then -1 else 1
          | Static x, User_defined _ ->
            if x < application_precedence then -1 else 1
      end) :
        Ord.ORD with type t := t)
  end

  include Make_parenthesizer (Precedence)

  let rec pp_kind ppf kind =
    let parent_precedence = Precedence.of_kind kind in
    match kind with
    | Kind.Typ _ -> Format.fprintf ppf "type"
    | Kind.Arrow { domain; range; _ } ->
      (* Right arrows are right-associative *)
      Format.fprintf ppf "@[<2>%a →@ %a@]"
        (parenthesize_left_argument_right_associative_operator
           Precedence.of_typ ~parent_precedence pp_typ)
        domain pp_kind range
    | Kind.Pi { parameter_identifier; parameter_type; body; _ } -> (
      (* Pi-operators are weak prefix operators *)
      match parameter_identifier with
      | Option.None ->
        Format.fprintf ppf "@[<2>{@ _ :@ %a@ }@ %a@]" pp_typ parameter_type
          pp_kind body
      | Option.Some parameter_identifier ->
        Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]" Identifier.pp
          parameter_identifier pp_typ parameter_type pp_kind body)

  and pp_typ ppf typ =
    let parent_precedence = Precedence.of_typ typ in
    match typ with
    | Typ.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
      else QualifiedIdentifier.pp ppf identifier
    | Typ.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | Typ.Constant { operator; quoted = false; _ } ->
            `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | Term.Application
              { applicand = Term.Constant { operator; quoted = false; _ }
              ; _
              } -> `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:Precedence.of_typ
        ~precedence_of_argument:Precedence.of_term ~pp_applicand:pp_typ
        ~pp_argument:pp_term ~parent_precedence ppf (applicand, arguments)
    | Typ.Arrow { domain; range; orientation = `Forward; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows, so backward arrows have to be parenthesized *)
      Format.fprintf ppf "@[<2>%a →@ %a@]"
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
         forward arrows, so forward arrows have to be parenthesized *)
      Format.fprintf ppf "@[<2>%a@ ← %a@]"
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
      (* Pi-operators are weak prefix operators *)
      Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]"
        (fun ppf -> function
          | Option.Some parameter_identifier ->
            Identifier.pp ppf parameter_identifier
          | Option.None -> Format.fprintf ppf "_")
        parameter_identifier pp_typ parameter_type pp_typ body

  and pp_term ppf term =
    let parent_precedence = Precedence.of_term term in
    match term with
    | Term.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Term.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
    | Term.Constant { identifier; quoted = false; _ } ->
      QualifiedIdentifier.pp ppf identifier
    | Term.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | Term.Constant { operator; quoted = false; _ } ->
            `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | Term.Application
              { applicand = Term.Constant { operator; quoted = false; _ }
              ; _
              } -> `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:Precedence.of_term
        ~precedence_of_argument:Precedence.of_term ~pp_applicand:pp_term
        ~pp_argument:pp_term ~parent_precedence ppf (applicand, arguments)
    | Term.Abstraction { parameter_identifier; parameter_type; body; _ } -> (
      (* Lambdas are weak prefix operators, so the body of the lambda never
         requires parentheses *)
      match (parameter_identifier, parameter_type) with
      | Option.None, Option.None ->
        Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term body
      | Option.None, Option.Some parameter_type ->
        Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type pp_term
          body
      | Option.Some parameter_identifier, Option.None ->
        Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
          parameter_identifier pp_term body
      | Option.Some parameter_identifier, Option.Some parameter_type ->
        Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
          parameter_identifier pp_typ parameter_type pp_term body)
    | Term.Wildcard _ -> Format.fprintf ppf "_"
    | Term.TypeAnnotated { term; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term ~parent_precedence pp_term)
        term pp_typ typ
end

(** {1 Printing Contextual LF Types, Terms, Type Patterns and Term Patterns} *)
module CLF = struct
  open CLF

  (** Precedence computations on contextual LF types, terms and patterns.

      The values used as precedence levels are defined based on the recursive
      descent parsers in {!Parser}. *)
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
      | Term.Variable _
      | Term.Parameter_variable _
      | Term.Substitution_variable _
      | Term.Constant _
      | Term.Hole _
      | Term.Tuple _ -> Static 8

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
      | Term.Pattern.Parameter_variable _
      | Term.Pattern.Substitution_variable _
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
            if application_precedence <= y then -1 else 1
          | Static x, User_defined _ ->
            if x < application_precedence then -1 else 1
      end) :
        Ord.ORD with type t := t)
  end

  include Make_parenthesizer (Precedence)

  let rec pp_typ ppf typ =
    let parent_precedence = Precedence.of_typ typ in
    match typ with
    | Typ.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
      else QualifiedIdentifier.pp ppf identifier
    | Typ.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | Typ.Constant { operator; quoted = false; _ } ->
            `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | Term.Application
              { applicand = Term.Constant { operator; quoted = false; _ }
              ; _
              } -> `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:Precedence.of_typ
        ~precedence_of_argument:Precedence.of_term ~pp_applicand:pp_typ
        ~pp_argument:pp_term ~parent_precedence ppf (applicand, arguments)
    | Typ.Arrow { domain; range; orientation = `Forward; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows, so backward arrows have to be parenthesized *)
      Format.fprintf ppf "@[<2>%a →@ %a@]"
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
         forward arrows, so forward arrows have to be parenthesized *)
      Format.fprintf ppf "@[<2>%a@ ← %a@]"
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
      (* Pi-operators are weak prefix operators *)
      Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]"
        (fun ppf -> function
          | Option.Some parameter_identifier ->
            Identifier.pp ppf parameter_identifier
          | Option.None -> Format.fprintf ppf "_")
        parameter_identifier pp_typ parameter_type pp_typ body
    | Typ.Block { elements = `Unnamed typ; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]" pp_typ typ
    | Typ.Block { elements = `Record nts; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]"
        (List1.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
             Format.fprintf ppf "%a :@ %a" Identifier.pp i pp_typ t))
        nts

  and pp_term ppf term =
    let parent_precedence = Precedence.of_term term in
    match term with
    | Term.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Term.Parameter_variable { identifier; _ } ->
      Identifier.pp ppf identifier
    | Term.Substitution_variable { identifier; _ } ->
      Identifier.pp ppf identifier
    | Term.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
    | Term.Constant { identifier; quoted = false; _ } ->
      QualifiedIdentifier.pp ppf identifier
    | Term.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | Term.Constant { operator; quoted = false; _ } ->
            `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | Term.Application
              { applicand = Term.Constant { operator; quoted = false; _ }
              ; _
              } -> `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:Precedence.of_term
        ~precedence_of_argument:Precedence.of_term ~pp_applicand:pp_term
        ~pp_argument:pp_term ~parent_precedence ppf (applicand, arguments)
    | Term.Abstraction { parameter_identifier; parameter_type; body; _ } -> (
      (* Lambdas are weak prefix operators, so the body of a lambda does not
         need to be parenthesized *)
      match (parameter_identifier, parameter_type) with
      | Option.None, Option.None ->
        Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term body
      | Option.None, Option.Some parameter_type ->
        Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type pp_term
          body
      | Option.Some parameter_identifier, Option.None ->
        Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
          parameter_identifier pp_term body
      | Option.Some parameter_identifier, Option.Some parameter_type ->
        Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
          parameter_identifier pp_typ parameter_type pp_term body)
    | Term.Hole { variant = `Underscore; _ } -> Format.fprintf ppf "_"
    | Term.Hole { variant = `Unlabelled; _ } -> Format.fprintf ppf "?"
    | Term.Hole { variant = `Labelled label; _ } ->
      Format.fprintf ppf "?%a" Identifier.pp label
    | Term.Substitution { term; substitution; _ } ->
      (* Substitutions are left-associative *)
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
      Format.fprintf ppf "@[<2>%a :@ %a@]"
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
        (List.pp ~pp_sep:Format.comma pp_term)
        terms
    | { Substitution.head = Substitution.Head.Identity _; terms; _ } ->
      Format.fprintf ppf "@[<2>..,@ %a@]"
        (List.pp ~pp_sep:Format.comma pp_term)
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
        (List.pp ~pp_sep:Format.comma pp_term)
        terms
    | { Substitution.head =
          Substitution.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a[%a],@ %a@]" Identifier.pp identifier
        pp_substitution closure
        (List.pp ~pp_sep:Format.comma pp_term)
        terms

  and pp_context ppf context =
    let pp_typing ppf typing =
      match typing with
      | identifier, Option.None -> Identifier.pp ppf identifier
      | identifier, Option.Some typ ->
        Format.fprintf ppf "%a :@ %a" Identifier.pp identifier pp_typ typ
    in
    match context with
    | { Context.head = Context.Head.None _; bindings = []; _ } ->
      Format.fprintf ppf "^"
    | { Context.head = Context.Head.Hole _; bindings = []; _ } ->
      Format.fprintf ppf "_"
    | { Context.head = Context.Head.Context_variable { identifier; _ }
      ; bindings = []
      ; _
      } -> Identifier.pp ppf identifier
    | { Context.head = Context.Head.None _; bindings; _ } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings
    | { Context.head = Context.Head.Hole _; bindings; _ } ->
      Format.fprintf ppf "@[<2>_,@ %a@]"
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings
    | { Context.head = Context.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings

  let rec pp_term_pattern ppf term =
    let parent_precedence = Precedence.of_term_pattern term in
    match term with
    | Term.Pattern.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Term.Pattern.Parameter_variable { identifier; _ } ->
      Identifier.pp ppf identifier
    | Term.Pattern.Substitution_variable { identifier; _ } ->
      Identifier.pp ppf identifier
    | Term.Pattern.Constant { identifier; quoted = true; _ } ->
      Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
    | Term.Pattern.Constant { identifier; quoted = false; _ } ->
      QualifiedIdentifier.pp ppf identifier
    | Term.Pattern.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | Term.Pattern.Constant { operator; quoted = false; _ } ->
            `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | Term.Pattern.Application
              { applicand =
                  Term.Pattern.Constant { operator; quoted = false; _ }
              ; _
              } -> `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:Precedence.of_term_pattern
        ~precedence_of_argument:Precedence.of_term_pattern
        ~pp_applicand:pp_term_pattern ~pp_argument:pp_term_pattern
        ~parent_precedence ppf (applicand, arguments)
    | Term.Pattern.Abstraction
        { parameter_identifier; parameter_type; body; _ } -> (
      (* Lambdas are weak prefix operators, so the body of a lambda never
         requires parentheses. *)
      match (parameter_identifier, parameter_type) with
      | Option.None, Option.None ->
        Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term_pattern body
      | Option.None, Option.Some parameter_type ->
        Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type
          pp_term_pattern body
      | Option.Some parameter_identifier, Option.None ->
        Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
          parameter_identifier pp_term_pattern body
      | Option.Some parameter_identifier, Option.Some parameter_type ->
        Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
          parameter_identifier pp_typ parameter_type pp_term_pattern body)
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
      Format.fprintf ppf "@[<2>%a :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_term_pattern ~parent_precedence pp_term_pattern)
        term pp_typ typ

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
        (List.pp ~pp_sep:Format.comma pp_term_pattern)
        terms
    | { Substitution.Pattern.head = Substitution.Pattern.Head.Identity _
      ; terms
      ; _
      } ->
      Format.fprintf ppf "@[<2>..,@ %a@]"
        (List.pp ~pp_sep:Format.comma pp_term_pattern)
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
        (List.pp ~pp_sep:Format.comma pp_term_pattern)
        terms
    | { Substitution.Pattern.head =
          Substitution.Pattern.Head.Substitution_variable
            { identifier; closure = Option.Some closure; _ }
      ; terms
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a[%a],@ %a@]" Identifier.pp identifier
        pp_substitution closure
        (List.pp ~pp_sep:Format.comma pp_term_pattern)
        terms

  and pp_context_pattern ppf context_pattern =
    let pp_typing ppf (i, t) =
      Format.fprintf ppf "%a :@ %a" Identifier.pp i pp_typ t
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
      } -> Identifier.pp ppf identifier
    | { Context.Pattern.head = Context.Pattern.Head.None _; bindings; _ } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings
    | { Context.Pattern.head = Context.Pattern.Head.Hole _; bindings; _ } ->
      Format.fprintf ppf "@[<2>_,@ %a@]"
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings
    | { Context.Pattern.head =
          Context.Pattern.Head.Context_variable { identifier; _ }
      ; bindings
      ; _
      } ->
      Format.fprintf ppf "@[<2>%a,@ %a@]" Identifier.pp identifier
        (List.pp ~pp_sep:Format.comma pp_typing)
        bindings
end

(** {1 Printing Meta-Types, Meta-Objects, Meta-Patterns, Meta-Contexts} *)
module Meta = struct
  open Meta

  (** Precedence computations on context schemas.

      The values used as precedence levels are defined based on the recursive
      descent parsers in {!Parser}. *)
  module Precedence : sig
    type t

    val of_schema : Schema.t -> t

    include Ord.ORD with type t := t
  end = struct
    type t = Static of Int.t [@unboxed]

    let of_schema schema =
      match schema with
      | Schema.Alternation _ -> Static 1
      | Schema.Constant _ | Schema.Element _ -> Static 2

    include (
      Ord.Make (struct
        type nonrec t = t

        let compare (Static x) (Static y) = Int.compare x y
      end) :
        Ord.ORD with type t := t)
  end

  include Make_parenthesizer (Precedence)

  let rec pp_typ ppf typ =
    match typ with
    | Typ.Context_schema { schema; _ } -> pp_schema ppf schema
    | Typ.Contextual_typ { context; typ; _ } ->
      Format.fprintf ppf "@[<2>(%a@ ⊢@ %a)@]" CLF.pp_context context
        CLF.pp_typ typ
    | Typ.Parameter_typ { context; typ; _ } ->
      Format.fprintf ppf "@[<2>#(%a@ ⊢@ %a)@]" CLF.pp_context context
        CLF.pp_typ typ
    | Typ.Plain_substitution_typ { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$(%a@ ⊢@ %a)@]" CLF.pp_context domain
        CLF.pp_context range
    | Typ.Renaming_substitution_typ { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$(%a@ ⊢#@ %a)@]" CLF.pp_context domain
        CLF.pp_context range

  and pp_object ppf object_ =
    match object_ with
    | Object.Context { context; _ } ->
      Format.fprintf ppf "@[[%a]@]" CLF.pp_context context
    | Object.Contextual_term { context; term; _ } ->
      Format.fprintf ppf "@[<2>[%a@ ⊢@ %a]@]" CLF.pp_context context
        CLF.pp_term term
    | Object.Plain_substitution { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$[%a@ ⊢@ %a]@]" CLF.pp_context domain
        CLF.pp_substitution range
    | Object.Renaming_substitution { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$[%a@ ⊢#@ %a]@]" CLF.pp_context domain
        CLF.pp_substitution range

  and pp_pattern ppf pattern =
    match pattern with
    | Pattern.Context { context; _ } ->
      Format.fprintf ppf "@[[%a]@]" CLF.pp_context_pattern context
    | Pattern.Contextual_term { context; term; _ } ->
      Format.fprintf ppf "@[<2>[%a@ ⊢@ %a]@]" CLF.pp_context_pattern context
        CLF.pp_term_pattern term
    | Pattern.Plain_substitution { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$[%a@ ⊢@ %a]@]" CLF.pp_context_pattern domain
        CLF.pp_substitution_pattern range
    | Pattern.Renaming_substitution { domain; range; _ } ->
      Format.fprintf ppf "@[<2>$[%a@ ⊢#@ %a]@]" CLF.pp_context_pattern domain
        CLF.pp_substitution_pattern range

  and pp_context ppf context =
    let { Context.bindings; _ } = context in
    List.pp ~pp_sep:Format.comma
      (fun ppf (i, t) ->
        Format.fprintf ppf "@[%a :@ %a@]" Identifier.pp i pp_typ t)
      ppf bindings

  and pp_schema ppf schema =
    let parent_precedence = Precedence.of_schema schema in
    let pp_bindings =
      List1.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
          Format.fprintf ppf "@[%a :@ %a@]" Identifier.pp i CLF.pp_typ t)
    in
    match schema with
    | Schema.Constant { identifier; _ } ->
      QualifiedIdentifier.pp ppf identifier
    | Schema.Alternation { schemas; _ } ->
      List2.pp
        ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ +@ ")
        (parenthesize_term_of_lesser_than_or_equal_precedence
           Precedence.of_schema ~parent_precedence pp_schema)
        ppf schemas
    | Schema.Element { some = Option.None; block = `Unnamed t; _ } ->
      Format.fprintf ppf "@[<2>block@ %a@]" CLF.pp_typ t
    | Schema.Element { some = Option.None; block = `Record bindings; _ } ->
      Format.fprintf ppf "@[<2>block@ (%a)@]" pp_bindings bindings
    | Schema.Element
        { some = Option.Some some_bindings; block = `Unnamed t; _ } ->
      Format.fprintf ppf "@[<2>some@ [%a]@ block@ %a@]" pp_bindings
        some_bindings CLF.pp_typ t
    | Schema.Element
        { some = Option.Some some_bindings
        ; block = `Record block_bindings
        ; _
        } ->
      Format.fprintf ppf "@[<2>some@ [%a]@ block@ (%a)@]" pp_bindings
        some_bindings pp_bindings block_bindings
end

(** Pretty-printing for computation-level syntax. *)
module Comp = struct
  open Comp

  (** Precedence computations on computation-level kinds, types, expressions
      and patterns.

      The values used as precedence levels are defined based on the recursive
      descent parsers in {!Parser}. *)
  module Precedence : sig
    type t

    val of_kind : Kind.t -> t

    val of_typ : Typ.t -> t

    val of_expression : Expression.t -> t

    val of_pattern : Pattern.t -> t

    include Ord.ORD with type t := t
  end = struct
    type t =
      | Static of Int.t
      | User_defined_type of Int.t
      | User_defined_expression of Int.t

    let type_application_precedence = 4

    let expression_application_precedence = 2

    let of_kind kind =
      match kind with
      | Kind.Pi _ -> Static 1
      | Kind.Arrow _ -> Static 2
      | Kind.Ctype _ -> Static 5

    let of_typ typ =
      match typ with
      | Typ.Pi _ -> Static 1
      | Typ.Arrow _ -> Static 2
      | Typ.Cross _ -> Static 3
      | Typ.Application { applicand = Typ.Constant { operator; _ }; _ }
        when Operator.is_prefix operator
             (* Juxtapositions are of higher precedence than user-defined
                operators *) -> Static type_application_precedence
      | Typ.Application
          { applicand = Typ.Constant { operator; quoted = false; _ }; _ }
      (* User-defined operator application *) ->
        User_defined_type (Operator.precedence operator)
      | Typ.Constant _ | Typ.Box _ -> Static 5

    let of_expression expression =
      match expression with
      | Expression.TypeAnnotated _ -> Static 1
      | Expression.Application
          { applicand = Expression.Constant { operator; _ }; _ }
        when Operator.is_prefix operator
             (* Juxtapositions are of higher precedence than user-defined
                operators *) -> Static expression_application_precedence
      | Expression.Application
          { applicand = Expression.Constant { operator; quoted = false; _ }
          ; _
          }
      (* User-defined operator application *) ->
        User_defined_expression (Operator.precedence operator)
      | Expression.Let _
      | Expression.Box _
      | Expression.Impossible _
      | Expression.Case _
      | Expression.Tuple _
      | Expression.Hole _
      | Expression.BoxHole _
      | Expression.Observation _
      | Expression.Variable _
      | Expression.Constant _
      | Expression.Fn _
      | Expression.Mlam _
      | Expression.Fun _ -> Static 3

    let of_pattern pattern =
      match pattern with
      | Pattern.MetaTypeAnnotated _ -> Static 1
      | Pattern.TypeAnnotated _ -> Static 2
      | Pattern.Observation _ | Pattern.Application _ -> Static 3
      | Pattern.Variable _
      | Pattern.Constant _
      | Pattern.MetaObject _
      | Pattern.Tuple _
      | Pattern.Wildcard _ -> Static 4

    include (
      Ord.Make (struct
        type nonrec t = t

        let compare x y =
          match (x, y) with
          | Static x, Static y -> Int.compare x y
          | User_defined_type x, User_defined_type y -> Int.compare x y
          | User_defined_type _, Static y ->
            if type_application_precedence <= y then -1 else 1
          | Static x, User_defined_type _ ->
            if x < type_application_precedence then -1 else 1
          | User_defined_expression x, User_defined_expression y ->
            Int.compare x y
          | User_defined_expression _, Static y ->
            if expression_application_precedence <= y then -1 else 1
          | Static x, User_defined_expression _ ->
            if x < expression_application_precedence then -1 else 1
          | _ ->
            Error.violation
              "[Precedence.compare] cannot compare precedences for \
               user-defined type and expression constants"
      end) :
        Ord.ORD with type t := t)
  end

  include Make_parenthesizer (Precedence)

  (** [is_atomic_pattern pattern] is [true] if and only if [pattern] is an
      atomic pattern as defined in {!Parser}, meaning that it never requires
      additional enclosing parentheses during printing to avoid ambiguities. *)
  let is_atomic_pattern pattern =
    match pattern with
    | Pattern.Variable _
    | Pattern.Constant _
    | Pattern.MetaObject _
    | Pattern.Tuple _
    | Pattern.Wildcard _ -> true
    | _ -> false

  let rec pp_kind ppf kind =
    let parent_precedence = Precedence.of_kind kind in
    match kind with
    | Kind.Ctype _ -> Format.pp_print_string ppf "ctype"
    | Kind.Arrow { domain; range; _ } ->
      (* Right arrows are right-associative *)
      Format.fprintf ppf "@[<2>%a@ →@ %a@]"
        (parenthesize_left_argument_right_associative_operator
           Precedence.of_typ ~parent_precedence pp_typ)
        domain pp_kind range
    | Kind.Pi { parameter_identifier; parameter_type; body; _ } -> (
      (* Pi-operators are weak prefix operators *)
      match parameter_identifier with
      | Option.None ->
        Format.fprintf ppf "@[<2>{@ _ :@ %a@ }@ %a@]" Meta.pp_typ
          parameter_type pp_kind body
      | Option.Some parameter_identifier ->
        Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]" Identifier.pp
          parameter_identifier Meta.pp_typ parameter_type pp_kind body)

  and pp_typ ppf typ =
    let parent_precedence = Precedence.of_typ typ in
    match typ with
    | Typ.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
      else QualifiedIdentifier.pp ppf identifier
    | Typ.Pi { parameter_identifier; plicity; parameter_type; body; _ } -> (
      (* Pi-operators are weak prefix operators *)
      let pp_parameter_identifier parameter_type ppf parameter_identifier =
        match (parameter_identifier, parameter_type) with
        | Option.Some parameter_identifier, _ ->
          Identifier.pp ppf parameter_identifier
        | ( Option.None
          , ( Synext'.Meta.Typ.Context_schema _
            | Synext'.Meta.Typ.Contextual_typ _ ) ) ->
          Format.pp_print_string ppf "_"
        | Option.None, Synext'.Meta.Typ.Parameter_typ _ ->
          Format.pp_print_string ppf "#_"
        | ( Option.None
          , ( Synext'.Meta.Typ.Plain_substitution_typ _
            | Synext'.Meta.Typ.Renaming_substitution_typ _ ) ) ->
          Format.pp_print_string ppf "$_"
      in
      match plicity with
      | Plicity.Implicit ->
        Format.fprintf ppf "@[<2>(@ %a :@ %a@ )@ %a@]"
          (pp_parameter_identifier parameter_type)
          parameter_identifier Meta.pp_typ parameter_type pp_typ body
      | Plicity.Explicit ->
        Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]"
          (pp_parameter_identifier parameter_type)
          parameter_identifier Meta.pp_typ parameter_type pp_typ body)
    | Typ.Arrow { domain; range; orientation = `Forward; _ } ->
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows *)
      Format.fprintf ppf "@[<2>%a →@ %a@]"
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
      Format.fprintf ppf "@[<2>%a@ ← %a@]"
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
    | Typ.Cross { types; _ } ->
      List2.pp
        ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ * ")
        (parenthesize_term_of_lesser_than_or_equal_precedence
           Precedence.of_typ ~parent_precedence pp_typ)
        ppf types
    | Typ.Box { meta_type; _ } -> Meta.pp_typ ppf meta_type
    | Typ.Application { applicand; arguments; _ } -> (
      match applicand with
      | Typ.Application
          { applicand =
              Typ.Constant { identifier; operator; quoted = false; _ }
          ; _
          } -> (
        match Operator.fixity operator with
        | Fixity.Prefix ->
          Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp
            identifier
            (List1.pp ~pp_sep:Format.pp_print_space Meta.pp_object)
            arguments
        | Fixity.Infix ->
          assert (
            List1.compare_length_with arguments 2
            = 0
              (* Infix operators must be applied with exactly two
                 arguments. *));
          let[@warning "-8"] (List1.T (left_argument, [ right_argument ])) =
            arguments
          in
          Format.fprintf ppf "@[<2>%a@ %a@ %a@]" Meta.pp_object left_argument
            QualifiedIdentifier.pp identifier Meta.pp_object right_argument
        | Fixity.Postfix ->
          assert (
            List1.compare_length_with arguments 1
            = 0
              (* Postfix operators must be applied with exactly one
                 argument. *));
          let[@warning "-8"] (List1.T (argument, [])) = arguments in
          Format.fprintf ppf "@[<2>%a@ %a@]" Meta.pp_object argument
            QualifiedIdentifier.pp identifier)
      | _ ->
        Format.fprintf ppf "@[<2>%a@ %a@]"
          (parenthesize_term_of_lesser_than_or_equal_precedence
             Precedence.of_typ ~parent_precedence pp_typ)
          applicand
          (List1.pp ~pp_sep:Format.pp_print_space Meta.pp_object)
          arguments)

  and pp_expression ppf expression =
    let parent_precedence = Precedence.of_expression expression in
    match expression with
    | Expression.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Expression.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
      else QualifiedIdentifier.pp ppf identifier
    | Expression.Fn { parameters; body; _ } ->
      let pp_parameter ppf parameter =
        match parameter with
        | Option.None -> Format.pp_print_string ppf "_"
        | Option.Some parameter -> Identifier.pp ppf parameter
      in
      Format.fprintf ppf "@[<2>fn@ %a =>@ %a@]"
        (List1.pp ~pp_sep:Format.pp_print_space pp_parameter)
        parameters pp_expression body
    | Expression.Mlam { parameters; body; _ } ->
      let pp_parameter ppf (parameter, modifier) =
        match (parameter, modifier) with
        | Option.Some parameter, _ -> Identifier.pp ppf parameter
        | Option.None, `Plain -> Format.pp_print_string ppf "_"
        | Option.None, `Hash -> Format.pp_print_string ppf "#_"
        | Option.None, `Dollar -> Format.pp_print_string ppf "$_"
      in
      let pp_parameters =
        List1.pp ~pp_sep:Format.pp_print_space pp_parameter
      in
      Format.fprintf ppf "@[<2>mlam@ %a =>@ %a@]" pp_parameters parameters
        pp_expression body
    | Expression.Fun { branches; _ } ->
      let pp_branch_pattern ppf pattern =
        if is_atomic_pattern pattern then pp_pattern ppf pattern
        else parenthesize pp_pattern ppf pattern
      in
      let pp_branch_patterns =
        List1.pp ~pp_sep:Format.pp_print_space pp_branch_pattern
      in
      let pp_branch ppf (patterns, expression) =
        Format.fprintf ppf "@[<hov 2>|@ %a =>@ %a@]" pp_branch_patterns
          patterns pp_expression expression
      in
      let pp_branches = List1.pp ~pp_sep:Format.pp_print_cut pp_branch in
      Format.fprintf ppf "@[<2>fun@;%a@]" pp_branches branches
    | Expression.Let { pattern; scrutinee; body; _ } ->
      Format.fprintf ppf "@[<2>let@ %a =@ %a@ in@ %a@]" pp_pattern pattern
        pp_expression scrutinee pp_expression body
    | Expression.Box { meta_object; _ } -> Meta.pp_object ppf meta_object
    | Expression.Impossible { scrutinee; _ } ->
      (* [impossible (impossible (...))] is right-associative *)
      Format.fprintf ppf "@[<2>impossible@ %a@]"
        (parenthesize_right_argument_right_associative_operator
           Precedence.of_expression ~parent_precedence pp_expression)
        scrutinee
    | Expression.Case { scrutinee; check_coverage; branches; _ } ->
      let pp_branch ppf (pattern, expression) =
        Format.fprintf ppf "@[<hov 2>|@ %a =>@ %a@]" pp_pattern pattern
          pp_expression expression
      in
      let pp_branches = List1.pp ~pp_sep:Format.pp_print_cut pp_branch in
      if check_coverage then
        Format.fprintf ppf "@[case@ %a@ --not@ of@;%a@]" pp_expression
          scrutinee pp_branches branches
      else
        Format.fprintf ppf "@[case@ %a@ of@;%a@]" pp_expression scrutinee
          pp_branches branches
    | Expression.Tuple { elements; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]"
        (List2.pp ~pp_sep:Format.comma pp_expression)
        elements
    | Expression.Hole { label; _ } -> (
      match label with
      | Option.None -> Format.pp_print_string ppf "?"
      | Option.Some label -> Format.fprintf ppf "?%a" Identifier.pp label)
    | Expression.BoxHole _ -> Format.pp_print_string ppf "_"
    | Expression.Observation { observation; arguments; _ } -> (
      match List1.of_list arguments with
      | Option.None ->
        Format.fprintf ppf ".%a" QualifiedIdentifier.pp observation
      | Option.Some arguments ->
        Format.fprintf ppf ".%a@ %a" QualifiedIdentifier.pp observation
          (List1.pp ~pp_sep:Format.pp_print_space
             (parenthesize_argument_prefix_operator Precedence.of_expression
                ~parent_precedence pp_expression))
          arguments)
    | Expression.TypeAnnotated { expression; typ; _ } ->
      (* Type ascriptions are left-associative *)
      Format.fprintf ppf "@[<2>%a :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_expression ~parent_precedence pp_expression)
        expression
        (parenthesize_right_argument_left_associative_operator
           Precedence.of_typ ~parent_precedence pp_typ)
        typ
    | Expression.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | Expression.Constant { operator; quoted = false; _ } ->
            `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | Expression.Application
              { applicand =
                  Expression.Constant { operator; quoted = false; _ }
              ; _
              } -> `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:Precedence.of_expression
        ~precedence_of_argument:Precedence.of_expression
        ~pp_applicand:pp_expression ~pp_argument:pp_expression
        ~parent_precedence ppf (applicand, arguments)

  and pp_pattern ppf pattern =
    let parent_precedence = Precedence.of_pattern pattern in
    match pattern with
    | Pattern.Variable { identifier; _ } -> Identifier.pp ppf identifier
    | Pattern.Constant { identifier; quoted; operator; _ } ->
      if quoted && Bool.not (Operator.is_nullary operator) then
        Format.fprintf ppf "(%a)" QualifiedIdentifier.pp identifier
      else QualifiedIdentifier.pp ppf identifier
    | Pattern.MetaObject { meta_pattern; _ } ->
      Meta.pp_pattern ppf meta_pattern
    | Pattern.Tuple { elements; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]"
        (List2.pp ~pp_sep:Format.comma pp_pattern)
        elements
    | Pattern.Observation { observation; arguments; _ } -> (
      match List1.of_list arguments with
      | Option.None ->
        Format.fprintf ppf "@[<2>.%a@]" QualifiedIdentifier.pp observation
      | Option.Some arguments ->
        Format.fprintf ppf "@[<2>.%a@ %a@]" QualifiedIdentifier.pp
          observation
          (List1.pp ~pp_sep:Format.pp_print_space pp_pattern)
          arguments)
    | Pattern.TypeAnnotated { pattern; typ; _ } ->
      (* The type annotation operator is left-associative *)
      Format.fprintf ppf "@[<2>%a :@ %a@]"
        (parenthesize_left_argument_left_associative_operator
           Precedence.of_pattern ~parent_precedence pp_pattern)
        pattern
        (parenthesize_right_argument_left_associative_operator
           Precedence.of_typ ~parent_precedence pp_typ)
        typ
    | Pattern.MetaTypeAnnotated
        { annotation_identifier; annotation_type; body; _ } ->
      Format.fprintf ppf "@[<2>{@ %a :@ %a@ }@ %a@]" Identifier.pp
        annotation_identifier Meta.pp_typ annotation_type pp_pattern body
    | Pattern.Wildcard _ -> Format.pp_print_string ppf "_"
    | Pattern.Application { applicand; arguments; _ } ->
      pp_application
        ~guard_operator:(function
          | Pattern.Constant { operator; quoted = false; _ } ->
            `Operator operator
          | _ -> `Term)
        ~guard_operator_application:(function
          | Pattern.Application
              { applicand = Pattern.Constant { operator; quoted = false; _ }
              ; _
              } -> `Operator_application operator
          | _ -> `Term)
        ~precedence_of_applicand:Precedence.of_pattern
        ~precedence_of_argument:Precedence.of_pattern
        ~pp_applicand:pp_pattern ~pp_argument:pp_pattern ~parent_precedence
        ppf (applicand, arguments)

  and pp_context ppf context =
    let pp_binding ppf (identifier, typ) =
      Format.fprintf ppf "%a :@ %a" Identifier.pp identifier pp_typ typ
    in
    let { Context.bindings; _ } = context in
    List.pp ~pp_sep:Format.comma pp_binding ppf bindings
end

(** Pretty-printing for Harpoon syntax. *)
module Harpoon = struct
  open Harpoon

  let rec pp_proof ppf proof =
    match proof with
    | Proof.Incomplete { label; _ } -> (
      match label with
      | Option.None -> Format.pp_print_string ppf "?"
      | Option.Some label -> Identifier.pp ppf label)
    | Proof.Command { command; body; _ } ->
      Format.fprintf ppf "@[%a@];@,%a" pp_command command pp_proof body
    | Proof.Directive { directive; _ } -> pp_directive ppf directive

  and pp_command ppf command =
    match command with
    | Command.By { expression; assignee; _ } ->
      Format.fprintf ppf "@[<2>by@ %a@ as@ %a@]" Comp.pp_expression
        expression Identifier.pp assignee
    | Command.Unbox { expression; assignee; modifier = Option.None; _ } ->
      Format.fprintf ppf "@[<2>unbox@ %a@ as@ %a@]" Comp.pp_expression
        expression Identifier.pp assignee
    | Command.Unbox
        { expression; assignee; modifier = Option.Some `Strengthened; _ } ->
      Format.fprintf ppf "@[<2>strengthen@ %a@ as@ %a@]" Comp.pp_expression
        expression Identifier.pp assignee

  and pp_directive ppf directive =
    match directive with
    | Directive.Intros { hypothetical; _ } ->
      Format.fprintf ppf "@[<v>intros@,%a@]" pp_hypothetical hypothetical
    | Directive.Solve { solution; _ } ->
      Format.fprintf ppf "@[<hov 2>solve@ %a@]" Comp.pp_expression solution
    | Directive.Split { scrutinee; branches; _ } ->
      Format.fprintf ppf "@[split@ %a as@]@,@[<v>%a@]" Comp.pp_expression
        scrutinee
        (List1.pp ~pp_sep:Format.pp_print_cut pp_split_branch)
        branches
    | Directive.Impossible { scrutinee; _ } ->
      Format.fprintf ppf "@[impossible@ @[%a@]@]" Comp.pp_expression
        scrutinee
    | Directive.Suffices { scrutinee; branches; _ } ->
      Format.fprintf ppf "@[<v>@[<2>suffices by@ %a@] toshow@,@[<v>%a@]@]"
        Comp.pp_expression scrutinee
        (List.pp ~pp_sep:Format.pp_print_cut pp_suffices_branch)
        branches

  and pp_split_branch ppf branch =
    let { Split_branch.label; body; _ } = branch in
    Format.fprintf ppf "@[<v>case %a:@,%a@]" pp_split_branch_label label
      pp_hypothetical body

  and pp_split_branch_label ppf label =
    match label with
    | Split_branch.Label.Constant { identifier; _ } ->
      QualifiedIdentifier.pp ppf identifier
    | Split_branch.Label.Bound_variable _ ->
      Format.pp_print_string ppf "head variable"
    | Split_branch.Label.Empty_context _ ->
      Format.pp_print_string ppf "empty context"
    | Split_branch.Label.Extended_context { schema_element; _ } ->
      Format.fprintf ppf "extended by %d" schema_element
    | Split_branch.Label.Parameter_variable { schema_element; projection; _ }
      -> (
      match projection with
      | Option.None -> Format.fprintf ppf "%d" schema_element
      | Option.Some projection ->
        Format.fprintf ppf "%d.%d" schema_element projection)

  and pp_suffices_branch ppf branch =
    let { Suffices_branch.goal; proof; _ } = branch in
    Format.fprintf ppf "@[<v 2>@[%a@] {@,@[<v>%a@]@]@,}" Comp.pp_typ goal
      pp_proof proof

  and pp_hypothetical ppf hypothetical =
    let { Hypothetical.meta_context =
            { Synext'.Meta.Context.bindings = meta_context_bindings; _ }
        ; comp_context =
            { Synext'.Comp.Context.bindings = comp_context_bindings; _ }
        ; proof
        ; _
        } =
      hypothetical
    in
    Format.fprintf ppf "@[<v>{ @[<hv>%a@]@,| @[<hv>%a@]@,; @[<v>%a@]@,}@]"
      (List.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
           Format.fprintf ppf "@[<2>%a :@ %a@]" Identifier.pp i Meta.pp_typ t))
      meta_context_bindings
      (List.pp ~pp_sep:Format.comma (fun ppf (i, t) ->
           Format.fprintf ppf "@[<2>%a :@ %a@]" Identifier.pp i Comp.pp_typ t))
      comp_context_bindings pp_proof proof

  and pp_repl_command ppf repl_command =
    match repl_command with
    | Repl.Command.Rename { rename_from; rename_to; level = `comp; _ } ->
      Format.fprintf ppf "@[<2>rename@ comp@ %a@ %a@]" Identifier.pp
        rename_from Identifier.pp rename_to
    | Repl.Command.Rename { rename_from; rename_to; level = `meta; _ } ->
      Format.fprintf ppf "@[<2>rename@ meta@ %a@ %a@]" Identifier.pp
        rename_from Identifier.pp rename_to
    | Repl.Command.ToggleAutomation { kind; change; _ } ->
      let pp_toggle_automation_kind ppf = function
        | `auto_intros -> Format.pp_print_string ppf "auto-intros"
        | `auto_solve_trivial ->
          Format.pp_print_string ppf "auto-solve-trivial"
      and pp_toggle_automation_change ppf = function
        | `on -> Format.pp_print_string ppf "on"
        | `off -> Format.pp_print_string ppf "off"
        | `toggle -> Format.pp_print_string ppf "toggle"
      in
      Format.fprintf ppf "@[<2>toggle-automation@ %a@ %a@]"
        pp_toggle_automation_kind kind pp_toggle_automation_change change
    | Repl.Command.Type { scrutinee; _ } ->
      Format.fprintf ppf "@[<2>type@ %a@]" Comp.pp_expression scrutinee
    | Repl.Command.Info { kind; object_identifier; _ } ->
      let pp_info_kind ppf = function
        | `prog -> Format.pp_print_string ppf "theorem"
      in
      Format.fprintf ppf "@[<2>info@ %a@ %a@]" pp_info_kind kind
        QualifiedIdentifier.pp object_identifier
    | Repl.Command.SelectTheorem { theorem; _ } ->
      Format.fprintf ppf "@[<2>select@ %a@]" QualifiedIdentifier.pp theorem
    | Repl.Command.Theorem { subcommand; _ } ->
      let pp_theorem_subcommand ppf = function
        | `list -> Format.pp_print_string ppf "list"
        | `defer -> Format.fprintf ppf "defer"
        | `show_ihs -> Format.pp_print_string ppf "show-ihs"
        | `show_proof -> Format.pp_print_string ppf "show-proof"
        | `dump_proof path -> Format.fprintf ppf "dump-proof@ \"%s\"" path
      in
      Format.fprintf ppf "@[<2>theorem@ %a@]" pp_theorem_subcommand
        subcommand
    | Repl.Command.Session { subcommand; _ } ->
      let pp_session_subcommand ppf = function
        | `list -> Format.pp_print_string ppf "list"
        | `defer -> Format.pp_print_string ppf "defer"
        | `create -> Format.pp_print_string ppf "create"
        | `serialize -> Format.pp_print_string ppf "serialize"
      in
      Format.fprintf ppf "@[<2>session@ %a@]" pp_session_subcommand
        subcommand
    | Repl.Command.Subgoal { subcommand; _ } ->
      let pp_subgoal_subcommand ppf = function
        | `list -> Format.pp_print_string ppf "list"
        | `defer -> Format.pp_print_string ppf "defer"
      in
      Format.fprintf ppf "@[<2>subgoal@ %a@]" pp_subgoal_subcommand
        subcommand
    | Repl.Command.Undo _ -> Format.pp_print_string ppf "undo"
    | Repl.Command.Redo _ -> Format.pp_print_string ppf "redo"
    | Repl.Command.History _ -> Format.pp_print_string ppf "history"
    | Repl.Command.Translate { theorem; _ } ->
      Format.fprintf ppf "@[<2>translate@ %a@]" QualifiedIdentifier.pp
        theorem
    | Repl.Command.Intros { introduced_variables = Option.None; _ } ->
      Format.pp_print_string ppf "intros"
    | Repl.Command.Intros { introduced_variables = Option.Some variables; _ }
      ->
      Format.fprintf ppf "@[intros@ %a@]"
        (List1.pp ~pp_sep:Format.pp_print_space Identifier.pp)
        variables
    | Repl.Command.Split { scrutinee; _ } ->
      Format.fprintf ppf "@[<2>split@ %a@]" Comp.pp_expression scrutinee
    | Repl.Command.Invert { scrutinee; _ } ->
      Format.fprintf ppf "@[<2>invert@ %a@]" Comp.pp_expression scrutinee
    | Repl.Command.Impossible { scrutinee; _ } ->
      Format.fprintf ppf "@[<2>impossible@ %a@]" Comp.pp_expression scrutinee
    | Repl.Command.MSplit { identifier; _ } ->
      Format.fprintf ppf "@[<2>msplit@ %a@]" Identifier.pp identifier
    | Repl.Command.Solve { solution; _ } ->
      Format.fprintf ppf "@[<2>solve@ %a@]" Comp.pp_expression solution
    | Repl.Command.Unbox { expression; assignee; modifier = None; _ } ->
      Format.fprintf ppf "@[<2>unbox@ %a@ as@ %a@]" Comp.pp_expression
        expression Identifier.pp assignee
    | Repl.Command.Unbox
        { expression; assignee; modifier = Option.Some `Strengthened; _ } ->
      Format.fprintf ppf "@[<2>strengthen@ %a@ as@ %a@]" Comp.pp_expression
        expression Identifier.pp assignee
    | Repl.Command.By { expression; assignee; _ } ->
      Format.fprintf ppf "@[<2>by@ %a@ as@ %a@]" Comp.pp_expression
        expression Identifier.pp assignee
    | Repl.Command.Suffices { implication; goal_premises; _ } ->
      Format.fprintf ppf "@[suffices@ by@ %a@ toshow@ %a@]"
        Comp.pp_expression implication
        (List.pp ~pp_sep:Format.comma (fun ppf -> function
           | `exact typ -> Comp.pp_typ ppf typ
           | `infer _ -> Format.pp_print_string ppf "_"))
        goal_premises
    | Repl.Command.Help _ -> Format.pp_print_string ppf "help"
end
