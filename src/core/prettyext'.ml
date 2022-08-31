(** Pretty-printing for the external syntax. *)

open Support
open Synext'

(** {1 Handling Parentheses}

    The external syntax models parentheses explicitly. This allows for
    handling operator quoting, whereby infix and postfix operators may be
    written in prefix notation when the operator is parenthesized. Having
    parentheses modelled in the AST also allows for better error-reporting
    since there is a discrepancy between the location of an object and that
    same object in parentheses. Most importantly, having parentheses modelled
    in the AST allows for decoupling the elimination of redundant parentheses
    and the re-introduction of necessary parentheses from the printing
    functions. This enables finer testing.

    {2 Removing Parentheses}

    The syntax tree structure captures the grouping of terms without the need
    for parentheses. As part of pretty-printing for the external syntax, we
    can remove semantically irrelevant parentheses for normalization, and
    re-introduce them as needed when printing. As such, program generation
    from the internal syntax to the external syntax does not need to handle
    parenthesizing.

    {2 Adding Necessary Parentheses}

    Parentheses are re-introduced in the AST for printing using the
    precedence ordering specified in the parser. Careful thought is required
    when adding parentheses for user-defined operators, especially when
    operator precedences are equal.

    Let [->] be a right-associative infix operator and [<-] be a
    left-associative infix operator, both of the same precedence.

    Parentheses are required in the following cases:

    - [(a <- b) -> c]
    - [(a -> b) -> c]
    - [a <- (b -> c)]
    - [a <- (b <- c)]

    Parentheses are not required in the following cases:

    - [a -> b -> c], which is parsed as [a -> (b -> c)]
    - [a <- b <- c], which is parsed as [(a <- b) <- c]
    - [a -> b <- c], which is parsed as [(a -> b) <- c]
    - [a <- b -> c], which is parsed as [a <- (b -> c)]

    Beluga's specification also mentions weak prefix operators. One such
    operator is lambda abstraction. Since it is prefix, then it is
    right-associative. However, in contrast with right-associative operators,
    its right argument does not need to be parenthesized at all. *)

(** AST nodes that can explicitly be parenthesized. *)
module type PARENTHESIZABLE = sig
  (** The type of AST node. *)
  type t

  (** [add_parentheses node] is [node] with the addition of a pair of outer
      parentheses. *)
  val add_parentheses : t -> t
end

(** Functor for creating a helper module for parenthesizing AST nodes. *)
module Make_parenthesizer (Argument : sig
  include PARENTHESIZABLE

  (** [precedence node] is the value corresponding to the order of [node] as
      it was parsed in a recursive descent parser. *)
  val precedence : t -> Int.t
end) : sig
  (** The type of AST node. *)
  type t = Argument.t

  (** [add_parentheses node] is [node] with the addition of a pair of outer
      parentheses. *)
  val add_parentheses : t -> t

  (** [precedence node] is the value corresponding to the order of [node] as
      it was parsed in a recursive descent parser. *)
  val precedence : t -> Int.t

  (** [parenthesize_left_argument_left_associative_operator parent_precedence node]
      parenthesizes [node] as if it were a left argument to a
      left-associative infix operator in a parent node of precedence
      [parent_precedence]. *)
  val parenthesize_left_argument_left_associative_operator :
    parent_precedence:Int.t -> t -> t

  (** [parenthesize_right_argument_left_associative_operator parent_precedence node]
      parenthesizes [node] as if it were a right argument to a
      left-associative infix operator in a parent node of precedence
      [parent_precedence]. *)
  val parenthesize_right_argument_left_associative_operator :
    parent_precedence:Int.t -> t -> t

  (** [parenthesize_left_argument_right_associative_operator parent_precedence node]
      parenthesizes [node] as if it were a left argument to a
      right-associative infix operator in a parent node of precedence
      [parent_precedence]. *)
  val parenthesize_left_argument_right_associative_operator :
    parent_precedence:Int.t -> t -> t

  (** [parenthesize_right_argument_right_associative_operator parent_precedence node]
      parenthesizes [node] as if it were a right argument to a
      right-associative infix operator in a parent node of precedence
      [parent_precedence]. *)
  val parenthesize_right_argument_right_associative_operator :
    parent_precedence:Int.t -> t -> t

  (** [parenthesize_argument_non_associative_operator parent_precedence node]
      parenthesizes [node] as if it were an argument to a non-associative
      infix operator in a parent node of precedence [parent_precedence]. *)
  val parenthesize_argument_non_associative_operator :
    parent_precedence:Int.t -> t -> t

  (** [parenthesize_argument_prefix_operator parent_precedence node]
      parenthesizes [node] as if it were an argument to a prefix operator in
      a parent node of precedence [parent_precedence]. *)
  val parenthesize_argument_prefix_operator :
    parent_precedence:Int.t -> t -> t

  (** [parenthesize_argument_postfix_operator parent_precedence node]
      parenthesizes [node] as if it were an argument to a postfix operator in
      a parent node of precedence [parent_precedence]. *)
  val parenthesize_argument_postfix_operator :
    parent_precedence:Int.t -> t -> t
end = struct
  include Argument

  let[@inline] parenthesize_argument_of_lesser_precedence ~parent_precedence
      argument =
    if precedence argument < parent_precedence then
      Argument.add_parentheses argument
    else argument

  let[@inline] parenthesize_argument_of_lesser_than_or_equal_precedence
      ~parent_precedence argument =
    if precedence argument <= parent_precedence then
      Argument.add_parentheses argument
    else argument

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
    parenthesize_argument_of_lesser_than_or_equal_precedence
end

(** {1 Printing LF Kinds, Types and Terms} *)
module LF = struct
  open LF

  (** {1 Removing Parentheses} *)

  (** [remove_parentheses_kind ?(unquote_operators = true) kind] is [kind]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this kind with {!pp_kind} may not result in a syntactically
      valid LF kind. *)
  let rec remove_parentheses_kind ?(unquote_operators = true) kind =
    match kind with
    | Kind.Typ _ -> kind
    | Kind.Arrow { location; domain; range } ->
      let domain' = remove_parentheses_typ ~unquote_operators domain
      and range' = remove_parentheses_kind ~unquote_operators range in
      Kind.Arrow { location; domain = domain'; range = range' }
    | Kind.Pi { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' =
        remove_parentheses_typ ~unquote_operators parameter_type
      and body' = remove_parentheses_kind ~unquote_operators body in
      Kind.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Kind.Parenthesized { kind; _ } ->
      remove_parentheses_kind ~unquote_operators kind

  (** [remove_parentheses_typ ?(unquote_operators = true) typ] is [typ]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this type with {!pp_typ} may not result in a syntactically
      valid LF type. *)
  and remove_parentheses_typ ?(unquote_operators = true) typ =
    match typ with
    | Typ.Constant _ -> typ
    | Typ.Application { location; applicand; arguments } ->
      let applicand' = remove_parentheses_typ ~unquote_operators applicand
      and arguments' =
        List.map (remove_parentheses_term ~unquote_operators) arguments
      in
      let applicand'' =
        match applicand' with
        | Typ.Parenthesized { typ = Typ.Constant _ as constant; _ }
          when unquote_operators -> constant
        | _ -> applicand'
      in
      Typ.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Typ.ForwardArrow { location; domain; range } ->
      let domain' = remove_parentheses_typ ~unquote_operators domain
      and range' = remove_parentheses_typ ~unquote_operators range in
      Typ.ForwardArrow { location; domain = domain'; range = range' }
    | Typ.BackwardArrow { location; domain; range } ->
      let domain' = remove_parentheses_typ domain
      and range' = remove_parentheses_typ range in
      Typ.BackwardArrow { location; domain = domain'; range = range' }
    | Typ.Pi { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' =
        remove_parentheses_typ ~unquote_operators parameter_type
      and body' = remove_parentheses_typ ~unquote_operators body in
      Typ.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Typ.Parenthesized { typ = Typ.Constant { operator; _ } as constant; _ }
      when Operator.is_nullary operator (* Unnecessary operator quoting *) ->
      constant
    | Typ.Parenthesized { typ = Typ.Constant _; _ }
    (* Necessary quoting of operator *) -> typ
    | Typ.Parenthesized { typ; _ } ->
      remove_parentheses_typ ~unquote_operators typ

  (** [remove_parentheses_term ?(unquote_operators = true) term] is [term]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this term with {!pp_term} may not result in a syntactically
      valid LF term. *)
  and remove_parentheses_term ?(unquote_operators = true) term =
    match term with
    | Term.Variable _ -> term
    | Term.Constant _ -> term
    | Term.Application { location; applicand; arguments } ->
      let applicand' = remove_parentheses_term ~unquote_operators applicand
      and arguments' =
        List.map (remove_parentheses_term ~unquote_operators) arguments
      in
      let applicand'' =
        match applicand' with
        | Term.Parenthesized { term = Term.Constant _ as constant; _ }
          when unquote_operators -> constant
        | _ -> applicand'
      in
      Term.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Term.Abstraction
        { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' =
        Option.map (remove_parentheses_typ ~unquote_operators) parameter_type
      and body' = remove_parentheses_term ~unquote_operators body in
      Term.Abstraction
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Term.Wildcard _ -> term
    | Term.TypeAnnotated { location; term; typ } ->
      let term' = remove_parentheses_term ~unquote_operators term
      and typ' = remove_parentheses_typ ~unquote_operators typ in
      Term.TypeAnnotated { location; term = term'; typ = typ' }
    | Term.Parenthesized
        { term = Term.Constant { operator; _ } as constant; _ }
      when Operator.is_nullary operator (* Unnecessary operator quoting *) ->
      constant
    | Term.Parenthesized { term = Term.Constant _; _ }
    (* Necessary quoting of operator *) -> term
    | Term.Parenthesized { term; _ } ->
      remove_parentheses_term ~unquote_operators term

  (** {1 Adding Necessary Parentheses} *)

  module Kind_parenthesizer = Make_parenthesizer (struct
    type t = Kind.t

    let[@inline] add_parentheses kind =
      let location = location_of_kind kind in
      Kind.Parenthesized { location; kind }

    (** [precedence kind] is the precedence of [kind] based on the order of
        the recursive descent parsing of LF objects. *)
    let precedence kind =
      match kind with
      | Kind.Pi _ -> 10
      | Kind.Arrow _ -> 20
      | Kind.Typ _ | Kind.Parenthesized _ -> 50
  end)

  module Typ_parenthesizer = Make_parenthesizer (struct
    type t = Typ.t

    let[@inline] add_parentheses typ =
      let location = location_of_typ typ in
      Typ.Parenthesized { location; typ }

    (** [precedence typ] is the precedence of [typ] based on the order of the
        recursive descent parsing of LF objects.

        Exceptionally, the juxtaposition of LF objects has higher precedence
        than user-defined operator applications. *)
    let precedence typ =
      match typ with
      | Typ.Pi _ -> 10
      | Typ.ForwardArrow _ | Typ.BackwardArrow _ -> 20
      | Typ.Application { applicand = Typ.Constant _; _ }
      (* User-defined operator application *) -> 39
      | Typ.Application _ -> 40
      | Typ.Constant _ | Typ.Parenthesized _ -> 50
  end)

  module Term_parenthesizer = Make_parenthesizer (struct
    type t = Term.t

    let[@inline] add_parentheses term =
      let location = location_of_term term in
      Term.Parenthesized { location; term }

    (** [precedence term] is the precedence of [term] based on the order of
        the recursive descent parsing of LF objects.

        Exceptionally, the juxtaposition of LF objects has higher precedence
        than user-defined operator applications. *)
    let precedence term =
      match term with
      | Term.Abstraction _ -> 10
      | Term.TypeAnnotated _ -> 30
      | Term.Application { applicand = Term.Constant _; _ }
      (* User-defined operator application *) -> 39
      | Term.Application _ -> 40
      | Term.Wildcard _
      | Term.Variable _
      | Term.Constant _
      | Term.Parenthesized _ -> 60
  end)

  (** [parenthesize_kind kind] is [kind] with the addition of necessary
      parentheses for printing.

      If this is done after the application of {!remove_parentheses_kind},
      then the resultant LF kind can be parsed to the same AST, modulo
      {!remove_parentheses_kind} and without considering locations. *)
  let rec parenthesize_kind kind =
    match kind with
    | Kind.Arrow { location; domain; range } ->
      let domain' = parenthesize_typ domain
      and range' = parenthesize_kind range in
      (* Arrows are weakly right-associative *)
      let domain'' =
        Typ_parenthesizer
        .parenthesize_left_argument_right_associative_operator
          ~parent_precedence:(Kind_parenthesizer.precedence kind)
          domain'
      in
      Kind.Arrow { location; domain = domain''; range = range' }
    | Kind.Pi { location; parameter_identifier; parameter_type; body } ->
      (* Pis are weak prefix operators *)
      let parameter_type' = parenthesize_typ parameter_type
      and body' = parenthesize_kind body in
      Kind.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Kind.Typ _ | Kind.Parenthesized _ -> kind

  (** [parenthesize_typ typ] is [typ] with the addition of necessary
      parentheses for printing.

      If this is done after the application of {!remove_parentheses_typ},
      then the resultant LF type can be parsed to the same AST, modulo
      {!remove_parentheses_typ} and without considering locations. *)
  and parenthesize_typ typ =
    match typ with
    | Typ.Application
        { location
        ; applicand =
            Typ.Constant { operator = applicand_operator; _ } as applicand
        ; arguments
        }
    (* User-defined type constant application *) ->
      let arguments' =
        parenthesize_operator_application_arguments
          (Typ_parenthesizer.precedence typ)
          applicand_operator arguments
      in
      Typ.Application { location; applicand; arguments = arguments' }
    | Typ.Application { location; applicand; arguments }
    (* Arbitrary type application *) ->
      let parent_precedence = Typ_parenthesizer.precedence typ in
      let applicand' = parenthesize_typ applicand in
      (* Parenthesize as application in prefix notation *)
      let applicand'' =
        Typ_parenthesizer.parenthesize_argument_prefix_operator
          ~parent_precedence applicand'
      in
      let arguments' =
        parenthesize_application_arguments parent_precedence arguments
      in
      Typ.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Typ.ForwardArrow { location; domain; range } ->
      let domain' = parenthesize_typ domain
      and range' = parenthesize_typ range in
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows *)
      let domain'' =
        Typ_parenthesizer
        .parenthesize_left_argument_right_associative_operator
          ~parent_precedence:(Typ_parenthesizer.precedence typ)
          domain'
      in
      Typ.ForwardArrow { location; domain = domain''; range = range' }
    | Typ.BackwardArrow { location; range; domain } ->
      let range' = parenthesize_typ range
      and domain' = parenthesize_typ domain in
      (* Backward arrows are left-associative and of equal precedence with
         forward arrows *)
      let range'' =
        match range' with
        | Typ.BackwardArrow _ -> range'
        | _ ->
          Typ_parenthesizer
          .parenthesize_left_argument_left_associative_operator
            ~parent_precedence:(Typ_parenthesizer.precedence typ)
            range'
      and domain'' =
        match domain' with
        | Typ.BackwardArrow _ -> Typ_parenthesizer.add_parentheses domain'
        | _ -> domain'
      in
      Typ.BackwardArrow { location; range = range''; domain = domain'' }
    | Typ.Pi { location; parameter_identifier; parameter_type; body } ->
      (* Pis are weak prefix operators *)
      let parameter_type' = parenthesize_typ parameter_type
      and body' = parenthesize_typ body in
      Typ.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Typ.Constant _ | Typ.Parenthesized _ -> typ

  (** [parenthesize_term term] is [term] with the addition of necessary
      parentheses for printing.

      If this is done after the application of {!remove_parentheses_term},
      then the resultant LF term can be parsed to the same AST, modulo
      {!remove_parentheses_term} and without considering locations. *)
  and parenthesize_term term =
    match term with
    | Term.Application
        { location
        ; applicand =
            Term.Constant { operator = applicand_operator; _ } as applicand
        ; arguments
        }
    (* Term constant application *) ->
      let arguments' =
        parenthesize_operator_application_arguments
          (Term_parenthesizer.precedence term)
          applicand_operator arguments
      in
      Term.Application { location; applicand; arguments = arguments' }
    | Term.Application { location; applicand; arguments }
    (* Arbitrary term application *) ->
      let parent_precedence = Term_parenthesizer.precedence term in
      let applicand' = parenthesize_term applicand in
      (* Parenthesize as term application in prefix notation *)
      let applicand'' =
        Term_parenthesizer.parenthesize_argument_prefix_operator
          ~parent_precedence applicand'
      in
      let arguments' =
        parenthesize_application_arguments parent_precedence arguments
      in
      Term.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Term.Abstraction
        { location; parameter_identifier; parameter_type; body } ->
      (* Lambdas are weak prefix operators *)
      let parameter_type' = Option.map parenthesize_typ parameter_type
      and body' = parenthesize_term body in
      Term.Abstraction
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Term.TypeAnnotated { location; term = annotated_term; typ } ->
      (* Type ascriptions are left-associative *)
      let annotated_term' = parenthesize_term annotated_term in
      let annotated_term'' =
        Term_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence:(Term_parenthesizer.precedence term)
          annotated_term'
      and typ' = parenthesize_typ typ in
      Term.TypeAnnotated { location; term = annotated_term''; typ = typ' }
    | Term.Variable _
    | Term.Constant _
    | Term.Wildcard _
    | Term.Parenthesized _ -> term

  (** [parenthesize_application_arguments parent_precedence arguments] is the
      arguments in [argument] parenthesized as if they were applied to a
      non-operator applicand. *)
  and parenthesize_application_arguments parent_precedence arguments =
    List.map
      (fun argument ->
        let argument' = parenthesize_term argument in
        Term_parenthesizer.parenthesize_argument_prefix_operator
          ~parent_precedence argument')
      arguments

  (** [parenthesize_operator_application_arguments parent_precedence applicand_operator arguments]
      is the arguments in [arguments] parenthesized as if they were applied
      to an operator applicand described by [applicand_operator]. *)
  and parenthesize_operator_application_arguments parent_precedence
      applicand_operator arguments =
    match Operator.fixity applicand_operator with
    | Fixity.Prefix ->
      parenthesize_prefix_operator_application_arguments parent_precedence
        arguments
    | Fixity.Infix ->
      assert (List.length arguments = 2);
      let[@warning "-8"] [ left_argument; right_argument ] = arguments in
      parenthesize_infix_operator_application_arguments parent_precedence
        applicand_operator ~left_argument ~right_argument
    | Fixity.Postfix ->
      assert (List.length arguments = 1);
      let[@warning "-8"] [ argument ] = arguments in
      parenthesize_postfix_operator_application_arguments parent_precedence
        applicand_operator argument

  and parenthesize_prefix_operator_application_arguments parent_precedence
      arguments =
    parenthesize_application_arguments parent_precedence arguments

  and parenthesize_infix_operator_application_arguments parent_precedence
      applicand_operator ~left_argument ~right_argument =
    match Operator.associativity applicand_operator with
    | Associativity.Left_associative ->
      parenthesize_infix_left_associative_operator_application_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument
    | Associativity.Right_associative ->
      parenthesize_infix_right_associative_operator_application_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument
    | Associativity.Non_associative ->
      parenthesize_infix_non_associative_operator_application_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument

  and parenthesize_infix_left_associative_operator_application_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    let left_argument' = parenthesize_term left_argument
    and right_argument' = parenthesize_term right_argument in
    let left_argument'' =
      match left_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = left_argument_operator; _ }
          ; _
          }
        when Operator.precedence left_argument_operator
             >= Operator.precedence applicand_operator -> left_argument'
      | _ ->
        Term_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence left_argument'
    and right_argument'' =
      match right_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = right_argument_operator; _ }
          ; _
          }
        when Operator.precedence right_argument_operator
             > Operator.precedence applicand_operator
             || Operator.is_right_associative right_argument_operator
                && Operator.precedence right_argument_operator
                   >= Operator.precedence applicand_operator ->
        right_argument'
      | _ ->
        Term_parenthesizer
        .parenthesize_right_argument_left_associative_operator
          ~parent_precedence right_argument'
    in
    [ left_argument''; right_argument'' ]

  and parenthesize_infix_right_associative_operator_application_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    let left_argument' = parenthesize_term left_argument
    and right_argument' = parenthesize_term right_argument in
    let left_argument'' =
      match left_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = left_argument_operator; _ }
          ; _
          }
        when Operator.precedence left_argument_operator
             > Operator.precedence applicand_operator -> left_argument'
      | _ ->
        Term_parenthesizer
        .parenthesize_left_argument_right_associative_operator
          ~parent_precedence left_argument'
    and right_argument'' =
      match right_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = right_argument_operator; _ }
          ; _
          }
        when Operator.precedence right_argument_operator
             >= Operator.precedence applicand_operator -> right_argument'
      | _ ->
        Term_parenthesizer
        .parenthesize_right_argument_right_associative_operator
          ~parent_precedence right_argument'
    in
    [ left_argument''; right_argument'' ]

  and parenthesize_infix_non_associative_operator_application_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    let left_argument' = parenthesize_term left_argument
    and right_argument' = parenthesize_term right_argument in
    let left_argument'' =
      match left_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = left_argument_operator; _ }
          ; _
          }
        when Operator.precedence left_argument_operator
             >= Operator.precedence applicand_operator -> left_argument'
      | _ ->
        Term_parenthesizer.parenthesize_argument_non_associative_operator
          ~parent_precedence left_argument'
    and right_argument'' =
      match right_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = right_argument_operator; _ }
          ; _
          }
        when Operator.precedence right_argument_operator
             >= Operator.precedence applicand_operator -> right_argument'
      | _ ->
        Term_parenthesizer.parenthesize_argument_non_associative_operator
          ~parent_precedence right_argument'
    in
    [ left_argument''; right_argument'' ]

  and parenthesize_postfix_operator_application_arguments parent_precedence
      applicand_operator argument =
    let argument' = parenthesize_term argument in
    let argument'' =
      match argument' with
      | Term.Application
          { applicand = Term.Constant { operator = argument_operator; _ }
          ; _
          }
        when Operator.is_postfix applicand_operator
             || Operator.precedence argument_operator
                > Operator.precedence applicand_operator -> argument'
      | _ ->
        Term_parenthesizer.parenthesize_argument_postfix_operator
          ~parent_precedence argument'
    in
    [ argument'' ]

  let re_parenthesize_kind =
    Fun.(
      remove_parentheses_kind ~unquote_operators:true >> parenthesize_kind)

  let re_parenthesize_typ =
    Fun.(remove_parentheses_typ ~unquote_operators:true >> parenthesize_typ)

  let re_parenthesize_term =
    Fun.(
      remove_parentheses_term ~unquote_operators:true >> parenthesize_term)

  (** {1 Printing} *)

  let rec pp_kind ppf kind =
    match kind with
    | Kind.Typ _ -> Format.fprintf ppf "type"
    | Kind.Arrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]" pp_typ domain pp_kind range
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
    | Kind.Parenthesized { kind; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_kind kind

  and pp_typ ppf typ =
    match typ with
    | Typ.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_typ applicand
    | Typ.Application
        { applicand = Typ.Constant { identifier; operator; _ }
        ; arguments
        ; _
        } -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@ %a@]" pp_term left_argument
          QualifiedIdentifier.pp identifier pp_term right_argument
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]" pp_term argument
          QualifiedIdentifier.pp identifier)
    | Typ.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_typ applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
        arguments
    | Typ.ForwardArrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]" pp_typ domain pp_typ range
    | Typ.BackwardArrow { range; domain; _ } ->
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]" pp_typ range pp_typ domain
    | Typ.Pi { parameter_identifier = Option.None; parameter_type; body; _ }
      ->
      Format.fprintf ppf "@[<2>{@ _@ :@ %a@ }@ %a@]" pp_typ parameter_type
        pp_typ body
    | Typ.Pi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_typ body
    | Typ.Parenthesized { typ; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_typ typ

  and pp_term ppf term =
    match term with
    | Term.Variable { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Term.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_term applicand
    | Term.Application
        { applicand = Term.Constant { identifier; operator; _ }
        ; arguments
        ; _
        } -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@ %a@]" pp_term left_argument
          QualifiedIdentifier.pp identifier pp_term right_argument
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]" pp_term argument
          QualifiedIdentifier.pp identifier)
    | Term.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_term applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
        arguments
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.None
        ; body
        ; _
        } -> Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type pp_term
        body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
        parameter_identifier pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_term body
    | Term.Wildcard _ -> Format.fprintf ppf "_"
    | Term.TypeAnnotated { term; typ; _ } ->
      Format.fprintf ppf "@[<2>%a@ :@ %a@]" pp_term term pp_typ typ
    | Term.Parenthesized { term; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_term term

  module Debug = struct
    let rec pp_kind ppf kind =
      match kind with
      | Kind.Typ _ -> Format.fprintf ppf "type"
      | Kind.Arrow { domain; range; _ } ->
        Format.fprintf ppf "@[<2>KindArrow(@,%a@ ->@ %a)@]" pp_typ domain
          pp_kind range
      | Kind.Pi
          { parameter_identifier = Option.None; parameter_type; body; _ } ->
        Format.fprintf ppf "@[<2>KindPi(@,{@ _@ :@ %a@ }@ %a)@]" pp_typ
          parameter_type pp_kind body
      | Kind.Pi
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>KindPi(@,{@ %a@ :@ %a@ }@ %a)@]"
          Identifier.pp parameter_identifier pp_typ parameter_type pp_kind
          body
      | Kind.Parenthesized { kind; _ } ->
        Format.fprintf ppf "@[<2>KindParenthesized(@,%a)@]" pp_kind kind

    and pp_typ ppf typ =
      match typ with
      | Typ.Constant { identifier; _ } ->
        Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
      | Typ.Application { applicand; arguments; _ } ->
        Format.fprintf ppf "@[<2>TypeApplication(@,%a(%a))@]" pp_typ
          applicand
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
          arguments
      | Typ.ForwardArrow { domain; range; _ } ->
        Format.fprintf ppf "@[<2>TypeArrow(@,%a@ ->@ %a)@]" pp_typ domain
          pp_typ range
      | Typ.BackwardArrow { range; domain; _ } ->
        Format.fprintf ppf "@[<2>TypeArrow(@,%a@ <-@ %a)@]" pp_typ range
          pp_typ domain
      | Typ.Pi
          { parameter_identifier = Option.None; parameter_type; body; _ } ->
        Format.fprintf ppf "@[<2>TypePi(@,{@ _@ :@ %a@ }@ %a)@]" pp_typ
          parameter_type pp_typ body
      | Typ.Pi
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TypePi(@,{@ %a@ :@ %a@ }@ %a)@]"
          Identifier.pp parameter_identifier pp_typ parameter_type pp_typ
          body
      | Typ.Parenthesized { typ; _ } ->
        Format.fprintf ppf "@[<2>TypeParenthesized(@,%a)@]" pp_typ typ

    and pp_term ppf term =
      match term with
      | Term.Variable { identifier; _ } ->
        Format.fprintf ppf "%a" Identifier.pp identifier
      | Term.Constant { identifier; _ } ->
        Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
      | Term.Application { applicand; arguments; _ } ->
        Format.fprintf ppf "@[<2>TermApplication(@,%a(%a))@]" pp_term
          applicand
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
          arguments
      | Term.Abstraction
          { parameter_identifier = Option.None
          ; parameter_type = Option.None
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(@,\\_.@ %a)@]" pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.None
          ; parameter_type = Option.Some parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(@,\\_:%a.@ %a)@]" pp_typ
          parameter_type pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type = Option.None
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(@,\\%a.@ %a)@]"
          Identifier.pp parameter_identifier pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type = Option.Some parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(@,\\%a:%a.@ %a)@]"
          Identifier.pp parameter_identifier pp_typ parameter_type pp_term
          body
      | Term.Wildcard _ -> Format.fprintf ppf "_"
      | Term.TypeAnnotated { term; typ; _ } ->
        Format.fprintf ppf "@[<2>TermAnnotated(@,%a@ :@ %a)@]" pp_term term
          pp_typ typ
      | Term.Parenthesized { term; _ } ->
        Format.fprintf ppf "@[<2>TermParenthesized(@,%a)@]" pp_term term
  end
end

module CLF = struct
  open CLF

  (** {1 Removing Parentheses} *)

  (** [remove_parentheses_typ ?(unquote_operators = true) typ] is [typ]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this type with {!pp_typ} may not result in a syntactically
      valid LF type. *)
  let rec remove_parentheses_typ ?(unquote_operators = true) typ =
    match typ with
    | Typ.Constant _ -> typ
    | Typ.Application { location; applicand; arguments } ->
      let applicand' = remove_parentheses_typ ~unquote_operators applicand
      and arguments' =
        List.map (remove_parentheses_term ~unquote_operators) arguments
      in
      let applicand'' =
        match applicand' with
        | Typ.Parenthesized { typ = Typ.Constant _ as constant; _ }
          when unquote_operators -> constant
        | _ -> applicand'
      in
      Typ.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Typ.ForwardArrow { location; domain; range } ->
      let domain' = remove_parentheses_typ ~unquote_operators domain
      and range' = remove_parentheses_typ ~unquote_operators range in
      Typ.ForwardArrow { location; domain = domain'; range = range' }
    | Typ.BackwardArrow { location; domain; range } ->
      let domain' = remove_parentheses_typ domain
      and range' = remove_parentheses_typ range in
      Typ.BackwardArrow { location; domain = domain'; range = range' }
    | Typ.Pi { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' =
        remove_parentheses_typ ~unquote_operators parameter_type
      and body' = remove_parentheses_typ ~unquote_operators body in
      Typ.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Typ.Parenthesized { typ = Typ.Constant { operator; _ } as constant; _ }
      when Operator.is_nullary operator (* Unnecessary operator quoting *) ->
      constant
    | Typ.Block { location; elements = (l1, t1), xs } ->
      let t1' = remove_parentheses_typ ~unquote_operators t1
      and xs' =
        List.map
          (Pair.map_right (remove_parentheses_typ ~unquote_operators))
          xs
      in
      Typ.Block { location; elements = ((l1, t1'), xs') }
    | Typ.Parenthesized { typ = Typ.Constant _; _ }
    (* Necessary quoting of operator *) -> typ
    | Typ.Parenthesized { typ; _ } ->
      remove_parentheses_typ ~unquote_operators typ

  (** [remove_parentheses_term ?(unquote_operators = true) term] is [term]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this term with {!pp_term} may not result in a syntactically
      valid LF term. *)
  and remove_parentheses_term ?(unquote_operators = true) term =
    match term with
    | Term.Variable _ -> term
    | Term.Constant _ -> term
    | Term.Substitution { location; term; substitution } ->
      let term' = remove_parentheses_term ~unquote_operators term
      and substitution' =
        remove_parentheses_substitution ~unquote_operators substitution
      in
      Term.Substitution
        { location; term = term'; substitution = substitution' }
    | Term.Application { location; applicand; arguments } ->
      let applicand' = remove_parentheses_term ~unquote_operators applicand
      and arguments' =
        List.map (remove_parentheses_term ~unquote_operators) arguments
      in
      let applicand'' =
        match applicand' with
        | Term.Parenthesized { term = Term.Constant _ as constant; _ }
          when unquote_operators -> constant
        | _ -> applicand'
      in
      Term.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Term.Abstraction
        { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' =
        Option.map (remove_parentheses_typ ~unquote_operators) parameter_type
      and body' = remove_parentheses_term ~unquote_operators body in
      Term.Abstraction
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Term.Hole _ -> term
    | Term.Tuple { location; terms } ->
      let terms' =
        List1.map (remove_parentheses_term ~unquote_operators) terms
      in
      Term.Tuple { location; terms = terms' }
    | Term.Projection { location; term; projection } ->
      let term' = remove_parentheses_term ~unquote_operators term in
      Term.Projection { location; term = term'; projection }
    | Term.TypeAnnotated { location; term; typ } ->
      let term' = remove_parentheses_term ~unquote_operators term
      and typ' = remove_parentheses_typ ~unquote_operators typ in
      Term.TypeAnnotated { location; term = term'; typ = typ' }
    | Term.Parenthesized
        { term = Term.Constant { operator; _ } as constant; _ }
      when Operator.is_nullary operator (* Unnecessary operator quoting *) ->
      constant
    | Term.Parenthesized { term = Term.Constant _; _ }
    (* Necessary quoting of operator *) -> term
    | Term.Parenthesized { term; _ } ->
      remove_parentheses_term ~unquote_operators term

  (** [remove_parentheses_substitution ?(unquote_operators = true) term] is
      [term] without parentheses. If [unquote_operators = true], then
      non-nullary operators that do not appear as application arguments are
      unquoted.

      Printing this substitution with {!pp_substitution} may not result in a
      syntactically valid contextual LF substitution. *)
  and remove_parentheses_substitution ?(unquote_operators = true)
      substitution =
    match substitution with
    | Substitution.{ location; extends_identity; terms } ->
      let terms' =
        List.map (remove_parentheses_term ~unquote_operators) terms
      in
      Substitution.{ location; extends_identity; terms = terms' }

  (** [remove_parentheses_typ_pattern ?(unquote_operators = true) typ_pattern]
      is [typ_pattern] without parentheses. If [unquote_operators = true],
      then non-nullary operators that do not appear as application arguments
      are unquoted.

      Printing this type with {!pp_typ_pattern} may not result in a
      syntactically valid LF type pattern. *)
  let rec remove_parentheses_typ_pattern ?(unquote_operators = true)
      typ_pattern =
    match typ_pattern with
    | Typ.Pattern.Constant _ -> typ_pattern
    | Typ.Pattern.Application { location; applicand; arguments } ->
      let applicand' =
        remove_parentheses_typ_pattern ~unquote_operators applicand
      and arguments' =
        List.map
          (remove_parentheses_term_pattern ~unquote_operators)
          arguments
      in
      let applicand'' =
        match applicand' with
        | Typ.Pattern.Parenthesized
            { pattern = Typ.Pattern.Constant _ as constant; _ }
          when unquote_operators -> constant
        | _ -> applicand'
      in
      Typ.Pattern.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Typ.Pattern.Parenthesized
        { pattern = Typ.Pattern.Constant { operator; _ } as constant; _ }
      when Operator.is_nullary operator (* Unnecessary operator quoting *) ->
      constant
    | Typ.Pattern.Block { location; elements = (l1, t1), xs } ->
      let t1' = remove_parentheses_typ_pattern ~unquote_operators t1
      and xs' =
        List.map
          (Pair.map_right
             (remove_parentheses_typ_pattern ~unquote_operators))
          xs
      in
      Typ.Pattern.Block { location; elements = ((l1, t1'), xs') }
    | Typ.Pattern.Parenthesized { pattern = Typ.Pattern.Constant _; _ }
    (* Necessary quoting of operator *) -> typ_pattern
    | Typ.Pattern.Parenthesized { pattern; _ } ->
      remove_parentheses_typ_pattern ~unquote_operators pattern

  (** [remove_parentheses_term_pattern ?(unquote_operators = true) term_pattern]
      is [term_pattern] without parentheses. If [unquote_operators = true],
      then non-nullary operators that do not appear as application arguments
      are unquoted.

      Printing this term with {!pp_term_pattern} may not result in a
      syntactically valid LF term pattern. *)
  and remove_parentheses_term_pattern ?(unquote_operators = true)
      term_pattern =
    match term_pattern with
    | Term.Pattern.Variable _ -> term_pattern
    | Term.Pattern.Constant _ -> term_pattern
    | Term.Pattern.Wildcard _ -> term_pattern
    | Term.Pattern.Substitution { location; term; substitution } ->
      let term' = remove_parentheses_term_pattern ~unquote_operators term
      and substitution' =
        remove_parentheses_substitution ~unquote_operators substitution
      in
      Term.Pattern.Substitution
        { location; term = term'; substitution = substitution' }
    | Term.Pattern.Application { location; applicand; arguments } ->
      let applicand' =
        remove_parentheses_term_pattern ~unquote_operators applicand
      and arguments' =
        List.map
          (remove_parentheses_term_pattern ~unquote_operators)
          arguments
      in
      let applicand'' =
        match applicand' with
        | Term.Pattern.Parenthesized
            { pattern = Term.Pattern.Constant _ as constant; _ }
          when unquote_operators -> constant
        | _ -> applicand'
      in
      Term.Pattern.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Term.Pattern.Abstraction
        { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' =
        Option.map (remove_parentheses_typ ~unquote_operators) parameter_type
      and body' = remove_parentheses_term_pattern ~unquote_operators body in
      Term.Pattern.Abstraction
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Term.Pattern.Tuple { location; terms } ->
      let terms' =
        List1.map (remove_parentheses_term_pattern ~unquote_operators) terms
      in
      Term.Pattern.Tuple { location; terms = terms' }
    | Term.Pattern.Projection { location; term; projection } ->
      let term' = remove_parentheses_term_pattern ~unquote_operators term in
      Term.Pattern.Projection { location; term = term'; projection }
    | Term.Pattern.TypeAnnotated { location; term; typ } ->
      let term' = remove_parentheses_term_pattern ~unquote_operators term
      and typ' = remove_parentheses_typ ~unquote_operators typ in
      Term.Pattern.TypeAnnotated { location; term = term'; typ = typ' }
    | Term.Pattern.Parenthesized
        { pattern = Term.Pattern.Constant { operator; _ } as constant; _ }
      when Operator.is_nullary operator (* Unnecessary operator quoting *) ->
      constant
    | Term.Pattern.Parenthesized { pattern = Term.Pattern.Constant _; _ }
    (* Necessary quoting of operator *) -> term_pattern
    | Term.Pattern.Parenthesized { pattern; _ } ->
      remove_parentheses_term_pattern ~unquote_operators pattern

  (** {1 Adding Necessary Parentheses} *)

  module Typ_parenthesizer = Make_parenthesizer (struct
    type t = Typ.t

    let[@inline] add_parentheses typ =
      let location = location_of_typ typ in
      Typ.Parenthesized { location; typ }

    (** [precedence typ] is the precedence of [typ] based on the order of the
        recursive descent parsing of LF objects.

        Exceptionally, the juxtaposition of LF objects has higher precedence
        than user-defined operator applications. *)
    let precedence typ =
      match typ with
      | Typ.Pi _ -> 10
      | Typ.ForwardArrow _ | Typ.BackwardArrow _ -> 20
      | Typ.Block _ -> 40
      | Typ.Application { applicand = Typ.Constant _; _ }
      (* User-defined operator application *) -> 49
      | Typ.Application _ -> 50
      | Typ.Constant _ | Typ.Parenthesized _ -> 80
  end)

  module Term_parenthesizer = Make_parenthesizer (struct
    type t = Term.t

    let[@inline] add_parentheses term =
      let location = location_of_term term in
      Term.Parenthesized { location; term }

    (** [precedence term] is the precedence of [term] based on the order of
        the recursive descent parsing of LF objects.

        Exceptionally, the juxtaposition of LF objects has higher precedence
        than user-defined operator applications. *)
    let precedence term =
      match term with
      | Term.Abstraction _ -> 10
      | Term.TypeAnnotated _ -> 30
      | Term.Application { applicand = Term.Constant _; _ }
      (* User-defined operator application *) -> 49
      | Term.Application _ -> 50
      | Term.Substitution _ -> 60
      | Term.Projection _ -> 70
      | Term.Variable _
      | Term.Constant _
      | Term.Hole _
      | Term.Tuple _
      | Term.Parenthesized _ -> 80
  end)

  module Typ_pattern_parenthesizer = Make_parenthesizer (struct
    type t = Typ.Pattern.t

    let[@inline] add_parentheses pattern =
      let location = location_of_typ_pattern pattern in
      Typ.Pattern.Parenthesized { location; pattern }

    (** [precedence typ_pattern] is the precedence of [typ_pattern] based on
        the order of the recursive descent parsing of LF objects.

        Exceptionally, the juxtaposition of LF objects has higher precedence
        than user-defined operator applications. *)
    let precedence typ_pattern =
      match typ_pattern with
      | Typ.Pattern.Block _ -> 40
      | Typ.Pattern.Application { applicand = Typ.Pattern.Constant _; _ }
      (* User-defined operator application *) -> 49
      | Typ.Pattern.Application _ -> 50
      | Typ.Pattern.Constant _ | Typ.Pattern.Parenthesized _ -> 80
  end)

  module Term_pattern_parenthesizer = Make_parenthesizer (struct
    type t = Term.Pattern.t

    let[@inline] add_parentheses pattern =
      let location = location_of_term_pattern pattern in
      Term.Pattern.Parenthesized { location; pattern }

    (** [precedence term_pattern] is the precedence of [term_pattern] based
        on the order of the recursive descent parsing of LF objects.

        Exceptionally, the juxtaposition of LF objects has higher precedence
        than user-defined operator applications. *)
    let precedence term_pattern =
      match term_pattern with
      | Term.Pattern.Abstraction _ -> 10
      | Term.Pattern.TypeAnnotated _ -> 30
      | Term.Pattern.Application { applicand = Term.Pattern.Constant _; _ }
      (* User-defined operator application *) -> 49
      | Term.Pattern.Application _ -> 50
      | Term.Pattern.Substitution _ -> 60
      | Term.Pattern.Projection _ -> 70
      | Term.Pattern.Variable _
      | Term.Pattern.Constant _
      | Term.Pattern.Wildcard _
      | Term.Pattern.Tuple _
      | Term.Pattern.Parenthesized _ -> 80
  end)

  (** [parenthesize_typ typ] is [typ] with the addition of necessary
      parentheses for printing.

      If this is done after the application of {!remove_parentheses_typ},
      then the resultant LF type can be parsed to the same AST, modulo
      {!remove_parentheses_typ} and without considering locations. *)
  let rec parenthesize_typ typ =
    match typ with
    | Typ.Constant _ -> typ
    | Typ.Application
        { location
        ; applicand =
            Typ.Constant { operator = applicand_operator; _ } as applicand
        ; arguments
        }
    (* User-defined type constant application *) ->
      let arguments' =
        parenthesize_operator_application_arguments
          (Typ_parenthesizer.precedence typ)
          applicand_operator arguments
      in
      Typ.Application { location; applicand; arguments = arguments' }
    | Typ.Application { location; applicand; arguments }
    (* Arbitrary type application *) ->
      let parent_precedence = Typ_parenthesizer.precedence typ in
      let applicand' = parenthesize_typ applicand in
      (* Parenthesize as application in prefix notation *)
      let applicand'' =
        Typ_parenthesizer.parenthesize_argument_prefix_operator
          ~parent_precedence applicand'
      in
      let arguments' =
        parenthesize_application_arguments parent_precedence arguments
      in
      Typ.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Typ.ForwardArrow { location; domain; range } ->
      let domain' = parenthesize_typ domain
      and range' = parenthesize_typ range in
      (* Forward arrows are right-associative and of equal precedence with
         backward arrows *)
      let domain'' =
        Typ_parenthesizer
        .parenthesize_left_argument_right_associative_operator
          ~parent_precedence:(Typ_parenthesizer.precedence typ)
          domain'
      in
      Typ.ForwardArrow { location; domain = domain''; range = range' }
    | Typ.BackwardArrow { location; range; domain } ->
      let range' = parenthesize_typ range
      and domain' = parenthesize_typ domain in
      (* Backward arrows are left-associative and of equal precedence with
         forward arrows *)
      let range'' =
        match range' with
        | Typ.BackwardArrow _ -> range'
        | _ ->
          Typ_parenthesizer
          .parenthesize_left_argument_left_associative_operator
            ~parent_precedence:(Typ_parenthesizer.precedence typ)
            range'
      and domain'' =
        match domain' with
        | Typ.BackwardArrow _ -> Typ_parenthesizer.add_parentheses domain'
        | _ -> domain'
      in
      Typ.BackwardArrow { location; range = range''; domain = domain'' }
    | Typ.Pi { location; parameter_identifier; parameter_type; body } ->
      (* Pis are weak prefix operators *)
      let parameter_type' = parenthesize_typ parameter_type
      and body' = parenthesize_typ body in
      Typ.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Typ.Block { location; elements } ->
      let (l1, t1), xs = elements in
      let t1' = parenthesize_typ t1
      and xs' = List.map (Pair.map_right parenthesize_typ) xs in
      let elements' = ((l1, t1'), xs') in
      Typ.Block { location; elements = elements' }
    | Typ.Parenthesized _ -> typ

  (** [parenthesize_term term] is [term] with the addition of necessary
      parentheses for printing.

      If this is done after the application of {!remove_parentheses_term},
      then the resultant LF term can be parsed to the same AST, modulo
      {!remove_parentheses_term} and without considering locations. *)
  and parenthesize_term term =
    match term with
    | Term.Variable _ -> term
    | Term.Constant _ -> term
    | Term.Substitution
        { location; term = term_under_substitution; substitution } ->
      (* Substitutions are left-associative *)
      let term_under_substitution' =
        parenthesize_term term_under_substitution
      in
      let term_under_substitution'' =
        Term_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence:(Term_parenthesizer.precedence term)
          term_under_substitution'
      and substitution' = parenthesize_substitution substitution in
      Term.Substitution
        { location
        ; term = term_under_substitution''
        ; substitution = substitution'
        }
    | Term.Application
        { location
        ; applicand =
            Term.Constant { operator = applicand_operator; _ } as applicand
        ; arguments
        }
    (* Term constant application *) ->
      let arguments' =
        parenthesize_operator_application_arguments
          (Term_parenthesizer.precedence term)
          applicand_operator arguments
      in
      Term.Application { location; applicand; arguments = arguments' }
    | Term.Application { location; applicand; arguments }
    (* Arbitrary term application *) ->
      let parent_precedence = Term_parenthesizer.precedence term in
      let applicand' = parenthesize_term applicand in
      (* Parenthesize as term application in prefix notation *)
      let applicand'' =
        Term_parenthesizer.parenthesize_argument_prefix_operator
          ~parent_precedence applicand'
      in
      let arguments' =
        parenthesize_application_arguments parent_precedence arguments
      in
      Term.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Term.Abstraction
        { location; parameter_identifier; parameter_type; body } ->
      (* Lambdas are weak prefix operators *)
      let parameter_type' = Option.map parenthesize_typ parameter_type
      and body' = parenthesize_term body in
      Term.Abstraction
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Term.Hole _ -> term
    | Term.Tuple { location; terms } ->
      let terms' = List1.map parenthesize_term terms in
      Term.Tuple { location; terms = terms' }
    | Term.Projection { location; term = projected_term; projection } ->
      (* Projections are left-associative *)
      let projected_term' = parenthesize_term projected_term in
      let projected_term'' =
        Term_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence:(Term_parenthesizer.precedence term)
          projected_term'
      in
      Term.Projection { location; term = projected_term''; projection }
    | Term.TypeAnnotated { location; term = annotated_term; typ } ->
      (* Type ascriptions are left-associative *)
      let annotated_term' = parenthesize_term annotated_term in
      let annotated_term'' =
        Term_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence:(Term_parenthesizer.precedence term)
          annotated_term'
      and typ' = parenthesize_typ typ in
      Term.TypeAnnotated { location; term = annotated_term''; typ = typ' }
    | Term.Parenthesized _ -> term

  (** [parenthesize_application_arguments parent_precedence arguments] is the
      arguments in [argument] parenthesized as if they were applied to a
      non-operator applicand. *)
  and parenthesize_application_arguments parent_precedence arguments =
    List.map
      (fun argument ->
        let argument' = parenthesize_term argument in
        Term_parenthesizer.parenthesize_argument_prefix_operator
          ~parent_precedence argument')
      arguments

  (** [parenthesize_operator_application_arguments parent_precedence applicand_operator arguments]
      is the arguments in [arguments] parenthesized as if they were applied
      to an operator applicand described by [applicand_operator]. *)
  and parenthesize_operator_application_arguments parent_precedence
      applicand_operator arguments =
    match Operator.fixity applicand_operator with
    | Fixity.Prefix ->
      parenthesize_prefix_operator_application_arguments parent_precedence
        arguments
    | Fixity.Infix ->
      assert (List.length arguments = 2);
      let[@warning "-8"] [ left_argument; right_argument ] = arguments in
      parenthesize_infix_operator_application_arguments parent_precedence
        applicand_operator ~left_argument ~right_argument
    | Fixity.Postfix ->
      assert (List.length arguments = 1);
      let[@warning "-8"] [ argument ] = arguments in
      parenthesize_postfix_operator_application_arguments parent_precedence
        applicand_operator argument

  and parenthesize_prefix_operator_application_arguments parent_precedence
      arguments =
    parenthesize_application_arguments parent_precedence arguments

  and parenthesize_infix_operator_application_arguments parent_precedence
      applicand_operator ~left_argument ~right_argument =
    match Operator.associativity applicand_operator with
    | Associativity.Left_associative ->
      parenthesize_infix_left_associative_operator_application_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument
    | Associativity.Right_associative ->
      parenthesize_infix_right_associative_operator_application_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument
    | Associativity.Non_associative ->
      parenthesize_infix_non_associative_operator_application_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument

  and parenthesize_infix_left_associative_operator_application_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    let left_argument' = parenthesize_term left_argument
    and right_argument' = parenthesize_term right_argument in
    let left_argument'' =
      match left_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = left_argument_operator; _ }
          ; _
          }
        when Operator.precedence left_argument_operator
             >= Operator.precedence applicand_operator -> left_argument'
      | _ ->
        Term_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence left_argument'
    and right_argument'' =
      match right_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = right_argument_operator; _ }
          ; _
          }
        when Operator.precedence right_argument_operator
             > Operator.precedence applicand_operator
             || Operator.is_right_associative right_argument_operator
                && Operator.precedence right_argument_operator
                   >= Operator.precedence applicand_operator ->
        right_argument'
      | _ ->
        Term_parenthesizer
        .parenthesize_right_argument_left_associative_operator
          ~parent_precedence right_argument'
    in
    [ left_argument''; right_argument'' ]

  and parenthesize_infix_right_associative_operator_application_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    let left_argument' = parenthesize_term left_argument
    and right_argument' = parenthesize_term right_argument in
    let left_argument'' =
      match left_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = left_argument_operator; _ }
          ; _
          }
        when Operator.precedence left_argument_operator
             > Operator.precedence applicand_operator -> left_argument'
      | _ ->
        Term_parenthesizer
        .parenthesize_left_argument_right_associative_operator
          ~parent_precedence left_argument'
    and right_argument'' =
      match right_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = right_argument_operator; _ }
          ; _
          }
        when Operator.precedence right_argument_operator
             >= Operator.precedence applicand_operator -> right_argument'
      | _ ->
        Term_parenthesizer
        .parenthesize_right_argument_right_associative_operator
          ~parent_precedence right_argument'
    in
    [ left_argument''; right_argument'' ]

  and parenthesize_infix_non_associative_operator_application_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    let left_argument' = parenthesize_term left_argument
    and right_argument' = parenthesize_term right_argument in
    let left_argument'' =
      match left_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = left_argument_operator; _ }
          ; _
          }
        when Operator.precedence left_argument_operator
             >= Operator.precedence applicand_operator -> left_argument'
      | _ ->
        Term_parenthesizer.parenthesize_argument_non_associative_operator
          ~parent_precedence left_argument'
    and right_argument'' =
      match right_argument' with
      | Term.Application
          { applicand =
              Term.Constant { operator = right_argument_operator; _ }
          ; _
          }
        when Operator.precedence right_argument_operator
             >= Operator.precedence applicand_operator -> right_argument'
      | _ ->
        Term_parenthesizer.parenthesize_argument_non_associative_operator
          ~parent_precedence right_argument'
    in
    [ left_argument''; right_argument'' ]

  and parenthesize_postfix_operator_application_arguments parent_precedence
      applicand_operator argument =
    let argument' = parenthesize_term argument in
    let argument'' =
      match argument' with
      | Term.Application
          { applicand = Term.Constant { operator = argument_operator; _ }
          ; _
          }
        when Operator.is_postfix applicand_operator
             || Operator.precedence argument_operator
                > Operator.precedence applicand_operator -> argument'
      | _ ->
        Term_parenthesizer.parenthesize_argument_postfix_operator
          ~parent_precedence argument'
    in
    [ argument'' ]

  and parenthesize_substitution substitution =
    match substitution with
    | Substitution.{ location; extends_identity; terms } ->
      let terms' = List.map parenthesize_term terms in
      Substitution.{ location; extends_identity; terms = terms' }

  (** [parenthesize_typ_pattern typ_pattern] is [typ_pattern] with the
      addition of necessary parentheses for printing.

      If this is done after the application of
      {!remove_parentheses_typ_pattern}, then the resultant LF type pattern
      can be parsed to the same AST, modulo {!remove_parentheses_typ_pattern}
      and without considering locations. *)
  let rec parenthesize_typ_pattern typ_pattern =
    match typ_pattern with
    | Typ.Pattern.Constant _ -> typ_pattern
    | Typ.Pattern.Application
        { location
        ; applicand =
            Typ.Pattern.Constant { operator = applicand_operator; _ } as
            applicand
        ; arguments
        }
    (* User-defined type constant application *) ->
      let arguments' =
        parenthesize_operator_application_pattern_arguments
          (Typ_pattern_parenthesizer.precedence typ_pattern)
          applicand_operator arguments
      in
      Typ.Pattern.Application { location; applicand; arguments = arguments' }
    | Typ.Pattern.Application { location; applicand; arguments }
    (* Arbitrary type application *) ->
      let parent_precedence =
        Typ_pattern_parenthesizer.precedence typ_pattern
      in
      let applicand' = parenthesize_typ_pattern applicand in
      (* Parenthesize as application in prefix notation *)
      let applicand'' =
        Typ_pattern_parenthesizer.parenthesize_argument_prefix_operator
          ~parent_precedence applicand'
      in
      let arguments' =
        parenthesize_application_pattern_arguments parent_precedence
          arguments
      in
      Typ.Pattern.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Typ.Pattern.Block { location; elements } ->
      let (l1, t1), xs = elements in
      let t1' = parenthesize_typ_pattern t1
      and xs' = List.map (Pair.map_right parenthesize_typ_pattern) xs in
      let elements' = ((l1, t1'), xs') in
      Typ.Pattern.Block { location; elements = elements' }
    | Typ.Pattern.Parenthesized _ -> typ_pattern

  (** [parenthesize_term_pattern term_pattern] is [term_pattern] with the
      addition of necessary parentheses for printing.

      If this is done after the application of
      {!remove_parentheses_term_pattern}, then the resultant LF term pattern
      can be parsed to the same AST, modulo
      {!remove_parentheses_term_pattern} and without considering locations. *)
  and parenthesize_term_pattern term_pattern =
    match term_pattern with
    | Term.Pattern.Variable _ -> term_pattern
    | Term.Pattern.Constant _ -> term_pattern
    | Term.Pattern.Substitution
        { location; term = term_under_substitution; substitution } ->
      (* Substitutions are left-associative *)
      let term_under_substitution' =
        parenthesize_term_pattern term_under_substitution
      in
      let term_under_substitution'' =
        Term_pattern_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence:
            (Term_pattern_parenthesizer.precedence term_pattern)
          term_under_substitution'
      and substitution' = parenthesize_substitution substitution in
      Term.Pattern.Substitution
        { location
        ; term = term_under_substitution''
        ; substitution = substitution'
        }
    | Term.Pattern.Application
        { location
        ; applicand =
            Term.Pattern.Constant { operator = applicand_operator; _ } as
            applicand
        ; arguments
        }
    (* Term constant application pattern *) ->
      let arguments' =
        parenthesize_operator_application_pattern_arguments
          (Term_pattern_parenthesizer.precedence term_pattern)
          applicand_operator arguments
      in
      Term.Pattern.Application
        { location; applicand; arguments = arguments' }
    | Term.Pattern.Application { location; applicand; arguments }
    (* Arbitrary term application pattern *) ->
      let parent_precedence =
        Term_pattern_parenthesizer.precedence term_pattern
      in
      let applicand' = parenthesize_term_pattern applicand in
      (* Parenthesize as term application in prefix notation *)
      let applicand'' =
        Term_pattern_parenthesizer.parenthesize_argument_prefix_operator
          ~parent_precedence applicand'
      in
      let arguments' =
        parenthesize_application_pattern_arguments parent_precedence
          arguments
      in
      Term.Pattern.Application
        { location; applicand = applicand''; arguments = arguments' }
    | Term.Pattern.Abstraction
        { location; parameter_identifier; parameter_type; body } ->
      let parameter_type' = Option.map parenthesize_typ parameter_type
      and body' = parenthesize_term_pattern body in
      Term.Pattern.Abstraction
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Term.Pattern.Wildcard _ -> term_pattern
    | Term.Pattern.Tuple { location; terms } ->
      let terms' = List1.map parenthesize_term_pattern terms in
      Term.Pattern.Tuple { location; terms = terms' }
    | Term.Pattern.Projection { location; term = projected_term; projection }
      ->
      (* Projections are left-associative *)
      let projected_term' = parenthesize_term_pattern projected_term in
      let projected_term'' =
        Term_pattern_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence:
            (Term_pattern_parenthesizer.precedence term_pattern)
          projected_term'
      in
      Term.Pattern.Projection
        { location; term = projected_term''; projection }
    | Term.Pattern.TypeAnnotated { location; term = annotated_term; typ } ->
      (* Type ascriptions are left-associative *)
      let annotated_term' = parenthesize_term_pattern annotated_term in
      let annotated_term'' =
        Term_pattern_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence:
            (Term_pattern_parenthesizer.precedence term_pattern)
          annotated_term'
      and typ' = parenthesize_typ typ in
      Term.Pattern.TypeAnnotated
        { location; term = annotated_term''; typ = typ' }
    | Term.Pattern.Parenthesized _ -> term_pattern

  (** [parenthesize_application_pattern_arguments parent_precedence arguments]
      is the arguments in [argument] parenthesized as if they were applied to
      a non-operator applicand. *)
  and parenthesize_application_pattern_arguments parent_precedence arguments
      =
    List.map
      (fun argument ->
        let argument' = parenthesize_term_pattern argument in
        Term_pattern_parenthesizer.parenthesize_argument_prefix_operator
          ~parent_precedence argument')
      arguments

  (** [parenthesize_operator_application_pattern_arguments parent_precedence applicand_operator arguments]
      is the arguments in [arguments] parenthesized as if they were applied
      to an operator applicand described by [applicand_operator]. *)
  and parenthesize_operator_application_pattern_arguments parent_precedence
      applicand_operator arguments =
    match Operator.fixity applicand_operator with
    | Fixity.Prefix ->
      parenthesize_prefix_operator_application_pattern_arguments
        parent_precedence arguments
    | Fixity.Infix ->
      assert (List.length arguments = 2);
      let[@warning "-8"] [ left_argument; right_argument ] = arguments in
      parenthesize_infix_operator_application_pattern_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument
    | Fixity.Postfix ->
      assert (List.length arguments = 1);
      let[@warning "-8"] [ argument ] = arguments in
      parenthesize_postfix_operator_application_pattern_arguments
        parent_precedence applicand_operator argument

  and parenthesize_prefix_operator_application_pattern_arguments
      parent_precedence arguments =
    parenthesize_application_pattern_arguments parent_precedence arguments

  and parenthesize_infix_operator_application_pattern_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    match Operator.associativity applicand_operator with
    | Associativity.Left_associative ->
      parenthesize_infix_left_associative_operator_application_pattern_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument
    | Associativity.Right_associative ->
      parenthesize_infix_right_associative_operator_application_pattern_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument
    | Associativity.Non_associative ->
      parenthesize_infix_non_associative_operator_application_pattern_arguments
        parent_precedence applicand_operator ~left_argument ~right_argument

  and parenthesize_infix_left_associative_operator_application_pattern_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    let left_argument' = parenthesize_term_pattern left_argument
    and right_argument' = parenthesize_term_pattern right_argument in
    let left_argument'' =
      match left_argument' with
      | Term.Pattern.Application
          { applicand =
              Term.Pattern.Constant { operator = left_argument_operator; _ }
          ; _
          }
        when Operator.precedence left_argument_operator
             >= Operator.precedence applicand_operator -> left_argument'
      | _ ->
        Term_pattern_parenthesizer
        .parenthesize_left_argument_left_associative_operator
          ~parent_precedence left_argument'
    and right_argument'' =
      match right_argument' with
      | Term.Pattern.Application
          { applicand =
              Term.Pattern.Constant { operator = right_argument_operator; _ }
          ; _
          }
        when Operator.precedence right_argument_operator
             > Operator.precedence applicand_operator
             || Operator.is_right_associative right_argument_operator
                && Operator.precedence right_argument_operator
                   >= Operator.precedence applicand_operator ->
        right_argument'
      | _ ->
        Term_pattern_parenthesizer
        .parenthesize_right_argument_left_associative_operator
          ~parent_precedence right_argument'
    in
    [ left_argument''; right_argument'' ]

  and parenthesize_infix_right_associative_operator_application_pattern_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    let left_argument' = parenthesize_term_pattern left_argument
    and right_argument' = parenthesize_term_pattern right_argument in
    let left_argument'' =
      match left_argument' with
      | Term.Pattern.Application
          { applicand =
              Term.Pattern.Constant { operator = left_argument_operator; _ }
          ; _
          }
        when Operator.precedence left_argument_operator
             > Operator.precedence applicand_operator -> left_argument'
      | _ ->
        Term_pattern_parenthesizer
        .parenthesize_left_argument_right_associative_operator
          ~parent_precedence left_argument'
    and right_argument'' =
      match right_argument' with
      | Term.Pattern.Application
          { applicand =
              Term.Pattern.Constant { operator = right_argument_operator; _ }
          ; _
          }
        when Operator.precedence right_argument_operator
             >= Operator.precedence applicand_operator -> right_argument'
      | _ ->
        Term_pattern_parenthesizer
        .parenthesize_right_argument_right_associative_operator
          ~parent_precedence right_argument'
    in
    [ left_argument''; right_argument'' ]

  and parenthesize_infix_non_associative_operator_application_pattern_arguments
      parent_precedence applicand_operator ~left_argument ~right_argument =
    let left_argument' = parenthesize_term_pattern left_argument
    and right_argument' = parenthesize_term_pattern right_argument in
    let left_argument'' =
      match left_argument' with
      | Term.Pattern.Application
          { applicand =
              Term.Pattern.Constant { operator = left_argument_operator; _ }
          ; _
          }
        when Operator.precedence left_argument_operator
             >= Operator.precedence applicand_operator -> left_argument'
      | _ ->
        Term_pattern_parenthesizer
        .parenthesize_argument_non_associative_operator ~parent_precedence
          left_argument'
    and right_argument'' =
      match right_argument' with
      | Term.Pattern.Application
          { applicand =
              Term.Pattern.Constant { operator = right_argument_operator; _ }
          ; _
          }
        when Operator.precedence right_argument_operator
             >= Operator.precedence applicand_operator -> right_argument'
      | _ ->
        Term_pattern_parenthesizer
        .parenthesize_argument_non_associative_operator ~parent_precedence
          right_argument'
    in
    [ left_argument''; right_argument'' ]

  and parenthesize_postfix_operator_application_pattern_arguments
      parent_precedence applicand_operator argument =
    let argument' = parenthesize_term_pattern argument in
    let argument'' =
      match argument' with
      | Term.Pattern.Application
          { applicand =
              Term.Pattern.Constant { operator = argument_operator; _ }
          ; _
          }
        when Operator.is_postfix applicand_operator
             || Operator.precedence argument_operator
                > Operator.precedence applicand_operator -> argument'
      | _ ->
        Term_pattern_parenthesizer.parenthesize_argument_postfix_operator
          ~parent_precedence argument'
    in
    [ argument'' ]

  let re_parenthesize_typ =
    Fun.(remove_parentheses_typ ~unquote_operators:true >> parenthesize_typ)

  let re_parenthesize_typ_pattern =
    Fun.(
      remove_parentheses_typ_pattern ~unquote_operators:true
      >> parenthesize_typ_pattern)

  let re_parenthesize_term =
    Fun.(
      remove_parentheses_term ~unquote_operators:true >> parenthesize_term)

  let re_parenthesize_term_pattern =
    Fun.(
      remove_parentheses_term_pattern ~unquote_operators:true
      >> parenthesize_term_pattern)

  let re_parenthesize_substitution =
    Fun.(
      remove_parentheses_substitution ~unquote_operators:true
      >> parenthesize_substitution)

  (** {1 Printing} *)

  let rec pp_typ ppf typ =
    match typ with
    | Typ.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_typ applicand
    | Typ.Application
        { applicand = Typ.Constant { identifier; operator; _ }
        ; arguments
        ; _
        } -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@ %a@]" pp_term left_argument
          QualifiedIdentifier.pp identifier pp_term right_argument
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]" pp_term argument
          QualifiedIdentifier.pp identifier)
    | Typ.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_typ applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
        arguments
    | Typ.ForwardArrow { domain; range; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]" pp_typ domain pp_typ range
    | Typ.BackwardArrow { range; domain; _ } ->
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]" pp_typ range pp_typ domain
    | Typ.Pi { parameter_identifier = Option.None; parameter_type; body; _ }
      ->
      Format.fprintf ppf "@[<2>{@ _@ :@ %a@ }@ %a@]" pp_typ parameter_type
        pp_typ body
    | Typ.Pi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_typ body
    | Typ.Block { elements = (Option.None, typ), []; _ } ->
      Format.fprintf ppf "@[<2>block %a]" pp_typ typ
    | Typ.Block { elements = (Option.None, _typ), _nt1 :: _nts; _ } ->
      raise
      @@ Invalid_argument
           "[pp_typ] missing identifier for first type in block"
    | Typ.Block { elements = (Option.Some i1, t1), nts; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]"
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,")
           (fun ppf (i, t) ->
             Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t))
        ((i1, t1) :: nts)
    | Typ.Parenthesized { typ; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_typ typ

  and pp_typ_pattern ppf typ_pattern =
    match typ_pattern with
    | Typ.Pattern.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Typ.Pattern.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_typ_pattern applicand
    | Typ.Pattern.Application
        { applicand = Typ.Pattern.Constant { identifier; operator; _ }
        ; arguments
        ; _
        } -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
             pp_term_pattern)
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@ %a@]" pp_term_pattern left_argument
          QualifiedIdentifier.pp identifier pp_term_pattern right_argument
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]" pp_term_pattern argument
          QualifiedIdentifier.pp identifier)
    | Typ.Pattern.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_typ_pattern applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           pp_term_pattern)
        arguments
    | Typ.Pattern.Block { elements = (Option.None, typ), []; _ } ->
      Format.fprintf ppf "@[<2>block %a]" pp_typ_pattern typ
    | Typ.Pattern.Block { elements = (Option.None, _typ), _nt1 :: _nts; _ }
      ->
      raise
      @@ Invalid_argument
           "[pp_typ_pattern] missing identifier for first type in block"
    | Typ.Pattern.Block { elements = (Option.Some i1, t1), nts; _ } ->
      Format.fprintf ppf "@[<2>block (%a)]"
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,")
           (fun ppf (i, t) ->
             Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ_pattern t))
        ((i1, t1) :: nts)
    | Typ.Pattern.Parenthesized { pattern; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_typ_pattern pattern

  and pp_term ppf term =
    match term with
    | Term.Variable { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Term.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_term applicand
    | Term.Application
        { applicand = Term.Constant { identifier; operator; _ }
        ; arguments
        ; _
        } -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@ %a@]" pp_term left_argument
          QualifiedIdentifier.pp identifier pp_term right_argument
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]" pp_term argument
          QualifiedIdentifier.pp identifier)
    | Term.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_term applicand
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_term)
        arguments
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.None
        ; body
        ; _
        } -> Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type pp_term
        body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
        parameter_identifier pp_term body
    | Term.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_term body
    | Term.Hole _ -> Format.fprintf ppf "_"
    | Term.Substitution { term; substitution; _ } ->
      Format.fprintf ppf "@[<2>%a%a@]" pp_term term pp_substitution
        substitution
    | Term.Tuple { terms; _ } ->
      Format.fprintf ppf "@[<2><%a>@]"
        (List1.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,") pp_term)
        terms
    | Term.Projection { term; projection = `By_position i; _ } ->
      Format.fprintf ppf "@[<2>%a.%d@]" pp_term term i
    | Term.Projection { term; projection = `By_identifier i; _ } ->
      Format.fprintf ppf "@[<2>%a.%a@]" pp_term term Identifier.pp i
    | Term.TypeAnnotated { term; typ; _ } ->
      Format.fprintf ppf "@[<2>%a@ :@ %a@]" pp_term term pp_typ typ
    | Term.Parenthesized { term; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_term term

  and pp_term_pattern ppf term_pattern =
    match term_pattern with
    | Term.Pattern.Variable { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Term.Pattern.Constant { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Term.Pattern.Wildcard _ -> Format.fprintf ppf "_"
    | Term.Pattern.Tuple { terms; _ } ->
      Format.fprintf ppf "@[<2><%a>@]"
        (List1.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,")
           pp_term_pattern)
        terms
    | Term.Pattern.Projection { term; projection = `By_identifier i; _ } ->
      Format.fprintf ppf "@[<2>%a.%a@]" pp_term_pattern term Identifier.pp i
    | Term.Pattern.Projection { term; projection = `By_position i; _ } ->
      Format.fprintf ppf "@[<2>%a.%d@]" pp_term_pattern term i
    | Term.Pattern.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.None
        ; body
        ; _
        } -> Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_term_pattern body
    | Term.Pattern.Abstraction
        { parameter_identifier = Option.None
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_typ parameter_type
        pp_term_pattern body
    | Term.Pattern.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
        parameter_identifier pp_term_pattern body
    | Term.Pattern.Abstraction
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_type = Option.Some parameter_type
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
        parameter_identifier pp_typ parameter_type pp_term_pattern body
    | Term.Pattern.Substitution { term; substitution; _ } ->
      Format.fprintf ppf "@[<2>%a%a@]" pp_term_pattern term pp_substitution
        substitution
    | Term.Pattern.Application { applicand; arguments = []; _ } ->
      Format.fprintf ppf "@[<2>%a@]" pp_term_pattern applicand
    | Term.Pattern.Application
        { applicand = Term.Pattern.Constant { identifier; operator; _ }
        ; arguments
        ; _
        } -> (
      match Operator.fixity operator with
      | Fixity.Prefix ->
        Format.fprintf ppf "@[<2>%a@ %a@]" QualifiedIdentifier.pp identifier
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
             pp_term_pattern)
          arguments
      | Fixity.Infix ->
        assert (List.length arguments = 2);
        let[@warning "-8"] [ left_argument; right_argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@ %a@]" pp_term_pattern left_argument
          QualifiedIdentifier.pp identifier pp_term_pattern right_argument
      | Fixity.Postfix ->
        assert (List.length arguments = 1);
        let[@warning "-8"] [ argument ] = arguments in
        Format.fprintf ppf "@[<2>%a@ %a@]" pp_term_pattern argument
          QualifiedIdentifier.pp identifier)
    | Term.Pattern.Application { applicand; arguments; _ } ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pp_term_pattern applicand
        (List.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           pp_term_pattern)
        arguments
    | Term.Pattern.TypeAnnotated { term; typ; _ } ->
      Format.fprintf ppf "@[<2>%a@ :@ %a@]" pp_term_pattern term pp_typ typ
    | Term.Pattern.Parenthesized { pattern; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_term_pattern pattern

  and pp_substitution ppf substitution =
    match substitution with
    | Substitution.{ extends_identity = false; terms = []; _ } ->
      Format.fprintf ppf "[]"
    | Substitution.{ extends_identity = true; terms = []; _ } ->
      Format.fprintf ppf "[..]"
    | Substitution.{ extends_identity = false; terms; _ } ->
      Format.fprintf ppf "@[<2>[%a]@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,") pp_term)
        terms
    | Substitution.{ extends_identity = true; terms; _ } ->
      Format.fprintf ppf "@[<2>[..,@,%a]@]"
        (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,") pp_term)
        terms

  module Debug = struct
    let rec pp_typ ppf typ =
      match typ with
      | Typ.Constant { identifier; _ } ->
        Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
      | Typ.Application { applicand; arguments; _ } ->
        Format.fprintf ppf "@[<2>TypeApplication(%a(%a))@]" pp_typ applicand
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
          arguments
      | Typ.ForwardArrow { domain; range; _ } ->
        Format.fprintf ppf "@[<2>TypeArrow(%a@ ->@ %a)@]" pp_typ domain
          pp_typ range
      | Typ.BackwardArrow { range; domain; _ } ->
        Format.fprintf ppf "@[<2>TypeArrow(%a@ <-@ %a)@]" pp_typ range pp_typ
          domain
      | Typ.Pi
          { parameter_identifier = Option.None; parameter_type; body; _ } ->
        Format.fprintf ppf "@[<2>TypePi({@ _@ :@ %a@ }@ %a)@]" pp_typ
          parameter_type pp_typ body
      | Typ.Pi
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TypePi({@ %a@ :@ %a@ }@ %a)@]" Identifier.pp
          parameter_identifier pp_typ parameter_type pp_typ body
      | Typ.Block { elements = (Option.None, typ), []; _ } ->
        Format.fprintf ppf "@[<2>TypeBlock(block %a)]" pp_typ typ
      | Typ.Block { elements = (Option.None, _typ), _nt1 :: _nts; _ } ->
        raise
        @@ Invalid_argument
             "[pp_typ] missing identifier for first type in block"
      | Typ.Block { elements = (Option.Some i1, t1), nts; _ } ->
        Format.fprintf ppf "@[<2>TypeBlock(block (%a))]"
          (List.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,")
             (fun ppf (i, t) ->
               Format.fprintf ppf "%a@ :@ %a" Identifier.pp i pp_typ t))
          ((i1, t1) :: nts)
      | Typ.Parenthesized { typ; _ } ->
        Format.fprintf ppf "@[<2>TypeParenthesized(%a)@]" pp_typ typ

    and pp_term ppf term =
      match term with
      | Term.Variable { identifier; _ } ->
        Format.fprintf ppf "%a" Identifier.pp identifier
      | Term.Constant { identifier; _ } ->
        Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
      | Term.Application { applicand; arguments; _ } ->
        Format.fprintf ppf "@[<2>TermApplication(%a(%a))@]" pp_term applicand
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") pp_term)
          arguments
      | Term.Abstraction
          { parameter_identifier = Option.None
          ; parameter_type = Option.None
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\_.@ %a)@]" pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.None
          ; parameter_type = Option.Some parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\_:%a.@ %a)@]" pp_typ
          parameter_type pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type = Option.None
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\%a.@ %a)@]" Identifier.pp
          parameter_identifier pp_term body
      | Term.Abstraction
          { parameter_identifier = Option.Some parameter_identifier
          ; parameter_type = Option.Some parameter_type
          ; body
          ; _
          } ->
        Format.fprintf ppf "@[<2>TermAbstraction(\\%a:%a.@ %a)@]"
          Identifier.pp parameter_identifier pp_typ parameter_type pp_term
          body
      | Term.Hole { variant = `Underscore; _ } -> Format.fprintf ppf "_"
      | Term.Hole { variant = `Unlabelled; _ } -> Format.fprintf ppf "?"
      | Term.Hole { variant = `Labelled label; _ } ->
        Format.fprintf ppf "?%s" label
      | Term.Substitution { term; substitution; _ } ->
        Format.fprintf ppf "@[<2>TermSubstitution(%a%a)@]" pp_term term
          pp_substitution substitution
      | Term.Tuple { terms; _ } ->
        Format.fprintf ppf "@[<2>TermTuple(<%a>)@]"
          (List1.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@,") pp_term)
          terms
      | Term.Projection { term; projection = `By_position i; _ } ->
        Format.fprintf ppf "@[<2>TermProjection(%a.%d)@]" pp_term term i
      | Term.Projection { term; projection = `By_identifier i; _ } ->
        Format.fprintf ppf "@[<2>TermProjection(%a.%a)@]" pp_term term
          Identifier.pp i
      | Term.TypeAnnotated { term; typ; _ } ->
        Format.fprintf ppf "@[<2>TermAnnotated(%a@ :@ %a)@]" pp_term term
          pp_typ typ
      | Term.Parenthesized { term; _ } ->
        Format.fprintf ppf "@[<2>TermParenthesized(%a)@]" pp_term term

    and pp_substitution ppf substitution =
      match substitution with
      | Substitution.{ extends_identity = false; terms = []; _ } ->
        Format.fprintf ppf "Substitution([])"
      | Substitution.{ extends_identity = true; terms = []; _ } ->
        Format.fprintf ppf "Substitution([..])"
      | Substitution.{ extends_identity = false; terms; _ } ->
        Format.fprintf ppf "@[<2>Substitution([%a])@]"
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,") pp_term)
          terms
      | Substitution.{ extends_identity = true; terms; _ } ->
        Format.fprintf ppf "@[<2>Substitution([..,@,%a])@]"
          (List.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@,") pp_term)
          terms
  end
end
