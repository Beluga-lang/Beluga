open Support
open Beluga_syntax
open Parser_combinator

module type PARSER_STATE = sig
  include PARSER_STATE

  include PARSER_LOCATION_STATE with type state := state

  include BACKTRACKING_STATE with type state := state
end

module type COMMON_PARSER = sig
  include Parser_combinator.PARSER

  val keyword : string -> unit t

  val integer : int t

  val dot_integer : int t

  val pragma : string -> unit t

  val string_literal : string t

  val dot : unit t

  val dots : unit t

  val comma : unit t

  val colon : unit t

  val semicolon : unit t

  val slash : unit t

  val equals : unit t

  val lambda : unit t

  val hat : unit t

  val underscore : unit t

  val pipe : unit t

  val forward_arrow : unit t

  val backward_arrow : unit t

  val thick_forward_arrow : unit t

  val plus : unit t

  val star : unit t

  val hash : unit t

  val double_colon : unit t

  val turnstile : unit t

  val turnstile_hash : unit t

  val left_parenthesis : unit t

  val right_parenthesis : unit t

  val left_brace : unit t

  val right_brace : unit t

  val left_brack : unit t

  val right_brack : unit t

  val left_angle : unit t

  val right_angle : unit t

  val parens : 'a t -> 'a t

  val braces : 'a t -> 'a t

  val bracks : 'a t -> 'a t

  val angles : 'a t -> 'a t

  val opt_parens : 'a t -> 'a t

  val opt_braces : 'a t -> 'a t

  val opt_bracks : 'a t -> 'a t

  val opt_angles : 'a t -> 'a t

  val hash_parens : 'a t -> 'a t

  val dollar_parens : 'a t -> 'a t

  val hash_bracks : 'a t -> 'a t

  val dollar_bracks : 'a t -> 'a t

  val identifier : Identifier.t t

  val dot_identifier : Identifier.t t

  val hash_identifier : Identifier.t t

  val dollar_identifier : Identifier.t t

  val omittable_identifier : Identifier.t option t

  val omittable_hash_identifier : Identifier.t option t

  val omittable_dollar_identifier : Identifier.t option t

  val qualified_identifier : Qualified_identifier.t t

  val dot_qualified_identifier : Qualified_identifier.t t

  val qualified_or_plain_identifier :
    [> `Plain of Identifier.t | `Qualified of Qualified_identifier.t ] t

  val omittable_meta_object_identifier :
    (Identifier.t option * [> `Dollar | `Hash | `Plain ]) t

  val meta_object_identifier :
    (Identifier.t * [> `Dollar | `Hash | `Plain ]) t

  val hole : [> `Labelled of Identifier.t | `Unlabelled ] parser

  val block_comment : (Location.t * string) t
end

module Make
    (Parser : Parser_combinator.PARSER
                with type token = Located_token.t
                 and type location = Location.t) :
  COMMON_PARSER
    with type token = Located_token.t
     and type location = Location.t
     and type state = Parser.state
     and type input = Parser.input = struct
  include Parser

  exception Unexpected_end_of_input of { expected : Token.t }

  exception
    Unexpected_token of
      { expected : Token.t
      ; actual : Token.t
      }

  let token expected =
    satisfy (function
      | Option.Some { Located_token.token = actual; _ } ->
          if Token.equal expected actual then Result.ok ()
          else Result.error (Unexpected_token { expected; actual })
      | Option.None -> Result.error (Unexpected_end_of_input { expected }))

  exception
    Expected_keyword of
      { expected_keyword : string
      ; actual : Token.t Option.t
      }

  let keyword = function
    | "and" -> token Token.KW_AND
    | "block" -> token Token.KW_BLOCK
    | "case" -> token Token.KW_CASE
    | "if" -> token Token.KW_IF
    | "then" -> token Token.KW_THEN
    | "else" -> token Token.KW_ELSE
    | "impossible" -> token Token.KW_IMPOSSIBLE
    | "let" -> token Token.KW_LET
    | "in" -> token Token.KW_IN
    | "of" -> token Token.KW_OF
    | "rec" -> token Token.KW_REC
    | "schema" -> token Token.KW_SCHEMA
    | "some" -> token Token.KW_SOME
    | "fn" -> token Token.KW_FN
    | "mlam" -> token Token.KW_MLAM
    | "module" -> token Token.KW_MODULE
    | "struct" -> token Token.KW_STRUCT
    | "end" -> token Token.KW_END
    | "total" -> token Token.KW_TOTAL
    | "trust" -> token Token.KW_TRUST
    | "type" -> token Token.KW_TYPE
    | "ctype" -> token Token.KW_CTYPE
    | "prop" -> token Token.KW_PROP
    | "inductive" -> token Token.KW_INDUCTIVE
    | "coinductive" -> token Token.KW_COINDUCTIVE
    | "stratified" -> token Token.KW_STRATIFIED
    | "LF" -> token Token.KW_LF
    | "fun" -> token Token.KW_FUN
    | "typedef" -> token Token.KW_TYPEDEF
    | "proof" -> token Token.KW_PROOF
    | "as" -> token Token.KW_AS
    | "by" -> token Token.KW_BY
    | "suffices" -> token Token.KW_SUFFICES
    | "toshow" -> token Token.KW_TOSHOW
    | kw ->
        satisfy (function
          | Option.Some { Located_token.token = Token.IDENT kw'; _ }
            when String.equal kw kw' ->
              Result.ok ()
          | Option.Some { Located_token.token; _ } ->
              Result.error
                (Expected_keyword
                   { expected_keyword = kw; actual = Option.some token })
          | Option.None ->
              Result.error
                (Expected_keyword
                   { expected_keyword = kw; actual = Option.none }))

  exception Expected_integer_literal of { actual : Token.t Option.t }

  let integer =
    satisfy (function
      | Option.Some { Located_token.token = Token.INTLIT k; _ } ->
          Result.ok k
      | Option.Some { Located_token.token; _ } ->
          Result.error
            (Expected_integer_literal { actual = Option.some token })
      | Option.None ->
          Result.error (Expected_integer_literal { actual = Option.none }))

  exception Expected_dot_integer_literal of { actual : Token.t Option.t }

  let dot_integer =
    satisfy (function
      | Option.Some { Located_token.token = Token.DOT_INTLIT k; _ } ->
          Result.ok k
      | Option.Some { Located_token.token; _ } ->
          Result.error
            (Expected_dot_integer_literal { actual = Option.some token })
      | Option.None ->
          Result.error
            (Expected_dot_integer_literal { actual = Option.none }))

  exception
    Expected_pragma of
      { expected_pragma : string
      ; actual : Token.t Option.t
      }

  let pragma s =
    satisfy (function
      | Option.Some { Located_token.token = Token.PRAGMA s'; _ }
        when String.equal s s' ->
          Result.ok ()
      | Option.Some { Located_token.token; _ } ->
          Result.error
            (Expected_pragma
               { expected_pragma = s; actual = Option.some token })
      | Option.None ->
          Result.error
            (Expected_pragma { expected_pragma = s; actual = Option.none }))

  exception Expected_string_literal of { actual : Token.t Option.t }

  let string_literal =
    satisfy (function
      | Option.Some { Located_token.token = Token.STRING s; _ } ->
          Result.ok s
      | Option.Some { Located_token.token; _ } ->
          Result.error
            (Expected_string_literal { actual = Option.some token })
      | Option.None ->
          Result.error (Expected_string_literal { actual = Option.none }))

  (** {1 Tokens} *)

  let dots = token Token.DOTS

  let comma = token Token.COMMA

  let colon = token Token.COLON

  let semicolon = token Token.SEMICOLON

  let slash = token Token.SLASH

  let equals = token Token.EQUALS

  let lambda = token Token.LAMBDA

  let hat = token Token.HAT

  let underscore = token Token.UNDERSCORE

  let pipe = token Token.PIPE

  let forward_arrow = token Token.ARROW

  let backward_arrow = token Token.BACKARROW

  let thick_forward_arrow = token Token.THICK_ARROW

  let plus = token Token.PLUS

  let star = token Token.STAR

  let hash = token Token.HASH

  let double_colon = token Token.DOUBLE_COLON

  let turnstile = token Token.TURNSTILE

  let turnstile_hash = token Token.TURNSTILE_HASH

  (** {1 Parentheses} *)

  let left_parenthesis = token Token.LPAREN

  let right_parenthesis = token Token.RPAREN

  let left_brace = token Token.LBRACE

  let right_brace = token Token.RBRACE

  let left_brack = token Token.LBRACK

  let right_brack = token Token.RBRACK

  let left_angle = token Token.LANGLE

  let right_angle = token Token.RANGLE

  (** [parens p] parses [`(' p `)']. *)
  let parens p = left_parenthesis &> p <& right_parenthesis

  (** [braces p] parses [`{' p `}']. *)
  let braces p = left_brace &> p <& right_brace

  (** [bracks p] parses [`\[' p `\]']. *)
  let bracks p = left_brack &> p <& right_brack

  (** [angles p] parses [`<' p `>']. *)
  let angles p = left_angle &> p <& right_angle

  (** [opt_parens p] parses [`(' p `)' | p]. *)
  let opt_parens p = alt (parens p) p

  (** [opt_braces p] parses [`{' p `}' | p]. *)
  let opt_braces p = alt (braces p) p

  (** [opt_bracks p] parses [`\[' p `\]' | p]. *)
  let opt_bracks p = alt (bracks p) p

  (** [opt_angles p] parses [`<' p `>' | p]. *)
  let opt_angles p = alt (angles p) p

  let hash_left_parenthesis = token Token.HASH_LPAREN

  (** [hash_parens p] parses [`#(' p `)']. *)
  let hash_parens p = hash_left_parenthesis &> p <& right_parenthesis

  let dollar_left_parenthesis = token Token.DOLLAR_LPAREN

  (** [dollar_parens p] parses [`$(' p `)']. *)
  let dollar_parens p = dollar_left_parenthesis &> p <& right_parenthesis

  let hash_left_brack = token Token.HASH_LBRACK

  (** [hash_bracks p] parses [`#\[' p `\]']. *)
  let hash_bracks p = hash_left_brack &> p <& right_brack

  let dollar_left_brack = token Token.DOLLAR_LBRACK

  (** [dollar_bracks p] parses [`$\[' p `\]']. *)
  let dollar_bracks p = dollar_left_brack &> p <& right_brack

  (** {1 Identifiers} *)

  exception Expected_identifier of { actual : Token.t Option.t }

  let identifier =
    satisfy (function
      | Option.Some
          { Located_token.token = Token.IDENT identifier; location } ->
          Result.ok (Identifier.make ~location identifier)
      | Option.Some { Located_token.token; _ } ->
          Result.error (Expected_identifier { actual = Option.some token })
      | Option.None ->
          Result.error (Expected_identifier { actual = Option.none }))
    |> labelled "Identifier"

  exception Expected_dot_identifier of { actual : Token.t Option.t }

  let dot_identifier =
    satisfy (function
      | Option.Some
          { Located_token.token = Token.DOT_IDENT identifier; location } ->
          Result.ok (Identifier.make ~location identifier)
      | Option.Some { Located_token.token; _ } ->
          Result.error
            (Expected_dot_identifier { actual = Option.some token })
      | Option.None ->
          Result.error (Expected_dot_identifier { actual = Option.none }))
    |> labelled "Identifier prefixed by a dot symbol"

  (*=
     Old style LF declarations and pragmas are terminated with a dot.
     However, the typical lexical convention is such that
     [base : tp. arr : tp -> tp -> tp.] is tokenized as
     [IDENT "base"; COLON; IDENT "tp"; DOT; IDENT "arr"; COLON; ...].
     This causes [IDENT "tp"; DOT; IDENT "arr"] to be parsed as a qualified
     identifier.

     The lexical convention is adjusted with the addition of the
     [DOT_IDENT _] and [DOT_INTLIT _] tokens for the cases where a dot is
     immediately followed (white-space sensitive) by an identifier or integer
     respectively. In the case where a [DOT] is expected, [DOT_IDENT _] and
     [DOT_INTLIT _] may be accepted instead, but only if we then insert an
     [IDENT] or [INTLIT] token in the input stream. This effectively restores
     the initial tokenization as [DOT; IDENT _] and [DOT; INTLIT _]. *)
  let dot =
    let dot_identifier_and_insert_ident =
      span dot_identifier >>= fun (location, identifier) ->
      let ident_token =
        Located_token.make ~location
          ~token:(Token.IDENT (Identifier.name identifier))
      in
      insert_token ident_token
    and dot_integer_and_insert_intlit =
      span dot_integer >>= fun (location, integer) ->
      let intlit_token =
        Located_token.make ~location ~token:(Token.INTLIT integer)
      in
      insert_token intlit_token
    in
    choice
      [ token Token.DOT
      ; dot_identifier_and_insert_ident
      ; dot_integer_and_insert_intlit
      ]

  exception Expected_hash_identifier of { actual : Token.t Option.t }

  let hash_identifier =
    satisfy (function
      | Option.Some
          { Located_token.token = Token.HASH_IDENT identifier; location } ->
          Result.ok (Identifier.make ~location identifier)
      | Option.Some { Located_token.token; _ } ->
          Result.error
            (Expected_hash_identifier { actual = Option.some token })
      | Option.None ->
          Result.error (Expected_hash_identifier { actual = Option.none }))
    |> labelled "Identifier prefixed by a hash symbol"

  exception Expected_dollar_identifier of { actual : Token.t Option.t }

  let dollar_identifier =
    satisfy (function
      | Option.Some { Located_token.token = Token.DOLLAR_IDENT s; location }
        ->
          Result.ok (Identifier.make ~location s)
      | Option.Some { Located_token.token; _ } ->
          Result.error
            (Expected_dollar_identifier { actual = Option.some token })
      | Option.None ->
          Result.error (Expected_dollar_identifier { actual = Option.none }))
    |> labelled "Identifier prefixed by a dollar symbol"

  (*=
    <omittable-identifier> ::=
      | `_'
      | <identifier>
  *)
  let omittable_identifier =
    let underscore =
      underscore $> (fun () -> Option.none) |> labelled "Omitted identifier"
    and identifier = identifier $> Option.some in
    alt underscore identifier

  (*=
    <omittable-hash-identifier> ::=
      | `#_'
      | <hash-identifier>
  *)
  let omittable_hash_identifier =
    let hash_underscore =
      token Token.HASH_BLANK
      $> (fun () -> Option.none)
      |> labelled "Omitted hash identifier"
    and hash_identifier = hash_identifier $> Option.some in
    alt hash_underscore hash_identifier

  (*=
    <omittable-dollar-identifier> ::=
      | `$_'
      | <dollar-identifier>
  *)
  let omittable_dollar_identifier =
    alt
      (token Token.DOLLAR_BLANK $> fun () -> Option.none)
      (dollar_identifier $> Option.some)

  (*=
    <qualified-identifier> ::= <identifier> (<dot-identifier>)*
  *)
  let qualified_identifier =
    seq2 identifier (many dot_identifier) |> span
    $> fun (location, (head, tail)) ->
    let namespaces, identifier = List1.unsnoc (List1.from head tail) in
    Qualified_identifier.make ~location ~namespaces identifier

  (*=
    <dot-qualified-identifier> ::= <dot-identifier>+
  *)
  let dot_qualified_identifier =
    some dot_identifier |> span $> fun (location, identifiers) ->
    let namespaces, identifier = List1.unsnoc identifiers in
    Qualified_identifier.make ~location ~namespaces identifier

  (*=
    <qualified-or-plain-identifier> ::=
      | <identifier>
      | <identifier> (<dot-identifier>)*
  *)
  let qualified_or_plain_identifier =
    seq2 identifier (many dot_identifier) |> span $> function
    | _, (head, []) -> `Plain head
    | location, (head, tail) ->
        let namespaces, identifier = List1.unsnoc (List1.from head tail) in
        `Qualified
          (Qualified_identifier.make ~location ~namespaces identifier)

  let omittable_meta_object_identifier =
    let plain = omittable_identifier $> fun i -> (i, `Plain)
    and hash = omittable_hash_identifier $> fun i -> (i, `Hash)
    and dollar = omittable_dollar_identifier $> fun i -> (i, `Dollar) in
    choice [ plain; hash; dollar ]

  let meta_object_identifier =
    let plain = identifier $> fun i -> (i, `Plain)
    and hash = hash_identifier $> fun i -> (i, `Hash)
    and dollar = dollar_identifier $> fun i -> (i, `Dollar) in
    choice [ plain; hash; dollar ]

  exception Expected_hole of { actual : Token.t Option.t }

  let hole =
    satisfy (function
      | Option.Some { Located_token.token = Token.HOLE Option.None; _ } ->
          Result.ok `Unlabelled
      | Option.Some
          { Located_token.token = Token.HOLE (Option.Some label); location }
        ->
          Result.ok (`Labelled (Identifier.make ~location label))
      | Option.Some { Located_token.token; _ } ->
          Result.error (Expected_hole { actual = Option.some token })
      | Option.None -> Result.error (Expected_hole { actual = Option.none }))

  exception Expected_block_comment of { actual : Token.t Option.t }

  let block_comment =
    satisfy (function
      | Option.Some
          { Located_token.token = Token.BLOCK_COMMENT content; location } ->
          Result.ok (location, content)
      | Option.Some { Located_token.token; _ } ->
          Result.error
            (Expected_block_comment { actual = Option.some token })
      | Option.None ->
          Result.error (Expected_block_comment { actual = Option.none }))

  (** {1 Exceptions Printing} *)

  let () =
    Error.register_exception_printer (function
      | Parser_error cause ->
          let cause_printer = Error.find_printer cause in
          Format.dprintf "@[Failed to parse %t@]" cause_printer
      | Labelled_exception { label; cause } ->
          let cause_printer = Error.find_printer cause in
          Format.dprintf "%s.@;@[%t@]" label cause_printer
      | No_more_choices exceptions ->
          let exception_printers = List.map Error.find_printer exceptions in
          Format.dprintf "@[<v 2>Exhausted alternatives in parsing:@,%a@]"
            (List.pp ~pp_sep:Format.pp_print_cut
               (fun ppf exception_printer ->
                 Format.fprintf ppf "- @[%t@]" exception_printer))
            exception_printers
      | Expected_end_of_input ->
          Format.dprintf "%a" Format.pp_print_text
            "Expected the parser input to end here."
      | Unexpected_end_of_input { expected } ->
          Format.dprintf
            "Expected the token `%a', but reached the end of input." Token.pp
            expected
      | Unexpected_token { expected; actual } ->
          Format.dprintf "Expected the token `%a', but got the token `%a'."
            Token.pp expected Token.pp actual
      | Expected_keyword { expected_keyword; actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected the keyword `%s', but got the token `%a'."
                expected_keyword Token.pp actual
          | Option.None ->
              Format.dprintf
                "Expected the keyword `%s', but reached the end of input."
                expected_keyword)
      | Expected_integer_literal { actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected an integer literal, but got the token `%a'."
                Token.pp actual
          | Option.None ->
              Format.dprintf "%a" Format.pp_print_text
                "Expected an integer literal, but reached the end of input.")
      | Expected_dot_integer_literal { actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected a number prefixed by a dot, but got the token \
                 `%a'."
                Token.pp actual
          | Option.None ->
              Format.dprintf "%a" Format.pp_print_text
                "Expected a number prefixed by a dot, but reached the end \
                 of input.")
      | Expected_pragma { expected_pragma; actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected a `--%s' pragma, but got the token `%a'."
                expected_pragma Token.pp actual
          | Option.None ->
              Format.dprintf
                "Expected a `--%s' pragma, but reached the end of input."
                expected_pragma)
      | Expected_string_literal { actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected a string literal, but got the token `%a'." Token.pp
                actual
          | Option.None ->
              Format.dprintf "%a" Format.pp_print_text
                "Expected a string literal, but reached the end of input.")
      | Expected_identifier { actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected an identifier, but got the token `%a'." Token.pp
                actual
          | Option.None ->
              Format.dprintf
                "Expected an identifier, but reached the end of input.")
      | Expected_dot_identifier { actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected an identifier prefixed by a dot `.', but got the \
                 token `%a'."
                Token.pp actual
          | Option.None ->
              Format.dprintf "%a" Format.pp_print_text
                "Expected an identifier prefixed by a dot `.', but reached \
                 the end of input.")
      | Expected_hash_identifier { actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected an identifier prefixed by a hash sign `#id', but \
                 got the token `%a'."
                Token.pp actual
          | Option.None ->
              Format.dprintf "%a" Format.pp_print_text
                "Expected an identifier prefixed by a hash sign `#id', but \
                 reached the end of input.")
      | Expected_dollar_identifier { actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected an identifier prefixed by a dollar sign `$id', \
                 but got the token `%a'."
                Token.pp actual
          | Option.None ->
              Format.dprintf "%a" Format.pp_print_text
                "Expected an identifier prefixed by a dollar sign `$id', \
                 but reached the end of input.")
      | Expected_hole { actual } -> (
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected an unnamed hole `?' or a labelled hole `?id', but \
                 got the token `%a'."
                Token.pp actual
          | Option.None ->
              Format.dprintf "%a" Format.pp_print_text
                "Expected an unnamed hole `?' or a labelled hole `?id', but \
                 reached the end of input.")
      | Expected_block_comment { actual } -> (
          (* Workaround format string errors when inputting the documentation
             comment delimiters *)
          let left_delimiter = "%{{"
          and right_delimiter = "}}%" in
          match actual with
          | Option.Some actual ->
              Format.dprintf
                "Expected a block comment delimited by `%s' and `%s', but \
                 got the token `%a'."
                left_delimiter right_delimiter Token.pp actual
          | Option.None ->
              Format.dprintf
                "Expected a block comment delimited by `%s' and `%s', but \
                 reached the end of input."
                left_delimiter right_delimiter)
      | cause -> Error.raise_unsupported_exception_printing cause)
end
