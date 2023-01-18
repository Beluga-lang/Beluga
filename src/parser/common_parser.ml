open Support
open Beluga_syntax

include Parser_combinator.Make (struct
  type t = Location.t * Token.t

  let location = Pair.fst
end)

exception
  Unexpected_token of
    { expected : Token.t
    ; actual : Token.t
    }

let token expected =
  satisfy (fun (_location, actual) ->
      if Token.equal expected actual then Result.ok ()
      else Result.error (Unexpected_token { expected; actual }))

exception Expected_keyword of string

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
        | _location, Token.IDENT kw' when String.equal kw kw' -> Result.ok ()
        | _location, _token -> Result.error (Expected_keyword kw))

exception Expected_integer_literal

let integer =
  satisfy (function
    | _location, Token.INTLIT k -> Result.ok k
    | _location, _token -> Result.error Expected_integer_literal)

exception Expected_dot_number

let dot_integer =
  satisfy (function
    | _location, Token.DOT_NUMBER k -> Result.ok k
    | _location, _token -> Result.error Expected_dot_number)

exception Expected_pragma of string

let pragma s =
  satisfy (function
    | _location, Token.PRAGMA s' when String.equal s s' -> Result.ok ()
    | _location, _token -> Result.error (Expected_pragma s))

exception Expected_string_literal

let string_literal =
  satisfy (function
    | _location, Token.STRING s -> Result.ok s
    | _location, _token -> Result.error Expected_string_literal)

(** {1 Tokens} *)

let dot = token Token.DOT

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

exception Expected_identifier

let identifier =
  satisfy (function
    | location, Token.IDENT identifier ->
        Result.ok (Identifier.make ~location identifier)
    | _location, _token -> Result.error Expected_identifier)

exception Expected_dot_identifier

let dot_identifier =
  satisfy (function
    | location, Token.DOT_IDENT identifier ->
        Result.ok (Identifier.make ~location identifier)
    | _location, _token -> Result.error Expected_dot_identifier)

exception Expected_hash_identifier

let hash_identifier =
  satisfy (function
    | location, Token.HASH_IDENT identifier ->
        Result.ok (Identifier.make ~location identifier)
    | _location, _token -> Result.error Expected_hash_identifier)

exception Expected_dollar_identifier

let dollar_identifier =
  satisfy (function
    | location, Token.DOLLAR_IDENT s ->
        Result.ok (Identifier.make ~location s)
    | _location, _token -> Result.error Expected_dollar_identifier)

(*=
    <omittable-identifier> ::=
      | `_'
      | <identifier>
*)
let omittable_identifier =
  alt
    (token Token.UNDERSCORE $> fun () -> Option.none)
    (identifier $> Option.some)

(*=
    <omittable-hash-identifier> ::=
      | `#_'
      | <hash-identifier>
*)
let omittable_hash_identifier =
  alt
    (token Token.HASH_BLANK $> fun () -> Option.none)
    (hash_identifier $> Option.some)

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
   <qualified-identifier> ::= <identifier> <dot-identifier>*
*)
let[@warning "-32"] qualified_identifier =
  seq2 identifier (many dot_identifier) |> span
  $> fun (location, (head, tail)) ->
  let modules, identifier = List1.unsnoc (List1.from head tail) in
  Qualified_identifier.make ~location ~modules identifier

(*=
   <dot-qualified-identifier> ::= <dot-identifier>+
*)
let dot_qualified_identifier =
  some dot_identifier |> span $> fun (location, identifiers) ->
  let modules, identifier = List1.unsnoc identifiers in
  Qualified_identifier.make ~location ~modules identifier

(*=
    <qualified-or-plain-identifier> ::=
      | <identifier>
      | <identifier> <dot-identifier>*
*)
let qualified_or_plain_identifier =
  seq2 identifier (many dot_identifier) |> span $> function
  | _, (head, []) -> `Plain head
  | location, (head, tail) ->
      let modules, identifier = List1.unsnoc (List1.from head tail) in
      `Qualified (Qualified_identifier.make ~location ~modules identifier)

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

exception Expected_hole

let hole =
  satisfy (function
    | _location, Token.HOLE "" -> Result.ok `Unlabelled
    | location, Token.HOLE label ->
        Result.ok (`Labelled (Identifier.make ~location label))
    | _location, _token -> Result.error Expected_hole)
  |> labelled "hole"

exception Expected_block_comment

let block_comment =
  satisfy (function
    | location, Token.BLOCK_COMMENT content -> Result.ok (location, content)
    | _location, _token -> Result.error Expected_block_comment)

(** {1 Exceptions Printing} *)

let rec flatten_choice_exceptions exceptions_rev acc =
  match exceptions_rev with
  | [] -> List.rev acc
  | No_more_choices e :: es ->
      flatten_choice_exceptions es (flatten_choice_exceptions e acc)
  | e :: es -> flatten_choice_exceptions es (e :: acc)

let pp_exception' ppf = function
  | Labelled_exception { label; cause } ->
      Format.fprintf ppf "@[<v 0>%s:@,%s@]" label (Printexc.to_string cause)
  | No_more_choices exceptions_rev ->
      let exceptions = flatten_choice_exceptions exceptions_rev [] in
      let exceptions_strings =
        List.map
          (fun exn -> String.split_on_char '\n' (Printexc.to_string exn))
          exceptions
      in
      Format.fprintf ppf "@[<v 2>Exhausted alternatives in parsing:@,%a@]"
        (List.pp ~pp_sep:Format.pp_print_cut (fun ppf exception_lines ->
             Format.fprintf ppf "- @[<v 0>%a@]"
               (List.pp ~pp_sep:Format.pp_print_cut Format.pp_print_string)
               exception_lines))
        exceptions_strings
  | _ ->
      Error.raise (Invalid_argument "[pp_exception'] unsupported exception")

let pp_exception ppf = function
  | Parser_error (Labelled_exception { label; cause }) ->
      Format.fprintf ppf "@[<v 0>Parse error for %s.@,%s@]" label
        (Printexc.to_string cause)
  | Parser_error cause ->
      Format.fprintf ppf "@[<v 0>Parse error.@,%s@]"
        (Printexc.to_string cause)
  | Expected_end_of_input ->
      Format.fprintf ppf "Expected the parser input to end."
  | Unexpected_end_of_input ->
      Format.fprintf ppf
        "Unexpectedly reached the end of input during parsing."
  | Unexpected_token { expected; actual } ->
      Format.fprintf ppf "Expected the token `%a', but got the token `%a'."
        Token.pp expected Token.pp actual
  | Expected_keyword kw -> Format.fprintf ppf "Expected the keyword `%s'." kw
  | Expected_integer_literal ->
      Format.fprintf ppf "Expected an integer literal."
  | Expected_dot_number ->
      Format.fprintf ppf "Expected a number prefixed by a dot."
  | Expected_pragma p -> Format.fprintf ppf "Expected pragma `--%s'." p
  | Expected_string_literal ->
      Format.fprintf ppf "Expected a string literal."
  | Expected_identifier -> Format.fprintf ppf "Expected an identifier."
  | Expected_dot_identifier ->
      Format.fprintf ppf "Expected an identifier prefixed by a dot `.'."
  | Expected_hash_identifier ->
      Format.fprintf ppf
        "Expected an identifier prefixed by a hash sign `#'."
  | Expected_dollar_identifier ->
      Format.fprintf ppf
        "Expected an identifier prefixed by a dollar sign `$'."
  | Expected_hole ->
      Format.fprintf ppf
        "Expected an unnamed hole `?' or a labelled hole `?id'."
  | Expected_block_comment -> Format.fprintf ppf "Expected a block comment."
  | cause -> pp_exception' ppf cause

let () =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify pp_exception exn) with
      | Invalid_argument _ -> Option.none)
