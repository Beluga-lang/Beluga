open Support
open Beluga_syntax

include
  Centiparsec.Make
    (Location)
    (struct
      type t = Location.t * Token.t

      let location = Pair.fst
    end)

exception
  Unexpected_token of
    { expected : Token.t
    ; actual : Token.t
    }

let token t =
  satisfy (fun (_location, token) ->
      if Token.equal t token then Result.ok ()
      else Result.error (Unexpected_token { expected = t; actual = token }))

let tokens ts = traverse_void token ts

let keyword kw = token (Token.IDENT kw)

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

let pragma s = token (Token.PRAGMA s)

exception Expected_string_literal

let string_literal =
  satisfy (function
    | _location, Token.STRING s -> Result.ok s
    | _location, _token -> Result.error Expected_string_literal)

(** [bracketed start stop p] is the parser that runs [p] between [start] and
    [stop] whose results are ignored. *)
let bracketed start stop p = start &> p <& stop

(** [bracketed' b p] is the parser that runs [p] between the two instances of
    the same parser [b] whose results are ignored. *)
let bracketed' b p = bracketed b b p

exception Expected_left_parenthesis

let left_parenthesis =
  satisfy (function
    | _location, Token.LPAREN -> Result.ok ()
    | _location, _token -> Result.error Expected_left_parenthesis)

exception Expected_right_parenthesis

let right_parenthesis =
  satisfy (function
    | _location, Token.RPAREN -> Result.ok ()
    | _location, _token -> Result.error Expected_right_parenthesis)

exception Expected_left_brace

let left_brace =
  satisfy (function
    | _location, Token.LBRACE -> Result.ok ()
    | _location, _token -> Result.error Expected_left_brace)

exception Expected_right_brace

let right_brace =
  satisfy (function
    | _location, Token.RBRACE -> Result.ok ()
    | _location, _token -> Result.error Expected_right_brace)

exception Expected_left_brack

let left_brack =
  satisfy (function
    | _location, Token.LBRACK -> Result.ok ()
    | _location, _token -> Result.error Expected_left_brack)

exception Expected_right_brack

let right_brack =
  satisfy (function
    | _location, Token.RBRACK -> Result.ok ()
    | _location, _token -> Result.error Expected_right_brack)

exception Expected_left_angle

let left_angle =
  satisfy (function
    | _location, Token.LANGLE -> Result.ok ()
    | _location, _token -> Result.error Expected_left_angle)

exception Expected_right_angle

let right_angle =
  satisfy (function
    | _location, Token.RANGLE -> Result.ok ()
    | _location, _token -> Result.error Expected_right_angle)

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

(** [hash_parens p] parses [`#(' p `)']. *)
let hash_parens p = token Token.HASH_LPAREN &> p <& right_parenthesis

(** [dollar_parens p] parses [`$(' p `)']. *)
let dollar_parens p = token Token.DOLLAR_LPAREN &> p <& right_parenthesis

(** [hash_bracks p] parses [`#\[' p `\]']. *)
let hash_bracks p = token Token.HASH_LBRACK &> p <& right_brack

(** [dollar_bracks p] parses [`$\[' p `\]']. *)
let dollar_bracks p = token Token.DOLLAR_LBRACK &> p <& right_brack

(** [only p] is the parser that runs [p] and requires that the input stream
    be finished afterwards. *)
let only p = p <& eoi

exception Expected_identifier

let identifier : Identifier.t t =
  satisfy (function
    | location, Token.IDENT identifier ->
        Result.ok (Identifier.make ~location identifier)
    | _location, _token -> Result.error Expected_identifier)

exception Expected_dot_identifier

let dot_identifier : Identifier.t t =
  satisfy (function
    | location, Token.DOT_IDENT identifier ->
        Result.ok (Identifier.make ~location identifier)
    | _location, _token -> Result.error Expected_dot_identifier)

exception Expected_hash_identifier

let hash_identifier : Identifier.t t =
  satisfy (function
    | location, Token.HASH_IDENT identifier ->
        Result.ok (Identifier.make ~location identifier)
    | _location, _token -> Result.error Expected_hash_identifier)

exception Expected_dollar_identifier

let dollar_identifier : Identifier.t t =
  satisfy (function
    | location, Token.DOLLAR_IDENT s ->
        Result.ok (Identifier.make ~location s)
    | _location, _token -> Result.error Expected_dollar_identifier)

(*=
    <omittable-identifier> ::=
      | `_'
      | <identifier>
*)
let omittable_identifier : Identifier.t option t =
  alt
    (token Token.UNDERSCORE $> fun () -> Option.none)
    (identifier $> Option.some)

(*=
    <omittable-hash-identifier> ::=
      | `#_'
      | <hash-identifier>
*)
let omittable_hash_identifier : Identifier.t option t =
  alt
    (token Token.HASH_BLANK $> fun () -> Option.none)
    (hash_identifier $> Option.some)

(*=
    <omittable-dollar-identifier> ::=
      | `$_'
      | <dollar-identifier>
*)
let omittable_dollar_identifier : Identifier.t option t =
  alt
    (token Token.DOLLAR_BLANK $> fun () -> Option.none)
    (dollar_identifier $> Option.some)

(*=
   <qualified-identifier> ::= <identifier> <dot-identifier>*
*)
let[@warning "-32"] qualified_identifier : Qualified_identifier.t t =
  seq2 identifier (many dot_identifier) |> span
  $> fun (location, (head, tail)) ->
  let modules, identifier = List1.unsnoc (List1.from head tail) in
  Qualified_identifier.make ~location ~modules identifier

(*=
   <dot-qualified-identifier> ::= <dot-identifier>+
*)
let dot_qualified_identifier : Qualified_identifier.t t =
  some dot_identifier |> span $> fun (location, identifiers) ->
  let modules, identifier = List1.unsnoc identifiers in
  Qualified_identifier.make ~location ~modules identifier

(*=
    <qualified-or-plain-identifier> ::=
      | <identifier>
      | <identifier> <dot-identifier>*
*)
let qualified_or_plain_identifier :
    [ `Plain of Identifier.t | `Qualified of Qualified_identifier.t ] t =
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
