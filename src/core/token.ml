open Support

(**********************************)
(* Token Type and Token Functions *)
(**********************************)

(** Tokens *)
type t =
  (* End of Input, usually the same thing as EOF. *)
  | EOI

  (* Symbols *)
  | LPAREN (* ( *)
  | RPAREN (* ) *)
  | LBRACK (* [ *)
  | RBRACK (* ] *)
  | LBRACE (* { *)
  | RBRACE (* } *)
  | LANGLE (* < *)
  | RANGLE (* > *)
  | COMMA (* , *)
  | DOUBLE_COLON (* :: *)
  | COLON (* : *)
  | SEMICOLON (* ; *)
  | PIPE (* | *)
  | TURNSTILE (* |- *)
  | HASH_TURNSTILE (* #|- *)
  | DOTS (* .. *)
  | BACKARROW (* <- *)
  | ARROW (* -> *)
  | THICK_ARROW (* => *)
  | HAT (* ^ *)
  | DOT (* . *)
  | LAMBDA (* \ *)
  | STAR (* * *)
  | EQUALS (* = *)
  | SLASH (* / *)
  | UNDERSCORE (* _ *)
  | HASH (* # *)
  | DOLLAR (* $ *)
  | PLUS (* + *)

  (* Keywords *)
  | KW_AND
  | KW_BLOCK
  | KW_CASE
  | KW_IF
  | KW_THEN
  | KW_ELSE
  | KW_IMPOSSIBLE
  | KW_LET
  | KW_IN
  | KW_OF
  | KW_REC
  | KW_SCHEMA
  | KW_SOME
  | KW_FN
  | KW_MLAM
  | KW_MODULE
  | KW_STRUCT
  | KW_END
  | KW_TOTAL
  | KW_TRUST
  | KW_TYPE
  | KW_CTYPE
  | KW_PROP
  | KW_INDUCTIVE
  | KW_COINDUCTIVE
  | KW_STRATIFIED
  | KW_LF
  | KW_FUN
  | KW_TYPEDEF
  | KW_PROOF
  | KW_BY
  | KW_AS
  | KW_SUFFICES
  | KW_TOSHOW

  (* A string literal *)
  | STRING of string
  (* Can mean identifier, operator, etc. *)
  | IDENT  of string
  (* Two dashes followed by an identifier *)
  | PRAGMA of string
  (* A dot followed by an integer; used for projections *)
  | DOT_NUMBER of int (* .n *)
  (* A dot followed by an identifier; used for projections *)
  | DOT_IDENT of string (* .x *)
  (* A hash followed by an identifier; used for parameter variables. *)
  | HASH_IDENT of string (* #x *)
  (* A dollar followed by an identifier; used for substitution variables. *)
  | DOLLAR_IDENT of string (* $x *)
  (* A hash followed by an underscore. *)
  | HASH_BLANK (* #_ *)
  (* A dollar followed by an underscore. *)
  | DOLLAR_BLANK (* $_ *)
  (* A question mark followed by an identifier *)
  | HOLE of string
  (* An integer literal. *)
  | INTLIT  of int
  (* A block comment of the form %{{ ... }}% *)
  | BLOCK_COMMENT of string

include (Eq.Make (struct
  type nonrec t = t

  let equal = Stdlib.(=)
end) : Eq.EQ with type t := t)

include (Show.Make (struct
  type nonrec t = t

  let pp ppf =
    let p x = Format.fprintf ppf x in
    function
    | EOI -> p "EOI"

    | LPAREN -> p "("
    | RPAREN -> p ")"
    | LBRACK -> p "["
    | RBRACK -> p "]"
    | LBRACE -> p "{"
    | RBRACE -> p "}"
    | LANGLE -> p "<"
    | RANGLE -> p ">"
    | COMMA -> p ","
    | DOUBLE_COLON -> p "::"
    | COLON -> p ":"
    | SEMICOLON -> p ";"
    | PIPE -> p "|"
    | TURNSTILE -> p "|-"
    | HASH_TURNSTILE -> p "#|-"
    | DOTS -> p ".."
    | BACKARROW -> p "<-"
    | ARROW -> p "->"
    | THICK_ARROW -> p "=>"
    | HAT -> p "^"
    | DOT -> p "."
    | LAMBDA -> p "\\"
    | STAR -> p "*"
    | EQUALS -> p "="
    | SLASH -> p "/"
    | UNDERSCORE -> p "_"
    | HASH -> p "#"
    | DOLLAR -> p "$"
    | PLUS -> p "+"

    | KW_AND -> p "and"
    | KW_BLOCK -> p "block"
    | KW_CASE -> p "case"
    | KW_IF -> p "if"
    | KW_THEN -> p "then"
    | KW_ELSE -> p "else"
    | KW_IMPOSSIBLE -> p "impossible"
    | KW_LET -> p "let"
    | KW_IN -> p "in"
    | KW_OF -> p "of"
    | KW_REC -> p "rec"
    | KW_SCHEMA -> p "schema"
    | KW_SOME -> p "some"
    | KW_FN -> p "fn"
    | KW_MLAM -> p "mlam"
    | KW_MODULE -> p "module"
    | KW_STRUCT -> p "struct"
    | KW_END -> p "end"
    | KW_TOTAL -> p "total"
    | KW_TRUST -> p "trust"
    | KW_TYPE -> p "type"
    | KW_CTYPE -> p "ctype"
    | KW_PROP -> p "prop"
    | KW_INDUCTIVE -> p "inductive"
    | KW_COINDUCTIVE -> p "coinductive"
    | KW_STRATIFIED -> p "stratified"
    | KW_LF -> p "LF"
    | KW_FUN -> p "fun"
    | KW_TYPEDEF -> p "typedef"
    | KW_PROOF -> p "proof"
    | KW_AS -> p "as"
    | KW_BY -> p "by"
    | KW_SUFFICES -> p "suffices"
    | KW_TOSHOW -> p "toshow"

    | STRING s -> p "STRING %S" s
    | BLOCK_COMMENT s -> p "%%{{ %s %%}}" s
    | IDENT s -> p "%s" s
    | HOLE s -> p "?%s" s
    | INTLIT n -> p "%d" n
    | DOT_NUMBER k -> p ".%d" k
    | DOT_IDENT s -> p ".%s" s
    | HASH_IDENT s -> p "#%s" s
    | DOLLAR_IDENT s -> p "$%s" s
    | PRAGMA s -> p "--%s" s
    | HASH_BLANK -> p "#_"
    | DOLLAR_BLANK -> p "$_"
end) : Show.SHOW with type t := t)

module Class = struct
  include (Show.Make (struct
    type nonrec t = t

    let pp ppf =
      let p x = Format.fprintf ppf x in
      function
      | EOI -> p "EOI"

      | LPAREN -> p "LPAREN"
      | RPAREN -> p "RPAREN"
      | LBRACK -> p "LBRACK"
      | RBRACK -> p "RBRACK"
      | LBRACE -> p "LBRACE"
      | RBRACE -> p "RBRACE"
      | LANGLE -> p "LANGLE"
      | RANGLE -> p "RANGLE"
      | COMMA -> p "COMMA"
      | DOUBLE_COLON -> p "DOUBLE_COLON"
      | COLON -> p "COLON"
      | SEMICOLON -> p "SEMICOLON"
      | PIPE -> p "PIPE"
      | TURNSTILE -> p "TURNSTILE"
      | HASH_TURNSTILE -> p "HASH_TURNSTILE"
      | DOTS -> p "DOTS"
      | BACKARROW -> p "BACKARROW"
      | ARROW -> p "ARROW"
      | THICK_ARROW -> p "THICK_ARROW"
      | HAT -> p "HAT"
      | DOT -> p "DOT"
      | LAMBDA -> p "LAMBDA"
      | STAR -> p "STAR"
      | EQUALS -> p "EQUALS"
      | SLASH -> p "SLASH"
      | UNDERSCORE -> p "UNDERSCORE"
      | HASH -> p "HASH"
      | DOLLAR -> p "DOLLAR"
      | PLUS -> p "PLUS"

      | KW_AND -> p "KW_AND"
      | KW_BLOCK -> p "KW_BLOCK"
      | KW_CASE -> p "KW_CASE"
      | KW_IF -> p "KW_IF"
      | KW_THEN -> p "KW_THEN"
      | KW_ELSE -> p "KW_ELSE"
      | KW_IMPOSSIBLE -> p "KW_IMPOSSIBLE"
      | KW_LET -> p "KW_LET"
      | KW_IN -> p "KW_IN"
      | KW_OF -> p "KW_OF"
      | KW_REC -> p "KW_REC"
      | KW_SCHEMA -> p "KW_SCHEMA"
      | KW_SOME -> p "KW_SOME"
      | KW_FN -> p "KW_FN"
      | KW_MLAM -> p "KW_MLAM"
      | KW_MODULE -> p "KW_MODULE"
      | KW_STRUCT -> p "KW_STRUCT"
      | KW_END -> p "KW_END"
      | KW_TOTAL -> p "KW_TOTAL"
      | KW_TRUST -> p "KW_TRUST"
      | KW_TYPE -> p "KW_TYPE"
      | KW_CTYPE -> p "KW_CTYPE"
      | KW_PROP -> p "KW_PROP"
      | KW_INDUCTIVE -> p "KW_INDUCTIVE"
      | KW_COINDUCTIVE -> p "KW_COINDUCTIVE"
      | KW_STRATIFIED -> p "KW_STRATIFIED"
      | KW_LF -> p "KW_LF"
      | KW_FUN -> p "KW_FUN"
      | KW_TYPEDEF -> p "KW_TYPEDEF"
      | KW_PROOF -> p "KW_PROOF"
      | KW_AS -> p "KW_AS"
      | KW_BY -> p "KW_BY"
      | KW_SUFFICES -> p "KW_SUFFICES"
      | KW_TOSHOW -> p "KW_TOSHOW"

      | STRING _ -> p "STRING"
      | BLOCK_COMMENT _ -> p "BLOCK_COMMENT"
      | IDENT _ -> p "IDENT"
      | HOLE _ -> p "HOLE"
      | INTLIT _ -> p "INTLIT"
      | DOT_NUMBER _ -> p "DOT_NUMBER"
      | DOT_IDENT _ -> p "DOT_IDENT"
      | HASH_IDENT _ -> p "HASH_IDENT"
      | DOLLAR_IDENT _ -> p "DOLLAR_IDENT"
      | PRAGMA _ -> p "PRAGMA"
      | HASH_BLANK -> p "HASH_BLANK"
      | DOLLAR_BLANK -> p "DOLLAR_BLANK"
  end) : Show.SHOW with type t := t)
end
