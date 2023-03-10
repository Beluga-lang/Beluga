open Support

(** Tokens *)
type t =
  (* Symbols *)
  | LPAREN (* ( *)
  | HASH_LPAREN (* #( *)
  | DOLLAR_LPAREN (* $( *)
  | RPAREN (* ) *)
  | LBRACK (* [ *)
  | HASH_LBRACK (* #[ *)
  | DOLLAR_LBRACK (* $[ *)
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
  | TURNSTILE_HASH (* |-# *)
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
  | IDENT of string
  (* Two dashes followed by an identifier *)
  | PRAGMA of string
  (* A dot followed by an identifier; used for projections and qualified
     identifiers. *)
  | DOT_IDENT of string (* .x *)
  (* A dot followed by an integer literal; used for projections. *)
  | DOT_INTLIT of int (* .n *)
  (* A hash followed by an identifier; used for parameter variables. *)
  | HASH_IDENT of string (* #x *)
  (* A dollar followed by an identifier; used for substitution variables. *)
  | DOLLAR_IDENT of string (* $x *)
  (* A hash followed by an underscore. *)
  | HASH_BLANK (* #_ *)
  (* A dollar followed by an underscore. *)
  | DOLLAR_BLANK (* $_ *)
  (* A question mark followed by an identifier *)
  | HOLE of string option
  (* An integer literal. *)
  | INTLIT of int
  (* A block comment of the form %{{ ... }}% *)
  | BLOCK_COMMENT of string

include (
  Eq.Make (struct
    type nonrec t = t

    let equal = Stdlib.( = )
  end) :
    Eq.EQ with type t := t)

include (
  Show.Make (struct
    type nonrec t = t

    let pp ppf =
      let p x = Format.fprintf ppf x in
      function
      | LPAREN -> p "("
      | HASH_LPAREN -> p "#("
      | DOLLAR_LPAREN -> p "$("
      | RPAREN -> p ")"
      | LBRACK -> p "["
      | HASH_LBRACK -> p "#["
      | DOLLAR_LBRACK -> p "$["
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
      | TURNSTILE_HASH -> p "|-#"
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
      | HOLE Option.None -> p "?"
      | HOLE (Option.Some s) -> p "?%s" s
      | INTLIT n -> p "%d" n
      | DOT_IDENT s -> p ".%s" s
      | DOT_INTLIT n -> p ".%d" n
      | HASH_IDENT s -> p "%s" s
      | DOLLAR_IDENT s -> p "%s" s
      | PRAGMA s -> p "--%s" s
      | HASH_BLANK -> p "#_"
      | DOLLAR_BLANK -> p "$_"
  end) :
    Show.SHOW with type t := t)
