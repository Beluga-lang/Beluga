open Support

(**********************************)
(* Token Type and Token Functions *)
(**********************************)

(** Tokens *)
type t =
  (* End of Input, usually the same thing as EOF. *)
  | EOI
  | DUMMY

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
  | DOTS (* .. *)
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
  (* A hash followed by an identifier; used for parameter variables. *)
  | HASH_IDENT of string (* #x *)
  (* A dollar followed by an identifier; used for substitution variables. *)
  | DOLLAR_IDENT of string (* $x *)
  (* A question mark followed by an identifier *)
  | HOLE of string
  (* An integer literal. *)
  | INTLIT  of int
  (* A block comment of the form %{{ ... %}} *)
  | BLOCK_COMMENT of string

type class_or_string = [ `CLASS | `TOKEN ]

let print (c : class_or_string) ppf =
  let p x = Format.fprintf ppf x in
  let case p1 p2 =
    match c with
    | `TOKEN -> Lazy.force p1
    | `CLASS -> Lazy.force p2
  in
  function
  | EOI       -> case (lazy (p "EOI")) (lazy (p "EOI"))
  | DUMMY -> case (lazy (p "DUMMY")) (lazy (p "DUMMY"))

  | LPAREN (* ( *) -> case (lazy (p "(")) (lazy (p "LPAREN"))
  | RPAREN (* ) *) -> case (lazy (p ")")) (lazy (p "RPAREN"))
  | LBRACK (* [ *) -> case (lazy (p "[")) (lazy (p "LBRACK"))
  | RBRACK (* ] *) -> case (lazy (p "]")) (lazy (p "RBRACK"))
  | LBRACE (* { *) -> case (lazy (p "{")) (lazy (p "LBRACE"))
  | RBRACE (* } *) -> case (lazy (p "}")) (lazy (p "RBRACE"))
  | LANGLE (* < *) -> case (lazy (p "<")) (lazy (p "LANGLE"))
  | RANGLE (* > *) -> case (lazy (p ">")) (lazy (p "RANGLE"))
  | COMMA (* , *) -> case (lazy (p ",")) (lazy (p "COMMA"))
  | DOUBLE_COLON (* :: *) -> case (lazy (p "::")) (lazy (p "DOUBLE_COLON"))
  | COLON (* : *) -> case (lazy (p ":")) (lazy (p "COLON" ))
  | SEMICOLON (* ; *) -> case (lazy (p ";")) (lazy (p "SEMICOLON"))
  | PIPE (* | *) -> case (lazy (p "|")) (lazy (p "PIPE"))
  | TURNSTILE (* |- *) -> case (lazy (p "|-")) (lazy (p "TURNSTILE"))
  | DOTS (* .. *) -> case (lazy (p "..")) (lazy (p "DOTS"))
  | ARROW (* -> *) -> case (lazy (p "->")) (lazy (p "ARROW" ))
  | THICK_ARROW (* => *) -> case (lazy (p "=>")) (lazy (p "THICK_ARROW"))
  | HAT (* ^ *) -> case (lazy (p "^")) (lazy (p "HAT"))
  | DOT (* . *) -> case (lazy (p ".")) (lazy (p "DOT"))
  | LAMBDA (* \ *) -> case (lazy (p "\\")) (lazy (p "LAMBDA"))
  | STAR (* * *) -> case (lazy (p "*")) (lazy (p "STAR"))
  | EQUALS (* = *) -> case (lazy (p "=")) (lazy (p "EQUALS"))
  | SLASH (* / *) -> case (lazy (p "/")) (lazy (p "SLASH"))
  | UNDERSCORE (* _ *) -> case (lazy (p "_")) (lazy (p "UNDERSCORE"))
  | HASH (* # *) -> case (lazy (p "#")) (lazy (p "HASH"))
  | DOLLAR (* $ *) -> case (lazy (p "$")) (lazy (p "DOLLAR"))
  | PLUS (* + *) -> case (lazy (p "+")) (lazy (p "PLUS"))

  | KW_AND -> case (lazy (p "and")) (lazy (p "KW_AND"))
  | KW_BLOCK -> case (lazy (p "block")) (lazy (p "KW_BLOCK"))
  | KW_CASE -> case (lazy (p "case")) (lazy (p "KW_CASE"))
  | KW_IF -> case (lazy (p "if")) (lazy (p "KW_IF"))
  | KW_THEN -> case (lazy (p "then")) (lazy (p "KW_THEN"))
  | KW_ELSE -> case (lazy (p "else")) (lazy (p "KW_ELSE"))
  | KW_IMPOSSIBLE -> case (lazy (p "impossible")) (lazy (p "KW_IMPOSSIBLE"))
  | KW_LET -> case (lazy (p "let")) (lazy (p "KW_LET"))
  | KW_IN -> case (lazy (p "in")) (lazy (p "KW_IN"))
  | KW_OF -> case (lazy (p "of")) (lazy (p "KW_OF"))
  | KW_REC -> case (lazy (p "rec")) (lazy (p "KW_REC"))
  | KW_SCHEMA -> case (lazy (p "schema")) (lazy (p "KW_SCHEMA"))
  | KW_SOME -> case (lazy (p "some")) (lazy (p "KW_SOME"))
  | KW_FN -> case (lazy (p "fn")) (lazy (p "KW_FN"))
  | KW_MLAM -> case (lazy (p "mlam")) (lazy (p "KW_MLAM"))
  | KW_MODULE -> case (lazy (p "module")) (lazy (p "KW_MODULE"))
  | KW_STRUCT -> case (lazy (p "struct")) (lazy (p "KW_STRUCT"))
  | KW_END -> case (lazy (p "end")) (lazy (p "KW_END"))
  | KW_TOTAL -> case (lazy (p "total")) (lazy (p "KW_TOTAL"))
  | KW_TRUST -> case (lazy (p "trust")) (lazy (p "KW_TRUST"))
  | KW_TYPE -> case (lazy (p "type")) (lazy (p "KW_TYPE"))
  | KW_CTYPE -> case (lazy (p "ctype")) (lazy (p "KW_CTYPE"))
  | KW_PROP -> case (lazy (p "prop")) (lazy (p "KW_PROP"))
  | KW_INDUCTIVE -> case (lazy (p "inductive")) (lazy (p "KW_INDUCTIVE"))
  | KW_COINDUCTIVE -> case (lazy (p "coinductive")) (lazy (p "KW_COINDUCTIVE"))
  | KW_STRATIFIED -> case (lazy (p "stratified")) (lazy (p "KW_STRATIFIED"))
  | KW_LF -> case (lazy (p "LF")) (lazy (p "KW_LF"))
  | KW_FUN -> case (lazy (p "fun")) (lazy (p "KW_FUN"))
  | KW_TYPEDEF -> case (lazy (p "typedef")) (lazy (p "KW_TYPEDEF"))
  | KW_PROOF -> case (lazy (p "proof")) (lazy (p "KW_PROOF"))
  | KW_AS -> case (lazy (p "as")) (lazy (p "KW_AS"))
  | KW_BY -> case (lazy (p "by")) (lazy (p "KW_BY"))
  | KW_SUFFICES -> case (lazy (p "suffices")) (lazy (p "KW_SUFFICES"))
  | KW_TOSHOW -> case (lazy (p "toshow")) (lazy (p "KW_TOSHOW"))

  | STRING s -> case (lazy (p "STRING %S" s)) (lazy (p "STRING"))
  | BLOCK_COMMENT s -> case (lazy (p "%%{{ %s %%}}" s)) (lazy (p "BLOCK_COMMENT"))
  | IDENT s -> case (lazy (p "%s" s)) (lazy (p "IDENT"))
  | HOLE s -> case (lazy (p "?%s" s)) (lazy (p "HOLE"))
  | INTLIT n -> case (lazy (p "%d" n)) (lazy (p "INTLIT"))
  | DOT_NUMBER k -> case (lazy (p ".%d" k)) (lazy (p "DOT_NUMBER"))
  | HASH_IDENT s -> case (lazy (p "#%s" s)) (lazy (p "HASH_IDENT"))
  | DOLLAR_IDENT s -> case (lazy (p "$%s" s)) (lazy (p "DOLLAR_IDENT"))
  | PRAGMA s -> case (lazy (p "--%s" s)) (lazy (p "PRAGMA"))

let to_string t = Fmt.stringify (print `TOKEN) t
let class_to_string t = Fmt.stringify (print `CLASS) t
