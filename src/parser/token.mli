open Support

(** Tokens *)
type t =
  (* Symbols *)
  | LPAREN  (** [(] *)
  | HASH_LPAREN  (** [#(] *)
  | DOLLAR_LPAREN  (** [$(] *)
  | RPAREN  (** [)] *)
  | LBRACK  (** [\[] *)
  | HASH_LBRACK  (** [#\[] *)
  | DOLLAR_LBRACK  (** [$\[] *)
  | RBRACK  (** [\]] *)
  | LBRACE  (** [{] *)
  | RBRACE  (** [}] *)
  | LANGLE  (** [<] *)
  | RANGLE  (** [>] *)
  | COMMA  (** [,] *)
  | DOUBLE_COLON  (** [::] *)
  | COLON  (** [:] *)
  | SEMICOLON  (** [;] *)
  | PIPE  (** [|] *)
  | TURNSTILE  (** [|-] *)
  | TURNSTILE_HASH  (** [|-#] *)
  | DOTS  (** [..] *)
  | BACKARROW  (** [<-] *)
  | ARROW  (** [->] *)
  | THICK_ARROW  (** [=>] *)
  | HAT  (** [^] *)
  | DOT  (** [.] *)
  | LAMBDA  (** [\ ] *)
  | STAR  (** [*] *)
  | EQUALS  (** [=] *)
  | SLASH  (** [/] *)
  | UNDERSCORE  (** [_] *)
  | HASH  (** [#] *)
  | DOLLAR  (** [$] *)
  | PLUS  (** [+] *)
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
  | STRING of string
      (** [STRING s] is a string literal ["\"" ^ String.escaped s ^ "\""]. *)
  | IDENT of string
      (** [IDENT x] is an identifier [x] that may represent an operator, a
          variable, etc.. *)
  | PRAGMA of string  (** [PRAGMA p] is [--p]. *)
  | HASH_IDENT of string
      (** [HASH_IDENT x] is [x] where [x] starts with [#]. *)
  | DOLLAR_IDENT of string
      (** [DOLLAR_IDENT x] is [x] where [x] starts with [$]. *)
  | HASH_BLANK  (** [#_] *)
  | DOLLAR_BLANK  (** [$_] *)
  | HOLE of string  (** [HOLE x] is [?x]. *)
  | INTLIT of int  (** [INTLIT i] is the integer literal [i]. *)
  | BLOCK_COMMENT of string  (** A block comment of the form [%{{ ... }}%] *)

(** {1 Instances} *)

include Eq.EQ with type t := t

include Show.SHOW with type t := t
