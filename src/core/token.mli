open Support

(** Tokens *)
type t =
  | EOI (** End of Input, usually the same thing as EOF. *)

  (* Symbols *)
  | LPAREN (** ( *)
  | HASH_LPAREN (* #( *)
  | DOLLAR_LPAREN (* $( *)
  | RPAREN (** ) *)
  | LBRACK (** [\[] *)
  | HASH_LBRACK (** [#\[] *)
  | DOLLAR_LBRACK (** [$\[] *)
  | RBRACK (** [\]] *)
  | LBRACE (** [{] *)
  | RBRACE (** [}] *)
  | LANGLE (** < *)
  | RANGLE (** > *)
  | COMMA (** , *)
  | DOUBLE_COLON (** :: *)
  | COLON (** : *)
  | SEMICOLON (** ; *)
  | PIPE (** | *)
  | TURNSTILE (** |- *)
  | TURNSTILE_HASH (** |-# *)
  | DOTS (** .. *)
  | BACKARROW (** <- *)
  | ARROW (** -> *)
  | THICK_ARROW (** => *)
  | HAT (** ^ *)
  | DOT (** . *)
  | LAMBDA (** \ *)
  | STAR (** * *)
  | EQUALS (** = *)
  | SLASH (** / *)
  | UNDERSCORE (** _ *)
  | HASH (** # *)
  | DOLLAR (** $ *)
  | PLUS (** [+] *)

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

  | STRING of string (** A string literal *)
  | IDENT  of string (** Can mean identifier, operator, etc. *)
  | PRAGMA of string (** Two dashes followed by an identifier *)
  (* A dot followed by an integer; used for projections *)
  | DOT_NUMBER of int (** .n *)
  (* A dot followed by an identifier; used for projections *)
  | DOT_IDENT of string (** .x *)
  (* A hash followed by an identifier; used for parameter variables. *)
  | HASH_IDENT of string (** #x *)
  (* A dollar followed by an identifier; used for substitution variables. *)
  | DOLLAR_IDENT of string (** $x *)
  (* A hash followed by an underscore. *)
  | HASH_BLANK (** #_ *)
  (* A dollar followed by an underscore. *)
  | DOLLAR_BLANK (** $_ *)
  | HOLE of string (** A question mark followed by an identifier *)
  | INTLIT  of int (** An integer literal. *)
  | BLOCK_COMMENT of string (** A block comment of the form [%{{ ... }}%] *)

(** {1 Instances} *)

include Eq.EQ with type t := t

include Show.SHOW with type t := t

module Class : sig
  include Show.SHOW with type t := t
end
