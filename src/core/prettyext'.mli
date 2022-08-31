open Synext'

(** Pretty-printing for LF kinds, types and terms. *)
module LF : sig
  open LF

  (** {1 Removing Parentheses} *)

  (** [remove_parentheses_kind ?(unquote_operators = true) kind] is [kind]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this kind with {!pp_kind} may not result in a syntactically
      valid LF kind. *)
  val remove_parentheses_kind : ?unquote_operators:bool -> Kind.t -> Kind.t

  (** [remove_parentheses_typ ?(unquote_operators = true) typ] is [typ]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this type with {!pp_typ} may not result in a syntactically
      valid LF type. *)
  val remove_parentheses_typ : ?unquote_operators:bool -> Typ.t -> Typ.t

  (** [remove_parentheses_term ?(unquote_operators = true) term] is [term]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this term with {!pp_term} may not result in a syntactically
      valid LF term. *)
  val remove_parentheses_term : ?unquote_operators:bool -> Term.t -> Term.t

  (** {1 Adding Necessary Parentheses} *)

  (** [parenthesize_kind kind] is [kind] with the addition of necessary
      parentheses for printing.

      The resultant LF kind can be parsed to the same AST, without
      considering locations. *)
  val parenthesize_kind : Kind.t -> Kind.t

  (** [parenthesize_typ typ] is [typ] with the addition of necessary
      parentheses for printing.

      The resultant LF type can be parsed to the same AST, without
      considering locations. *)
  val parenthesize_typ : Typ.t -> Typ.t

  (** [parenthesize_term term] is [term] with the addition of necessary
      parentheses for printing.

      The resultant LF term can be parsed to the same AST, without
      considering locations. *)
  val parenthesize_term : Term.t -> Term.t

  (** [re_parenthesize_kind kind] is the LF kind suitable for printing
      [kind].

      [re_parenthesize_kind] is the function composition of
      {!remove_parentheses_kind} and {!parenthesize_kind}. *)
  val re_parenthesize_kind : Kind.t -> Kind.t

  (** [re_parenthesize_typ typ] is the LF type suitable for printing [typ].

      [re_parenthesize_typ] is the function composition of
      {!remove_parentheses_typ} and {!parenthesize_typ}. *)
  val re_parenthesize_typ : Typ.t -> Typ.t

  (** [re_parenthesize_term term] is the LF term suitable for printing
      [term].

      [re_parenthesize_term] is the function composition of
      {!remove_parentheses_term} and {!parenthesize_term}. *)
  val re_parenthesize_term : Term.t -> Term.t

  (** {1 Printing} *)

  val pp_kind : Format.formatter -> Kind.t -> unit

  val pp_typ : Format.formatter -> Typ.t -> unit

  val pp_term : Format.formatter -> Term.t -> unit

  (** Not-so-pretty printing for LF kinds, types and terms, for use in
      debugging. *)
  module Debug : sig
    val pp_kind : Format.formatter -> Kind.t -> unit

    val pp_typ : Format.formatter -> Typ.t -> unit

    val pp_term : Format.formatter -> Term.t -> unit
  end
end

(** Pretty-printing for contextual LF types, terms, substitutions, and type
    and term patterns. *)
module CLF : sig
  open CLF

  (** {1 Removing Parentheses} *)

  (** [remove_parentheses_typ ?(unquote_operators = true) typ] is [typ]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this type with {!pp_typ} may not result in a syntactically
      valid contextual LF type. *)
  val remove_parentheses_typ : ?unquote_operators:bool -> Typ.t -> Typ.t

  (** [remove_parentheses_term ?(unquote_operators = true) term] is [term]
      without parentheses. If [unquote_operators = true], then non-nullary
      operators that do not appear as application arguments are unquoted.

      Printing this term with {!pp_term} may not result in a syntactically
      valid contextual LF term. *)
  val remove_parentheses_term : ?unquote_operators:bool -> Term.t -> Term.t

  (** [remove_parentheses_substitution ?(unquote_operators = true) term] is
      [term] without parentheses. If [unquote_operators = true], then
      non-nullary operators that do not appear as application arguments are
      unquoted.

      Printing this substitution with {!pp_substitution} may not result in a
      syntactically valid contextual LF substitution. *)
  val remove_parentheses_substitution :
    ?unquote_operators:bool -> Substitution.t -> Substitution.t

  (** [remove_parentheses_typ_pattern ?(unquote_operators = true) typ_pattern]
      is [typ_pattern] without parentheses. If [unquote_operators = true],
      then non-nullary operators that do not appear as application arguments
      are unquoted.

      Printing this type with {!pp_typ_pattern} may not result in a
      syntactically valid LF type pattern. *)
  val remove_parentheses_typ_pattern :
    ?unquote_operators:bool -> Typ.Pattern.t -> Typ.Pattern.t

  (** [remove_parentheses_term_pattern ?(unquote_operators = true) term_pattern]
      is [term_pattern] without parentheses. If [unquote_operators = true],
      then non-nullary operators that do not appear as application arguments
      are unquoted.

      Printing this term with {!pp_term_pattern} may not result in a
      syntactically valid LF term pattern. *)
  val remove_parentheses_term_pattern :
    ?unquote_operators:bool -> Term.Pattern.t -> Term.Pattern.t

  (** {1 Adding Necessary Parentheses} *)

  (** [parenthesize_typ typ] is [typ] with the addition of necessary
      parentheses for printing.

      The resultant contextual LF type can be parsed to the same AST, without
      considering locations. *)
  val parenthesize_typ : Typ.t -> Typ.t

  (** [parenthesize_term term] is [term] with the addition of necessary
      parentheses for printing.

      The resultant contextual LF term can be parsed to the same AST, without
      considering locations. *)
  val parenthesize_term : Term.t -> Term.t

  (** [parenthesize_substitution substitution] is [substitution] with the
      addition of necessary parentheses for printing.

      The resultant contextual LF substitution can be parsed to the same AST,
      without considering locations. *)
  val parenthesize_substitution : Substitution.t -> Substitution.t

  (** [parenthesize_typ_pattern typ_pattern] is [typ_pattern] with the
      addition of necessary parentheses for printing.

      The resultant contextual LF type pattern can be parsed to the same AST,
      without considering locations. *)
  val parenthesize_typ_pattern : Typ.Pattern.t -> Typ.Pattern.t

  (** [parenthesize_term_pattern term_pattern] is [term_pattern] with the
      addition of necessary parentheses for printing.

      The resultant contextual LF term pattern can be parsed to the same AST,
      without considering locations. *)
  val parenthesize_term_pattern : Term.Pattern.t -> Term.Pattern.t

  (** [re_parenthesize_typ typ] is the contextual LF type suitable for
      printing [typ].

      [re_parenthesize_typ] is the function composition of
      {!remove_parentheses_typ} and {!parenthesize_typ}. *)
  val re_parenthesize_typ : Typ.t -> Typ.t

  (** [re_parenthesize_term term] is the contextual LF term suitable for
      printing [term].

      [re_parenthesize_term] is the function composition of
      {!remove_parentheses_term} and {!parenthesize_term}. *)
  val re_parenthesize_term : Term.t -> Term.t

  (** [re_parenthesize_substitution substitution] is the contextual LF
      substitution suitable for printing [substitution].

      [re_parenthesize_substitution] is the function composition of
      {!remove_parentheses_substitution} and {!parenthesize_substitution}. *)
  val re_parenthesize_substitution : Substitution.t -> Substitution.t

  (** [re_parenthesize_typ_pattern typ_pattern] is the contextual LF type
      pattern suitable for printing [typ_pattern].

      [re_parenthesize_typ_pattern] is the function composition of
      {!remove_parentheses_typ_pattern} and {!parenthesize_typ_pattern}. *)
  val re_parenthesize_typ_pattern : Typ.Pattern.t -> Typ.Pattern.t

  (** [re_parenthesize_term_pattern term_pattern] is the contextual LF term
      pattern suitable for printing [term_pattern].

      [re_parenthesize_term_pattern] is the function composition of
      {!remove_parentheses_term_pattern} and {!parenthesize_term_pattern}. *)
  val re_parenthesize_term_pattern : Term.Pattern.t -> Term.Pattern.t

  (** {1 Printing} *)

  val pp_typ : Format.formatter -> Typ.t -> unit

  val pp_term : Format.formatter -> Term.t -> unit

  val pp_substitution : Format.formatter -> Substitution.t -> unit

  val pp_typ_pattern : Format.formatter -> Typ.Pattern.t -> unit

  val pp_term_pattern : Format.formatter -> Term.Pattern.t -> unit

  (** Not-so-pretty printing for contextual LF types, terms, substitutions,
      and type and term patterns, for use in debugging. *)
  module Debug : sig
    val pp_typ : Format.formatter -> Typ.t -> unit

    val pp_term : Format.formatter -> Term.t -> unit

    val pp_substitution : Format.formatter -> Substitution.t -> unit

    val pp_typ_pattern : Format.formatter -> Typ.Pattern.t -> unit

    val pp_term_pattern : Format.formatter -> Term.Pattern.t -> unit
  end
end
