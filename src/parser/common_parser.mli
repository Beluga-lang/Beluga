(** Common parser definitions for parsing Beluga signatures.

    @author Jacob Thomas Errington
    @author Marc-Antoine Ouimet *)

open Beluga_syntax
open Parser_combinator

module type PARSER_STATE = sig
  include PARSER_STATE

  include PARSER_LOCATION_STATE with type state := state

  include BACKTRACKING_STATE with type state := state
end

module type COMMON_PARSER = sig
  include Parser_combinator.PARSER

  (** [keyword s] parses the string [s] either as a keyword token, or an
      identifier matching [s]. *)
  val keyword : string -> unit t

  (** [integer] parses an integer. *)
  val integer : int t

  (** [dot_integer] parses a dot followed by an integer. *)
  val dot_integer : int t

  (** [pragma s] parses [--s]. *)
  val pragma : string -> unit t

  (** [string_literal] parses an escaped string literal between double
      quotes. *)
  val string_literal : string t

  (** [dot] parses [`.']. *)
  val dot : unit t

  (** [dots] parses [`..']. *)
  val dots : unit t

  (** [comma] parses [`,']. *)
  val comma : unit t

  (** [colon] parses [`:']. *)
  val colon : unit t

  (** [semicolon] parses [`;']. *)
  val semicolon : unit t

  (** [slash] pases [`/']. *)
  val slash : unit t

  (** [equals] parses [`=']. *)
  val equals : unit t

  (** [lambda] parses [`\']. *)
  val lambda : unit t

  (** [hat] parses [`^']. *)
  val hat : unit t

  (** [underscore] parses [`_']. *)
  val underscore : unit t

  (** [pipe] parses [`|']. *)
  val pipe : unit t

  (** [forward_arrow] parses [`->']. *)
  val forward_arrow : unit t

  (** [backward_arrow] parses [`<-']. *)
  val backward_arrow : unit t

  (** [thick_forward_arrow] parses [`=>']. *)
  val thick_forward_arrow : unit t

  (** [plus] parses [`+']. *)
  val plus : unit t

  (** [star] parses [`*']. *)
  val star : unit t

  (** [hash] parses [`#']. For identifiers prefixed by a hash symbol, see
      {!hash_identifier} and {!omittable_hash_identifier}. *)
  val hash : unit t

  (** [double_colon] parses [`::']. *)
  val double_colon : unit t

  (** [turnstile] parses [`|-']. *)
  val turnstile : unit t

  (** [turnstile_hash] parses [`|-#']. *)
  val turnstile_hash : unit t

  (** [left_parenthesis] parses [`(']. *)
  val left_parenthesis : unit t

  (** [right_parenthesis] parses [`)']. *)
  val right_parenthesis : unit t

  (** [left_brace] parses [`{']. *)
  val left_brace : unit t

  (** [right_brace] parses [`}']. *)
  val right_brace : unit t

  (** [left_brack] parses [`\[']. *)
  val left_brack : unit t

  (** [right_brack] parses [`\]']. *)
  val right_brack : unit t

  (** [left_angle] parses [`<']. *)
  val left_angle : unit t

  (** [right_angle] parses [`>']. *)
  val right_angle : unit t

  (** [parens p] parses [`(' p `)']. *)
  val parens : 'a t -> 'a t

  (** [braces p] parses [`{' p `}']. *)
  val braces : 'a t -> 'a t

  (** [bracks p] parses [`\[' p `\]']. *)
  val bracks : 'a t -> 'a t

  (** [angles p] parses [`<' p `>']. *)
  val angles : 'a t -> 'a t

  (** [opt_parens p] parses [`(' p `)' | p]. *)
  val opt_parens : 'a t -> 'a t

  (** [opt_braces p] parses [`{' p `}' | p]. *)
  val opt_braces : 'a t -> 'a t

  (** [opt_bracks p] parses [`\[' p `\]' | p]. *)
  val opt_bracks : 'a t -> 'a t

  (** [opt_angles p] parses [`<' p `>' | p]. *)
  val opt_angles : 'a t -> 'a t

  (** [hash_parens p] parses [`#(' p `)']. *)
  val hash_parens : 'a t -> 'a t

  (** [dollar_parens p] parses [`$(' p `)']. *)
  val dollar_parens : 'a t -> 'a t

  (** [hash_bracks p] parses [`#\[' p `\]']. *)
  val hash_bracks : 'a t -> 'a t

  (** [dollar_bracks p] parses [`$\[' p `\]']. *)
  val dollar_bracks : 'a t -> 'a t

  (** [identifier] parses a plain identifier. *)
  val identifier : Identifier.t t

  (** [dot_identifier] parses a dot followed by an identifier. *)
  val dot_identifier : Identifier.t t

  (** [hash_identifier] parses an identifier starting with [`#']. The prefix
      [`#'] is included in the identifier. *)
  val hash_identifier : Identifier.t t

  (** [dollar_identifier] parses an identifier starting with [`$']. The
      prefix [`$'] is included in the identifier. *)
  val dollar_identifier : Identifier.t t

  (** [omittable_identifier] parses [`_' | <identifier>]. *)
  val omittable_identifier : Identifier.t option t

  (** [omittable_hash_identifier] parses [`#_' | <hash-identifier>]. *)
  val omittable_hash_identifier : Identifier.t option t

  (** [omittable_dollar_identifier] parses [`$_' | <dollar-identifier>]. *)
  val omittable_dollar_identifier : Identifier.t option t

  (** [qualified_identifier] parses [<identifier> (<dot-identifier>)*]. *)
  val qualified_identifier : Qualified_identifier.t t

  (** [dot_qualified_identifier] parses a dot followed by a qualified
      identifier. *)
  val dot_qualified_identifier : Qualified_identifier.t t

  (** [qualified_or_plain_identifier] parses a plain identifier or a
      qualified identifier, whichever is the longest parse. That is, if
      [qualified_or_plain_identifier] parses a qualified identifier, then it
      has at least one namespace. *)
  val qualified_or_plain_identifier :
    [> `Plain of Identifier.t | `Qualified of Qualified_identifier.t ] t

  (** [omittable_meta_object_identifier] parses
      [`_' | `#_' | `$_' | <identifier> | <hash-identifier> | <dollar-identifier>]. *)
  val omittable_meta_object_identifier :
    (Identifier.t option * [> `Dollar | `Hash | `Plain ]) t

  (** [meta_object_identifier] parses
      [<identifier> | <hash-identifier> | <dollar-identifier>]. *)
  val meta_object_identifier :
    (Identifier.t * [> `Dollar | `Hash | `Plain ]) t

  (** [hole] parses [`?' | `?'<identifier>]. *)
  val hole : [> `Labelled of Identifier.t | `Unlabelled ] parser

  (** [block_comment] parses [%{{ c }}%]. *)
  val block_comment : (Location.t * string) t
end

module Make
    (Parser : Parser_combinator.PARSER
                with type token = Location.t * Token.t
                 and type location = Location.t) :
  COMMON_PARSER
    with type token = Parser.token
     and type location = Parser.location
     and type state = Parser.state
     and type input = Parser.input
