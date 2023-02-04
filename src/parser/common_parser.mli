(** Common parser definitions for parsing Beluga signatures.

    @author Jacob Thomas Errington
    @author Marc-Antoine Ouimet *)

open Beluga_syntax
open Parser_combinator

module type PARSER_STATE = sig
  include PARSER_STATE

  include PARSER_LOCATION_STATE with type state := state

  include BACKTRACKING_STATE with type state := state

  val initial : ?initial_location:location -> token Seq.t -> state
end

module type COMMON_PARSER = sig
  include Parser_combinator.PARSER

  val keyword : string -> unit t

  val integer : int t

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

  val hash_identifier : Identifier.t t

  val dollar_identifier : Identifier.t t

  val omittable_identifier : Identifier.t option t

  val omittable_hash_identifier : Identifier.t option t

  val omittable_dollar_identifier : Identifier.t option t

  val qualified_identifier : Qualified_identifier.t t

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
                with type token = Location.t * Token.t
                 and type location = Location.t) :
  COMMON_PARSER
    with type token = Parser.token
     and type location = Parser.location
     and type state = Parser.state
     and type input = Parser.input
