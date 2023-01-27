open Beluga_syntax

module type PARSER_STATE = sig
  type t

  type token

  type location

  val observe : t -> (token * t) option

  val enable_backtracking : t -> t

  val disable_backtracking : t -> t

  val is_backtracking_enabled : t -> bool

  val can_backtrack : from:t -> to_:t -> bool

  val next_location : t -> location option

  val previous_location : t -> location option

  val initial_state : ?last_location:location -> token Seq.t -> t
end

module type COMMON_PARSER = sig
  include Parser_combinator.PARSER_WITH_LOCATIONS

  val keyword : string -> unit t

  val integer : int t

  val dot_integer : int t

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

  val dot_identifier : Identifier.t t

  val hash_identifier : Identifier.t t

  val dollar_identifier : Identifier.t t

  val omittable_identifier : Identifier.t option t

  val omittable_hash_identifier : Identifier.t option t

  val omittable_dollar_identifier : Identifier.t option t

  val qualified_identifier : Qualified_identifier.t t

  val dot_qualified_identifier : Qualified_identifier.t t

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
    (Parser : Parser_combinator.PARSER_WITH_LOCATIONS
                with type token = Location.t * Token.t
                 and type location = Location.t) :
  COMMON_PARSER
    with type token = Parser.token
     and type location = Parser.location
     and type state = Parser.state
     and type input = Parser.input

module Simple_common_parser : sig
  include
    COMMON_PARSER
      with type token = Location.t * Token.t
       and type location = Location.t

  val initial_state :
    ?last_location:Location.t -> (Location.t * Token.t) Seq.t -> state
end
