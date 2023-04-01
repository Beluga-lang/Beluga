(** Lexer tokens annotated with locations. *)

open Beluga_syntax

type token = Token.t

type location = Location.t

type t = private
  { location : location
  ; token : token
  }

(** {1 Constructors} *)

val make : location:location -> token:token -> t

(** {1 Destructors} *)

val location : t -> location

val token : t -> token
