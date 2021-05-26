(** The things needed to build a tokenizer. *)
module type TokenizerInfo = sig
  module Stream : Types.BasicStream

  type 'a token

  (** A way to construct a token. *)
  val token : 'a -> Span.t -> 'a token
end

(** Basic tokenizer. *)
module type Base = sig
  (** The type of tokens emitted by the tokenizer. *)
  type 'a token

  module Stream : Types.BasicStream

  (** Considers everything to be on the same line, and sequentially
  numbers each token. *)
  val trivial_tokenize_from : Loc.t -> 'a Stream.t -> 'a token Stream.t
  val char_tokenize_from : Loc.t -> char Stream.t -> char token Stream.t
end

module Make (T : TokenizerInfo) : Base
       with module Stream = T.Stream
       with type 'a token = 'a T.token

(** Creates a basic tokenizer suitable for a given parser. *)
module ForParser (P : Mupc.Base) : Base
       with module Stream = P.Stream
       with type 'a token = 'a P.Token.t
