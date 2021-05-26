open Support

(** The things needed to build a tokenizer. *)
module type TokenizerInfo = sig
  type 'a token

  module Stream : Types.BasicStream

  (** A way to construct a token. *)
  val token : 'a -> Span.t -> 'a token
end

(** Basic tokenizer. *)
module type Base = sig
  (** The type of tokens emitted by the tokenizer. *)
  type 'a token

  (** The streams processed by the tokenizer. *)
  module Stream : Types.BasicStream

  (** Considers everything to be on the same line, and sequentially
  numbers each token. *)
  val trivial_tokenize_from : Loc.t -> 'a Stream.t -> 'a token Stream.t
  val char_tokenize_from : Loc.t -> char Stream.t -> char token Stream.t
end

module Make (T : TokenizerInfo) : Base
       with module Stream = T.Stream
       with type 'a token = 'a T.token = struct
  type 'a token = 'a T.token

  module Stream = T.Stream

  let trivial_inc (l : Loc.t) : Loc.t =
    let open Loc in
    { l with offset = l.offset + 1 }

  let trivial_tokenize_from (l : Loc.t) (s : 'a Stream.t) : 'a token Stream.t =
    Stream.unfold
      (fun (l, s) ->
        let open Maybe in
        Stream.observe s $>
          fun (x, s) ->
          let l' = trivial_inc l in
          (T.token x (Span.of_pair' l l')), (l', s))
      (l, s)

  (** Tokenizes a stream of characters and increments the line number
  whenever '\n' is encountered. *)
  let char_tokenize_from (l : Loc.t) (s : char Stream.t) : char token Stream.t =
    Stream.unfold
      (fun (l, s) ->
        let open Maybe in
        Stream.observe s $>
          fun (x, s) ->
          let l' = Loc.inc_by_char x l in
          (T.token x (Span.of_pair' l l')), (l', s))
      (l, s)
end

module ForParser (P : Mupc.Base) : Base
       with module Stream = P.Stream
       with type 'a token = 'a P.Token.t = struct
  include Make
            (struct
              module Stream = P.Stream
              type 'a token = 'a P.Token.t
              let token x = P.Token.make x
            end)
end
