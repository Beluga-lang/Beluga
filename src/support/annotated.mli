(** Tokens make up input streams, which are what microparsec parses.
    A token is simply some value annotated with a span which
    represents its location inside the input stream.
 *)

module type Type = sig
  type t
end
                 
module type Base = sig
  type annotation
     
  (** A value with an annotation. *)
  type 'a t =
    { value : 'a;
      annotation : annotation;
    }


  val make : 'a -> annotation -> 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
  val amap : (annotation -> annotation) -> 'a t -> 'a t
end

(** Constructs an annotated type. *)
module Make (T : Type) : Base with type annotation = T.t
