module type Type = sig
  type t
end

module type Base = sig
  type annotation

  type 'a t =
    { value : 'a;
      annotation : annotation;
    }

  val make : 'a -> annotation -> 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
  val amap : (annotation -> annotation) -> 'a t -> 'a t
end

module Make (T : Type) : Base with type annotation = T.t = struct
  type annotation = T.t

  type 'a t =
    { value : 'a;
      annotation : annotation;
    }

  let make (x : 'a) (a : annotation) =
    { value = x;
      annotation = a;
    }

  let map (f : 'a -> 'b) (a : 'a t) =
    { a with value = f a.value }

  let amap (f : annotation -> annotation) (a : 'a t) : 'a t =
    { a with annotation = f a.annotation }
end
