include Hamt

module type S = sig
  include S

  val find_opt : key -> 'a t -> 'a option
end

module type HASH_TYPE = sig
  type t

  include Eq.EQ with type t := t

  include Hash.HASH with type t := t
end

module Make (Key : HASH_TYPE) : S with type key = Key.t = struct
  include Make (StdConfig) (Key)

  let find_opt = ExceptionLess.find
end
