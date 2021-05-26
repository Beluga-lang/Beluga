val create_symbols : string array -> string Stream.t


(** Functionality for generating unique symbols *)
module type GENSYM = sig
  val gensym : unit -> string
  val name_gensym : string -> (unit -> string)

  val reset : unit -> unit
end


(** Symbol generation for data variables.  Symbols take the form
    [a,..., z, a1, ...z1, a2, ...] *)
module VarData : GENSYM

module MVarData : GENSYM

val reset : unit -> unit
