(** The empty module. This is the module-level equivalent of unit. *)
module type UNIT = sig end

(** The canonical UNIT module. *)
module Unit : UNIT = struct end
