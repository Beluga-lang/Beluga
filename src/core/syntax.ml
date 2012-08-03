(**
   @author Brigitte Pientka
*)

(** Syntax for the LF and Computation languages *)

open Id
open Pragma

module Loc : Camlp4.Sig.Loc with type t = Camlp4.PreCast.Loc.t = struct
  include Camlp4.PreCast.Loc

  (* Override camlp4's to_string implementation. *)
  let to_string loc =
    if is_ghost loc then "<unknown location>"
    else to_string loc
end

module Int = Synint
module Apx = Synapx
module Ext = Synext
