open Support
open Beluga_syntax
open Beluga_parser

module type LOAD_STATE = sig
  include Imperative_state.IMPERATIVE_STATE

  val read_signature_file :
    state -> filename:String.t -> Synext.signature_file

  val reconstruct_signature_file :
    state -> Synext.signature_file -> Synint.Sgn.sgn_file

  val get_leftover_vars :
    state -> (Abstract.free_var Synint.LF.ctx * Location.t) List.t
end

module Make_load_state
    (Disambiguation_state : Beluga_parser.DISAMBIGUATION_STATE)
    (Disambiguation : Beluga_parser.DISAMBIGUATION
                        with type state = Disambiguation_state.state)
    (Signature_reconstruction_state : Recsgn_state
                                      .SIGNATURE_RECONSTRUCTION_STATE)
    (Signature_reconstruction : Recsgn.SIGNATURE_RECONSTRUCTION
                                  with type state =
                                    Signature_reconstruction_state.state) :
  LOAD_STATE
[@@warning "-67"]

module type LOAD = sig
  include Imperative_state.IMPERATIVE_STATE

  val load : state -> String.t -> String.t List.t * Synint.Sgn.sgn
end

module Make_load (Load_state : LOAD_STATE) :
  LOAD with type state = Load_state.state

val load :
     Parser.Disambiguation_state.state
  -> Recsgn_state.Signature_reconstruction_state.state
  -> string
  -> string list * Synint.Sgn.sgn

(** [load_fresh filename] clears all internal state and loads the given path
    to a [.cfg] or [.bel] file. The list of resolved paths (paths to [.bel]
    files) is returned, along with the loaded signature. *)
val load_fresh : string -> string list * Synint.Sgn.sgn
