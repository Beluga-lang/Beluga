open Beluga
open Beluga_syntax
open Beluga_parser

(** [revisit_disambiguation sgn] is a lookup table for the disambiguation
    state at each Harpoon proof in [sgn]. These disambiguation states are
    snapshots, and should be used with a checkpoint to disambiguate new
    parsemes. *)
val revisit_disambiguation :
     Synint.Sgn.sgn
  -> Disambiguation_state.Disambiguation_state.state Id.Prog.Hashtbl.t

(** [revisit_indexing sgn] is a lookup table for the indexing state at each
    Harpoon proof in [sgn]. These indexing states are snapshots, and should
    be used with a checkpoint to index new ASTs. *)
val revisit_indexing :
  Synint.Sgn.sgn -> Index_state.Indexing_state.state Id.Prog.Hashtbl.t
