(**
   @author Brigitte Pientka
*)

open Syntax
open Int
open LF

type error =
  | BlockInDctx of mctx * head * typ * dctx

type t

exception Error of Syntax.Loc.t * error
val fmt_ppr_conv_list : Format.formatter -> t -> unit

val strans_typ  : mctx -> dctx -> tclo  -> t -> typ
val strans_norm : mctx -> dctx -> nclo  -> t -> normal
val strans_sub  : mctx -> dctx -> sub   -> t -> sub

(** Translates a bound variable index according to the sigma
    conversion. *)
val map : t -> Id.offset -> Id.offset

val flattenDCtx : mctx -> dctx -> dctx * t
val gen_proj_sub: t -> sub
val gen_tup_sub : t -> sub

(** Constructs a unification variable for the given tclo,
    strengthening its type. *)
val etaExpandMMVstr : Loc.t -> mctx -> dctx -> tclo -> depend -> Id.name option -> normal

(** gen_flattening cD cPsi = (cPhi, lazy s_proj, lazy s_tup)
    Generates a flattened LF context cPhi in which all blocks present
    in cPsi have been decomposed.
    Packing and unpacking substitutions s_proj and s_tup are lazily
    computed to mediate between the contexts.
    Specifically:
      if cD |- cPsi ctx
      then cD |- cPhi ctx such that
      cD ; cPsi |- s_proj : cPhi
      cD ; cPhi |- s_tup : cPsi

    The naming of s_proj and s_tup is based on what kind of terms
    these substitutions *contain*; e.g. s_proj contains projections,
    so it takes us from the block context to the flat context.
 *)
val gen_flattening : mctx -> dctx -> dctx * sub Lazy.t * sub Lazy.t
