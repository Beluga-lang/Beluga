open Format

module CompS = Store.Cid.Comp

module Control = struct
  type substitution_style = Natural | DeBruijn

  let substitutionStyle = ref Natural
  let printImplicit = ref false
  let printNormal = ref false
  let db() =
    match !substitutionStyle with
    | DeBruijn -> true
    | _ -> false
end

let with_implicits b' f =
  let b = !Control.printImplicit in
  Control.printImplicit := b';
  f ();
  Control.printImplicit := b

let fmt_ppr_implicits b f ppf x =
  with_implicits b (fun () -> f ppf x)

module Common = struct
  module type T = sig
    open Syntax.Common

    type depend_print_style =
      [ `depend
      | `inductive
      | `clean
      ]

    val fmt_ppr_lf_depend     : depend_print_style -> formatter -> LF.depend -> unit
    val fmt_ppr_lf_svar_class : formatter -> LF.svar_class -> unit
    val fmt_ppr_cmp_split_kind : formatter -> Harpoon.split_kind -> unit
    val fmt_ppr_cmp_context_case : formatter -> Comp.context_case -> unit
  end
end

module Int = struct
  module type T = sig
    include Common.T

    type lvl
    val l0 : lvl

    open Syntax.Int

    val fmt_ppr_sgn           : formatter -> Sgn.sgn -> unit
    val fmt_ppr_sgn_decl      : formatter -> Sgn.decl  -> unit

    (* LF printers *)
    val fmt_ppr_lf_svar_class  : formatter -> LF.svar_class -> unit
    val fmt_ppr_lf_depend      : depend_print_style -> formatter -> LF.depend -> unit
    val fmt_ppr_lf_kind        : LF.dctx -> lvl -> formatter -> LF.kind      -> unit
    val fmt_ppr_lf_ctyp_decl   : ?depend:depend_print_style -> ?printing_holes:bool ->
                                 LF.mctx -> lvl -> formatter -> LF.ctyp_decl -> unit
    val fmt_ppr_lf_typ_rec     : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ_rec    -> unit
    val fmt_ppr_lf_typ         : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ    -> unit
    val fmt_ppr_lf_mtyp'       : LF.mctx -> string * string -> formatter -> LF.ctyp  -> unit
    val fmt_ppr_lf_mtyp        : LF.mctx                    -> formatter -> LF.ctyp  -> unit
    val fmt_ppr_lf_tuple       : LF.mctx -> LF.dctx -> lvl  -> formatter -> LF.tuple  -> unit
    val fmt_ppr_lf_normal      : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.normal -> unit
    val fmt_ppr_lf_head        : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.head   -> unit
    val fmt_ppr_lf_spine       : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.spine  -> unit
    val fmt_ppr_lf_sub         : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.sub    -> unit
    val fmt_ppr_lf_schema      : ?useName:bool -> lvl -> formatter -> LF.schema     -> unit
    val fmt_ppr_lf_sch_elem    : lvl -> formatter -> LF.sch_elem   -> unit
    val fmt_ppr_lf_dctx_hat    : LF.mctx -> lvl -> formatter -> LF.dctx  -> unit
    val fmt_ppr_lf_dctx        : LF.mctx -> lvl -> formatter -> LF.dctx  -> unit
    val fmt_ppr_lf_mctx        : ?all: bool -> ?sep: (formatter -> unit -> unit) -> lvl ->
                                 formatter -> LF.mctx -> unit
    val fmt_ppr_lf_ctx_var     : LF.mctx -> formatter -> LF.ctx_var -> unit
    val fmt_ppr_lf_mfront      : LF.mctx -> lvl -> formatter -> LF.mfront -> unit
    val fmt_ppr_lf_iterm       : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.iterm -> unit
    val fmt_ppr_lf_constraint  : formatter -> LF.constrnt -> unit
    val fmt_ppr_lf_constraints : formatter -> LF.cnstr list -> unit
    val fmt_ppr_lf_msub        : LF.mctx -> lvl -> formatter -> LF.msub -> unit

    (** Prints a typing judgment for an msub: cD' |- theta : cD *)
    val fmt_ppr_lf_msub_typing : formatter -> LF.mctx * LF.msub * LF.mctx -> unit

    (** Prints a typing judgment for an LF type: cD ; cPsi |- tA : type *)
    val fmt_ppr_lf_typ_typing : formatter -> LF.mctx * LF.dctx * LF.typ -> unit

    (** Prints a typing judgment for an LF substitution: cD ; cPsi |- s : cPsi' *)
    val fmt_ppr_lf_sub_typing : formatter -> LF.mctx * LF.dctx * LF.sub * LF.dctx -> unit

    (* computational printers *)
    val fmt_ppr_cmp_kind      : LF.mctx -> lvl -> formatter -> Comp.kind -> unit
    val fmt_ppr_cmp_typ       : LF.mctx -> lvl -> formatter -> Comp.typ -> unit
    val fmt_ppr_cmp_ctyp_decl : LF.mctx -> lvl -> formatter -> Comp.ctyp_decl -> unit
    val fmt_ppr_cmp_gctx      : ?sep:(formatter -> unit -> unit) ->
                                LF.mctx -> lvl -> formatter -> Comp.gctx -> unit
    val fmt_ppr_cmp_exp_chk   : LF.mctx -> Comp.gctx -> lvl -> formatter -> Comp.exp_chk  -> unit
    val fmt_ppr_cmp_exp_syn   : LF.mctx -> Comp.gctx -> lvl -> formatter -> Comp.exp_syn  -> unit
    val fmt_ppr_cmp_value     : lvl -> formatter -> Comp.value -> unit
    val fmt_ppr_cmp_branches  : LF.mctx -> Comp.gctx -> lvl -> formatter -> Comp.branch list -> unit
    val fmt_ppr_cmp_branch    : LF.mctx -> Comp.gctx -> lvl -> formatter -> Comp.branch      -> unit
    val fmt_ppr_cmp_ih_args   : LF.mctx -> Comp.gctx -> formatter -> Comp.ih_arg list -> unit
    val fmt_ppr_cmp_ih        : LF.mctx -> Comp.gctx -> formatter -> Comp.ih_decl -> unit
    val fmt_ppr_cmp_ihctx     : LF.mctx -> Comp.gctx -> formatter -> Comp.ihctx -> unit

    val fmt_ppr_cmp_total_dec_kind : formatter -> Comp.order Comp.total_dec_kind -> unit
    val fmt_ppr_cmp_total_dec : formatter -> Comp.total_dec -> unit
    val fmt_ppr_cmp_gctx_typing : formatter -> LF.mctx * Comp.gctx -> unit
    val fmt_ppr_cmp_typ_typing : formatter -> LF.mctx * Comp.typ -> unit

    val fmt_ppr_cmp_numeric_order : formatter -> Comp.order -> unit
    val fmt_ppr_cmp_hypotheses_listing : formatter -> Comp.hypotheses -> unit
    val fmt_ppr_cmp_subgoal_path : LF.mctx -> Comp.gctx -> formatter -> Comp.SubgoalPath.t -> unit
    val fmt_ppr_cmp_proof_state : formatter -> Comp.proof_state -> unit
    val fmt_ppr_cmp_proof     : LF.mctx -> Comp.gctx -> formatter -> Comp.proof -> unit
    val fmt_ppr_cmp_command   : LF.mctx -> Comp.gctx -> formatter -> Comp.command -> unit
    val fmt_ppr_cmp_directive : LF.mctx -> Comp.gctx -> formatter -> Comp.directive -> unit
    val fmt_ppr_cmp_hypothetical : LF.mctx -> Comp.gctx -> formatter -> Comp.hypothetical -> unit
    val fmt_ppr_cmp_pattern       : LF.mctx -> Comp.gctx -> lvl -> formatter -> Comp.pattern     -> unit
    val fmt_ppr_cmp_meta_typ      : LF.mctx -> formatter -> Comp.meta_typ -> unit
    val fmt_ppr_cmp_meta_obj      : LF.mctx -> lvl -> formatter -> Comp.meta_obj -> unit
    val fmt_ppr_cmp_meta_spine    : LF.mctx -> lvl -> formatter -> Comp.meta_spine -> unit

    val fmt_ppr_cmp_comp_prog_info : formatter -> CompS.entry -> unit

    val fmt_ppr_cmp_thm : formatter -> Comp.thm -> unit
    val fmt_ppr_sgn_thm_decl : formatter -> Sgn.thm_decl -> unit
  end
end

module Ext = struct
  module type T = sig
    include Common.T
    open Syntax.Ext

    type lvl
    val l0 : lvl

    (* Contextual Format Based Pretty Printers *)
    val fmt_ppr_sgn           : formatter -> Sgn.sgn -> unit
    val fmt_ppr_sgn_decl      : formatter -> Sgn.decl -> unit
    val fmt_ppr_lf_kind       : lvl -> formatter -> LF.kind      -> unit
    val fmt_ppr_lf_ctyp_decl  : formatter -> LF.ctyp_decl -> unit
    val fmt_ppr_lf_typ_rec    : formatter -> LF.typ_rec    -> unit

    val fmt_ppr_lf_typ        : lvl -> formatter -> LF.typ    -> unit
    val fmt_ppr_lf_normal     : lvl -> formatter -> LF.normal -> unit
    val fmt_ppr_lf_head       : lvl -> formatter -> LF.head   -> unit
    val fmt_ppr_lf_spine      : lvl -> formatter -> LF.spine  -> unit
    val fmt_ppr_lf_sub        : ?pp_empty:(formatter -> unit -> bool) ->
                                lvl -> formatter -> LF.sub    -> unit

    val fmt_ppr_lf_schema     : lvl -> formatter -> LF.schema     -> unit
    val fmt_ppr_lf_sch_elem   : lvl -> formatter -> LF.sch_elem   -> unit

    val fmt_ppr_lf_dctx_hat   : formatter -> LF.dctx  -> unit
    val fmt_ppr_lf_dctx       : lvl -> formatter -> LF.dctx  -> unit

    val fmt_ppr_lf_mctx       : ?sep:(formatter -> unit -> unit)
                                -> lvl -> formatter -> LF.mctx     -> unit
    val fmt_ppr_cmp_kind      : lvl -> formatter -> Comp.kind -> unit
    val fmt_ppr_cmp_typ       : lvl -> formatter -> Comp.typ -> unit
    val fmt_ppr_cmp_exp_chk   : lvl -> Format.formatter -> Comp.exp_chk -> unit
    val fmt_ppr_cmp_exp_syn   : lvl -> Format.formatter -> Comp.exp_syn -> unit
    val fmt_ppr_cmp_branches  : Format.formatter -> Comp.branch list -> unit
    val fmt_ppr_cmp_branch    : Format.formatter -> Comp.branch -> unit
    val fmt_ppr_pat_obj       : lvl -> Format.formatter -> Comp.pattern -> unit

    val fmt_ppr_patternOpt    : formatter -> LF.normal option -> unit
  end
end
