(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Pretty printing for external and internal syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html
*)



open Format



type lvl

val std_lvl : lvl



module type CID_RENDERER = sig

  open Id

  val render_name       : name     -> string

  val render_cid_typ    : cid_typ  -> string

  val render_cid_term   : cid_term -> string

  val render_offset     : offset   -> string

  val render_var        : var      -> string

end



module Ext : sig

  (*************************************)
  (* External Syntax Printer Signature *)
  (*************************************)

  module type PRINTER = sig

    open Syntax.Ext

    (*******************************************)
    (* Contextual Format Based Pretty Printers *)
    (*******************************************)

    val fmt_ppr_sgn_decl      : lvl -> formatter -> Sgn.decl         -> unit

    val fmt_ppr_lf_kind       : lvl -> formatter -> LF.kind          -> unit

    val fmt_ppr_lf_ctyp_decl  : lvl -> formatter -> LF.ctyp_decl     -> unit

    val fmt_ppr_lf_typ        : lvl -> formatter -> LF.typ           -> unit

    val fmt_ppr_lf_normal     : lvl -> formatter -> LF.normal        -> unit

    val fmt_ppr_lf_head       : lvl -> formatter -> LF.head          -> unit

    val fmt_ppr_lf_spine      : lvl -> formatter -> LF.spine         -> unit

    val fmt_ppr_lf_sub        : lvl -> formatter -> LF.sub           -> unit

    val fmt_ppr_lf_schema     : lvl -> formatter -> LF.schema        -> unit

    val fmt_ppr_lf_sch_elem   : lvl -> formatter -> LF.sch_elem      -> unit

    val fmt_ppr_lf_sigma_decl : lvl -> formatter -> LF.sigma_decl    -> unit

    val fmt_ppr_lf_psi_hat    : lvl -> formatter -> LF.psi_hat       -> unit

    val fmt_ppr_lf_dctx       : lvl -> formatter -> LF.dctx          -> unit

    val fmt_ppr_cmp_typ       : lvl -> formatter -> Comp.typ         -> unit

    val fmt_ppr_cmp_exp_chk   : lvl -> formatter -> Comp.exp_chk     -> unit

    val fmt_ppr_cmp_exp_syn   : lvl -> formatter -> Comp.exp_syn     -> unit

    val fmt_ppr_cmp_branches  : lvl -> formatter -> Comp.branch list -> unit

    val fmt_ppr_cmp_branch    : lvl -> formatter -> Comp.branch      -> unit



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    val ppr_sgn_decl      : Sgn.decl         -> unit

    val ppr_lf_kind       : LF.kind          -> unit

    val ppr_lf_ctyp_decl  : LF.ctyp_decl     -> unit

    val ppr_lf_typ        : LF.typ           -> unit

    val ppr_lf_normal     : LF.normal        -> unit

    val ppr_lf_head       : LF.head          -> unit

    val ppr_lf_spine      : LF.spine         -> unit

    val ppr_lf_sub        : LF.sub           -> unit

    val ppr_lf_schema     : LF.schema        -> unit

    val ppr_lf_sch_elem   : LF.sch_elem      -> unit

    val ppr_lf_sigma_decl : LF.sigma_decl    -> unit

    val ppr_lf_psi_hat    : LF.psi_hat       -> unit

    val ppr_lf_dctx       : LF.dctx          -> unit

    val ppr_cmp_typ       : Comp.typ         -> unit

    val ppr_cmp_exp_chk   : Comp.exp_chk     -> unit

    val ppr_cmp_exp_syn   : Comp.exp_syn     -> unit

    val ppr_cmp_branches  : Comp.branch list -> unit

    val ppr_cmp_branch    : Comp.branch      -> unit

  end



  (******************************************)
  (* External Syntax Pretty Printer Functor *)
  (******************************************)

  module Make : functor (R : CID_RENDERER) -> PRINTER



  (********************************************)
  (* Default CID_RENDERER for External Syntax *)
  (********************************************)

  module DefaultCidRenderer : CID_RENDERER



  (****************************************************************)
  (* Default External Syntax Pretty Printer Functor Instantiation *)
  (****************************************************************)

  module DefaultPrinter : PRINTER

end



module Int : sig

  (*************************************)
  (* Internal Syntax Printer Signature *)
  (*************************************)

  module type PRINTER = sig

    open Syntax.Int

    (*******************************************)
    (* Contextual Format Based Pretty Printers *)
    (*******************************************)

    val fmt_ppr_sgn_decl    : lvl -> formatter -> Sgn.decl  -> unit

    val fmt_ppr_lf_kind     : lvl -> formatter -> LF.kind   -> unit

    val fmt_ppr_lf_typ      : lvl -> formatter -> LF.typ    -> unit

    val fmt_ppr_lf_normal   : lvl -> formatter -> LF.normal -> unit

    val fmt_ppr_lf_head     : lvl -> formatter -> LF.head   -> unit

    val fmt_ppr_lf_spine    : lvl -> formatter -> LF.spine  -> unit

    val fmt_ppr_lf_sub      : lvl -> formatter -> LF.sub    -> unit

    val fmt_ppr_lf_front    : lvl -> formatter -> LF.front  -> unit

    val fmt_ppr_lf_cvar     : lvl -> formatter -> LF.cvar   -> unit



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    val ppr_sgn_decl    : Sgn.decl  -> unit

    val ppr_lf_kind     : LF.kind   -> unit

    val ppr_lf_typ      : LF.typ    -> unit

    val ppr_lf_normal   : LF.normal -> unit

    val ppr_lf_head     : LF.head   -> unit

    val ppr_lf_spine    : LF.spine  -> unit

    val ppr_lf_sub      : LF.sub    -> unit

    val ppr_lf_front    : LF.front  -> unit

    val ppr_lf_cvar     : LF.cvar   -> unit

  end



  (******************************************)
  (* Internal Syntax Pretty Printer Functor *)
  (******************************************)

  module Make : functor (R : CID_RENDERER) -> PRINTER



  (********************************************)
  (* Default CID_RENDERER for Internal Syntax *)
  (********************************************)

  module DefaultCidRenderer : CID_RENDERER



  (****************************************************************)
  (* Default Internal Syntax Pretty Printer Functor Instantiation *)
  (****************************************************************)

  module DefaultPrinter : PRINTER

end



module Error : sig

  (***************************)
  (* Error Printer Signature *)
  (***************************)

  module type PRINTER = sig

    module Check : sig

      (********************************)
      (* Format Based Pretty Printers *)
      (********************************)

      val fmt_ppr : formatter -> Check.LF.error -> unit



      (***************************)
      (* Regular Pretty Printers *)
      (***************************)

      val ppr : Check.LF.error -> unit

    end



    module Whnf : sig

      (********************************)
      (* Format Based Pretty Printers *)
      (********************************)

      val fmt_ppr : formatter -> Whnf.error -> unit



      (***************************)
      (* Regular Pretty Printers *)
      (***************************)

      val ppr : Whnf.error -> unit

    end

  end



  (***********************************)
  (* Default CID_RENDERER for Errors *)
  (***********************************)

  module DefaultCidRenderer : CID_RENDERER



  (*********************************)
  (* Error Pretty Printer Functor  *)
  (*********************************)

  module Make : functor (R : CID_RENDERER) -> PRINTER
      (* Might need a constraint here saying that IPF will be
      instantiated with R.  -dwm *)



  (******************************************************)
  (* Default Error Pretty Printer Functor Instantiation *)
  (******************************************************)

  module DefaultPrinter : PRINTER

end
