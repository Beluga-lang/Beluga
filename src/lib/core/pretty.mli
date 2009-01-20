(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Pretty printing for external and internal syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html
*)

open Format
open Error

type lvl

val std_lvl : lvl


module type CID_RENDERER = sig

  open Id

  val render_name       : name       -> string
  val render_cid_typ    : cid_typ    -> string
  val render_cid_term   : cid_term   -> string
  val render_cid_schema : cid_schema -> string
  val render_cid_prog   : cid_prog   -> string
  val render_offset     : offset     -> string
  val render_var        : var        -> string

end


module Ext : sig

  (* External Syntax Printer Signature *)
  module type PRINTER = sig

    open Syntax.Ext

    (* Contextual Format Based Pretty Printers *)
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
    val fmt_ppr_cmp_typ       : lvl -> formatter -> Comp.typ         -> unit
    val fmt_ppr_cmp_exp_chk   : lvl -> formatter -> Comp.exp_chk     -> unit
    val fmt_ppr_cmp_exp_syn   : lvl -> formatter -> Comp.exp_syn     -> unit
    val fmt_ppr_cmp_branches  : lvl -> formatter -> Comp.branch list -> unit
    val fmt_ppr_cmp_branch    : lvl -> formatter -> Comp.branch      -> unit

    (* Regular Pretty Printers *)
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

  (* External Syntax Pretty Printer Functor *)
  module Make : functor (R : CID_RENDERER) -> PRINTER

  (* Default CID_RENDERER for External Syntax *)
  module DefaultCidRenderer : CID_RENDERER

  (* Default External Syntax Pretty Printer Functor Instantiation *)
  module DefaultPrinter : PRINTER

end


module Int : sig

  (* Internal Syntax Printer Signature *)
  module type PRINTER = sig

    open Syntax.Int

    (* Contextual Format Based Pretty Printers *)
    val fmt_ppr_sgn_decl      : lvl -> formatter -> Sgn.decl         -> unit
    val fmt_ppr_lf_kind       : lvl -> formatter -> LF.kind          -> unit
    val fmt_ppr_lf_ctyp_decl  : lvl -> formatter -> LF.ctyp_decl     -> unit
    val fmt_ppr_lf_typ        : lvl -> formatter -> LF.typ           -> unit
    val fmt_ppr_lf_normal     : lvl -> formatter -> LF.normal        -> unit
    val fmt_ppr_lf_head       : lvl -> formatter -> LF.head          -> unit
    val fmt_ppr_lf_spine      : lvl -> formatter -> LF.spine         -> unit
    val fmt_ppr_lf_sub        : lvl -> formatter -> LF.sub           -> unit
    val fmt_ppr_lf_front      : lvl -> formatter -> LF.front         -> unit
    val fmt_ppr_lf_cvar       : lvl -> formatter -> LF.cvar          -> unit
    val fmt_ppr_lf_schema     : lvl -> formatter -> LF.schema        -> unit
    val fmt_ppr_lf_sch_elem   : lvl -> formatter -> LF.sch_elem      -> unit
    val fmt_ppr_lf_sigma_decl : lvl -> formatter -> LF.sigma_decl    -> unit
    val fmt_ppr_lf_psi_hat    : lvl -> formatter -> LF.psi_hat       -> unit
    val fmt_ppr_lf_dctx       : lvl -> formatter -> LF.dctx          -> unit 
    val fmt_ppr_lf_mctx       : lvl -> formatter -> LF.mctx          -> unit 
    val fmt_ppr_cmp_gctx      : lvl -> formatter -> Comp.gctx        -> unit 
    val fmt_ppr_cmp_typ       : lvl -> formatter -> Comp.typ         -> unit
    val fmt_ppr_cmp_exp_chk   : lvl -> formatter -> Comp.exp_chk     -> unit
    val fmt_ppr_cmp_exp_syn   : lvl -> formatter -> Comp.exp_syn     -> unit
    val fmt_ppr_cmp_branches  : lvl -> formatter -> Comp.branch list -> unit
    val fmt_ppr_cmp_branch    : lvl -> formatter -> Comp.branch      -> unit
    val fmt_ppr_cmp_msub      : lvl -> formatter -> Comp.msub        -> unit
    val fmt_ppr_cmp_mfront    : lvl -> formatter -> Comp.mfront      -> unit

    (* Regular Pretty Printers *)
    val ppr_sgn_decl      : Sgn.decl         -> unit
    val ppr_lf_kind       : LF.kind          -> unit
    val ppr_lf_ctyp_decl  : LF.ctyp_decl     -> unit
    val ppr_lf_typ        : LF.typ           -> unit
    val ppr_lf_normal     : LF.normal        -> unit
    val ppr_lf_head       : LF.head          -> unit
    val ppr_lf_spine      : LF.spine         -> unit
    val ppr_lf_sub        : LF.sub           -> unit
    val ppr_lf_front      : LF.front         -> unit
    val ppr_lf_cvar       : LF.cvar          -> unit
    val ppr_lf_schema     : LF.schema        -> unit
    val ppr_lf_sch_elem   : LF.sch_elem      -> unit
    val ppr_lf_sigma_decl : LF.sigma_decl    -> unit
    val ppr_lf_psi_hat    : LF.psi_hat       -> unit
    val ppr_lf_dctx       : LF.dctx          -> unit
    val ppr_lf_mctx       : LF.mctx          -> unit
    val ppr_cmp_gctx      : Comp.gctx        -> unit
    val ppr_cmp_typ       : Comp.typ         -> unit
    val ppr_cmp_exp_chk   : Comp.exp_chk     -> unit
    val ppr_cmp_exp_syn   : Comp.exp_syn     -> unit
    val ppr_cmp_branches  : Comp.branch list -> unit
    val ppr_cmp_branch    : Comp.branch      -> unit
    val ppr_cmp_msub      : Comp.msub        -> unit
    val ppr_cmp_mfront    : Comp.mfront      -> unit

    (* Conversion to string *)
    val headToString    : LF.head       -> string   
    val subToString     : LF.sub        -> string
    val spineToString   : LF.spine      -> string
    val typToString     : LF.typ        -> string
    val kindToString    : LF.kind       -> string
    val normalToString  : LF.normal     -> string
    val dctxToString    : LF.dctx       -> string
    val mctxToString    : LF.mctx       -> string
    val schemaToString  : LF.schema     -> string
    val gctxToString    : Comp.gctx     -> string
    val expChkToString  : Comp.exp_chk  -> string
    val expSynToString  : Comp.exp_syn  -> string
    val branchToString  : Comp.branch   -> string
    val compTypToString : Comp.typ      -> string
    val msubToString    : Comp.msub     -> string

  end


  (* Internal Syntax Pretty Printer Functor *)
  module Make : functor (R : CID_RENDERER) -> PRINTER

  (* Default CID_RENDERER for Internal Syntax *)
  module DefaultCidRenderer : CID_RENDERER

  (* Default Internal Syntax Pretty Printer Functor Instantiation *)
  module DefaultPrinter : PRINTER

end


module Error : sig

  (* Error Printer Signature *)
  module type PRINTER = sig

    (* Format Based Pretty Printers *)
    val fmt_ppr : formatter -> error -> unit

    (* Regular Pretty Printers *)
    val ppr     : error -> unit    

  end

  (* Default CID_RENDERER for Errors *)
  module DefaultCidRenderer : CID_RENDERER

  (* Error Pretty Printer Functor  *)
  module Make : functor (R : CID_RENDERER) -> PRINTER
    (* Might need a constraint here saying that IPF will be
       instantiated with R.  -dwm *)

  (* Default Error Pretty Printer Functor Instantiation *)
  module DefaultPrinter : PRINTER

end
