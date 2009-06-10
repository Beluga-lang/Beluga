(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Pretty printing for external and internal syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html
*)

open Format
open Error

type lvl

val std_lvl : lvl

module Control : sig
  type substitution_style = Natural | DeBruijn

  val substitutionStyle : substitution_style ref
  val printImplicit : bool ref
 
  val db : unit -> bool  (* true if !substitutionStyle = DeBruijn *)
end

module type CID_RENDERER = sig

  open Id
  open Syntax.Int

  val render_name       : name       -> string
  val render_cid_typ    : cid_typ    -> string
  val render_cid_term   : cid_term   -> string
  val render_cid_schema : cid_schema -> string
  val render_cid_prog   : cid_prog   -> string
  val render_offset     : offset     -> string

  val render_ctx_var    : LF.mctx    -> offset   -> string
  val render_cvar       : LF.mctx    -> offset   -> string
  val render_bvar       : LF.dctx    -> offset   -> string
  val render_var        : Comp.gctx  -> var      -> string

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
    val fmt_ppr_lf_typ_rec : lvl -> formatter -> LF.typ_rec    -> unit
    val fmt_ppr_lf_psi_hat    : lvl -> formatter -> LF.psi_hat       -> unit
    val fmt_ppr_lf_mctx       : lvl -> formatter -> LF.mctx          -> unit
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
    val ppr_lf_typ_rec : LF.typ_rec    -> unit
    val ppr_lf_psi_hat    : LF.psi_hat       -> unit
    val ppr_lf_dctx       : LF.dctx          -> unit
    val ppr_lf_mctx       : LF.mctx          -> unit
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
    (* Contextual Format Based Pretty Printers *)
    val fmt_ppr_sgn_decl      : lvl -> formatter -> Sgn.decl  -> unit
    val fmt_ppr_lf_kind       : LF.dctx -> lvl -> formatter -> LF.kind      -> unit
    val fmt_ppr_lf_ctyp_decl  : LF.mctx -> LF.mctx -> lvl -> formatter -> LF.ctyp_decl -> unit
    val fmt_ppr_lf_typ_rec    : LF.mctx -> LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ_rec    -> unit

    val fmt_ppr_lf_typ        : LF.mctx -> LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ    -> unit
    val fmt_ppr_lf_normal     : LF.mctx -> LF.mctx -> LF.dctx -> lvl -> formatter -> LF.normal -> unit
    val fmt_ppr_lf_head       : LF.mctx -> LF.mctx -> LF.dctx -> lvl -> formatter -> LF.head   -> unit
    val fmt_ppr_lf_spine      : LF.mctx -> LF.mctx -> LF.dctx -> lvl -> formatter -> LF.spine  -> unit
    val fmt_ppr_lf_sub        : LF.mctx -> LF.mctx -> LF.dctx -> lvl -> formatter -> LF.sub    -> unit

    val fmt_ppr_lf_schema     : lvl -> formatter -> LF.schema     -> unit
    val fmt_ppr_lf_sch_elem   : lvl -> formatter -> LF.sch_elem   -> unit

    val fmt_ppr_lf_psi_hat    : LF.mctx -> lvl -> formatter -> LF.dctx  -> unit 
    val fmt_ppr_lf_mctx       : LF.mctx -> lvl -> formatter -> LF.mctx     -> unit
    val fmt_ppr_cmp_typ       : LF.mctx -> LF.mctx -> lvl -> formatter -> Comp.typ -> unit
    val fmt_ppr_cmp_exp_chk   : LF.mctx -> LF.mctx -> Comp.gctx -> lvl -> formatter -> Comp.exp_chk  -> unit
    val fmt_ppr_cmp_exp_syn   : LF.mctx -> LF.mctx -> Comp.gctx -> lvl -> formatter -> Comp.exp_syn  -> unit
    val fmt_ppr_cmp_branches  : LF.mctx -> LF.mctx -> Comp.gctx -> lvl -> formatter -> Comp.branch list -> unit
    val fmt_ppr_cmp_branch    : LF.mctx -> LF.mctx -> Comp.gctx -> lvl -> formatter -> Comp.branch      -> unit

    (* Regular Pretty Printers *)
    val ppr_sgn_decl      : Sgn.decl         -> unit
    val ppr_lf_kind       : LF.dctx -> LF.kind -> unit
    val ppr_lf_ctyp_decl  : LF.mctx -> LF.mctx -> LF.ctyp_decl  -> unit
    val ppr_lf_typ_rec    : LF.mctx -> LF.mctx -> LF.dctx -> LF.typ_rec -> unit
    val ppr_lf_typ        : LF.mctx -> LF.mctx -> LF.dctx -> LF.typ     -> unit
    val ppr_lf_normal     : LF.mctx -> LF.mctx -> LF.dctx -> LF.normal  -> unit
    val ppr_lf_head       : LF.mctx -> LF.mctx -> LF.dctx -> LF.head    -> unit
    val ppr_lf_spine      : LF.mctx -> LF.mctx -> LF.dctx -> LF.spine   -> unit
    val ppr_lf_sub        : LF.mctx -> LF.mctx -> LF.dctx -> LF.sub     -> unit

    val ppr_lf_schema     : LF.schema        -> unit
    val ppr_lf_sch_elem   : LF.sch_elem      -> unit

    (* val ppr_lf_psi_hat    : LF.mctx -> LF.dctx -> unit *)
    val ppr_lf_dctx       : LF.mctx -> LF.mctx -> LF.dctx  -> unit
    val ppr_lf_mctx       : LF.mctx -> LF.mctx -> unit
    val ppr_cmp_typ       : LF.mctx -> LF.mctx -> Comp.typ -> unit
    val ppr_cmp_exp_chk   : LF.mctx -> LF.mctx -> Comp.gctx -> Comp.exp_chk -> unit
    val ppr_cmp_exp_syn   : LF.mctx -> LF.mctx -> Comp.gctx -> Comp.exp_syn -> unit
    val ppr_cmp_branches  : LF.mctx -> LF.mctx -> Comp.gctx -> Comp.branch list -> unit
    val ppr_cmp_branch    : LF.mctx -> LF.mctx -> Comp.gctx -> Comp.branch      -> unit

    (* Conversion to string *)
    val subToString       : LF.mctx -> LF.mctx -> LF.dctx -> LF.sub      -> string
    val spineToString     : LF.mctx -> LF.mctx -> LF.dctx -> LF.sclo     -> string
    val typToString       : LF.mctx -> LF.mctx -> LF.dctx -> LF.tclo     -> string
    val typRecToString    : LF.mctx -> LF.mctx -> LF.dctx -> LF.trec_clo -> string
    val kindToString      : LF.dctx -> (LF.kind * LF.sub) -> string
    val normalToString    : LF.mctx -> LF.mctx -> LF.dctx -> LF.nclo     -> string
    val headToString      : LF.mctx -> LF.mctx -> LF.dctx -> LF.head     -> string
    val tupleToString     : LF.mctx -> LF.mctx -> LF.dctx -> LF.tuple    -> string
    val dctxToString      : LF.mctx -> LF.mctx -> LF.dctx -> string
    val mctxToString      : LF.mctx -> LF.mctx -> string
    val octxToString      : LF.mctx ->  string

    val schemaToString    : LF.schema     -> string 
    val gctxToString      : LF.mctx -> LF.mctx -> Comp.gctx  -> string
    val expChkToString    : LF.mctx -> LF.mctx -> Comp.gctx  -> Comp.exp_chk  -> string
    val expSynToString    : LF.mctx -> LF.mctx -> Comp.gctx  -> Comp.exp_syn  -> string
    val branchToString    : LF.mctx -> LF.mctx -> Comp.gctx  -> Comp.branch   -> string
    val compTypToString   : LF.mctx -> LF.mctx -> Comp.typ      -> string
    val msubToString      : LF.mctx -> LF.mctx -> LF.msub     -> string

  end


  (* Internal Syntax Pretty Printer Functor *)
  module Make : functor (R : CID_RENDERER) -> PRINTER

  (* Default CID_RENDERER for Internal Syntax *)
  module DefaultCidRenderer : CID_RENDERER

  (* Named Renderer for Internal Syntax *)
  module NamedRenderer : CID_RENDERER

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
