(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Pretty printing for external and internal syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html

    @author Darin Morrison
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

    val fmt_ppr_sgn_decl : lvl -> formatter -> sgn_decl -> unit

    val fmt_ppr_kind     : lvl -> formatter -> kind     -> unit

    val fmt_ppr_typ      : lvl -> formatter -> typ      -> unit

    val fmt_ppr_normal   : lvl -> formatter -> normal   -> unit

    val fmt_ppr_head     :        formatter -> head     -> unit

    val fmt_ppr_spine    : lvl -> formatter -> spine    -> unit



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    val ppr_sgn_decl : sgn_decl -> unit

    val ppr_kind     : kind     -> unit

    val ppr_type     : typ      -> unit

    val ppr_normal   : normal   -> unit

    val ppr_head     : head     -> unit

    val ppr_spine    : spine    -> unit

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

    val fmt_ppr_sgn_decl : lvl -> formatter -> sgn_decl -> unit

    val fmt_ppr_kind     : lvl -> formatter -> kind     -> unit

    val fmt_ppr_typ      : lvl -> formatter -> typ      -> unit

    val fmt_ppr_normal   : lvl -> formatter -> normal   -> unit

    val fmt_ppr_head     :        formatter -> head     -> unit

    val fmt_ppr_spine    : lvl -> formatter -> spine    -> unit

    val fmt_ppr_sub      :        formatter -> sub      -> unit

    val fmt_ppr_front    : lvl -> formatter -> front    -> unit



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    val ppr_sgn_decl : sgn_decl -> unit

    val ppr_kind     : kind     -> unit

    val ppr_type     : typ      -> unit

    val ppr_normal   : normal   -> unit

    val ppr_head     : head     -> unit

    val ppr_spine    : spine    -> unit

    val ppr_sub      : sub      -> unit

    val ppr_front    : front    -> unit

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

      val fmt_ppr : formatter -> Check.error -> unit



      (***************************)
      (* Regular Pretty Printers *)
      (***************************)

      val ppr : Check.error -> unit

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
