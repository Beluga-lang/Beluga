(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Pretty printing for external and internal syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html
*)

open Format



(* Explanation of formatting markup:

   "@[" opens a box (open_box 0).  You may specify more information
   with an argument, e.g., "@[<hov n>" is equivalent to open_hovbox n

   "@]" closes a box (close_box ())

   "@ " outputs a breakable space (print_space ())

   "@," output a break hint (print_cut ())

   "@." end the pretty-printing, closing all boxes still opened
   (print_newline ())

   "@;<n m>" emit a "full" break hint (print_break n m)

   "@?" output pending material in the pretty-printer queue
   (print_flush ())
*)



type lvl    = int

let std_lvl = 0


let l_paren_if cond =
  if cond
  then "("
  else ""

let r_paren_if cond =
  if cond
  then ")"
  else ""



module type CID_RENDERER = sig

  open Id



  val render_name     : name     -> string

  val render_cid_typ  : cid_typ  -> string

  val render_cid_term : cid_term -> string

  val render_offset   : offset   -> string

  val render_var      : var      -> string

end



module Ext = struct

  open Id
  open Syntax.Ext



  (*************************************)
  (* External Syntax Printer Signature *)
  (*************************************)

  module type PRINTER = sig

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

  module Make = functor (R : CID_RENDERER) -> struct

    (*******************************************)
    (* Contextual Format Based Pretty Printers *)
    (*******************************************)

    let rec fmt_ppr_sgn_decl lvl ppf = function
      | Sgn.Const (_, c, a) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_name    c)
            (fmt_ppr_lf_typ lvl) a

      | Sgn.Pragma (_, _) -> ()

      | Sgn.Rec (_, f, tau, e) ->
          fprintf ppf "rec %s : %a =@ %a;@.@?"
            (R.render_name f)
            (fmt_ppr_cmp_typ lvl) tau
            (fmt_ppr_cmp_exp_chk lvl) e

      | Sgn.Schema (_, w, tW) ->
          fprintf ppf "schema %s = %a;@.@?"
            (R.render_name w)
            (fmt_ppr_lf_schema lvl) tW

      | Sgn.Typ (_, a, k) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_name a)
            (fmt_ppr_lf_kind lvl) k



    and fmt_ppr_lf_kind lvl ppf = function
      | LF.Typ _ ->
          fprintf ppf "type"

      | LF.ArrKind (_, a, k) ->
          let cond = lvl > 0 in
            fprintf ppf "@[%s%a -> %a%s@]"
              (l_paren_if cond)
              (fmt_ppr_lf_typ  1) a
              (fmt_ppr_lf_kind 0) k
              (r_paren_if cond)

      | LF.PiKind (_, LF.TypDecl (x, a), k) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name   x)
              (fmt_ppr_lf_typ  0) a
              (fmt_ppr_lf_kind 0) k
              (r_paren_if cond)



    and fmt_ppr_lf_ctyp_decl _lvl ppf = function
      | LF.MDecl (_, u, tA, cPsi) ->
          fprintf ppf "{%s :: %a[%a]}"
            (R.render_name u)
            (fmt_ppr_lf_typ 0) tA
            (fmt_ppr_lf_dctx 0) cPsi

      | LF.PDecl (_, p, tA, cPsi) ->
          fprintf ppf "{#%s :: %a[%a]}"
            (R.render_name p)
            (fmt_ppr_lf_typ 0) tA
            (fmt_ppr_lf_dctx 0) cPsi


    and fmt_ppr_lf_typ lvl ppf = function
      | LF.Atom (_, a, LF.Nil) ->
          fprintf ppf "%s"
            (R.render_name a)

      | LF.Atom (_, a, ms) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%s%a%s"
              (l_paren_if cond)
              (R.render_name    a)
              (fmt_ppr_lf_spine 2) ms
              (r_paren_if cond)

      | LF.ArrTyp (_, a, b) ->
          let cond = lvl > 0 in
            fprintf ppf "@[%s%a -> %a%s@]"
              (l_paren_if cond)
              (fmt_ppr_lf_typ 1) a
              (fmt_ppr_lf_typ 0) b
              (r_paren_if cond)

      | LF.PiTyp (_, LF.TypDecl (x, a), b) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name  x)
              (fmt_ppr_lf_typ 0) a
              (fmt_ppr_lf_typ 0) b
              (r_paren_if cond)



    and fmt_ppr_lf_normal lvl ppf = function
      | LF.Lam (_, x, tM) ->
          let cond = lvl > 0 in
            fprintf ppf "%s[%s] %a%s"
              (l_paren_if cond)
              (R.render_name   x)
              (fmt_ppr_lf_normal 0) tM
              (r_paren_if cond)

      | LF.Root (_, h, LF.Nil) ->
          fprintf ppf "%a"
            (fmt_ppr_lf_head lvl) h

      | LF.Root (_, h, ms)  ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a%a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_head lvl) h
              (fmt_ppr_lf_spine 2)  ms
              (r_paren_if cond)



    and fmt_ppr_lf_head _lvl ppf = function
      | LF.Name (_, x) ->
          fprintf ppf "%s"
            (R.render_name x)

      | LF.MVar (_, x, sigma) ->
          fprintf ppf "%s[%a]"
            (R.render_name x)
            (fmt_ppr_lf_sub 0) sigma

      | LF.PVar (_, x, sigma) ->
          fprintf ppf "#%s[%a]"
            (R.render_name x)
            (fmt_ppr_lf_sub 0) sigma



    and fmt_ppr_lf_spine lvl ppf = function
      | LF.Nil ->
          fprintf ppf ""

      | LF.App (_, m, ms) ->
          fprintf ppf " %a%a"
            (fmt_ppr_lf_normal lvl) m
            (fmt_ppr_lf_spine  lvl) ms



    and fmt_ppr_lf_sub _lvl ppf = function
      | LF.Dot _ ->
          fprintf ppf "."

      | LF.Normal (_, sigma, tM) ->
          fprintf ppf "%a, %a"
          (fmt_ppr_lf_sub 0) sigma
          (fmt_ppr_lf_normal 0) tM

      | LF.Id (_, x) ->
          fprintf ppf "id(%s)"
            (R.render_name x)



    and fmt_ppr_lf_schema lvl ppf = function
      | LF.Schema [] -> ()

      | LF.Schema (f :: []) ->
            fprintf ppf "%a"
              (fmt_ppr_lf_sch_elem lvl) f

      | LF.Schema (f :: fs) ->
            fprintf ppf "%a@ +"
              (fmt_ppr_lf_sch_elem lvl) f
          ; fmt_ppr_lf_schema lvl ppf (LF.Schema fs)

    and fmt_ppr_lf_sch_elem lvl ppf = function
      | LF.SchElem (_, typDecls, sgmDecl) ->
          let rec ppr_typ_decl_ctx ppf = function
            | LF.Empty -> ()

            | LF.Dec (LF.Empty, LF.TypDecl (x, tA)) ->
                fprintf ppf "%s : %a"
                  (R.render_name x)
                  (fmt_ppr_lf_typ 0) tA

            | LF.Dec (xs, LF.TypDecl (x, tA)) ->
                  fprintf ppf "%s : %a,@ "
                    (R.render_name x)
                    (fmt_ppr_lf_typ 0) tA
                ; ppr_typ_decl_ctx ppf xs
          in
            fprintf ppf "some [%a] block %a"
              ppr_typ_decl_ctx            typDecls
              (fmt_ppr_lf_sigma_decl lvl) sgmDecl

    and fmt_ppr_lf_sigma_decl _lvl ppf = function
      | LF.SigmaDecl (_x, tAs) ->
          let rec ppr_typ_rec ppf = function
            | [tA] ->
                fprintf ppf "%a"
                  (fmt_ppr_lf_typ 0) tA
(*             | [] -> () *)

(*             | tA :: [] -> *)
(*                 fprintf ppf "%a" *)
(*                   (fmt_ppr_lf_typ 0) tA *)

(*             | tA :: tAs -> *)
(*                   fprintf ppf "%a,@ %a" *)
(*                     (fmt_ppr_lf_typ 0) tA *)
(*                     ppr_typ_rec        tAs *)
          in
            fprintf ppf "%a"
              ppr_typ_rec tAs

    and fmt_ppr_lf_psi_hat _lvl ppf = function
      | []      -> ()

      | x :: [] ->
          fprintf ppf "%s"
            (R.render_name x)

      | x :: xs ->
          fprintf ppf "%s : %a"
            (R.render_name x)
            (fmt_ppr_lf_psi_hat 0) xs



    and fmt_ppr_lf_dctx _lvl ppf = function
      | LF.Null ->
          fprintf ppf "."

      | LF.CtxVar psi ->
          fprintf ppf "%s" (R.render_name psi)

      | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
          fprintf ppf "%a, %s : %a"
            (fmt_ppr_lf_dctx 0) cPsi
            (R.render_name x)
            (fmt_ppr_lf_typ 0) tA



    and fmt_ppr_cmp_typ lvl ppf = function
      | Comp.TypBox (_, tA, cPsi) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_typ 1) tA
            (fmt_ppr_lf_dctx 0) cPsi

      | Comp.TypArr (_, tau1, tau2) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%a -> %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_typ 1) tau1
              (fmt_ppr_cmp_typ 0) tau2
              (r_paren_if cond)

      | Comp.TypCtxPi (_, (psi, w), tau) ->
          let cond = lvl > 0 in
            fprintf ppf "%s{%s:(%s)*} %a%s"
              (l_paren_if cond)
              (R.render_name psi)
              (R.render_name w)
              (fmt_ppr_cmp_typ 0) tau
              (r_paren_if cond)

      | Comp.TypPiBox (_, ctyp_decl, tau) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%a %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_ctyp_decl 1) ctyp_decl
              (fmt_ppr_cmp_typ 0) tau
              (r_paren_if cond)



    and fmt_ppr_cmp_exp_chk lvl ppf = function
      | Comp.Syn (_, i) ->
          fmt_ppr_cmp_exp_syn lvl ppf i

      | Comp.Fun (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%sfn %s =>@ %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk 0) e
              (r_paren_if cond)

      | Comp.CtxFun (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%sFN %s =>@ %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk 0) e
              (r_paren_if cond)

      | Comp.MLam (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%smlam %s => %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk 0) e
              (r_paren_if cond)

      | Comp.Box (_, pHat, tM) ->
          let cond = lvl > 1 in
            fprintf ppf "%sbox (%a. %a)%s"
              (l_paren_if cond)
              (fmt_ppr_lf_psi_hat 0) pHat
              (fmt_ppr_lf_normal 0) tM
              (r_paren_if cond)

      | Comp.Case (_, i, bs) ->
          let cond = lvl > 1 in
            fprintf ppf "@[<2>%scase %a of@[<-1>%a@]%s@]"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn 0) i
              (fmt_ppr_cmp_branches 0) bs
              (r_paren_if cond)



    and fmt_ppr_cmp_exp_syn lvl ppf = function
      | Comp.Var (_, x) ->
          fprintf ppf "%s"
            (R.render_name x)

      | Comp.Apply (_, i, e) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn 1) i
              (fmt_ppr_cmp_exp_chk 2) e
              (r_paren_if cond)

      | Comp.CtxApp (_, i, cPsi) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a [%a]%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn 1) i
              (fmt_ppr_lf_dctx 0) cPsi
              (r_paren_if cond)

      | Comp.MApp (_, i, (pHat, tM)) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a [%a. %a]%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn 1) i
              (fmt_ppr_lf_psi_hat 0) pHat
              (fmt_ppr_lf_normal 0) tM
              (r_paren_if cond)

      | Comp.Ann (_, e, tau) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a : %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_chk 1) e
              (fmt_ppr_cmp_typ 2) tau
              (r_paren_if cond)



    and fmt_ppr_cmp_branches lvl ppf = function
      | [] -> ()

      | b :: [] ->
          fprintf ppf "%a"
            (fmt_ppr_cmp_branch 0) b

      | b :: bs ->
          fprintf ppf "%a@,|%a"
            (fmt_ppr_cmp_branch 0) b
            (fmt_ppr_cmp_branches lvl) bs



    and fmt_ppr_cmp_branch _lvl ppf = function
      | Comp.BranchBox (_, ctyp_decls, (pHat, tM, (tA, cPsi)), e) ->
          let rec ppr_ctyp_decls ppf = function
            | LF.Empty             -> ()

            | LF.Dec (decls, decl) ->
                fprintf ppf "%a %a"
                  ppr_ctyp_decls decls
                  (fmt_ppr_lf_ctyp_decl 1) decl
          in
            fprintf ppf "%a box (%a . %a) : %a[%a] => %a"
              ppr_ctyp_decls ctyp_decls
              (fmt_ppr_lf_psi_hat 0) pHat
              (fmt_ppr_lf_normal 0) tM
              (fmt_ppr_lf_typ 0) tA
              (fmt_ppr_lf_dctx 0) cPsi
              (fmt_ppr_cmp_exp_chk 0) e



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    let ppr_sgn_decl      = fmt_ppr_sgn_decl      std_lvl std_formatter

    let ppr_lf_kind       = fmt_ppr_lf_kind       std_lvl std_formatter

    let ppr_lf_ctyp_decl  = fmt_ppr_lf_ctyp_decl  std_lvl std_formatter

    let ppr_lf_typ        = fmt_ppr_lf_typ        std_lvl std_formatter

    let ppr_lf_normal     = fmt_ppr_lf_normal     std_lvl std_formatter

    let ppr_lf_head       = fmt_ppr_lf_head       std_lvl std_formatter

    let ppr_lf_spine      = fmt_ppr_lf_spine      std_lvl std_formatter

    let ppr_lf_sub        = fmt_ppr_lf_sub        std_lvl std_formatter

    let ppr_lf_schema     = fmt_ppr_lf_schema     std_lvl std_formatter

    let ppr_lf_sch_elem   = fmt_ppr_lf_sch_elem   std_lvl std_formatter

    let ppr_lf_sigma_decl = fmt_ppr_lf_sigma_decl std_lvl std_formatter

    let ppr_lf_psi_hat    = fmt_ppr_lf_psi_hat    std_lvl std_formatter

    let ppr_lf_dctx       = fmt_ppr_lf_dctx       std_lvl std_formatter

    let ppr_cmp_typ       = fmt_ppr_cmp_typ       std_lvl std_formatter

    let ppr_cmp_exp_chk   = fmt_ppr_cmp_exp_chk   std_lvl std_formatter

    let ppr_cmp_exp_syn   = fmt_ppr_cmp_exp_syn   std_lvl std_formatter

    let ppr_cmp_branches  = fmt_ppr_cmp_branches  std_lvl std_formatter

    let ppr_cmp_branch    = fmt_ppr_cmp_branch    std_lvl std_formatter

  end



  (********************************************)
  (* Default CID_RENDERER for External Syntax *)
  (********************************************)

  module DefaultCidRenderer = struct

    let render_name n   = n.string_of_name

    let render_cid_typ  = string_of_int

    let render_cid_term = string_of_int

    let render_offset   = string_of_int

    let render_var      = string_of_int

  end



  (****************************************************************)
  (* Default External Syntax Pretty Printer Functor Instantiation *)
  (****************************************************************)

  module DefaultPrinter = Make (DefaultCidRenderer)

end


module Int = struct

  open Id
  open Syntax.Int



  (*************************************)
  (* Internal Syntax Printer Signature *)
  (*************************************)

  module type PRINTER = sig

    (*******************************************)
    (* Contextual Format Based Pretty Printers *)
    (*******************************************)

    val fmt_ppr_sgn_decl    : lvl -> formatter -> Sgn.decl    -> unit

    val fmt_ppr_lf_kind     : lvl -> formatter -> LF.kind     -> unit

    val fmt_ppr_lf_typ      : lvl -> formatter -> LF.typ      -> unit

    val fmt_ppr_lf_normal   : lvl -> formatter -> LF.normal   -> unit

    val fmt_ppr_lf_head     : lvl -> formatter -> LF.head     -> unit

    val fmt_ppr_lf_spine    : lvl -> formatter -> LF.spine    -> unit

    val fmt_ppr_lf_sub      : lvl -> formatter -> LF.sub      -> unit

    val fmt_ppr_lf_front    : lvl -> formatter -> LF.front    -> unit

    val fmt_ppr_lf_cvar     : lvl -> formatter -> LF.cvar     -> unit



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    val ppr_sgn_decl      : Sgn.decl      -> unit

    val ppr_lf_kind       : LF.kind       -> unit

    val ppr_lf_typ        : LF.typ        -> unit

    val ppr_lf_normal     : LF.normal     -> unit

    val ppr_lf_head       : LF.head       -> unit

    val ppr_lf_spine      : LF.spine      -> unit

    val ppr_lf_sub        : LF.sub        -> unit

    val ppr_lf_front      : LF.front      -> unit

    val ppr_lf_cvar       : LF.cvar       -> unit

    val headToString      : LF.head       -> string

    val subToString       : LF.sub        -> string

    val spineToString     : LF.spine      -> string

    val typToString       : LF.typ        -> string

    val kindToString      : LF.kind       -> string

    val normalToString    : LF.normal     -> string

    val dctxToString      : LF.dctx       -> string
  end



  (******************************************)
  (* Internal Syntax Pretty Printer Functor *)
  (******************************************)

  module Make = functor (R : CID_RENDERER) -> struct

    module InstHashedType = struct
      type t    = LF.normal option ref
      let equal = (==)
      let hash  = Hashtbl.hash
    end

    module InstHashtbl = Hashtbl.Make (InstHashedType)

    let inst_hashtbl : string InstHashtbl.t = InstHashtbl.create 0

    (*******************************************)
    (* Contextual Format Based Pretty Printers *)
    (*******************************************)

    let rec fmt_ppr_sgn_decl lvl ppf = function
      | Sgn.Const (c, a) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_cid_term c)
            (fmt_ppr_lf_typ lvl)  a

      | Sgn.Typ (a, k) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_cid_typ  a)
            (fmt_ppr_lf_kind lvl) k



    and fmt_ppr_lf_kind lvl ppf = function
      | LF.Typ ->
          fprintf ppf "type"

      | LF.PiKind (LF.TypDecl (x, a), k) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name   x)
              (fmt_ppr_lf_typ  0) a
              (fmt_ppr_lf_kind 0) k
              (r_paren_if cond)



    and fmt_ppr_lf_typ lvl ppf = function
      | LF.Atom (a, LF.Nil) ->
          fprintf ppf "%s"
            (R.render_cid_typ a)

      | LF.Atom (a, ms) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%s%a%s"
              (l_paren_if cond)
              (R.render_cid_typ a)
              (fmt_ppr_lf_spine 2) ms
              (r_paren_if cond)

      | LF.PiTyp (LF.TypDecl (x, a), b) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name  x)
              (fmt_ppr_lf_typ 0) a
              (fmt_ppr_lf_typ 0) b
              (r_paren_if cond)

      | LF.TClo (tA, s) -> 
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_typ lvl) tA
            (fmt_ppr_lf_sub lvl) s


    and fmt_ppr_lf_normal lvl ppf = function
      | LF.Lam (x, m) ->
          let cond = lvl > 0 in
            fprintf ppf "%s\\ %s . %a%s"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_lf_normal 0) m
              (r_paren_if cond)

      | LF.Root (h, LF.Nil) ->
          fprintf ppf "%a"
            (fmt_ppr_lf_head lvl) h

      | LF.Root (h, ms)  ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a%a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_head lvl) h
              (fmt_ppr_lf_spine 2)  ms
              (r_paren_if cond)

      | LF.Clo(tM, s) -> 
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_normal lvl) tM
            (fmt_ppr_lf_sub lvl) s

    and fmt_ppr_lf_head lvl ppf = function
      | LF.BVar x  ->
          fprintf ppf "%s"
            (R.render_offset x)

      | LF.Const c ->
          fprintf ppf "%s"
            (R.render_cid_term c)

      | LF.MVar (c, s) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_cvar lvl) c
            (fmt_ppr_lf_sub  lvl) s

      | LF.FVar x ->
          fprintf ppf "%s"
            (R.render_name x)



    and fmt_ppr_lf_spine lvl ppf = function
      | LF.Nil ->
          fprintf ppf ""

      | LF.App (m, ms) ->
          fprintf ppf " %a%a"
            (fmt_ppr_lf_normal lvl) m
            (fmt_ppr_lf_spine  lvl) ms

      | LF.SClo (ms, s) ->
          let cond = lvl > 1 in
          fprintf ppf "%sSClo (%a, %a)%s"
            (l_paren_if cond)
            (fmt_ppr_lf_spine 0) ms
            (fmt_ppr_lf_sub lvl) s
            (r_paren_if cond)



    and fmt_ppr_lf_sub lvl ppf = function
      | LF.Shift n ->
          fprintf ppf "^%s"
            (R.render_offset n)

      | LF.SVar (c, s) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_cvar lvl) c
            (fmt_ppr_lf_sub  lvl) s

      | LF.Dot (f, s) ->
          fprintf ppf "%a@ .@ %a"
            (fmt_ppr_lf_front 1) f
            (fmt_ppr_lf_sub lvl) s


    and fmt_ppr_lf_front lvl ppf = function
      | LF.Head h ->
          fprintf ppf "%a"
            (fmt_ppr_lf_head lvl) h

      | LF.Obj m ->
          fprintf ppf "%a"
            (fmt_ppr_lf_normal lvl) m

      | LF.Undef ->
          fprintf ppf "_"

    and fmt_ppr_lf_cvar lvl ppf = function
      | LF.Offset n ->
          fprintf ppf "%s"
            (R.render_offset n)

      | LF.Inst ({ contents = None } as u, _, _, _) ->
          begin
            try
              fprintf ppf "%s"
                (InstHashtbl.find inst_hashtbl u)
            with
              | Not_found ->
                  (* Should probably create a sep. generator for this -dwm *)
                  let sym = String.uppercase (Gensym.VarData.gensym ()) in
                      InstHashtbl.replace inst_hashtbl u sym
                    ; fprintf ppf "%s" sym
          end

      | LF.Inst ({ contents = Some tM }, _, _, _) ->
          fprintf ppf "%a"
            (fmt_ppr_lf_normal lvl) tM



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    let ppr_sgn_decl      = fmt_ppr_sgn_decl  std_lvl std_formatter

    let ppr_lf_kind       = fmt_ppr_lf_kind   std_lvl std_formatter

    let ppr_lf_typ        = fmt_ppr_lf_typ    std_lvl std_formatter

    let ppr_lf_normal     = fmt_ppr_lf_normal std_lvl std_formatter

    let ppr_lf_head       = fmt_ppr_lf_head   std_lvl std_formatter

    let ppr_lf_spine      = fmt_ppr_lf_spine  std_lvl std_formatter

    let ppr_lf_sub        = fmt_ppr_lf_sub    std_lvl std_formatter

    let ppr_lf_front      = fmt_ppr_lf_front  std_lvl std_formatter

    let ppr_lf_cvar       = fmt_ppr_lf_cvar   std_lvl std_formatter

    let headToString h    = fmt_ppr_lf_head   std_lvl str_formatter h
                          ; flush_str_formatter ()

    let subToString  s    = fmt_ppr_lf_sub    std_lvl str_formatter s
                          ; flush_str_formatter ()

    let spineToString tS  = fmt_ppr_lf_spine  std_lvl str_formatter tS
                          ; flush_str_formatter ()

    let typToString tA    = fmt_ppr_lf_typ    std_lvl str_formatter tA
                          ; flush_str_formatter ()

    let kindToString tK   = fmt_ppr_lf_kind   std_lvl str_formatter tK
                          ; flush_str_formatter ()

    let normalToString tM = fmt_ppr_lf_normal std_lvl str_formatter tM
                          ; flush_str_formatter ()

    let rec dctxToString cPsi = match cPsi with
      | LF.Null -> " . "
      | LF.DDec (cPsi', LF.TypDecl (_x, tA)) -> 
          dctxToString cPsi' ^ " , _ : " ^ typToString tA


  end



  (********************************************)
  (* Default CID_RENDERER for External Syntax *)
  (********************************************)

  module DefaultCidRenderer = struct

    open Store.Cid

    let render_name     n = n.string_of_name

    let render_cid_typ  a = render_name (Typ .get a).Typ .name

    let render_cid_term c = render_name (Term.get c).Term.name

    let render_offset   i = string_of_int i

    let render_var      x = string_of_int x

  end



  (****************************************************************)
  (* Default Internal Syntax Pretty Printer Functor Instantiation *)
  (****************************************************************)

  module DefaultPrinter = Make (DefaultCidRenderer)

end


(* Disabled Error module to allow printing in check, whnf, unify, etc. 
   Wed Dec 17 21:12:38 2008 -bp 

module Error = struct

  open Syntax.Int

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



  (********************************)
  (* Error Pretty Printer Functor *)
  (********************************)

  module Make = functor (R : CID_RENDERER) -> struct

    module IP = Int.Make (R)

    module Check = struct

      open Check.LF

      (********************************)
      (* Format Based Pretty Printers *)
      (********************************)

      let fmt_ppr ppf = function
        | CtxVarMisMatch _ ->
            fprintf ppf
              "ctx variable mismatch"

        | TypIllTyped (_cD, _cPsi, _tA, _tB) ->
            fprintf ppf
              "Inferred _tA but expected _tB"

        | ExpAppNotFun ->
            fprintf ppf
              "Expression is applied, but not a function"

        | KindMisMatch ->
            fprintf ppf
              "Kind mismatch"

        | SubIllTyped ->
            fprintf ppf
              "Substitution not well-typed"

        | TypMisMatch (_cD, _cPsi, (tA1, s1), (tA2, s2)) ->
            fprintf ppf
              "Type mismatch ** WARNING: Types not in context **:@ @[%a[%a]@ =/=@ %a[%a]@]"
              (* The 2 is for precedence.  Treat printing
                 below as if it were similar to an application context as
                 far as precedence is concerned -dwm *)
              (IP.fmt_ppr_lf_typ 0)    tA1
              (IP.fmt_ppr_lf_sub std_lvl) s1
              (IP.fmt_ppr_lf_typ 0)    tA2
              (IP.fmt_ppr_lf_sub std_lvl) s2

        | SigmaIllTyped (_cD, _cPsi, (_tArec, _s1), (_tBrec, _s2)) -> 
            fprintf ppf
              "Sigma Type mismatch"

        | IllTyped (_cD, _cPsi, (_tM, _s1), (_tA, _s2)) -> 
            fprintf ppf
              "Illtyped normal object" 


      (***************************)
      (* Regular Pretty Printers *)
      (***************************)

      let ppr = fmt_ppr std_formatter

    end



    module Whnf = struct

      open Whnf

      (********************************)
      (* Format Based Pretty Printers *)
      (********************************)

      let fmt_ppr ppf = function
        | ConstraintsLeft ->
            fprintf ppf
              "Constraint of functional type are not simplified"

        | NotPatSub       ->
            fprintf ppf
              "Not a pattern substitution"



      (***************************)
      (* Regular Pretty Printers *)
      (***************************)

      let ppr = fmt_ppr std_formatter

    end

  end


  (***********************************)
  (* Default CID_RENDERER for Errors *)
  (***********************************)

  module DefaultCidRenderer = Int.DefaultCidRenderer



  (******************************************************)
  (* Default Error Pretty Printer Functor Instantiation *)
  (******************************************************)

  module DefaultPrinter = Make (DefaultCidRenderer)

end
*)
