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

  val render_name       : name       -> string
  val render_cid_typ    : cid_typ    -> string
  val render_cid_term   : cid_term   -> string
  val render_cid_schema : cid_schema -> string
  val render_cid_prog   : cid_prog   -> string
  val render_offset     : offset     -> string
  val render_var        : var        -> string

end


module Ext = struct

  open Id
  open Syntax.Ext

  (* External Syntax Printer Signature *)
  module type PRINTER = sig

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
    val ppr_lf_sigma_decl : LF.sigma_decl    -> unit
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
  module Make = functor (R : CID_RENDERER) -> struct

    (* Contextual Format Based Pretty Printers *)
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


    and fmt_ppr_lf_mctx lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cD, ctyp_decl) ->
          fprintf ppf "%a, %a"
            (fmt_ppr_lf_mctx 0) cD
            (fmt_ppr_lf_ctyp_decl lvl) ctyp_decl

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
          fprintf ppf "mvar %s[%a]"
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
      | LF.EmptySub _ ->
          fprintf ppf "."

      | LF.Dot (_, sigma, LF.Normal tM) ->
          fprintf ppf "%a; %a"
          (fmt_ppr_lf_sub 0) sigma
          (fmt_ppr_lf_normal 0) tM

      | LF.Dot (_, sigma, LF.Head h) ->
          fprintf ppf "%a, %a"
          (fmt_ppr_lf_sub 0) sigma
          (fmt_ppr_lf_head 0) h

      | LF.Id _ ->
          fprintf ppf "id"



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
      | LF.SigmaDecl (_x, typrec) ->
          let ppr_element ppf suffix = function
          | (x, tA) ->
                 fprintf ppf "%s:%a%s"
                   (R.render_name x)
                   (fmt_ppr_lf_typ 0) tA
                  suffix
          in let rec ppr_elements ppf = function
            | LF.SigmaLast tA -> fprintf ppf "%a" (fmt_ppr_lf_typ 0) tA
            | LF.SigmaElem (x, tA1, LF.SigmaLast tA2) -> begin ppr_element ppf ". " (x, tA1); fprintf ppf "%a" (fmt_ppr_lf_typ 0) tA2 end
            | LF.SigmaElem (x, tA, tAs)  -> begin ppr_element ppf ", " (x, tA); ppr_elements ppf  tAs end
(*             | tA :: tAs -> *)
(*                   fprintf ppf "%a,@ %a" *)
(*                     (fmt_ppr_lf_typ 0) tA *)
(*                     ppr_typ_rec        tAs *)
(*                fprintf ppf "Sigma %a. %a" *)
          in
            fprintf ppf "%a"
              (ppr_elements) typrec

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
      | Comp.BranchBox (_, ctyp_decls, (psi, tM, tau), e) ->
          begin match tau with
            | None -> 
                fprintf ppf "%a box (%a . %a) => %a"
                  (*                    ppr_ctyp_decls ctyp_decls *)
                  (fmt_ppr_lf_mctx 0) ctyp_decls
                  (fmt_ppr_lf_dctx 0) psi
                  (fmt_ppr_lf_normal 0) tM
                  (fmt_ppr_cmp_exp_chk 0) e

            | Some (tA, cPsi) -> 
                fprintf ppf "%a box (%a . %a) : %a[%a] => %a"
                  (*                  ppr_ctyp_decls ctyp_decls *)
                  (fmt_ppr_lf_mctx 0) ctyp_decls
                  (fmt_ppr_lf_dctx 0) psi
                  (fmt_ppr_lf_normal 0) tM
                  (fmt_ppr_lf_typ 0) tA
                  (fmt_ppr_lf_dctx 0) cPsi
                  (fmt_ppr_cmp_exp_chk 0) e
          end 

    (* Regular Pretty Printers *)
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
    let ppr_lf_mctx       = fmt_ppr_lf_mctx       std_lvl std_formatter
    let ppr_cmp_typ       = fmt_ppr_cmp_typ       std_lvl std_formatter
    let ppr_cmp_exp_chk   = fmt_ppr_cmp_exp_chk   std_lvl std_formatter
    let ppr_cmp_exp_syn   = fmt_ppr_cmp_exp_syn   std_lvl std_formatter
    let ppr_cmp_branches  = fmt_ppr_cmp_branches  std_lvl std_formatter
    let ppr_cmp_branch    = fmt_ppr_cmp_branch    std_lvl std_formatter

  end

  (* Default CID_RENDERER for External Syntax *)
  module DefaultCidRenderer = struct

    let render_name n     = n.string_of_name
    let render_cid_typ    = string_of_int
    let render_cid_term   = string_of_int
    let render_cid_schema = string_of_int
    let render_cid_prog   = string_of_int
    let render_offset     = string_of_int
    let render_var        = string_of_int

  end

  (* Default External Syntax Pretty Printer Functor Instantiation *)
  module DefaultPrinter = Make (DefaultCidRenderer)

end


module Int = struct

  open Id
  open Syntax.Int

  (* Internal Syntax Printer Signature *)
  module type PRINTER = sig

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
    val headToString      : LF.head       -> string
    val subToString       : LF.sub        -> string
    val spineToString     : LF.spine      -> string
    val typToString       : LF.typ        -> string
    val kindToString      : LF.kind       -> string
    val normalToString    : LF.normal     -> string
    val dctxToString      : LF.dctx       -> string
    val mctxToString      : LF.mctx       -> string
    val phatToString      : LF.psi_hat    -> string
    val schemaToString    : LF.schema     -> string 
    val gctxToString      : Comp.gctx     -> string
    val expChkToString    : Comp.exp_chk  -> string
    val expSynToString    : Comp.exp_syn  -> string
    val branchToString    : Comp.branch   -> string
    val compTypToString   : Comp.typ      -> string
    val msubToString      : Comp.msub     -> string

  end

  (* Internal Syntax Pretty Printer Functor *)
  module Make = functor (R : CID_RENDERER) -> struct

    module InstHashedType = struct
      type t    = LF.normal option ref
      let equal = (==)
      let hash  = Hashtbl.hash
    end

    module InstHashtbl = Hashtbl.Make (InstHashedType)

    let inst_hashtbl : string InstHashtbl.t = InstHashtbl.create 0


    module PInstHashedType = struct
      type t    = LF.head option ref
      let equal = (==)
      let hash  = Hashtbl.hash
    end

    module PInstHashtbl = Hashtbl.Make (PInstHashedType)

    let pinst_hashtbl : string PInstHashtbl.t = PInstHashtbl.create 0

    (* Contextual Format Based Pretty Printers *)
    let rec fmt_ppr_sgn_decl lvl ppf = function
      | Sgn.Const (c, a) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_cid_term c)
            (fmt_ppr_lf_typ lvl)  a

      | Sgn.Typ (a, k) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_cid_typ  a)
            (fmt_ppr_lf_kind lvl) k

      | Sgn.Schema (w, schema) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_cid_schema  w)
            (fmt_ppr_lf_schema lvl) schema

      | Sgn.Rec (f, tau, e) ->
          fprintf ppf "rec %s : %a = %a.@.@?"
            (R.render_cid_prog  f)
            (fmt_ppr_cmp_typ lvl) tau
            (fmt_ppr_cmp_exp_chk lvl) e


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


    and fmt_ppr_lf_ctyp_decl _lvl ppf = function
      | LF.MDecl (u, tA, cPsi) ->
          fprintf ppf "{%s :: %a[%a]}"
            (R.render_name u)
            (fmt_ppr_lf_typ 0) tA
            (fmt_ppr_lf_dctx 0) cPsi

      | LF.PDecl (p, tA, cPsi) ->
          fprintf ppf "{#%s :: %a[%a]}"
            (R.render_name p)
            (fmt_ppr_lf_typ 0) tA
            (fmt_ppr_lf_dctx 0) cPsi

      | LF.CDecl (name, schemaName) ->
          fprintf ppf "{#%s :: %a}"
            (R.render_name name)
            (fmt_ppr_lf_schema 0) (Store.Cid.Schema.get_schema schemaName)

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
          fprintf ppf "(mvar %a[%a])"
            (fmt_ppr_lf_cvar lvl) c
            (fmt_ppr_lf_sub  lvl) s

      | LF.PVar (c, s) ->
          fprintf ppf "#%a[%a]"
            (fmt_ppr_lf_cvar lvl) c
            (fmt_ppr_lf_sub  lvl) s

      | LF.FVar x ->
          fprintf ppf "%s"
            (R.render_name x)

      | LF.FMVar (u, s) ->
          fprintf ppf "%s[%a]"
            (R.render_name u)
            (fmt_ppr_lf_sub  lvl) s

      | LF.FPVar (p, s) ->
          fprintf ppf "#%s[%a]"
            (R.render_name p)
            (fmt_ppr_lf_sub  lvl) s


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
      | LF.Shift (None,n) -> 
          fprintf ppf "^%s"
            (R.render_offset n)

      | LF.Shift (Some (LF.CtxOffset psi), n) -> 
          fprintf ppf "^(ctx_var %s + %s)"
            (R.render_offset psi)
            (R.render_offset n)

      | LF.SVar (c, s) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_cvar lvl) c
            (fmt_ppr_lf_sub  lvl) s

      | LF.Dot (f, s) ->
          fprintf ppf "%a . %a"
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


      | LF.PInst ({ contents = None } as p, _, _, _) ->
          begin
            try
              fprintf ppf "#%s"
                (PInstHashtbl.find pinst_hashtbl p)
            with
              | Not_found ->
                  (* Should probably create a sep. generator for this -dwm *)
                  let sym = String.lowercase (Gensym.VarData.gensym ()) in
                      PInstHashtbl.replace pinst_hashtbl p sym
                    ; fprintf ppf "#%s" sym
          end

      | LF.PInst ({ contents = Some h }, _, _, _) ->
          fprintf ppf "%a"
            (fmt_ppr_lf_head lvl) h



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
      | LF.SchElem (typDecls, sgmDecl) ->
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
      | LF.SigmaDecl (_x, typrec) ->
          let ppr_element ppf suffix = function
          | (x, tA) ->
                 fprintf ppf "%s:%a%s"
                   (R.render_name x)
                   (fmt_ppr_lf_typ 0) tA
                  suffix
          in let rec ppr_elements ppf = function
            | LF.SigmaLast tA -> fprintf ppf "%a" (fmt_ppr_lf_typ 0) tA
            | LF.SigmaElem (x, tA1, LF.SigmaLast tA2) -> begin ppr_element ppf ". " (x, tA1); fprintf ppf "%a" (fmt_ppr_lf_typ 0) tA2 end
            | LF.SigmaElem (x, tA, tAs)  -> begin ppr_element ppf ", " (x, tA); ppr_elements ppf  tAs end
(*             | tA :: tAs -> *)
(*                   fprintf ppf "%a,@ %a" *)
(*                     (fmt_ppr_lf_typ 0) tA *)
(*                     ppr_typ_rec        tAs *)
(*                fprintf ppf "Sigma %a. %a" *)
          in
            fprintf ppf "%a"
              (ppr_elements) typrec

    and fmt_ppr_lf_psi_hat _lvl ppf = function
      | (None, offset)  -> fprintf ppf "%s" (R.render_offset offset)

      | (Some (LF.CtxName psi), offset) ->
          fprintf ppf "(%s , %s)"
            (R.render_name psi)          
            (R.render_offset offset)

      | (Some (LF.CtxOffset psi), offset) ->
          fprintf ppf "(%s , %s)"
            (R.render_offset psi)          
            (R.render_offset offset)


    and fmt_ppr_lf_dctx _lvl ppf = function
      | LF.Null ->
          fprintf ppf "."

      | LF.CtxVar (LF.CtxOffset psi) ->
          fprintf ppf "%s"
            (R.render_offset psi)

      | LF.CtxVar (LF.CtxName psi) ->
          fprintf ppf "%s"
            (R.render_name psi)

      | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
          fprintf ppf "%a, %s : %a"
            (fmt_ppr_lf_dctx 0) cPsi
            (R.render_name x)
            (fmt_ppr_lf_typ 0) tA


    and fmt_ppr_lf_mctx lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cD, ctyp_decl) ->
          fprintf ppf "%a, %a"
            (fmt_ppr_lf_mctx 0) cD
            (fmt_ppr_lf_ctyp_decl lvl) ctyp_decl


    and fmt_ppr_cmp_gctx lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cG, (x, tau)) ->
          fprintf ppf "%a, %s: %a"
            (fmt_ppr_cmp_gctx 0) cG
            (R.render_name x)
            (fmt_ppr_cmp_typ lvl) tau


    and fmt_ppr_cmp_typ lvl ppf = function
      | Comp.TypBox (tA, cPsi) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_typ 1) tA
            (fmt_ppr_lf_dctx 0) cPsi

      | Comp.TypArr (tau1, tau2) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%a -> %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_typ 1) tau1
              (fmt_ppr_cmp_typ 0) tau2
              (r_paren_if cond)

      | Comp.TypCtxPi ((psi, w), tau) ->
          let cond = lvl > 0 in
            fprintf ppf "%s{%s:(%s)*} %a%s"
              (l_paren_if cond)
              (R.render_name psi)
              (R.render_cid_schema w)
              (fmt_ppr_cmp_typ 0) tau
              (r_paren_if cond)

      | Comp.TypPiBox (ctyp_decl, tau) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%a %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_ctyp_decl 1) ctyp_decl
              (fmt_ppr_cmp_typ 0) tau
              (r_paren_if cond)

      | Comp.TypClo (tau, msub) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_cmp_typ lvl) tau
            (fmt_ppr_cmp_msub lvl) msub

    and fmt_ppr_cmp_exp_chk lvl ppf = function
      | Comp.Syn i ->
          fmt_ppr_cmp_exp_syn lvl ppf i

      | Comp.Fun (x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%sfn %s =>@ %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk 0) e
              (r_paren_if cond)

      | Comp.CtxFun (x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%sFN %s =>@ %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk 0) e
              (r_paren_if cond)

      | Comp.MLam (x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%smlam %s => %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk 0) e
              (r_paren_if cond)

      | Comp.Box (pHat, tM) ->
          let cond = lvl > 1 in
            fprintf ppf "%sbox (%a. %a)%s"
              (l_paren_if cond)
              (fmt_ppr_lf_psi_hat 0) pHat
              (fmt_ppr_lf_normal 0) tM
              (r_paren_if cond)

      | Comp.Case (i, bs) ->
          let cond = lvl > 1 in
            fprintf ppf "@[<2>%scase %a of@[<-1>%a@]%s@]"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn 0) i
              (fmt_ppr_cmp_branches 0) bs
              (r_paren_if cond)



    and fmt_ppr_cmp_exp_syn lvl ppf = function
      | Comp.Var x ->
          fprintf ppf "%s"
            (R.render_offset x)

      | Comp.Const prog ->
          fprintf ppf "%s"
            (R.render_cid_prog prog)

      | Comp.Apply (i, e) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn 1) i
              (fmt_ppr_cmp_exp_chk 2) e
              (r_paren_if cond)

      | Comp.CtxApp (i, cPsi) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a [%a]%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn 1) i
              (fmt_ppr_lf_dctx 0) cPsi
              (r_paren_if cond)

      | Comp.MApp (i, (pHat, tM)) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a <%a. %a>%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn 1) i
              (fmt_ppr_lf_psi_hat 0) pHat
              (fmt_ppr_lf_normal 0) tM
              (r_paren_if cond)

      | Comp.Ann (e, tau) ->
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
      | Comp.BranchBox (ctyp_decls, (pHat, tM, (tA, cPsi)), e) ->
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



    and fmt_ppr_cmp_msub lvl ppf = function
      | Comp.MShift k ->
          fprintf ppf "^%s" (string_of_int k)

      | Comp.MDot (f, s) ->
          fprintf ppf "%a@ ,@ %a"
            (fmt_ppr_cmp_mfront 1) f
            (fmt_ppr_cmp_msub lvl) s


    and fmt_ppr_cmp_mfront lvl ppf = function
      | Comp.MObj (psihat, m) ->
          fprintf ppf "M (%a . %a)"
            (fmt_ppr_lf_psi_hat lvl) psihat
            (fmt_ppr_lf_normal lvl) m

      | Comp.PObj (psihat, h) ->
          fprintf ppf "P (%a . %a)"
            (fmt_ppr_lf_psi_hat lvl) psihat
            (fmt_ppr_lf_head lvl) h

      | Comp.MV k ->
          fprintf ppf "MV %s "
            (string_of_int k)


    (* Regular Pretty Printers *)
    let ppr_sgn_decl      = fmt_ppr_sgn_decl      std_lvl std_formatter
    let ppr_lf_ctyp_decl  = fmt_ppr_lf_ctyp_decl  std_lvl std_formatter
    let ppr_lf_kind       = fmt_ppr_lf_kind       std_lvl std_formatter
    let ppr_lf_typ        = fmt_ppr_lf_typ        std_lvl std_formatter
    let ppr_lf_normal     = fmt_ppr_lf_normal     std_lvl std_formatter
    let ppr_lf_head       = fmt_ppr_lf_head       std_lvl std_formatter
    let ppr_lf_spine      = fmt_ppr_lf_spine      std_lvl std_formatter
    let ppr_lf_sub        = fmt_ppr_lf_sub        std_lvl std_formatter
    let ppr_lf_front      = fmt_ppr_lf_front      std_lvl std_formatter
    let ppr_lf_cvar       = fmt_ppr_lf_cvar       std_lvl std_formatter
    let ppr_lf_schema     = fmt_ppr_lf_schema     std_lvl std_formatter
    let ppr_lf_sch_elem   = fmt_ppr_lf_sch_elem   std_lvl std_formatter
    let ppr_lf_sigma_decl = fmt_ppr_lf_sigma_decl std_lvl std_formatter
    let ppr_lf_psi_hat    = fmt_ppr_lf_psi_hat    std_lvl std_formatter
    let ppr_lf_dctx       = fmt_ppr_lf_dctx       std_lvl std_formatter
    let ppr_lf_mctx       = fmt_ppr_lf_mctx       std_lvl std_formatter
    let ppr_cmp_gctx      = fmt_ppr_cmp_gctx      std_lvl std_formatter
    let ppr_cmp_typ       = fmt_ppr_cmp_typ       std_lvl std_formatter
    let ppr_cmp_exp_chk   = fmt_ppr_cmp_exp_chk   std_lvl std_formatter
    let ppr_cmp_exp_syn   = fmt_ppr_cmp_exp_syn   std_lvl std_formatter
    let ppr_cmp_branches  = fmt_ppr_cmp_branches  std_lvl std_formatter
    let ppr_cmp_branch    = fmt_ppr_cmp_branch    std_lvl std_formatter
    let ppr_cmp_msub      = fmt_ppr_cmp_msub      std_lvl std_formatter
    let ppr_cmp_mfront    = fmt_ppr_cmp_mfront    std_lvl std_formatter

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
      | LF.CtxVar (LF.CtxOffset k) -> "CtxV " ^ string_of_int k
      | LF.CtxVar (LF.CtxName psi)   -> "CtxV " ^ (R.render_name psi)
      | LF.DDec (cPsi', LF.TypDecl (_x, tA)) ->
          dctxToString cPsi' ^ " , _ : " ^ typToString tA


    let mctxToString cD = fmt_ppr_lf_mctx std_lvl str_formatter cD
                              ; flush_str_formatter ()


    let phatToString phat = fmt_ppr_lf_psi_hat std_lvl str_formatter phat
                              ; flush_str_formatter ()


    let schemaToString schema = fmt_ppr_lf_schema std_lvl str_formatter schema
                              ; flush_str_formatter ()

    let gctxToString cG = fmt_ppr_cmp_gctx std_lvl str_formatter cG
                              ; flush_str_formatter ()

    let expChkToString  e    = fmt_ppr_cmp_exp_chk std_lvl str_formatter e
                              ; flush_str_formatter ()

    let expSynToString  i    = fmt_ppr_cmp_exp_syn std_lvl str_formatter i
                              ; flush_str_formatter ()

    let branchToString  b    = fmt_ppr_cmp_branch std_lvl str_formatter b
                              ; flush_str_formatter ()


    let compTypToString tau  = fmt_ppr_cmp_typ std_lvl str_formatter tau
                              ; flush_str_formatter ()

    let msubToString    s    = fmt_ppr_cmp_msub    std_lvl str_formatter s
                              ; flush_str_formatter ()

  end

  (* Default CID_RENDERER for Internal Syntax *)
  module DefaultCidRenderer = struct

    open Store.Cid

    let render_name     n   = n.string_of_name
    let render_cid_typ  a   = render_name (Typ .get a).Typ .name
    let render_cid_term c   = render_name (Term.get c).Term.name
    let render_cid_schema w = render_name (Schema.get w).Schema.name
    let render_cid_prog f   = render_name (Comp.get f).Comp.name
    let render_cvar     u   = match u with
      | LF.Offset offset -> string_of_int offset
          (* other cases to be added *)
    let render_offset   i   = string_of_int i
    let render_var      x   = string_of_int x

  end


  (* Default Internal Syntax Pretty Printer Functor Instantiation *)
  module DefaultPrinter = Make (DefaultCidRenderer)

end


module Error = struct

  open Syntax.Int
  open Error

  (* Error Printer Signature *)
  module type PRINTER = sig

      val fmt_ppr : formatter -> error -> unit
      val ppr : error -> unit

  end

  (* Error Pretty Printer Functor *)
  module Make = functor (R : CID_RENDERER) -> struct

    module IP = Int.Make (R)

    (* Format Based Pretty Printers *)
    let fmt_ppr ppf = function
      | CtxVarMismatch _ ->
          fprintf ppf "ctx variable mismatch"

      | TypIllTyped (_cD, _cPsi, _tA, _tB) ->
          fprintf ppf "Inferred _tA but expected _tB"

      | ExpAppNotFun ->
          fprintf ppf "expression is not a function"

      | ExpNilNotAtom ->
          fprintf ppf "TODO"

      | KindMismatch ->
          fprintf ppf "Kind mismatch"

      | SubIllTyped ->
          fprintf ppf "Substitution not well-typed"

      | TypMismatch ((* _cD ,*) _cPsi, (tA1, s1), (tA2, s2)) ->
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
          fprintf ppf "Sigma Type mismatch"

      | IllTyped (_cPsi, (tM, _s1), (tA, _s2)) ->
          (* FIXME call normalisation or normalizing string conversion *)
          fprintf ppf
            "ill typed expression\n  expected type: %a\n  for expression:\n    %a" 
            (IP.fmt_ppr_lf_typ std_lvl) tA
            (IP.fmt_ppr_lf_normal std_lvl) tM
            (* (IP.fmt_ppr_lf_typ (Whnf.norm (tA, s2))) *)
            (* (IP.fmt_ppr_lf_normal (Whnf.normTyp (tM, s1))) *)

      | LeftoverConstraints ->
          fprintf ppf "constraints left after reconstruction"

      | LeftoverUndef ->
          fprintf ppf "Undef left after unification"

      | IllTypedIdSub ->
          fprintf ppf "TODO"

      | ValueRestriction ->
          fprintf ppf "value restriction (case construct)"

      | CompIllTyped ->
          fprintf ppf "TODO"

      | UnboundName n   ->
          fprintf ppf "unbound variable or constructor: %s" (R.render_name n)

      | ConstraintsLeft ->
          fprintf ppf "Constraint of functional type are not simplified"

      | NotPatSub       ->
          fprintf ppf "Not a pattern substitution"


    (* Regular Pretty Printers *)
    let ppr = fmt_ppr std_formatter

  end


  (* Default CID_RENDERER for Errors *)
  module DefaultCidRenderer = Int.DefaultCidRenderer

  (* Default Error Pretty Printer Functor Instantiation *)
  module DefaultPrinter = Make (DefaultCidRenderer)

end
