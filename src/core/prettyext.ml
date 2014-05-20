(** Pretty printing for external syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html
*)

open Format


type lvl = int

let std_lvl = 0


let l_paren_if cond =
  if cond
  then "("
  else ""

let r_paren_if cond =
  if cond
  then ")"
  else ""


module Control = struct
  type substitution_style = Natural | DeBruijn

  let substitutionStyle = ref Natural
  let printImplicit = ref true

  let db() = !substitutionStyle = DeBruijn
end (* Control *)


module Ext = struct

  open Syntax.Ext

  (* External Syntax Printer Signature *)
  module type PRINTER = sig

    (* Contextual Format Based Pretty Printers *)
    val fmt_ppr_sgn_decl      : ?asHtml:bool -> lvl -> formatter -> Sgn.decl  -> unit
    val fmt_ppr_lf_kind       : LF.dctx -> lvl -> formatter -> LF.kind      -> unit
    val fmt_ppr_lf_ctyp_decl  : LF.mctx -> lvl -> formatter -> LF.ctyp_decl -> unit
    val fmt_ppr_lf_typ_rec    : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ_rec    -> unit

    val fmt_ppr_lf_typ        : ?asHtml:bool -> LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ    -> unit
    val fmt_ppr_lf_normal     : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.normal -> unit
    val fmt_ppr_lf_head       : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.head   -> unit
    val fmt_ppr_lf_spine      : ?asHtml:bool -> LF.mctx -> LF.dctx -> lvl -> formatter -> LF.spine  -> unit
    val fmt_ppr_lf_sub        : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.sub    -> unit

    val fmt_ppr_lf_schema     : lvl -> formatter -> LF.schema     -> unit
    val fmt_ppr_lf_sch_elem   : lvl -> formatter -> LF.sch_elem   -> unit

    val fmt_ppr_lf_psi_hat    : LF.mctx -> lvl -> formatter -> LF.dctx  -> unit
    val fmt_ppr_lf_dctx       : LF.mctx -> lvl -> formatter -> LF.dctx  -> unit

    val fmt_ppr_lf_mctx       : lvl -> formatter -> LF.mctx     -> unit
    val fmt_ppr_cmp_kind      : LF.mctx -> lvl -> formatter -> Comp.kind -> unit
    val fmt_ppr_cmp_typ       : LF.mctx -> lvl -> formatter -> Comp.typ -> unit
    val fmt_ppr_cmp_exp_chk   : LF.ctyp_decl LF.ctx -> int -> Format.formatter -> Comp.exp_chk -> unit
    val fmt_ppr_cmp_exp_syn   : LF.ctyp_decl LF.ctx -> int -> Format.formatter -> Comp.exp_syn -> unit
    val fmt_ppr_cmp_branches  : LF.ctyp_decl LF.ctx -> int -> Format.formatter -> Comp.branch list -> unit
    val fmt_ppr_cmp_branch    : LF.ctyp_decl LF.ctx -> int -> Format.formatter -> Comp.branch -> unit
    val fmt_ppr_pat_obj       : LF.ctyp_decl LF.ctx -> int -> Format.formatter -> Comp.pattern -> unit

    val fmt_ppr_patternOpt    : LF.mctx -> LF.dctx -> formatter -> LF.normal option -> unit

    (* Regular Pretty Printers *)
    val ppr_sgn_decl      : Sgn.decl         -> unit
    val ppr_lf_kind       : LF.dctx -> LF.kind -> unit
    val ppr_lf_ctyp_decl  : LF.mctx -> LF.ctyp_decl  -> unit
    val ppr_lf_typ_rec    : LF.mctx -> LF.dctx -> LF.typ_rec -> unit
    val ppr_lf_typ        : LF.mctx -> LF.dctx -> LF.typ     -> unit
    val ppr_lf_normal     : LF.mctx -> LF.dctx -> LF.normal  -> unit
    val ppr_lf_head       : LF.mctx -> LF.dctx -> LF.head    -> unit
    val ppr_lf_spine      : LF.mctx -> LF.dctx -> LF.spine   -> unit
    val ppr_lf_sub        : LF.mctx -> LF.dctx -> LF.sub     -> unit

    val ppr_lf_schema     : LF.schema        -> unit
    val ppr_lf_sch_elem   : LF.sch_elem      -> unit

    (* val ppr_lf_psi_hat    : LF.mctx -> LF.dctx -> unit *)
    val ppr_lf_dctx       : LF.mctx -> LF.dctx  -> unit
    val ppr_lf_mctx       : LF.mctx -> unit
    val ppr_cmp_kind      : LF.mctx -> Comp.kind -> unit
    val ppr_cmp_typ       : LF.mctx -> Comp.typ -> unit
    val ppr_cmp_exp_chk   : LF.ctyp_decl LF.ctx -> Comp.exp_chk -> unit
    val ppr_cmp_exp_syn   : LF.ctyp_decl LF.ctx -> Comp.exp_syn -> unit
    val ppr_cmp_branches  : LF.ctyp_decl LF.ctx -> Comp.branch list -> unit
    val ppr_cmp_branch    : LF.ctyp_decl LF.ctx -> Comp.branch -> unit

    (* Conversion to string *)
    val subToString       : LF.mctx -> LF.dctx -> LF.sub      -> string
    val spineToString     : LF.ctyp_decl LF.ctx -> LF.dctx -> LF.spine -> string
    val typToString       : LF.ctyp_decl LF.ctx -> LF.dctx -> LF.typ -> string
    val typRecToString    : LF.ctyp_decl LF.ctx -> LF.dctx -> LF.typ_rec -> string
    val kindToString      : LF.dctx -> LF.kind -> string
    val normalToString    : LF.ctyp_decl LF.ctx -> LF.dctx -> LF.normal -> string
    val headToString      : LF.mctx -> LF.dctx -> LF.head     -> string
    val tupleToString     : LF.mctx -> LF.dctx -> LF.tuple    -> string
    val dctxToString      : LF.mctx -> LF.dctx -> string
    val mctxToString      : LF.mctx -> string

    val metaObjToString   : LF.mctx -> Comp.meta_obj -> string

    val schemaToString    : LF.schema     -> string
    val schElemToString   : LF.sch_elem   -> string

    val gctxToString      : LF.ctyp_decl LF.ctx -> LF.typ_decl LF.ctx -> string
    val patternToString   : LF.ctyp_decl LF.ctx -> Comp.pattern -> string
    val expChkToString    : LF.ctyp_decl LF.ctx -> Comp.exp_chk -> string
    val expSynToString    : LF.ctyp_decl LF.ctx -> Comp.exp_syn -> string
    val branchToString    : LF.ctyp_decl LF.ctx -> Syntax.Int.Comp.gctx -> Comp.branch -> string
    val compKindToString  : LF.mctx -> Comp.kind  -> string
    val compTypToString   : LF.mctx -> Comp.typ   -> string



  end (* Ext.PRINTER *)

  (* External Syntax Pretty Printer Functor *)
  module Make : functor (R : Store.Cid.RENDERER) -> PRINTER = functor (R : Store.Cid.RENDERER) -> struct

    module InstHashedType = struct
      type t    = LF.normal option ref
      let equal = (==)
      let hash  = Hashtbl.hash
    end

    module InstHashtbl = Hashtbl.Make (InstHashedType)

    module PInstHashedType = struct
      type t    = LF.head option ref
      let equal = (==)
      let hash  = Hashtbl.hash
    end

    module PInstHashtbl = Hashtbl.Make (PInstHashedType)

    let rec phatToDCtx phat = match phat with
      | [] -> LF.Null
      | h::[] -> LF.CtxVar (Loc.mk("null"),h)
      | h::t ->  LF.DDec (phatToDCtx t, LF.TypDecl ( h, LF.Atom(Loc.mk("null"),(Id.mk_name Id.NoName),LF.Nil)  ))


    (* Contextual Format Based Pretty Printers
     *
     * We assume types, terms, etc are all in normal form.
     *)

    let rec has_ctx_var psi = match psi with LF.CtxVar _ -> true | LF.Null -> false |  LF.DDec(cPsi, _x) -> has_ctx_var cPsi


    let rec fmt_ppr_lf_typ ?(asHtml = false) cD cPsi lvl ppf = function
      | LF.Atom (_, a, LF.Nil) ->
          let name = (R.render_name a) in
          let s = if asHtml then "<a href=#" ^ name ^ ">" ^ name ^ "</a>" else name in
          fprintf ppf "%s" s

      | LF.Atom (_, a, ms) ->
          let name = (R.render_name a) in
          let s = if asHtml then "<a href=#" ^ name ^ ">" ^ name ^ "</a>" else name in
          let cond = lvl > 1 in
            fprintf ppf "%s%s%a%s"
              (l_paren_if cond)
              s
              (fmt_ppr_lf_spine ~asHtml:asHtml cD cPsi 2) ms
              (r_paren_if cond)

      | LF.PiTyp (_,LF.TypDecl (x, a), b) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s implicit : %a} @ %a%s@]"
              (l_paren_if cond)
              (R.render_name  x)
              (fmt_ppr_lf_typ cD cPsi 0) a
              (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, a))) 0) b
              (r_paren_if cond)

      | LF.Sigma (_,typRec) ->
          fprintf ppf "block (%a)"
            (fmt_ppr_lf_typ_rec cD cPsi lvl) typRec

      | LF.ArrTyp (_, t1, t2) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a -> %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_typ ~asHtml:asHtml cD cPsi 0) t1
              (fmt_ppr_lf_typ ~asHtml:asHtml cD cPsi 0) t2
              (r_paren_if cond)

      | LF.Ctx   (_, cPsi)  ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a %s"
              (l_paren_if cond)
              (fmt_ppr_lf_dctx cD 0) cPsi
              (r_paren_if cond)


    and fmt_ppr_tuple cD cPsi lvl ppf = function
      | LF.Last tM ->
           fmt_ppr_lf_normal cD cPsi lvl ppf tM

      | LF.Cons(tM, rest) ->
           fprintf ppf "%a, %a"
             (fmt_ppr_lf_normal cD cPsi lvl) tM
             (fmt_ppr_tuple cD cPsi lvl) rest

    and fmt_ppr_lf_normal cD cPsi lvl ppf =
      let deimplicitize_spine h ms = match h with
        | LF.MVar _
        | LF.PVar _
        | LF.Name _
        | LF.Hole _
        | LF.ProjName _
        | LF.ProjPVar _ -> ms

      in function
        | LF.Lam (_, x, m) ->
            let cond = lvl > 0 in
              fprintf ppf "%s\\%s. %a%s"
                (l_paren_if cond)
                (R.render_name x)
                (fmt_ppr_lf_normal cD cPsi 0   ) m
                (r_paren_if cond)

        | LF.Tuple (_, tuple) ->
           fprintf ppf "<%a>"
             (fmt_ppr_tuple cD cPsi lvl) tuple

        | LF.Root (_, h, LF.Nil) ->
            fprintf ppf "%a"
              (fmt_ppr_lf_head cD cPsi lvl) h

        | LF.Root (_, h, ms)  ->
            let cond = lvl > 1 in
            let ms = deimplicitize_spine h ms in
              fprintf ppf "%s%a%a%s"
                (l_paren_if cond)
                (fmt_ppr_lf_head cD cPsi lvl) h
                (fmt_ppr_lf_spine cD cPsi 2)  ms
                (r_paren_if cond)

    and fmt_ppr_lf_head cD cPsi lvl ppf head =
      let paren s = not (Control.db()) && lvl > 0 && true
      in begin match head with
      | LF.MVar (_, x, s) ->
          fprintf ppf "%s%s%a%s"
            (l_paren_if (paren s))
            (R.render_name x)
            (fmt_ppr_lf_sub  cD cPsi lvl) s
            (r_paren_if (paren s))

      (* | LF.SVar (_, x, s) -> *)
      (*     fprintf ppf "%s%s%a%s" *)
      (*       (l_paren_if (paren s)) *)
      (*       (R.render_name x) *)
      (*       (fmt_ppr_lf_sub  cD cPsi lvl) s *)
      (*       (r_paren_if (paren s)) *)

      | LF.PVar (_,  x, s) ->
          fprintf ppf "%s#%s%a%s"
            (l_paren_if (paren s))
            (R.render_name x)
            (fmt_ppr_lf_sub  cD cPsi lvl) s
            (r_paren_if (paren s))

      | LF.Name(_, x) ->
          fprintf ppf "%s"
            (R.render_name x)

      | LF.Hole (_) ->
          fprintf ppf "_"

      | LF.ProjPVar (_, k, (x, sigma)) ->
          fprintf ppf "#%s%s%a"
          (R.render_name x)
          ("." ^ string_of_int k)
          (fmt_ppr_lf_sub cD cPsi 0) sigma

      | LF.ProjName (_, k, x) ->
          fprintf ppf "%s%s"
          (R.render_name x)
          ("." ^ string_of_int k)
      end

    and fmt_ppr_lf_spine ?(asHtml = false) cD cPsi lvl ppf = function
      | LF.Nil ->
          fprintf ppf ""

      | LF.App (_, m, ms) ->
          fprintf ppf " %a%a"
            (fmt_ppr_lf_normal  cD cPsi (lvl + 1)) m
            (fmt_ppr_lf_spine   cD cPsi lvl) ms

    and fmt_ppr_lf_sub cD cPsi lvl ppf s =
      match !Control.substitutionStyle with
        | Control.Natural -> fmt_ppr_lf_sub_natural cD cPsi lvl ppf s
        | Control.DeBruijn -> fmt_ppr_lf_sub_deBruijn cD cPsi lvl ppf s

    and fmt_ppr_lf_sub_natural cD cPsi lvl ppf s=
      let print_front = fmt_ppr_lf_front cD cPsi 1 in
      let hasCtxVar = has_ctx_var cPsi in
      let rec self lvl ppf =
        function
       (* Print ".." for a Shift when there is a context variable present,
          and nothing otherwise *)
       (* above is WRONG *)
        | LF.Dot (_, f, s) when hasCtxVar ->
            fprintf ppf "%a %a"
              (self lvl) f
              print_front s

        | LF.Dot (_, f, s) when not hasCtxVar ->
            fprintf ppf "%a %a"
              (self lvl) f
              print_front s

        | LF.Id _ when not hasCtxVar ->
            fprintf ppf ".."

        | LF.Id _ when hasCtxVar ->
            fprintf ppf ".."

        | LF.EmptySub _ when not hasCtxVar ->
            fprintf ppf ""

        | LF.EmptySub _ when hasCtxVar ->
            fprintf ppf ""
        | LF.SVar (_, s, f) ->
            fprintf ppf "#%s[%a]"
              (R.render_name s)
              (self lvl) f


      in
              fprintf ppf " %a"
                (self lvl) s

    and fmt_ppr_lf_sub_deBruijn cD cPsi lvl ppf s =
      let rec self lvl ppf = function

        | LF.Id _  ->
            fprintf ppf ".."

        | LF.EmptySub _ ->
            fprintf ppf ""

        | LF.Dot (_, s, f) ->
            fprintf ppf "%a . %a"
              (fmt_ppr_lf_front cD cPsi 1) f
              (self lvl) s
      in
        fprintf ppf "[%a]"
          (self lvl) s


    and fmt_ppr_lf_front cD cPsi lvl ppf = function
      | LF.Head h ->
          fprintf ppf "%a"
            (fmt_ppr_lf_head cD cPsi lvl) h

      | LF.Normal m ->
          fprintf ppf "%a"
            (fmt_ppr_lf_normal cD cPsi lvl) m

    and fmt_ppr_lf_typ_rec cD cPsi _lvl ppf typrec =
       let ppr_element cD cPsi ppf suffix = function
       | (x, tA) ->
              fprintf ppf "%s:%a%s"
                (R.render_name x)
                (fmt_ppr_lf_typ cD cPsi 0) tA
               suffix
       in
       let rec ppr_elements cD cPsi ppf = function
         | LF.SigmaLast tA -> fmt_ppr_lf_typ cD cPsi 0 ppf tA
         | LF.SigmaElem (x, tA1, LF.SigmaLast tA2) ->
             begin
               ppr_element cD cPsi  ppf ". " (x, tA1);
               fprintf ppf "%a" (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, tA1))) 0) tA2
             end
         | LF.SigmaElem (x, tA, tAs)  ->
             begin
               ppr_element cD cPsi ppf ", " (x, tA);
               ppr_elements cD (LF.DDec(cPsi, LF.TypDecl (x, tA))) ppf  tAs
             end
(*             | tA :: tAs -> *)
(*                   fprintf ppf "%a,@ %a" *)
(*                     (fmt_ppr_lf_typ cD cPsi 0) tA *)
(*                     ppr_typ_rec        tAs *)
(*                fprintf ppf "Sigma %a. %a" *)
       in
         ppr_elements cD cPsi ppf typrec

    and projectCtxIntoDctx = function
         |  LF.Empty -> LF.Null
         |  LF.Dec (rest, last) -> LF.DDec (projectCtxIntoDctx rest, last)

    and fmt_ppr_lf_schema lvl ppf = function
      | LF.Schema [] -> ()

      | LF.Schema (f :: []) ->
            fprintf ppf "%a"
              (fmt_ppr_lf_sch_elem lvl) f

      | LF.Schema (f :: fs) ->
            fprintf ppf "@[%a@]@ +@ @[%a@]"
              (fmt_ppr_lf_sch_elem lvl) f
              (fmt_ppr_lf_schema lvl) (LF.Schema fs)

    and frugal_block cD cPsi lvl ppf = function
      | LF.SigmaLast tA -> fmt_ppr_lf_typ cD cPsi 0 ppf tA
      | other -> fprintf ppf "block (%a)" (fmt_ppr_lf_typ_rec cD cPsi lvl) other

    and fmt_ppr_lf_sch_elem lvl ppf = function
      | LF.SchElem (_, LF.Empty, sgmDecl) ->
            fprintf ppf "%a"
              (frugal_block LF.Empty LF.Null lvl) sgmDecl

      | LF.SchElem (_, typDecls, sgmDecl) ->
          let cPsi = projectCtxIntoDctx typDecls in
            fprintf ppf "@[some [%a] %a@]"
              (ppr_typ_decl_dctx  LF.Empty)  cPsi
              (frugal_block LF.Empty cPsi lvl) sgmDecl


    and ppr_typ_decl_dctx cD ppf = function
      | LF.Null ->
          fprintf ppf ""

      | LF.DDec (LF.Null, LF.TypDecl (x, tA)) ->
          fprintf ppf "%s : %a"    (* formerly "., %s : %a"    -jd 2010-06-03 *)
            (R.render_name x)
            (fmt_ppr_lf_typ cD LF.Null 0) tA

      | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
          fprintf ppf "%a, %s : %a"
            (ppr_typ_decl_dctx cD) cPsi
            (R.render_name x)
            (fmt_ppr_lf_typ cD cPsi 0) tA

      | LF.CtxVar (_, x) ->
          fprintf ppf "%s"
            (R.render_name x)


    and fmt_ppr_lf_psi_hat cD _lvl ppf = function
      | LF.Null   -> fprintf ppf ""

      | LF.CtxVar (_, x) -> (***)
          fprintf ppf "%s"
            (R.render_name x)

      | LF.DDec (LF.Null, LF.TypDecl(x, _ )) ->
          fprintf ppf "%s"
            (R.render_name x)

      | LF.DDec (cPsi, LF.TypDecl(x, _ )) ->
          fprintf ppf "%a, %s"
            (fmt_ppr_lf_psi_hat cD 0) cPsi
            (R.render_name x)

    and fmt_ppr_lf_dctx cD _lvl ppf = function
      | LF.Null ->
          fprintf ppf ""

      | LF.CtxVar (_, x) ->
          fprintf ppf "%s"
            (R.render_name x)

      | LF.DDec (LF.Null, LF.TypDecl (x, tA)) ->
          fprintf ppf "%s : %a"
            (R.render_name x)
            (fmt_ppr_lf_typ cD LF.Null 0) tA

      | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
          fprintf ppf "%a, %s : %a"
            (fmt_ppr_lf_dctx cD 0) cPsi
            (R.render_name x)
            (fmt_ppr_lf_typ cD cPsi 0) tA

    and fmt_ppr_lf_mctx lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cD, ctyp_decl) ->
          fprintf ppf "%a, %a"
            (fmt_ppr_lf_mctx 0) cD
            (fmt_ppr_lf_ctyp_decl cD lvl) ctyp_decl


    and fmt_ppr_lf_kind cPsi lvl ppf = function
      | LF.Typ _ ->
          fprintf ppf "type"

      | LF.PiKind (_,LF.TypDecl (x, a), k) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name   x)
              (fmt_ppr_lf_typ LF.Empty cPsi  0) a
              (fmt_ppr_lf_kind (LF.DDec(cPsi, LF.TypDecl (x, a))) 0) k
              (r_paren_if cond)

      | LF.ArrKind (_, a, k) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%a -> %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_typ LF.Empty cPsi  0) a
              (fmt_ppr_lf_kind cPsi 0) k
              (r_paren_if cond)

    and fmt_ppr_lf_ctyp_decl cD _lvl ppf = function
      | LF.MDecl (_, u, tA, cPsi) ->
          fprintf ppf "{%s :: %a[%a]}"
            (R.render_name u)
            (fmt_ppr_lf_typ cD cPsi 2) tA
            (fmt_ppr_lf_dctx cD 0) cPsi

      | LF.PDecl (_, p, tA, cPsi) ->
          fprintf ppf "{#%s :: %a[%a]}"
            (R.render_name p)
            (fmt_ppr_lf_typ cD cPsi 2) tA
            (fmt_ppr_lf_dctx cD 0) cPsi

      | LF.SDecl (_, u, cPhi, cPsi) ->
          fprintf ppf "{%s :: %a[%a]}"
            (R.render_name u)
            (fmt_ppr_lf_dctx cD 0) cPhi
            (fmt_ppr_lf_dctx cD 0) cPsi

      | LF.CDecl (_, name, schemaName) ->
          fprintf ppf "{%s :: (%s)*}"
            (R.render_name name)
            (R.render_name schemaName)

    (* Computation-level *)
    let rec fmt_ppr_cmp_kind cD lvl ppf = function
      | Comp.Ctype _ -> fprintf ppf "ctype"
      | Comp.PiKind (_, (ctyp_decl, _dep), cK) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s%a@ %a%s@]"
              (l_paren_if cond)
              (fmt_ppr_lf_ctyp_decl cD 1) ctyp_decl
              (fmt_ppr_cmp_kind (LF.Dec(cD, ctyp_decl)) 1) cK
              (r_paren_if cond)

    let rec fmt_ppr_meta_spine cD lvl ppf = function
      | Comp.MetaNil ->
          fprintf ppf ""
      | Comp.MetaApp (mO, mS) ->
          fprintf ppf " %a%a"
            (fmt_ppr_meta_obj  cD (lvl + 1)) mO
            (fmt_ppr_meta_spine   cD lvl) mS

    and fmt_ppr_meta_obj cD lvl ppf = function
      | Comp.MetaCtx (_, cPsi) ->
            fprintf ppf "[%a]"
              (fmt_ppr_lf_dctx cD 0) cPsi
      | Comp.MetaObj (_, phat, tM) ->
          let cond = lvl > 1 in
          let cPsi = phatToDCtx phat in
            fprintf ppf "%s[%a. %a]%s"
              (l_paren_if cond)
               (fmt_ppr_lf_psi_hat cD 0) cPsi
              (fmt_ppr_lf_normal cD cPsi 0) tM
              (r_paren_if cond)
      | Comp.MetaObjAnn (_, cPsi, tM) ->
          let cond = lvl > 1 in
            fprintf ppf "%s[%a. %a]%s"
              (l_paren_if cond)
               (fmt_ppr_lf_dctx cD 0) cPsi
              (fmt_ppr_lf_normal cD cPsi 0) tM
              (r_paren_if cond)

    let rec fmt_ppr_cmp_typ cD lvl ppf = function
      | Comp.TypBase (_, x, mS)->
          let cond = lvl > 1 in
            fprintf ppf "%s%s%a%s"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_meta_spine cD 2) mS
              (r_paren_if cond)

      | Comp.TypBox (_, tA, cPsi) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_typ cD cPsi 2) tA
            (fmt_ppr_lf_dctx cD 0) cPsi

      | Comp.TypPBox (_, tA, cPsi) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_typ cD cPsi 2) tA
            (fmt_ppr_lf_dctx cD 0) cPsi

      | Comp.TypCtx (_, x) ->
            fprintf ppf "%s"
              (R.render_name x)

      | Comp.TypSub (_, cPhi, cPsi) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_dctx cD 0) cPhi
            (fmt_ppr_lf_dctx cD 0) cPsi

      | Comp.TypArr (_, tau1, tau2) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a -> %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_typ cD 2) tau1
              (fmt_ppr_cmp_typ cD 0) tau2
              (r_paren_if cond)

      | Comp.TypCross (_, tau1, tau2) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%a * %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_typ cD 1) tau1
              (fmt_ppr_cmp_typ cD 0) tau2
              (r_paren_if cond)

(*      | Comp.TypCtxPi (l, (psi, w, dep), tau) ->
          let cond = lvl > 1 in
            fprintf ppf "%s{%s:(%s)*}@ %a%s"
              (l_paren_if cond)
              (R.render_name psi)
              (R.render_name w)
              (fmt_ppr_cmp_typ (LF.Dec(cD, LF.CDecl(l, psi, w))) 0) tau
              (r_paren_if cond)
*)
      | Comp.TypPiBox (_, (LF.CDecl (l, name, schema), Comp.Implicit), tau) ->
          let cond = lvl > 1 in
            fprintf ppf "%s(%s:(%s)*)@ %a%s"
              (l_paren_if cond)
              (R.render_name name)
              (R.render_name schema)
              (fmt_ppr_cmp_typ (LF.Dec(cD, LF.CDecl(l, name, schema))) 0) tau
              (r_paren_if cond)

      | Comp.TypPiBox (_, (ctyp_decl, _dep), tau) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a@ %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_ctyp_decl cD 1) ctyp_decl
              (fmt_ppr_cmp_typ (LF.Dec(cD, ctyp_decl)) 1) tau
              (r_paren_if cond)

      | Comp.TypBool -> fprintf ppf "Bool"

    let rec fmt_ppr_pat_spine cD lvl ppf = (function
      | Comp.PatNil _ -> fprintf ppf ""
      | Comp.PatApp (_, pat, pat_spine) ->
          fprintf ppf "%a %a"
            (fmt_ppr_pat_obj cD (lvl+1)) pat
            (fmt_ppr_pat_spine cD lvl) pat_spine

                                          )
    and fmt_ppr_pat_obj cD lvl ppf = function
      | Comp.PatEmpty (_, cPsi) ->
          let cond = lvl > 1 in
            fprintf ppf "%s[%a. {}]%s"
              (l_paren_if cond)
              (fmt_ppr_lf_dctx cD 0) cPsi
              (r_paren_if cond)
      | Comp.PatMetaObj (_, mO) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a%s"
              (l_paren_if cond)
              (fmt_ppr_meta_obj cD 0) mO
              (r_paren_if cond)
      | Comp.PatConst (_, x, pat_spine) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%s %a%s"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_pat_spine cD 2) pat_spine
              (r_paren_if cond)

      | Comp.PatPair (_, pat1, pat2) ->
          fprintf ppf "(%a , %a)"
            (fmt_ppr_pat_obj cD 0) pat1
            (fmt_ppr_pat_obj cD 0) pat2
      | Comp.PatTrue _ -> fprintf ppf "tt"
      | Comp.PatFalse _ -> fprintf ppf "ff"
      | Comp.PatAnn (_, pat, tau) ->
          fprintf ppf "(%a : %a)"
            (fmt_ppr_pat_obj cD 0) pat
            (fmt_ppr_cmp_typ cD 0) tau

      | Comp.PatVar (_, x) ->
          fprintf ppf "%s"
            (R.render_name x)


    let rec fmt_ppr_cmp_exp_chk cD lvl ppf = function
      | Comp.Syn (_, i) ->
          fmt_ppr_cmp_exp_syn cD lvl ppf (strip_mapp_args cD i)

      | Comp.Fun (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "%sfn %s => "
              (l_paren_if cond)
              (R.render_name x);

            fprintf ppf "%a%s"
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond);

(*      | Comp.CtxFun (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%sFN %s =>@ %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond)
*)
      | Comp.MLam (_, (x, Comp.MObj), e) ->
          let cond = lvl > 0 in
            fprintf ppf "%smlam %s => "
              (l_paren_if cond)
              (R.render_name x);
            fprintf ppf "%a%s"
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond);

      | Comp.MLam (_, (x, Comp.PObj), e) ->
          let cond = lvl > 0 in
            fprintf ppf "%smlam # %s => "
              (l_paren_if cond)
              (R.render_name x);
            fprintf ppf "%a%s"
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond);

     | Comp.MLam (_, (x, Comp.SObj), e) ->
          let cond = lvl > 0 in
            fprintf ppf "%smlam #%s => "
              (l_paren_if cond)
              (R.render_name x);
            fprintf ppf "%a%s"
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond);

      | Comp.Pair (_, e1, e2) ->
            fprintf ppf "(%a , %a)"
              (fmt_ppr_cmp_exp_chk cD 0) e1
              (fmt_ppr_cmp_exp_chk cD 0) e2


      | Comp.LetPair(_, i, (x, y, e)) ->
          let cond = lvl > 1 in
            fprintf ppf "@[<2>%slet <%s,%s> = %a@ in %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (R.render_name y)
              (fmt_ppr_cmp_exp_syn cD 0) (strip_mapp_args cD i)
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond)


      | Comp.Let(_, i, (x, e)) ->
          let cond = lvl > 1 in
            fprintf ppf "@[<2>%slet %s = %a@ in %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_syn cD 0) (strip_mapp_args cD i)
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond)

      | Comp.Box (_ , m) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a%s"
              (l_paren_if cond)
              (fmt_ppr_meta_obj  cD 0) m
              (r_paren_if cond)

      | Comp.Case (_, prag, i, bs) ->
            fprintf ppf "@[<v>case @[%a@] of%s%a"
              (fmt_ppr_cmp_exp_syn cD 0) (strip_mapp_args cD i)
              (match prag with Pragma.RegularCase -> "" | Pragma.PragmaNotCase -> " %not ")
              (fmt_ppr_cmp_branches cD 0) bs

      | Comp.If (_, i, e1, e2) ->
          let cond = lvl > 1 in
            fprintf ppf "@[<2>%sif %a @[<-1>then %a @]else %a%s@]"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn cD 0) (strip_mapp_args cD i)
              (fmt_ppr_cmp_exp_chk cD 0) e1
              (fmt_ppr_cmp_exp_chk cD 0) e2
              (r_paren_if cond)

      | Comp.Hole (_) -> fprintf ppf " ? "

    and strip_mapp_args cD i =
      if !Control.printImplicit then
        i
      else
        let (i', _ ) = strip_mapp_args' cD i in i'

    and strip_mapp_args' cD i = match i with
      | Comp.Const (_, x) ->
          (i,  implicitCompArg  (R.render_name x))
      | Comp.DataConst (_, x) ->
          (i,  implicitCompArg  (R.render_name x))
      | Comp.Var (_, x) ->
          (i,  implicitCompArg  (R.render_name x))

      | Comp.Apply (loc, i, e) ->
          let (i', _ ) = strip_mapp_args' cD i in
            (Comp.Apply (loc, i', e), 0)

      | Comp.MApp (loc, i1, mO ) ->
          let (i', stripArg) = strip_mapp_args' cD i1 in
            if stripArg = 0 then
              (Comp.MApp (loc , i', mO), 0)
            else
              (i', stripArg - 1 )

      | Comp.Ann (loc, e, tau) -> (Comp.Ann (loc, e, tau), 0)


    and implicitCompArg tau = 0


    and fmt_ppr_cmp_exp_syn cD lvl ppf = function
      | Comp.Var(_, x) ->
          fprintf ppf "%s"
            (R.render_name x)

      | Comp.Const (_, x) ->
          fprintf ppf "%s"
            (R.render_name x)

      | Comp.DataConst (_, x) ->
          fprintf ppf "%s"
            (R.render_name x)

      | Comp.Apply (_, i, e) ->
          let cond = lvl > 1 in
            fprintf ppf "%s@[<2>%a@ %a@]%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn cD 1) i
              (fmt_ppr_cmp_exp_chk cD 2) e
              (r_paren_if cond)

      | Comp.MApp (_, i, mO) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a@ %s%a%s%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn cD 1) i
              ("")
              (fmt_ppr_meta_obj cD 0) mO
              ("")
              (r_paren_if cond)

      | Comp.BoxVal (_, cPsi, normal) ->
          let cond = lvl > 1 in
            fprintf ppf "%s %s%a. %a%s%s"
              (l_paren_if cond)
              ("")
              (fmt_ppr_lf_dctx cD 0) cPsi
              (fmt_ppr_lf_normal cD cPsi 0) normal
              ("")
              (r_paren_if cond)

      | Comp.Ann (_, e, tau) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a : %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_chk cD 1) e
              (fmt_ppr_cmp_typ cD 2) tau
              (r_paren_if cond)



      | Comp.Equal (_, i1, i2) ->
            fprintf ppf "%a == %a"
              (fmt_ppr_cmp_exp_syn cD 1) i1
              (fmt_ppr_cmp_exp_syn cD 1) i2

      | Comp.Boolean (_, true) ->
          fprintf ppf "true"

      | Comp.Boolean (_, false) ->
          fprintf ppf "false"

    and fmt_ppr_cmp_branch_prefix _lvl ppf = function
      | LF.Empty -> ()
      | other ->
          (let rec fmt_ppr_ctyp_decls' ppf = function
            | LF.Dec (LF.Empty, decl) ->
                fprintf ppf "%a"
                  (fmt_ppr_lf_ctyp_decl LF.Empty 1) decl
            | LF.Dec (cD, decl) ->
                fprintf ppf "%a @ %a"
                  (fmt_ppr_ctyp_decls') cD
                  (fmt_ppr_lf_ctyp_decl cD 1) decl
          in
            fprintf ppf "@[%a@]@ " (fmt_ppr_ctyp_decls') other
          )

    and fmt_ppr_cmp_branches cD lvl ppf = function
      | [] -> ()

      | b :: [] ->
          fprintf ppf "%a"
            (fmt_ppr_cmp_branch cD 0) b

      | b :: bs ->
          fprintf ppf "%a%a"
            (fmt_ppr_cmp_branch cD 0) b
            (fmt_ppr_cmp_branches cD lvl) bs

    and fmt_ppr_pattern cD1' cPsi ppf = function
      | Comp.NormalPattern (tM, _) -> fmt_ppr_lf_normal cD1' cPsi 0 ppf tM
      | Comp.EmptyPattern ->fprintf ppf "@[{}@]"

    and fmt_ppr_patternOpt cD1' cPsi ppf = function
      | Some tM -> fmt_ppr_lf_normal cD1' cPsi 0 ppf tM
      | None ->fprintf ppf "@[{}@]"

    and fmt_ppr_cmp_branch cD _lvl ppf = function
      | Comp.EmptyBranch (_, cD1, pat) ->
          fprintf ppf "@ @[<v2>| @[<v0>%a@[[ %a] @]  @]@  "
            (fmt_ppr_cmp_branch_prefix  0) cD1
            (fmt_ppr_pat_obj cD1 0) pat


      | Comp.Branch (_, cD1', Comp.PatMetaObj (_, mO), e) ->
          fprintf ppf "@ | @[<v0>%a@[%a @  => @]@ @[<2>@ %a@]@]@ "
            (fmt_ppr_cmp_branch_prefix  0) cD1'
            (fmt_ppr_meta_obj cD1' 0) mO
            (* NOTE: Technically: cD |- cG ctx and
             *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1|
             * -bp
             *)
            (fmt_ppr_cmp_exp_chk cD1' 1) e

      | Comp.Branch (_, cD1', pat, e) ->

          fprintf ppf "@ @[<v2>| @[<v0>%a ; @[ . %a @]  => @]@ @[<2>@ %a@]@]@ "
             (fmt_ppr_cmp_branch_prefix  0) cD1'
             (fmt_ppr_pat_obj cD1' 0) pat
             (fmt_ppr_cmp_exp_chk cD1' 1) e

      | Comp.BranchBox (_, cD1', (cPsi, pattern, _cs)) ->
          let rec ppr_ctyp_decls' ppf = function
            | LF.Dec (LF.Empty, decl) ->
                fprintf ppf "%a"
                  (fmt_ppr_lf_ctyp_decl cD 1) decl
            | LF.Dec (cD, decl) ->
                fprintf ppf "%a @ %a"
                  (ppr_ctyp_decls' ) cD
                  (fmt_ppr_lf_ctyp_decl cD 1) decl
          and ppr_ctyp_decls ppf = function
            | LF.Empty -> ()
            | other -> fprintf ppf "@[%a@]@ " (ppr_ctyp_decls') other
          in

            fprintf ppf "@ @[<v2>| @[<v0>%a@[([%a] %a)@ @]  => @]@ @[<2>@ @]@]@ "
              (ppr_ctyp_decls ) cD1'

              (fmt_ppr_lf_dctx cD1' 0) cPsi
              (fmt_ppr_pattern cD1' cPsi) pattern

      | Comp.BranchSBox (_, cD1', (cPsi, s, _cs), e) ->
          let rec ppr_ctyp_decls' ppf = function
            | LF.Dec (LF.Empty, decl) ->
                fprintf ppf "%a"
                  (fmt_ppr_lf_ctyp_decl cD 1) decl
            | LF.Dec (cD, decl) ->
                fprintf ppf "%a @ %a"
                  (ppr_ctyp_decls' ) cD
                  (fmt_ppr_lf_ctyp_decl cD 1) decl
          and ppr_ctyp_decls ppf = function
            | LF.Empty -> ()
            | other -> fprintf ppf "@[%a@]@ " (ppr_ctyp_decls') other
          in

            fprintf ppf "@ @[<v2>| @[<v0>%a@[([%a] %a)@ @]  => %a"
              (ppr_ctyp_decls ) cD1'
              (fmt_ppr_lf_dctx cD1' 0) cPsi
              (fmt_ppr_lf_sub  cD cPsi 0) s
              (fmt_ppr_cmp_exp_chk cD1' 1) e


    and fmt_ppr_cmp_gctx cD lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cG, LF.TypDecl (x, tau)) ->
          fprintf ppf "%a, %s: %a"
            (fmt_ppr_cmp_gctx cD 0) cG
            (R.render_name x)
            (fmt_ppr_lf_typ cD LF.Null lvl) tau

    let fmt_ppr_cmp_rec lvl ppf = function
      | Comp.RecFun (x, a, e) ->
          fprintf ppf "rec %s : %a => @ %a"
            (R.render_name x)
            (fmt_ppr_cmp_typ LF.Empty lvl)  a
            (fmt_ppr_cmp_exp_chk LF.Empty lvl)  e

    let rec fmt_ppr_rec lvl ppf = function
      | [] -> ()
      | h::t -> fprintf ppf "%a %a \n"
                   (fmt_ppr_cmp_rec lvl) h
                   (fmt_ppr_rec lvl) t

    let fmt_ppr_sgn_decl ?(asHtml = false) lvl ppf = function
      | Sgn.Const (_, x, a) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_name x)
            (fmt_ppr_lf_typ ~asHtml:asHtml LF.Empty LF.Null lvl)  a

      | Sgn.CompConst (_, x, a) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_name x)
            (fmt_ppr_cmp_typ LF.Empty lvl)  a

      | Sgn.Typ (_, x, k) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_name  x)
            (fmt_ppr_lf_kind LF.Null lvl) k

      | Sgn.CompTypAbbrev (_, x, k, a) ->
          fprintf ppf "%s : %a.@.@?:%a"
            (R.render_name  x)
            (fmt_ppr_cmp_kind LF.Empty lvl) k
            (fmt_ppr_cmp_typ LF.Empty lvl)  a

      | Sgn.CompTyp (_, x, k) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_name  x)
            (fmt_ppr_cmp_kind LF.Empty lvl) k

      | Sgn.Schema (_, x, schema) ->
          fprintf ppf "schema %s : %a;@.@?"
            (R.render_name  x)
            (fmt_ppr_lf_schema lvl) schema

     | Sgn.Rec (_, lrec) ->
           (fmt_ppr_rec lvl ppf) lrec

      | Sgn.Pragma (_, Sgn.NamePrag _) ->  ()

      | Sgn.Val (_, x, _, i) ->
          fprintf ppf "let %s = %a"
            (R.render_name  x)
            (fmt_ppr_cmp_exp_syn LF.Empty lvl) i

      | Sgn.Query _ ->
          fprintf ppf "query"



    (* Regular Pretty Printers *)
    let ppr_sgn_decl           = fmt_ppr_sgn_decl              std_lvl std_formatter
    let ppr_lf_ctyp_decl  cD   = fmt_ppr_lf_ctyp_decl cD    std_lvl std_formatter
    let ppr_lf_kind cPsi       = fmt_ppr_lf_kind cPsi          std_lvl std_formatter
    let ppr_lf_typ  cD cPsi    = fmt_ppr_lf_typ cD cPsi     std_lvl std_formatter
    let ppr_lf_normal cD cPsi  = fmt_ppr_lf_normal cD cPsi  std_lvl std_formatter
    let ppr_lf_head cD cPsi    = fmt_ppr_lf_head cD cPsi    std_lvl std_formatter
    let ppr_lf_spine cD cPsi   = fmt_ppr_lf_spine cD cPsi   std_lvl std_formatter
    let ppr_lf_sub cD cPsi     = fmt_ppr_lf_sub cD cPsi     std_lvl std_formatter

    let ppr_lf_schema          = fmt_ppr_lf_schema             std_lvl std_formatter
    let ppr_lf_sch_elem        = fmt_ppr_lf_sch_elem           std_lvl std_formatter

    let ppr_lf_typ_rec cD cPsi = fmt_ppr_lf_typ_rec cD cPsi std_lvl std_formatter

    let ppr_lf_dctx cD         = fmt_ppr_lf_dctx cD         std_lvl std_formatter
    let ppr_lf_mctx            = fmt_ppr_lf_mctx            std_lvl std_formatter
    let ppr_cmp_kind cD        = fmt_ppr_cmp_kind cD        std_lvl std_formatter
    let ppr_cmp_typ cD         = fmt_ppr_cmp_typ cD         std_lvl std_formatter
    let ppr_cmp_exp_chk cD     = fmt_ppr_cmp_exp_chk cD     std_lvl std_formatter
    let ppr_cmp_exp_syn cD     = fmt_ppr_cmp_exp_syn cD     std_lvl std_formatter
    let ppr_cmp_branches cD    = fmt_ppr_cmp_branches cD    std_lvl std_formatter
    let ppr_cmp_branch cD      = fmt_ppr_cmp_branch cD      std_lvl std_formatter

    let subToString cD cPsi s'  =
        fmt_ppr_lf_sub cD cPsi std_lvl str_formatter s'
        ; flush_str_formatter ()

    let spineToString cD cPsi sS  =
        fmt_ppr_lf_spine cD cPsi std_lvl str_formatter sS
        ; flush_str_formatter ()

    let typToString cD cPsi sA    =
        fmt_ppr_lf_typ cD cPsi std_lvl str_formatter sA
        ; flush_str_formatter ()

    let typRecToString cD cPsi typrec_clo =
      fmt_ppr_lf_typ_rec cD cPsi std_lvl str_formatter typrec_clo
      ; flush_str_formatter ()

    let kindToString cPsi sK   =
      fmt_ppr_lf_kind cPsi std_lvl str_formatter sK
      ; flush_str_formatter ()

    let tupleToString cD cPsi tuple =
      fmt_ppr_tuple cD cPsi std_lvl str_formatter tuple
      ; flush_str_formatter ()

    let headToString cD cPsi h =
      fmt_ppr_lf_head cD cPsi std_lvl str_formatter h
      ; flush_str_formatter ()

    let normalToString cD cPsi sM =
        fmt_ppr_lf_normal cD cPsi std_lvl str_formatter sM
        ; flush_str_formatter ()

    let dctxToString cD cPsi =
       (fmt_ppr_lf_dctx cD std_lvl str_formatter cPsi;
                 flush_str_formatter ())

    let mctxToString cD =
      fmt_ppr_lf_mctx std_lvl str_formatter cD
        ; flush_str_formatter ()

    let schemaToString schema =
      fmt_ppr_lf_schema std_lvl str_formatter schema
      ; flush_str_formatter ()

    let schElemToString sch_elem =
      fmt_ppr_lf_sch_elem std_lvl str_formatter sch_elem
      ; flush_str_formatter ()


    let metaObjToString  cD mO =
        fmt_ppr_meta_obj cD std_lvl str_formatter mO
        ; flush_str_formatter ()

    let gctxToString cD cG =
        fmt_ppr_cmp_gctx cD std_lvl str_formatter cG
        ; flush_str_formatter ()

    let patternToString cD pat    =
       fmt_ppr_pat_obj cD std_lvl str_formatter pat
      ; flush_str_formatter ()

    let expChkToString cD e    =
       fmt_ppr_cmp_exp_chk cD std_lvl str_formatter e
      ; flush_str_formatter ()

    let expSynToString cD i   =
      fmt_ppr_cmp_exp_syn cD std_lvl str_formatter i
      ; flush_str_formatter ()

    let branchToString cD cG  b    =
      fmt_ppr_cmp_branch cD std_lvl str_formatter b
      ; flush_str_formatter ()

    let compTypToString cD tau  =
        fmt_ppr_cmp_typ cD std_lvl str_formatter tau
        ; flush_str_formatter ()

    let compKindToString cD cK  =
(*      let cK' = Whnf.normCKind cK in  *)
        fmt_ppr_cmp_kind cD std_lvl str_formatter cK
        ; flush_str_formatter ()


  end (* Int.Make *)

  (* Default Error Pretty Printer Functor Instantiation *)
  module DefaultPrinter = Make (Store.Cid.NamedRenderer)

end (* Int *)
