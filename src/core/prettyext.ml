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
    val fmt_ppr_sgn_decl      : lvl -> formatter -> Sgn.decl  -> unit
    val fmt_ppr_lf_kind       : LF.dctx -> lvl -> formatter -> LF.kind      -> unit
    val fmt_ppr_lf_ctyp_decl  : LF.mctx -> lvl -> formatter -> LF.ctyp_decl -> unit
    val fmt_ppr_lf_typ_rec    : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ_rec    -> unit

    val fmt_ppr_lf_typ        : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ    -> unit
    val fmt_ppr_lf_normal     : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.normal -> unit
    val fmt_ppr_lf_head       : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.head   -> unit
    val fmt_ppr_lf_spine      : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.spine  -> unit
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

    (* Fresh name generation *)
    let rec get_names_dctx : LF.dctx -> Id.name list = function
      | LF.Null
      | LF.CtxHole -> []
      | LF.CtxVar (loc, n) -> [n]
      | LF.DDec (cPsi', LF.TypDecl (n, _))
      | LF.DDec (cPsi', LF.TypDeclOpt n) -> n :: get_names_dctx cPsi'

    let rec get_names_mctx : LF.mctx -> Id.name list = function
      | LF.Empty -> []
      | LF.Dec (cD', LF.Decl (n, _, _))
      | LF.Dec (cD', LF.DeclOpt n) -> n :: get_names_mctx cD'

    let fresh_name_dctx (cPsi : LF.dctx) : Id.name -> Id.name =
      Id.gen_fresh_name (get_names_dctx cPsi)
    let fresh_name_mctx (cD : LF.mctx) : Id.name -> Id.name =
      Id.gen_fresh_name (get_names_mctx cD)

    let fresh_name_ctyp_decl (cD: LF.mctx) : LF.ctyp_decl -> LF.ctyp_decl = function
      | LF.Decl (n, ct, dep) ->
         let n' = fresh_name_mctx cD n in LF.Decl (n', ct, dep)
      | LF.DeclOpt n ->
         let n' = fresh_name_mctx cD n in LF.DeclOpt n'

    (* Contextual Format Based Pretty Printers
     *
     * We assume types, terms, etc are all in normal form.
     *)

    let rec has_ctx_var = function
      | LF.CtxVar _
      | LF.CtxHole -> true
      | LF.Null -> false
      | LF.DDec(cPsi, _x) -> has_ctx_var cPsi

    type id_type =
    | Constructor
    | Typ
    | Fun
    | Schema

    type html =
    | Keyword
    | ID of id_type
    | Link
    | LinkOption

    let to_html (s : string) (tag : html) : string =
    if not !Html.printingHtml then s else match tag with
    | Keyword -> "<keyword>" ^ s ^ "</keyword>"
    | ID Constructor -> Html.addId s; "<span class=\"constructor\" id=\"" ^ s ^ "\">" ^ s ^ "</span>"
    | ID Typ -> Html.addId s; "<span class=\"typ\" id=\"" ^ s ^ "\">" ^ s ^ "</span>"
    | ID Fun -> Html.addId s; "<span class=\"function\" id=\"" ^ s ^ "\">" ^ s ^ "</span>"
    | ID Schema -> "<span class=\"schema\" id=\"" ^ s ^ "\">" ^ s ^ "</span>"
    | Link -> "<a href=\"#" ^ s ^ "\">" ^ s ^ "</a>"
    | LinkOption -> if Html.idExists s then "<a href=\"#" ^ s ^ "\">" ^ s ^ "</a>" else s
    let iteri f =
	    let rec iteri' i = function
	      | [] -> ()
	      | x::xs -> (f i x); iteri' (i+1) xs
	    in iteri' 0

    type symbol =
    | Turnstile
    | RArr
    | DblRArr
    | Dots
    | Lam

    let symbol_to_html : symbol -> string = function
    | Turnstile -> if !Html.printingHtml then "&#x22A2" else "|-"
    | RArr -> if !Html.printingHtml then "&#x2192" else "->"
    | DblRArr -> if !Html.printingHtml then "&#x21D2" else "=>"
    | Dots -> if !Html.printingHtml then "&hellip;" else ".."
    | Lam -> if !Html.printingHtml then "&lambda;" else "\\"

    let rec fmt_ppr_lf_typ  cD cPsi lvl ppf = function
      | LF.AtomTerm(_, n) -> fmt_ppr_lf_normal cD cPsi lvl ppf n

      | LF.Atom (_, a, LF.Nil) ->
          let name = to_html (Id.render_name a) Link in
          fprintf ppf "%s" name

      | LF.Atom (_, a, ms) ->
          let name = to_html (Id.render_name a) Link in
            fprintf ppf "%s%a"
              name
              (fmt_ppr_lf_spine cD cPsi 2) ms

      | LF.PiTyp (_,LF.TypDecl (x, a), (LF.ArrTyp _ as b)) ->
            let cond = lvl > 1 in
            let x = fresh_name_dctx cPsi x in
            let name = to_html (Id.render_name x) LinkOption in
            fprintf ppf "%s{%s : %a} %a%s"
              (l_paren_if cond)
              name
              (fmt_ppr_lf_typ cD cPsi 0) a
              (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, a))) 2) b
              (r_paren_if cond)
      | LF.PiTyp (_,LF.TypDecl (x, a), b) ->
            let cond = lvl > 1 in
            let x = fresh_name_dctx cPsi x in
            let name = to_html (Id.render_name x) LinkOption in
            fprintf ppf "%s{%s : %a} %a%s"
              (l_paren_if cond)
              name
              (fmt_ppr_lf_typ cD cPsi 0) a
              (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, a))) lvl) b
              (r_paren_if cond)

      | LF.Sigma (_,typRec) ->
          fprintf ppf "%s (%a)"
            (to_html "block" Keyword)
            (fmt_ppr_lf_typ_rec cD cPsi lvl) typRec

      | LF.ArrTyp (_, (LF.PiTyp _ as t1), t2) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a %s %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_typ cD cPsi 2) t1
              (symbol_to_html RArr)
              (fmt_ppr_lf_typ cD cPsi 0) t2
              (r_paren_if cond)

      | LF.ArrTyp (_, (LF.ArrTyp _ as t1), t2) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a %s %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_typ cD cPsi 2) t1
              (symbol_to_html RArr)
              (fmt_ppr_lf_typ cD cPsi 0) t2
              (r_paren_if cond)

      | LF.ArrTyp (_, t1, t2) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a %s %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_typ cD cPsi 0) t1
              (symbol_to_html RArr)
              (fmt_ppr_lf_typ cD cPsi 0) t2
              (r_paren_if cond)

      | LF.Ctx   (_, cPsi)  ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a%s"
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
        | LF.Proj _ -> ms

      in function
        | LF.Lam (_, x, m) ->
            let cond = lvl > 0 in
              fprintf ppf "%s%s%s. %a%s"
                (l_paren_if cond)
                (symbol_to_html Lam)
                (Id.render_name x)
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

        | LF.LFHole _ ->
          fprintf ppf "?"

        | LF.NTyp (u, tA)-> fmt_ppr_lf_typ cD cPsi lvl ppf tA

        | LF.TList(_, [x]) -> fmt_ppr_lf_normal cD cPsi lvl ppf x
        | LF.TList(_, l) ->
          let length = List.length l in
          fprintf ppf "%s" (l_paren_if (lvl > 0));

          iteri (fun i x ->
            if i = length - 1 then fprintf ppf "%a" (fmt_ppr_lf_normal cD cPsi (lvl + 1)) x
            else fprintf ppf "%a " (fmt_ppr_lf_normal cD cPsi (lvl + 1)) x) l;
          fprintf ppf "%s" (r_paren_if (lvl > 0));
	| LF.PatEmpty _ -> fprintf ppf "{}"

    and fmt_ppr_lf_head cD cPsi lvl ppf head =
      let paren s = not (Control.db()) && lvl > 0 && true
      in begin match head with
      | LF.MVar (_, x, LF.EmptySub _) ->
          fprintf ppf "%s[]" (Id.render_name x)
      | LF.MVar (_, x, s) ->
          fprintf ppf "%s%a"
            (Id.render_name x)
            (fmt_ppr_lf_sub  cD cPsi lvl) s

      (* | LF.SVar (_, x, s) -> *)
      (*     fprintf ppf "%s%s%a%s" *)
      (*       (l_paren_if (paren s)) *)
      (*       (Id.render_name x) *)
      (*       (fmt_ppr_lf_sub  cD cPsi lvl) s *)
      (*       (r_paren_if (paren s)) *)

      | LF.PVar (_,  x, s) ->
          fprintf ppf "%s#%s%a%s"
            (l_paren_if (paren s))
            (Id.render_name x)
            (fmt_ppr_lf_sub  cD cPsi lvl) s
            (r_paren_if (paren s))

      | LF.Name(_, x) ->
          fprintf ppf "%s"
            (to_html (Id.render_name x) LinkOption)

      | LF.Hole (_) ->
          fprintf ppf "_"

      | LF.Proj (_, (LF.Name _ as h), p) ->
	fprintf ppf "%a.%a"
	(fmt_ppr_lf_head cD cPsi lvl) h
	(fmt_ppr_lf_proj lvl) p

      | LF.Proj (_, LF.PVar (_,  x, s), p) ->
	fprintf ppf "#%s.%a%a"
            (Id.render_name x)
	    (fmt_ppr_lf_proj lvl) p
            (fmt_ppr_lf_sub  cD cPsi lvl) s
      end
    and fmt_ppr_lf_proj lvl ppf = function
      | LF.ByName n -> fprintf ppf "%s" (Id.render_name n)
      | LF.ByPos k -> fprintf ppf "%d" k

    and fmt_ppr_lf_spine cD cPsi lvl ppf = function
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

    and fmt_ppr_lf_sub_bare cD cPsi lvl ppf s = 
      match !Control.substitutionStyle with
        | Control.Natural -> fmt_ppr_lf_sub_natural_bare cD cPsi lvl ppf s
        | Control.DeBruijn -> fmt_ppr_lf_sub_deBruijn_bare cD cPsi lvl ppf s

    and fmt_ppr_lf_sub_natural_bare cD cPsi lvl ppf s = 
	 let print_front = fmt_ppr_lf_front cD cPsi 1 in
	 let hasCtxVar = has_ctx_var cPsi in 
	 let rec self lvl ppf s =  match s with 
	  | LF.Dot (_, f, s) when hasCtxVar ->
	     fprintf ppf "%a, %a" (self lvl) f
		     print_front s
					     
          | LF.Dot (_, f, s) when not hasCtxVar ->
            fprintf ppf "%a, %a"
              (self lvl) f
              print_front s

          | LF.Id _ ->
            fprintf ppf "%s" (symbol_to_html Dots)

          | LF.RealId -> () (* fprintf ppf "%s" (symbol_to_html Dots) *)

          | LF.EmptySub _ ->
            fprintf ppf ""
          | LF.SVar(_, s, LF.EmptySub _) ->
            fprintf ppf "#%s[^]"
            (Id.render_name s)
          | LF.SVar(_, s, LF.RealId) ->
            fprintf ppf "#%s"
            (Id.render_name s)
          | LF.SVar (_, s, f) ->
            fprintf ppf "#%s[%a]"
              (Id.render_name s)
              (self lvl) f
       in 
         self lvl ppf s

    and fmt_ppr_lf_sub_natural cD cPsi lvl ppf s = 
      (match s with 
       | LF.RealId -> fprintf ppf "" 
       | _       ->  fprintf ppf "[%a]" (fmt_ppr_lf_sub_natural_bare cD cPsi lvl) s)

    and fmt_ppr_lf_sub_deBruijn cD cPsi lvl ppf s =
        fprintf ppf "[%a]"
          (fmt_ppr_lf_sub_deBruijn_bare cD cPsi lvl) s

    and fmt_ppr_lf_sub_deBruijn_bare cD cPsi lvl ppf s = 
        let rec self lvl ppf = function
        | LF.Id _  ->
            fprintf ppf "%s" (symbol_to_html Dots)

        | LF.EmptySub _ ->
            fprintf ppf ""

        | LF.Dot (_, s, f) ->
            fprintf ppf "%a . %a"
              (fmt_ppr_lf_front cD cPsi 1) f
              (self lvl) s
      in
       self lvl ppf s


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
                (Id.render_name x)
                (fmt_ppr_lf_typ cD cPsi 0) tA
               suffix
       in
       let rec ppr_elements cD cPsi ppf = function
         | LF.SigmaLast (Some x, tA) -> ppr_element cD cPsi  ppf "" (x, tA)
         | LF.SigmaLast (None, tA) -> fmt_ppr_lf_typ cD cPsi 0 ppf tA
         | LF.SigmaElem (x, tA, tAs)  ->
             let x = fresh_name_dctx cPsi x in
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
            fprintf ppf "@[%a@] + @[%a@]"
              (fmt_ppr_lf_sch_elem lvl) f
              (fmt_ppr_lf_schema lvl) (LF.Schema fs)

    and frugal_block cD cPsi lvl ppf = function
      | LF.SigmaLast (_, tA) -> fmt_ppr_lf_typ cD cPsi 0 ppf tA
      | other -> fprintf ppf "%s (%a)"
				(to_html "block" Keyword)
				(fmt_ppr_lf_typ_rec cD cPsi lvl) other

    and fmt_ppr_lf_sch_elem lvl ppf = function
      | LF.SchElem (_, LF.Empty, sgmDecl) ->
            fprintf ppf "%a"
              (frugal_block LF.Empty LF.Null lvl) sgmDecl

      | LF.SchElem (_, typDecls, sgmDecl) ->
          let cPsi = projectCtxIntoDctx typDecls in
            fprintf ppf "%s [%a] %a"
              (to_html "some" Keyword)
              (ppr_typ_decl_dctx  LF.Empty)  cPsi
              (frugal_block LF.Empty cPsi lvl) sgmDecl


    and ppr_typ_decl_dctx cD ppf = function
      | LF.Null ->
          fprintf ppf ""

      | LF.DDec (LF.Null, LF.TypDecl (x, tA)) ->
          fprintf ppf "%s : %a"    (* formerly "., %s : %a"    -jd 2010-06-03 *)
            (Id.render_name x)
            (fmt_ppr_lf_typ cD LF.Null 0) tA

      | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
          fprintf ppf "%a, %s : %a"
            (ppr_typ_decl_dctx cD) cPsi
            (Id.render_name x)
            (fmt_ppr_lf_typ cD cPsi 0) tA

      | LF.CtxVar (_, x) ->
          fprintf ppf "%s"
            (Id.render_name x)


    and fmt_ppr_lf_psi_hat cD _lvl ppf = function
      | LF.Null   -> fprintf ppf ""

      | LF.CtxVar (_, x) -> (***)
          fprintf ppf "%s"
            (Id.render_name x)

      | LF.DDec (LF.Null, LF.TypDecl(x, _ )) ->
          fprintf ppf "%s"
            (Id.render_name x)

      | LF.DDec (cPsi, LF.TypDecl(x, _ )) ->
          fprintf ppf "%s, %a"
            (Id.render_name x)
            (fmt_ppr_lf_psi_hat cD 0) cPsi

    and fmt_ppr_lf_typ_decl cD cPsi lvl ppf = function
      | LF.TypDecl (x,tA) ->
	fprintf ppf "%s : %a"
	  (Id.render_name x)
	  (fmt_ppr_lf_typ cD cPsi lvl) tA
      | LF.TypDeclOpt x -> fprintf ppf "%s" (Id.render_name x)
    and fmt_ppr_lf_dctx cD lvl ppf = function
      | LF.CtxHole -> fprintf ppf "_"
      | LF.Null ->
          fprintf ppf ""

      | LF.CtxVar (_, x) ->
          fprintf ppf "%s"
            (Id.render_name x)

      | LF.DDec (LF.Null, d) ->
     	  fmt_ppr_lf_typ_decl cD LF.Null lvl ppf d

      | LF.DDec (cPsi, d) ->
          fprintf ppf "%a, %a"
            (fmt_ppr_lf_dctx cD 0) cPsi
            (fmt_ppr_lf_typ_decl cD cPsi lvl) d

    and fmt_ppr_lf_mctx lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cD, ctyp_decl) ->
          fprintf ppf "%a, %a"
            (fmt_ppr_lf_mctx 0) cD
            (fmt_ppr_lf_ctyp_decl cD lvl) ctyp_decl


    and fmt_ppr_lf_kind cPsi lvl ppf = function
      | LF.Typ _ ->
          fprintf ppf "%s"
          (to_html "type" Keyword)

      | LF.PiKind (_,LF.TypDecl (x, a), k) ->
          let cond = lvl > 0 in
          let x = fresh_name_dctx cPsi x in
          let name = Id.render_name x in
            fprintf ppf "%s{%s : %a} %a%s"
              (l_paren_if cond)
              (name)
              (fmt_ppr_lf_typ LF.Empty cPsi  0) a
              (fmt_ppr_lf_kind (LF.DDec(cPsi, LF.TypDecl (x, a))) 0) k
              (r_paren_if cond)

      | LF.ArrKind (_, a, k) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%a %s %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_typ LF.Empty cPsi  0) a
              (symbol_to_html RArr)
              (fmt_ppr_lf_kind cPsi 0) k
              (r_paren_if cond)

    and fmt_ppr_lf_ctyp_decl cD _lvl ppf = function
      | LF.Decl (u, (_,LF.ClTyp (LF.MTyp tA, cPsi)), _) ->
          fprintf ppf "{%s : [%a %s %a]}"
            (Id.render_name u)
            (fmt_ppr_lf_dctx cD 0) cPsi
            (symbol_to_html Turnstile)
            (fmt_ppr_lf_typ cD cPsi 0) tA
(*           fprintf ppf "{%s :: %a[%a]}"
            (Id.render_name u)
            (fmt_ppr_lf_typ cD cPsi 2) tA
            (fmt_ppr_lf_dctx cD 0) cPsi
 *)
      | LF.Decl (p, (_,LF.ClTyp (LF.PTyp tA, cPsi)), _) ->
          fprintf ppf "{#%s : [%a %s %a]}"
            (Id.render_name p)
            (fmt_ppr_lf_dctx cD 0) cPsi
            (symbol_to_html Turnstile)
            (fmt_ppr_lf_typ cD cPsi 0) tA
          (* fprintf ppf "{#%s :: %a[%a]}"
            (Id.render_name p)
            (fmt_ppr_lf_typ cD cPsi 2) tA
            (fmt_ppr_lf_dctx cD 0) cPsi *)

      | LF.Decl (u, (_,LF.ClTyp (LF.STyp (_, cPhi), cPsi)), _) ->
          fprintf ppf "[%a %s %a]"
            (fmt_ppr_lf_dctx cD 0) cPsi
            (symbol_to_html Turnstile)
            (fmt_ppr_lf_dctx cD 0) cPhi
          (* fprintf ppf "{%s :: %a[%a]}"
            (Id.render_name u)
            (fmt_ppr_lf_dctx cD 0) cPhi
            (fmt_ppr_lf_dctx cD 0) cPsi
 *)
      | LF.Decl (name, (_,LF.CTyp schemaName), _) ->
          fprintf ppf "{%s : %s}"
            (Id.render_name name)
            (to_html (Id.render_name schemaName) Link)

    (* Computation-level *)
    let rec fmt_ppr_cmp_kind cD lvl ppf = function
      | Comp.Ctype _ -> fprintf ppf "%s" (to_html "ctype" Keyword)
      | Comp.PiKind (_, ctyp_decl, cK) ->
          let ctyp_decl = fresh_name_ctyp_decl cD ctyp_decl in
          let cond = lvl > 1 in
            fprintf ppf "%s%a %s %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_ctyp_decl cD 1) ctyp_decl
              (symbol_to_html RArr)
              (fmt_ppr_cmp_kind (LF.Dec(cD, ctyp_decl)) 1) cK
              (r_paren_if cond)

    let rec fmt_ppr_meta_spine cD lvl ppf = function
      | Comp.MetaNil ->
          fprintf ppf ""
      | Comp.MetaApp (mO, mS) ->
          fprintf ppf " %a%a"
            (fmt_ppr_meta_obj  cD (lvl + 1)) mO
            (fmt_ppr_meta_spine   cD lvl) mS

    (* TODO: Refactor *)
    and fmt_ppr_meta_obj cD lvl ppf (_loc,cM) = match cM with
      | Comp.CObj cPsi ->
            fprintf ppf "[%a]"
              (fmt_ppr_lf_dctx cD 0) cPsi
      | Comp.ClObj (cPsi, Comp.MObj tM) ->
          let cond = lvl > 1 in
            fprintf ppf "%s[%a %s %a]%s"
              (l_paren_if cond)
              (fmt_ppr_lf_dctx cD 0) cPsi
              (symbol_to_html Turnstile)
              (fmt_ppr_lf_normal cD cPsi 0) tM
              (r_paren_if cond)
      | Comp.ClObj (cPsi, Comp.SObj (LF.EmptySub _)) ->
            fprintf ppf "[%a %s ^]"
               (fmt_ppr_lf_dctx cD 0) cPsi
               (symbol_to_html Turnstile)
      | Comp.ClObj (cPsi, Comp.SObj sigma) ->
            fprintf ppf "[%a %s %a]"
               (fmt_ppr_lf_dctx cD 0) cPsi
               (symbol_to_html Turnstile)
              (fmt_ppr_lf_sub_bare cD cPsi 0) sigma
      | Comp.ClObj (cPsi, Comp.PObj h) ->
            fprintf ppf "[%a %s %a]"
               (fmt_ppr_lf_psi_hat cD 0) cPsi
               (symbol_to_html Turnstile)
              (fmt_ppr_lf_head cD cPsi 0) h

    let rec fmt_ppr_cmp_typ cD lvl ppf = function
      | Comp.TypBase (_, x, mS)->
            fprintf ppf "%s%a"
              (to_html (Id.render_name x) Link)
              (fmt_ppr_meta_spine cD 0) mS


      | Comp.TypBox (_, (_,LF.ClTyp (LF.MTyp tA, cPsi))) ->
          fprintf ppf "[%a %s %a]"
            (fmt_ppr_lf_dctx cD 0) cPsi
            (symbol_to_html Turnstile)
            (fmt_ppr_lf_typ cD cPsi 0) tA

      | Comp.TypBox (_, (_,LF.ClTyp (LF.PTyp tA, cPsi))) ->
          fprintf ppf "#[%a %s %a]"
            (fmt_ppr_lf_dctx cD 0) cPsi
            (symbol_to_html Turnstile)
            (fmt_ppr_lf_typ cD cPsi 0) tA

      | Comp.TypBox (_, (_,LF.CTyp x)) ->
            fprintf ppf "%s"
              (to_html (Id.render_name x) Link)

      | Comp.TypBox (_, (_,LF.ClTyp (LF.STyp (_,cPhi), cPsi))) ->
          fprintf ppf "[%a %s %a]"
            (fmt_ppr_lf_dctx cD 0) cPsi
            (symbol_to_html Turnstile)
            (fmt_ppr_lf_dctx cD 0) cPhi

      | Comp.TypArr (_, tau1, tau2) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a %s %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_typ cD (lvl + 1)) tau1
              (symbol_to_html RArr)
              (fmt_ppr_cmp_typ cD 0) tau2
              (r_paren_if cond)

      | Comp.TypCross (_, tau1, tau2) ->
          fprintf ppf "(%a * %a)"
            (fmt_ppr_cmp_typ cD 0) tau1
            (fmt_ppr_cmp_typ cD 0) tau2
      | Comp.TypPiBox (_loc, (LF.Decl(name, (l,LF.CTyp schema), LF.Maybe) as cdecl), tau) ->
          let cdecl = fresh_name_ctyp_decl cD cdecl in
          let cond = lvl > 1 in
            fprintf ppf "%s(%s:%s) %a%s"
              (l_paren_if cond)
              (Id.render_name name)
              (to_html (Id.render_name schema) Link)
              (fmt_ppr_cmp_typ (LF.Dec(cD, cdecl)) 0) tau
              (r_paren_if cond)

      | Comp.TypPiBox (_, ctyp_decl, tau) ->
          let ctyp_decl = fresh_name_ctyp_decl cD ctyp_decl in
          let cond = lvl > 1 in
            fprintf ppf "%s%a %a%s"
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
              (to_html (Id.render_name x) Link)
              (fmt_ppr_pat_spine cD 2) pat_spine
              (r_paren_if cond)

      | Comp.PatPair (_, pat1, pat2) ->
          fprintf ppf "(%a , %a)"
            (fmt_ppr_pat_obj cD 0) pat1
            (fmt_ppr_pat_obj cD 0) pat2
      | Comp.PatTrue _ -> fprintf ppf "tt"
      | Comp.PatFalse _ -> fprintf ppf "ff"
      | Comp.PatAnn (_, pat, tau) ->
          fprintf ppf "%a : %a"
            (fmt_ppr_pat_obj cD 0) pat
            (fmt_ppr_cmp_typ cD 0) tau

      | Comp.PatVar (_, x) ->
          fprintf ppf "%s"
            (Id.render_name x)


    let rec fmt_ppr_cmp_exp_chk cD lvl ppf = function
      | Comp.Syn (_, i) ->
          fmt_ppr_cmp_exp_syn cD lvl ppf i

      | Comp.Fun (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%s %s %s %a%s"
              (l_paren_if cond)
              (to_html "fn" Keyword)
              (Id.render_name x)
              (symbol_to_html DblRArr)
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond);

      | Comp.Cofun (_, l) ->
          fprintf ppf "Some Cofun"

      | Comp.MLam (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%s %s %s %a%s"
              (l_paren_if cond)
              (to_html "mlam" Keyword)
              (Id.render_name x)
              (symbol_to_html DblRArr)
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond);

      | Comp.Pair (_, e1, e2) ->
            fprintf ppf "(%a , %a)"
              (fmt_ppr_cmp_exp_chk cD 0) e1
              (fmt_ppr_cmp_exp_chk cD 0) e2


      | Comp.LetPair(_, i, (x, y, e)) ->
          let cond = lvl > 1 in
            fprintf ppf "@[%s%s <%s,%s> =@ %a %s %a%s@]"
              (l_paren_if cond)
              (to_html "let" Keyword)
              (Id.render_name x)
              (Id.render_name y)
              (fmt_ppr_cmp_exp_syn cD 0) i
              (to_html "in" Keyword)
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond)

      | Comp.Let(_, i, (x, e)) ->
          let cond = lvl > 1 in
            fprintf ppf "@[%s%s %s =@ %a %s@ %a%s@]"
              (l_paren_if cond)
              (to_html "let" Keyword)
              (Id.render_name x)
              (fmt_ppr_cmp_exp_syn cD 0) i
              (to_html "in" Keyword)
              (fmt_ppr_cmp_exp_chk cD 0) e
              (r_paren_if cond)

      | Comp.Box (_ , m) ->
            fprintf ppf "(Box %a)"
              (fmt_ppr_meta_obj  cD 0) m


      | Comp.Case (_, Pragma.RegularCase, i, [b]) ->
        begin match b with
          | Comp.Branch(_, cD', Comp.PatMetaObj(_, m0), e) ->
              fprintf ppf "@[<0>%s %a %a =@ %a %s@ @]%a"
                (to_html "let" Keyword)
                (fmt_ppr_cmp_branch_prefix 0) cD'
                (fmt_ppr_meta_obj cD' 0) m0
                (fmt_ppr_cmp_exp_syn cD' 0) i
                (to_html "in" Keyword)
                (fmt_ppr_cmp_exp_chk cD' 0) e
          | Comp.Branch(_, cD', pat, e) ->
              fprintf ppf "@[%s %a %a=@ %a %s@ @]%a"
                (to_html "let" Keyword)
                (fmt_ppr_cmp_branch_prefix  0) cD'
                (fmt_ppr_pat_obj cD' 0) pat
                (fmt_ppr_cmp_exp_syn cD' 0) i
                (to_html "in" Keyword)
                (fmt_ppr_cmp_exp_chk cD' 0) e
          | _ ->
            fprintf ppf "%s %a %s%a"
              (to_html "case" Keyword)
              (fmt_ppr_cmp_exp_syn cD 0) i
              (to_html "of" Keyword)
              (fmt_ppr_cmp_branches cD 0) [b]
        end

      | Comp.Case (_, prag, i, bs) ->
            fprintf ppf "%s %a %s %s%a"
              (to_html "case" Keyword)
              (fmt_ppr_cmp_exp_syn cD 0) i
              (to_html "of" Keyword)
              (match prag with Pragma.RegularCase -> "" | Pragma.PragmaNotCase -> (to_html " %not " Keyword))
              (fmt_ppr_cmp_branches cD 0) bs

      | Comp.If (_, i, e1, e2) ->
          let cond = lvl > 1 in
            fprintf ppf "@[<2>%s%s %a @[<-1>%s %a @]%s %a%s@]"
              (l_paren_if cond)
              (to_html "if" Keyword)
              (fmt_ppr_cmp_exp_syn cD 0) i
              (to_html "then" Keyword)
              (fmt_ppr_cmp_exp_chk cD 0) e1
              (to_html "else" Keyword)
              (fmt_ppr_cmp_exp_chk cD 0) e2
              (r_paren_if cond)

      | Comp.Hole (_) -> fprintf ppf " ? "

    and fmt_ppr_cmp_exp_syn cD lvl ppf = function
      | Comp.Var(_, x) ->
          fprintf ppf "(Var %s)"
            (to_html (Id.render_name x) LinkOption)

      | Comp.Const (_, x) ->
          fprintf ppf "(Const %s)"
            (to_html (Id.render_name x) LinkOption)

      | Comp.DataConst (_, x) ->
          fprintf ppf "(DataConst %s)"
            (to_html (Id.render_name x) LinkOption)

      | Comp.Apply (_, i, e) ->
          let cond = lvl > 1 in
            fprintf ppf "%s(Apply %a (%a))%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn cD 1) i
              (fmt_ppr_cmp_exp_chk cD 2) e
              (r_paren_if cond)

      | Comp.BoxVal (_, m0) ->
          let cond = lvl > 1 in
            fprintf ppf "%s(BoxVal %a)%s"
              (l_paren_if cond)
              (fmt_ppr_meta_obj cD 0) m0
              (r_paren_if cond)

      | Comp.Ann (_, e, tau) ->
          let cond = lvl > 1 in
            fprintf ppf "%s(Ann %a : %a)%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_chk cD 1) e
              (fmt_ppr_cmp_typ cD 2) tau
              (r_paren_if cond)

      | Comp.PairVal(_, i1, i2) ->
          fprintf ppf "(PairVal (%a , %a))"
            (fmt_ppr_cmp_exp_syn cD 1) i1
            (fmt_ppr_cmp_exp_syn cD 1) i2


      | Comp.Equal (_, i1, i2) ->
            fprintf ppf "(Equal %a == %a)"
              (fmt_ppr_cmp_exp_syn cD 1) i1
              (fmt_ppr_cmp_exp_syn cD 1) i2

      | Comp.Boolean (_, true) ->
          fprintf ppf "(True %s)"
            (to_html "ttrue" Keyword)

      | Comp.Boolean (_, false) ->
          fprintf ppf "(False %s)"
            (to_html "ffalse" Keyword)

    and fmt_ppr_cmp_branch_prefix _lvl ppf = function
      | LF.Empty -> ()
      | other ->
          (let rec fmt_ppr_ctyp_decls' ppf = function
            | LF.Dec (LF.Empty, decl) ->
                fprintf ppf "%a"
                  (fmt_ppr_lf_ctyp_decl LF.Empty 1) decl
            | LF.Dec (cD, decl) ->
                fprintf ppf "%a@ %a"
                  (fmt_ppr_ctyp_decls') cD
                  (fmt_ppr_lf_ctyp_decl cD 1) decl
          in
            fprintf ppf "@[%a@] " (fmt_ppr_ctyp_decls') other
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

    and fmt_ppr_patternOpt cD1' cPsi ppf = function
      | Some tM -> fmt_ppr_lf_normal cD1' cPsi 0 ppf tM
      | None ->fprintf ppf "@[{}@]"

    and fmt_ppr_cmp_branch cD _lvl ppf = function
      | Comp.EmptyBranch (_, cD1, pat) ->
          fprintf ppf "@\n@[<hov2>| @[%a[%a]@]@]"
            (fmt_ppr_cmp_branch_prefix  0) cD1
            (fmt_ppr_pat_obj cD1 0) pat

      | Comp.Branch (_, cD1', Comp.PatMetaObj (_, mO), e) ->
          fprintf ppf "@\n@[<hov2>| %a%a %s@ @[<v>%a@]@]"
            (fmt_ppr_cmp_branch_prefix  0) cD1'
            (fmt_ppr_meta_obj cD1' 0) mO
            (* NOTE: Technically: cD |- cG ctx and
             *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1|
             * -bp
             *)
            (symbol_to_html DblRArr)
            (fmt_ppr_cmp_exp_chk cD1' 0) e

      | Comp.Branch (_, cD1', pat, e) ->
          fprintf ppf "@\n@[<hov2>| %a%a %s@ @[<v>%a@]@]"
             (fmt_ppr_cmp_branch_prefix  0) cD1'
             (fmt_ppr_pat_obj cD1' 0) pat
             (symbol_to_html DblRArr)
             (fmt_ppr_cmp_exp_chk cD1' 0) e

    and fmt_ppr_cmp_gctx cD lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cG, LF.TypDecl (x, tau)) ->
          fprintf ppf "%a, %s: %a"
            (fmt_ppr_cmp_gctx cD 0) cG
            (Id.render_name x)
            (fmt_ppr_lf_typ cD LF.Null lvl) tau

    let total_to_string tdec = match tdec with
      | None -> ""
      | Some (Comp.Total (_ , order, f, args)) ->
      let rec args_to_string args = match args with
        | [] -> ""
        | Some n :: args' -> Id.render_name n ^ " " ^ args_to_string args'
        | None :: args' -> " _ " ^ args_to_string args'
      in
	(match order with
	  | Some (Comp.Arg n) ->
	      "/ total " ^ Id.render_name n ^ " ( " ^
		Id.render_name f ^ " " ^ args_to_string args ^ ") /"
	  | None ->
	      "/ total " ^ " ( " ^
		Id.render_name f ^ " " ^ args_to_string args ^ ") /"
	)

    let fmt_ppr_cmp_rec prefix lvl ppf = function
      | Comp.RecFun (_, x, total, a, e) ->
          fprintf ppf "@[<h>%s %s : %a %s@] =@[<v2>%a@]"
            (to_html prefix Keyword)
            (to_html (Id.render_name x) (ID Fun))
            (fmt_ppr_cmp_typ LF.Empty lvl)  a
            (total_to_string total)
            (fmt_ppr_cmp_exp_chk LF.Empty lvl)  e

    let fmt_ppr_rec lvl ppf = function
      | [] -> ()
      | h::t -> fmt_ppr_cmp_rec "rec" lvl ppf h;
                List.iter (fun x -> fmt_ppr_cmp_rec "and" lvl ppf x) t;
                fprintf ppf ";@ "

    let fmt_ppr_mrec prefix lvl ppf = function
      | Sgn.Typ(_, n, kA) ->
        fprintf ppf "%s %s : %a = "
          (to_html prefix Keyword)
          (to_html (Id.render_name n) (ID Typ))
          (fmt_ppr_lf_kind LF.Null 0) kA
      | Sgn.Const(_, n, tA) ->
          fprintf ppf "@\n| %s : %a"
            (to_html (Id.render_name n) (ID Constructor))
            (fmt_ppr_lf_typ LF.Empty LF.Null 0)  tA
      | Sgn.CompTyp(_, n, kA, _)
      | Sgn.CompCotyp(_, n, kA) ->
          fprintf ppf "%s %s : %a = "
            (to_html prefix Keyword)
            (to_html (Id.render_name n) (ID Typ))
            (fmt_ppr_cmp_kind LF.Empty 1) kA
      | Sgn.CompConst(_, n, tA)
      | Sgn.CompDest(_, n, tA) ->
        fprintf ppf "@\n| %s : %a"
          (to_html (Id.render_name n) (ID Constructor))
          (fmt_ppr_cmp_typ LF.Empty 1)  tA
      | _ -> ()

    (* TODO: Refactor this *)
    let fl_to_prefix = function
      | Sgn.CompTyp (_,_,_,_) -> "inductive"
      | Sgn.CompCotyp (_,_,_) -> "coinductive"
      | Sgn.Typ (_,_,_) -> "LF"
    let fmt_ppr_mrec' lvl ppf (k,body) =
      fmt_ppr_mrec (fl_to_prefix k) lvl ppf k;
      List.iter (fun d -> fmt_ppr_mrec "" lvl ppf d) body

    let rec fmt_ppr_mrecs lvl ppf = function
      | [h] -> fmt_ppr_mrec' lvl ppf h; fprintf ppf ";@\n"
      | h::t -> fmt_ppr_mrec' lvl ppf h;
	        fprintf ppf "and";
	        fmt_ppr_mrecs lvl ppf t

    let rec fmt_ppr_sgn_decl lvl ppf = function
      | Sgn.Const (_, x, a) ->
          fprintf ppf "@[<h>%s : %a.@]@\n"
            (to_html (Id.render_name x) (ID Constructor))
            (fmt_ppr_lf_typ LF.Empty LF.Null lvl)  a

      | Sgn.Typ (_, x, k) ->
          fprintf ppf "@[<h>%s : %a.@]@\n"
            (to_html (Id.render_name x) (ID Typ))
            (fmt_ppr_lf_kind LF.Null lvl) k

      | Sgn.CompConst (_, x, a) ->
          fprintf ppf "@[<h>| %s : %a@]@\n"
            (to_html (Id.render_name x) (ID Constructor))
            (fmt_ppr_cmp_typ LF.Empty lvl)  a

      | Sgn.CompTypAbbrev (_, x, k, a) ->
          fprintf ppf "@[<v>%s %s : %a =@ %a;@]@\n"
            (to_html "datatype" Keyword)
            (Id.render_name  x)
            (fmt_ppr_cmp_kind LF.Empty 0) k
            (fmt_ppr_cmp_typ LF.Empty 0)  a

      | Sgn.CompTyp (_, x, k, _) ->
          fprintf ppf "@[<v>%s %s : %a = @]@\n"
            (to_html "datatype" Keyword)
            (to_html (Id.render_name x) (ID Typ))
            (fmt_ppr_cmp_kind LF.Empty 0) k

      | Sgn.Schema (_, x, schema) ->
          fprintf ppf "@[<h>%s %s = %a;@]@\n"
            (to_html "schema" Keyword)
            (to_html (Id.render_name  x) (ID Schema))
            (fmt_ppr_lf_schema 0) schema

     | Sgn.Rec (_, lrec) ->
           (fmt_ppr_rec lvl ppf) lrec

      | Sgn.Pragma (_, Sgn.NamePrag(name, s, s_opt)) ->
         fprintf ppf "@[<h>%s %s %s %s@]@\n"
          (to_html "%name" Keyword) (Id.render_name name)
          s (match s_opt with None -> "" | Some x -> x)

      | Sgn.Val (_, x, None, i) ->
          fprintf ppf "@[%s %s = %a;@]@\n"
            (to_html "let" Keyword)
            (Id.render_name  x)
            (fmt_ppr_cmp_exp_syn LF.Empty lvl) i

      | Sgn.Val (_, x, Some(tA), i) ->
          fprintf ppf "@[%s %s : %a =@ %a;@]@\n"
            (to_html "let" Keyword)
            (Id.render_name  x)
            (fmt_ppr_cmp_typ LF.Empty 0) tA
            (fmt_ppr_cmp_exp_syn LF.Empty lvl) i

      | Sgn.Query _ ->
          fprintf ppf "%s"
          (to_html "query" Keyword)

      | Sgn.Module(_, name, decls) ->
          let aux fmt t = List.iter (fun x -> (fmt_ppr_sgn_decl lvl fmt x)) t in
          fprintf ppf "@[%s %s = %s@ @[<v2>%a@]@ %s;@]@\n"
                    (to_html "module" Keyword) (name) (to_html "struct" Keyword) (aux) decls (to_html "end" Keyword)
      | Sgn.MRecTyp(l, decls) ->
          fmt_ppr_mrecs 0 ppf decls
      | _ -> ()


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
