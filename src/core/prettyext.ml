open Support.Equality
(** Pretty printing for external syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html
*)

open Support
open Format
open Syntax.Ext

module Make (_ : Store.Cid.RENDERER) : Printer.Ext.T = struct
  include Prettycom

  type lvl = int
  let l0 = 0

  (* Contextual Format Based Pretty Printers
   *
   * We assume types, terms, etc are all in normal form.
   *)

  type id_type =
    | Constructor
    | Typ
    (* | Fun *)
    | Schema

  type html =
    | Keyword
    | ID of id_type
    | Link
    | LinkOption

  let to_html (s : string) (tag : html) : string =
    match tag with
    | _ when not !Html.printing -> s
    | Keyword -> "<keyword>" ^ s ^ "</keyword>"
    | ID Constructor -> Html.addId s; "<span class=\"constructor\" id=\"" ^ s ^ "\">" ^ s ^ "</span>"
    | ID Typ -> Html.addId s; "<span class=\"typ\" id=\"" ^ s ^ "\">" ^ s ^ "</span>"
    (* | ID Fun -> Html.addId s; "<span class=\"function\" id=\"" ^ s ^ "\">" ^ s ^ "</span>" *)
    | ID Schema -> "<span class=\"schema\" id=\"" ^ s ^ "\">" ^ s ^ "</span>"
    | Link -> "<a href=\"#" ^ s ^ "\">" ^ s ^ "</a>"
    | LinkOption when Html.idExists s -> "<a href=\"#" ^ s ^ "\">" ^ s ^ "</a>"
    | LinkOption -> s

  let iteri f =
    let rec iteri' i =
      function
      | [] -> ()
      | x::xs -> (f i x); iteri' (i+1) xs
    in iteri' 0

  type symbol =
    | Turnstile
    | RArr
    | DblRArr
    | Dots
    | Lam

  let symbol_to_html : symbol -> string =
    let f s1 s2 =
      if !Html.printing
      then s1
      else s2
    in
    function
    | Turnstile -> f "&#x22A2" "|-"
    | RArr -> f "&#x2192" "->"
    | DblRArr -> f "&#x21D2" "=>"
    | Dots -> f "&hellip;" ".."
    | Lam -> f "&lambda;" "\\"

  let rec fmt_ppr_lf_typ lvl ppf : LF.typ -> unit =
    function
    | LF.AtomTerm (_, n) -> fmt_ppr_lf_normal lvl ppf n

    | LF.Atom (_, a, LF.Nil) ->
       let name = to_html (Id.render_name a) Link in
       fprintf ppf "%s" name

    | LF.Atom (_, a, ms) ->
       let name = to_html (Id.render_name a) Link in
       fprintf ppf "%s%a"
         name
         (fmt_ppr_lf_spine 2) ms

    | LF.PiTyp (_, LF.TypDecl (x, a), (LF.ArrTyp _ as b)) ->
       let cond = lvl > 1 in
       let name = to_html (Id.render_name x) LinkOption in
       fprintf ppf "%s{%s : %a} %a%s"
         (l_paren_if cond)
         name
         (fmt_ppr_lf_typ 0) a
         (fmt_ppr_lf_typ 2) b
         (r_paren_if cond)
    | LF.PiTyp (_, LF.TypDecl (x, a), b) ->
       let cond = lvl > 1 in
       let name = to_html (Id.render_name x) LinkOption in
       fprintf ppf "%s{%s : %a} %a%s"
         (l_paren_if cond)
         name
         (fmt_ppr_lf_typ 0) a
         (fmt_ppr_lf_typ lvl) b
         (r_paren_if cond)

    | LF.Sigma (_, typRec) ->
       fprintf ppf "%s (%a)"
         (to_html "block" Keyword)
         fmt_ppr_lf_typ_rec typRec

    | LF.ArrTyp (_, (LF.PiTyp _ as t1), t2) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a %s %a%s"
         (l_paren_if cond)
         (fmt_ppr_lf_typ 2) t1
         (symbol_to_html RArr)
         (fmt_ppr_lf_typ 0) t2
         (r_paren_if cond)

    | LF.ArrTyp (_, (LF.ArrTyp _ as t1), t2) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a %s %a%s"
         (l_paren_if cond)
         (fmt_ppr_lf_typ 2) t1
         (symbol_to_html RArr)
         (fmt_ppr_lf_typ 0) t2
         (r_paren_if cond)

    | LF.ArrTyp (_, t1, t2) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a %s %a%s"
         (l_paren_if cond)
         (fmt_ppr_lf_typ 0) t1
         (symbol_to_html RArr)
         (fmt_ppr_lf_typ 0) t2
         (r_paren_if cond)

    | LF.Ctx   (_, cPsi)  ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a%s"
         (l_paren_if cond)
         (fmt_ppr_lf_dctx 0) cPsi
         (r_paren_if cond)



  and fmt_ppr_tuple lvl ppf =
    function
    | LF.Last tM ->
       fmt_ppr_lf_normal lvl ppf tM

    | LF.Cons (tM, rest) ->
       fprintf ppf "%a, %a"
         (fmt_ppr_lf_normal lvl) tM
         (fmt_ppr_tuple lvl) rest (* the level should probably change here? -je *)

  and fmt_ppr_lf_normal lvl ppf =
    let deimplicitize_spine _ ms = ms in
    function
    | LF.Lam (_, x, m) ->
       let cond = lvl > 0 in
       fprintf ppf "%s%s%s. %a%s"
         (l_paren_if cond)
         (symbol_to_html Lam)
         (Id.render_name x)
         (fmt_ppr_lf_normal 0) m
         (r_paren_if cond)

    | LF.Tuple (_, tuple) ->
       fprintf ppf "<%a>"
         (fmt_ppr_tuple lvl) tuple

    | LF.Root (_, h, LF.Nil) ->
       fprintf ppf "%a"
         (fmt_ppr_lf_head lvl) h

    | LF.Root (_, h, ms)  ->
       let cond = lvl > 1 in
       let ms = deimplicitize_spine h ms in
       fprintf ppf "%s%a%a%s"
         (l_paren_if cond)
         (fmt_ppr_lf_head lvl) h
         (fmt_ppr_lf_spine 2)  ms
         (r_paren_if cond)

    | LF.LFHole _ ->
       fprintf ppf "?"

    | LF.NTyp (u, tA)-> fmt_ppr_lf_typ lvl ppf tA

    | LF.TList (_, [x]) -> fmt_ppr_lf_normal lvl ppf x
    | LF.TList (_, l) ->
       let length = List.length l in
       fprintf ppf "%s" (l_paren_if (lvl > 0));
       l
       |> iteri
            begin fun i x ->
            if i = length - 1
            then fprintf ppf "%a" (fmt_ppr_lf_normal (lvl + 1)) x
            else fprintf ppf "%a " (fmt_ppr_lf_normal (lvl + 1)) x
            end;
       fprintf ppf "%s" (r_paren_if (lvl > 0));
    | LF.PatEmpty _ -> fprintf ppf "{}"

  and fmt_ppr_lf_head lvl ppf head =
    let paren s = lvl > 0 && true in
    match head with
    | LF.PVar (_,  x, s) ->
       fprintf ppf "%s%s%a%s"
         (l_paren_if (paren s))
         (Id.render_name x)
         (Option.print
            (fun ppf sub ->
              fprintf ppf "[%a]"
                (fmt_ppr_lf_sub 0) sub))
         s
         (r_paren_if (paren s))

    | LF.Name (_, x, s) ->
       fprintf ppf "%s%a"
         (to_html (Id.render_name x) LinkOption)
         (Option.print
            (fun ppf sub ->
              fprintf ppf "[%a]"
                (fmt_ppr_lf_sub 0) sub))
         s

    | LF.Hole (_) ->
       fprintf ppf "_"

    | LF.Proj (_, (LF.Name _ as h), p) ->
       fprintf ppf "%a.%a"
         (fmt_ppr_lf_head lvl) h
         (fmt_ppr_lf_proj lvl) p

    | LF.Proj (_, LF.PVar (_,  x, s), p) ->
       fprintf ppf "%s.%a%a"
         (Id.render_name x)
         (fmt_ppr_lf_proj lvl) p
         (fmt_ppr_lf_sub_opt lvl) s

  and fmt_ppr_lf_proj lvl ppf =
    function
    | LF.ByName n -> fprintf ppf "%s" (Id.render_name n)
    | LF.ByPos k -> fprintf ppf "%d" k

  and fmt_ppr_lf_spine lvl ppf =
    function
    | LF.Nil ->
       fprintf ppf ""

    | LF.App (_, m, ms) ->
       fprintf ppf " %a%a"
         (fmt_ppr_lf_normal (lvl + 1)) m
         (fmt_ppr_lf_spine  lvl) ms

  (** Renders the given substitution in brackets, if it exists.
      Otherwise prints nothing.
   *)
  and fmt_ppr_lf_sub_opt lvl =
    Option.print
      begin fun ppf sub ->
      fprintf ppf "[%a]"
        (fmt_ppr_lf_sub lvl) sub
      end

  (** Prints a substitution.
      `pp_empty' is a printing function that prints the empty
      substitution. By default this prints nothing, and returns
      false. However, if you want to print the empty substitution as
      something else, e.g. `^', then you can override this and
      return true.
   *)
  and fmt_ppr_lf_sub ?(pp_empty = fun _ _ -> false) lvl (ppf : Format.formatter) (start, tms : LF.sub) =
    let print_tm = fmt_ppr_lf_normal 1 in
    let print_svar s s_opt =
      fprintf ppf "%s%a"
        (Id.render_name s)
        (Option.print
           begin fun ppf sub ->
           fprintf ppf "[%a]"
             (fmt_ppr_lf_sub ~pp_empty: (fun ppf () -> fprintf ppf "^"; true) 0) sub
           end) s_opt
    in
    let go ppf () =
      let nonempty =
        (* print the beginning of the substitution and give a boolean
           indicating whether some output was actually generated.
           This is so after we can correctly generate a comma.
         *)
        match start with
        | LF.EmptySub _ -> pp_empty ppf ()
        | LF.Id _ ->
           fprintf ppf "%s" (symbol_to_html Dots);
           true
        | LF.SVar (_, s, sub') ->
           print_svar s sub';
           true
      in

      (* then check if the list of terms is nonempty;
         if it is: print a comma, then each term comma-separated.
         else, just print each term comma-separated *)

      if nonempty && List.nonempty tms
      then Fmt.comma ppf ();

      pp_print_list ~pp_sep: Fmt.comma
        print_tm ppf tms;
    in

    fprintf ppf "@[<h>%a@]" go ();

  and fmt_ppr_lf_typ_rec ppf typrec =
    let ppr_element ppf suffix (x, tA) =
      fprintf ppf "%s:%a%s"
        (Id.render_name x)
        (fmt_ppr_lf_typ 0) tA
        suffix
    in
    let rec ppr_elements ppf =
      function
      | LF.SigmaLast (Some x, tA) -> ppr_element ppf "" (x, tA)
      | LF.SigmaLast (None, tA) -> fmt_ppr_lf_typ 0 ppf tA
      | LF.SigmaElem (x, tA, tAs)  ->
         ppr_element ppf ", " (x, tA);
         ppr_elements ppf tAs
    in
    ppr_elements ppf typrec

  and projectCtxIntoDctx =
    function
    | LF.Empty -> LF.Null
    | LF.Dec (rest, last) -> LF.DDec (projectCtxIntoDctx rest, last)

  and fmt_ppr_lf_schema lvl ppf =
    function
    | LF.Schema [] -> ()

    | LF.Schema (f :: []) ->
       fprintf ppf "%a"
         (fmt_ppr_lf_sch_elem lvl) f

    | LF.Schema (f :: fs) ->
       fprintf ppf "@[%a@] + @[%a@]"
         (fmt_ppr_lf_sch_elem lvl) f
         (fmt_ppr_lf_schema lvl) (LF.Schema fs)

  and frugal_block cD cPsi lvl ppf =
    function
    | LF.SigmaLast (_, tA) -> fmt_ppr_lf_typ 0 ppf tA
    | other ->
       fprintf ppf "%s (%a)"
         (to_html "block" Keyword)
         fmt_ppr_lf_typ_rec other

  and fmt_ppr_lf_sch_elem lvl ppf =
    function
    | LF.SchElem (_, LF.Empty, sgmDecl) ->
       fprintf ppf "%a"
         (frugal_block LF.Empty LF.Null lvl) sgmDecl

    | LF.SchElem (_, typDecls, sgmDecl) ->
       let cPsi = projectCtxIntoDctx typDecls in
       fprintf ppf "%s [%a] %a"
         (to_html "some" Keyword)
         (ppr_typ_decl_dctx  LF.Empty)  cPsi
         (frugal_block LF.Empty cPsi lvl) sgmDecl


  and ppr_typ_decl_dctx cD ppf =
    function
    | LF.Null ->
       fprintf ppf ""

    | LF.DDec (LF.Null, LF.TypDecl (x, tA)) ->
       fprintf ppf "%s : %a"    (* formerly "., %s : %a"    -jd 2010-06-03 *)
         (Id.render_name x)
         (fmt_ppr_lf_typ 0) tA

    | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
       fprintf ppf "%a, %s : %a"
         (ppr_typ_decl_dctx cD) cPsi
         (Id.render_name x)
         (fmt_ppr_lf_typ 0) tA

    | LF.CtxVar (_, x) ->
       fprintf ppf "%s"
         (Id.render_name x)


  and fmt_ppr_lf_dctx_hat ppf =
    function
    | LF.Null -> fprintf ppf ""

    | LF.CtxVar (_, x) -> (***)
       fprintf ppf "%s"
         (Id.render_name x)

    | LF.DDec (LF.Null, LF.TypDecl (x, _)) ->
       fprintf ppf "%s"
         (Id.render_name x)

    | LF.DDec (cPsi, LF.TypDecl (x, _)) ->
       fprintf ppf "%s, %a"
         (Id.render_name x)
         fmt_ppr_lf_dctx_hat cPsi

  and fmt_ppr_lf_typ_decl lvl ppf =
    function
    | LF.TypDecl (x, tA) ->
       fprintf ppf "%s : %a"
         (Id.render_name x)
         (fmt_ppr_lf_typ lvl) tA
    | LF.TypDeclOpt x ->
       fprintf ppf "%s" (Id.render_name x)

  and fmt_ppr_lf_dctx lvl ppf =
    function
    | LF.CtxHole -> fprintf ppf "_"
    | LF.Null ->
       fprintf ppf ""

    | LF.CtxVar (_, x) ->
       fprintf ppf "%s"
         (Id.render_name x)

    | LF.DDec (LF.Null, d) ->
       fmt_ppr_lf_typ_decl lvl ppf d

    | LF.DDec (cPsi, d) ->
       fprintf ppf "%a, %a"
         (fmt_ppr_lf_dctx 0) cPsi
         (fmt_ppr_lf_typ_decl lvl) d

  and fmt_ppr_lf_mctx ?(sep = Fmt.comma) lvl ppf =
    function
    | LF.Empty ->
       fprintf ppf "."

    | cD ->
       fprintf ppf "%a"
         (pp_print_list ~pp_sep: sep
            (fun ppf (cD, d) -> fmt_ppr_lf_ctyp_decl ppf d))
         (Context.to_sublist_rev cD);

  and fmt_ppr_lf_kind lvl ppf =
    function
    | LF.Typ _ ->
       fprintf ppf "%s"
         (to_html "type" Keyword)

    | LF.PiKind (_, LF.TypDecl (x, a), k) ->
       let cond = lvl > 0 in
       let name = Id.render_name x in
       fprintf ppf "%s{%s : %a} %a%s"
         (l_paren_if cond)
         (name)
         (fmt_ppr_lf_typ 0) a
         (fmt_ppr_lf_kind 0) k
         (r_paren_if cond)

    | LF.ArrKind (_, a, k) ->
       let cond = lvl > 0 in
       fprintf ppf "%s%a %s %a%s"
         (l_paren_if cond)
         (fmt_ppr_lf_typ 0) a
         (symbol_to_html RArr)
         (fmt_ppr_lf_kind 0) k
         (r_paren_if cond)

  and fmt_ppr_lf_ctyp_decl (ppf : formatter) : LF.ctyp_decl -> unit =
    function
    | LF.Decl (u, (_, LF.ClTyp (LF.MTyp tA, cPsi)), _) ->
       fprintf ppf "{%s : [%a %s %a]}"
         (Id.render_name u)
         (fmt_ppr_lf_dctx 0) cPsi
         (symbol_to_html Turnstile)
         (fmt_ppr_lf_typ 0) tA
    (*           fprintf ppf "{%s :: %a[%a]}"
                 (Id.render_name u)
                 (fmt_ppr_lf_typ cD cPsi 2) tA
                 (fmt_ppr_lf_dctx cD 0) cPsi
     *)
    | LF.Decl (p, (_, LF.ClTyp (LF.PTyp tA, cPsi)), _) ->
       fprintf ppf "{#%s : [%a %s %a]}"
         (Id.render_name p)
         (fmt_ppr_lf_dctx 0) cPsi
         (symbol_to_html Turnstile)
         (fmt_ppr_lf_typ 0) tA
    (* fprintf ppf "{#%s :: %a[%a]}"
       (Id.render_name p)
       (fmt_ppr_lf_typ cD cPsi 2) tA
       (fmt_ppr_lf_dctx cD 0) cPsi *)

    | LF.Decl (u, (_, LF.ClTyp (LF.STyp (_, cPhi), cPsi)), _) ->
       fprintf ppf "[%a %s %a]"
         (fmt_ppr_lf_dctx 0) cPsi
         (symbol_to_html Turnstile)
         (fmt_ppr_lf_dctx 0) cPhi
    (* fprintf ppf "{%s :: %a[%a]}"
       (Id.render_name u)
       (fmt_ppr_lf_dctx cD 0) cPhi
       (fmt_ppr_lf_dctx cD 0) cPsi
     *)
    | LF.Decl (name, (_, LF.CTyp schemaName), _) ->
       fprintf ppf "{%s : %s}"
         (Id.render_name name)
         (to_html (Id.render_name schemaName) Link)

  (* Computation-level *)
  let rec fmt_ppr_cmp_kind lvl ppf =
    function
    | Comp.Ctype _ -> fprintf ppf "%s" (to_html "ctype" Keyword)
    | Comp.PiKind (_, ctyp_decl, cK) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a %s %a%s"
         (l_paren_if cond)
         (fmt_ppr_lf_ctyp_decl) ctyp_decl
         (symbol_to_html RArr)
         (fmt_ppr_cmp_kind 1) cK
         (r_paren_if cond)

  let rec fmt_ppr_meta_spine lvl ppf =
    function
    | Comp.MetaNil ->
       fprintf ppf ""
    | Comp.MetaApp (mO, mS) ->
       fprintf ppf " %a%a"
         (fmt_ppr_cmp_meta_obj (lvl + 1)) mO
         (fmt_ppr_meta_spine lvl) mS

  and fmt_ppr_lf_mfront lvl ppf =
    function
    | LF.CObj cPsi ->
       fprintf ppf "[%a]"
         (fmt_ppr_lf_dctx 0) cPsi
    | LF.ClObj (cPsi, ms) ->
       let cond = lvl > 1 in
       fprintf ppf "%s[%a %s %a]%s"
         (l_paren_if cond)
         (fmt_ppr_lf_dctx 0) cPsi
         (symbol_to_html Turnstile)
         (fmt_ppr_lf_sub 0) ms
         (r_paren_if cond)

  (* TODO: Refactor *)
  and fmt_ppr_cmp_meta_obj lvl ppf (_, cM) =
    fmt_ppr_lf_mfront lvl ppf cM

  let rec fmt_ppr_cmp_typ lvl ppf =
    function
    | Comp.TypBase (_, x, mS)->
       fprintf ppf "%s%a"
         (to_html (Id.render_name x) Link)
         (fmt_ppr_meta_spine 0) mS


    | Comp.TypBox (_, (_, LF.ClTyp (LF.MTyp tA, cPsi))) ->
       fprintf ppf "[%a %s %a]"
         (fmt_ppr_lf_dctx 0) cPsi
         (symbol_to_html Turnstile)
         (fmt_ppr_lf_typ 0) tA

    | Comp.TypBox (_, (_, LF.ClTyp (LF.PTyp tA, cPsi))) ->
       fprintf ppf "#[%a %s %a]"
         (fmt_ppr_lf_dctx 0) cPsi
         (symbol_to_html Turnstile)
         (fmt_ppr_lf_typ 0) tA

    | Comp.TypBox (_, (_, LF.CTyp x)) ->
       fprintf ppf "%s"
         (to_html (Id.render_name x) Link)

    | Comp.TypBox (_, (_, LF.ClTyp (LF.STyp (_, cPhi), cPsi))) ->
       fprintf ppf "[%a %s %a]"
         (fmt_ppr_lf_dctx 0) cPsi
         (symbol_to_html Turnstile)
         (fmt_ppr_lf_dctx 0) cPhi

    | Comp.TypArr (_, tau1, tau2) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a %s %a%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_typ (lvl + 1)) tau1
         (symbol_to_html RArr)
         (fmt_ppr_cmp_typ 0) tau2
         (r_paren_if cond)

    | Comp.TypCross (_, tau1, tau2) ->
       fprintf ppf "(%a * %a)"
         (fmt_ppr_cmp_typ 0) tau1
         (fmt_ppr_cmp_typ 0) tau2
    | Comp.TypPiBox (_, LF.Decl (name, (l, LF.CTyp schema), LF.Maybe), tau) ->
       let cond = lvl > 1 in
       fprintf ppf "%s(%s:%s) %a%s"
         (l_paren_if cond)
         (Id.render_name name)
         (to_html (Id.render_name schema) Link)
         (fmt_ppr_cmp_typ 0) tau
         (r_paren_if cond)

    | Comp.TypPiBox (_, ctyp_decl, tau) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a %a%s"
         (l_paren_if cond)
         fmt_ppr_lf_ctyp_decl ctyp_decl
         (fmt_ppr_cmp_typ 1) tau
         (r_paren_if cond)

  let rec fmt_ppr_pat_spine lvl ppf =
    function
    | Comp.PatNil _ -> fprintf ppf ""
    | Comp.PatApp (_, pat, pat_spine) ->
       fprintf ppf "%a %a"
         (fmt_ppr_pat_obj (lvl+1)) pat
         (fmt_ppr_pat_spine lvl) pat_spine
    | Comp.PatObs (_, x, pat_spine) ->
       fprintf ppf "%s %a"
         (Id.render_name x)
         (fmt_ppr_pat_spine lvl) pat_spine


  and fmt_ppr_pat_obj lvl ppf : Comp.pattern -> unit =
    function
    | Comp.PatMetaObj (_, mO) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_meta_obj 0) mO
         (r_paren_if cond)
    | Comp.PatName (_, x, pat_spine) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%s %a%s"
         (l_paren_if cond)
         (to_html (Id.render_name x) Link)
         (fmt_ppr_pat_spine 2) pat_spine
         (r_paren_if cond)

    | Comp.PatPair (_, pat1, pat2) ->
       fprintf ppf "(%a , %a)"
         (fmt_ppr_pat_obj 0) pat1
         (fmt_ppr_pat_obj 0) pat2
    | Comp.PatAnn (_, pat, tau) ->
       fprintf ppf "%a : %a"
         (fmt_ppr_pat_obj 0) pat
         (fmt_ppr_cmp_typ 0) tau


  let rec fmt_ppr_cmp_exp_chk lvl ppf =
    function
    | Comp.Syn (_, i) ->
       fmt_ppr_cmp_exp_syn lvl ppf i

    | Comp.Fn (_, x, e) ->
       let cond = lvl > 0 in
       fprintf ppf "%s%s %s %s %a%s"
         (l_paren_if cond)
         (to_html "fn" Keyword)
         (Id.render_name x)
         (symbol_to_html DblRArr)
         (fmt_ppr_cmp_exp_chk 0) e
         (r_paren_if cond);

    | Comp.Fun (_, b) ->
       fprintf ppf "%s @[%a@]"
         (to_html "fun" Keyword)
         (fmt_ppr_cmp_fbranches lvl) b

    | Comp.MLam (_, x, e) ->
       let cond = lvl > 0 in
       fprintf ppf "%s%s %s %s %a%s"
         (l_paren_if cond)
         (to_html "mlam" Keyword)
         (Id.render_name x)
         (symbol_to_html DblRArr)
         (fmt_ppr_cmp_exp_chk 0) e
         (r_paren_if cond);

    | Comp.Pair (_, e1, e2) ->
       fprintf ppf "(%a , %a)"
         (fmt_ppr_cmp_exp_chk 0) e1
         (fmt_ppr_cmp_exp_chk 0) e2


    | Comp.LetPair (_, i, (x, y, e)) ->
       let cond = lvl > 1 in
       fprintf ppf "@[%s%s <%s,%s> =@ %a %s %a%s@]"
         (l_paren_if cond)
         (to_html "let" Keyword)
         (Id.render_name x)
         (Id.render_name y)
         (fmt_ppr_cmp_exp_syn 0) i
         (to_html "in" Keyword)
         (fmt_ppr_cmp_exp_chk 0) e
         (r_paren_if cond)

    | Comp.Let (_, i, (x, e)) ->
       let cond = lvl > 1 in
       fprintf ppf "@[%s%s %s =@ %a %s@ %a%s@]"
         (l_paren_if cond)
         (to_html "let" Keyword)
         (Id.render_name x)
         (fmt_ppr_cmp_exp_syn 0) i
         (to_html "in" Keyword)
         (fmt_ppr_cmp_exp_chk 0) e
         (r_paren_if cond)

    | Comp.Box (_, m) ->
       fprintf ppf "%a"
         (fmt_ppr_cmp_meta_obj  0) m


    | Comp.(Case (_, PragmaCase, i, [b])) ->
       begin match b with
       | Comp.Branch (_, cD', Comp.PatMetaObj (_, m0), e) ->
          fprintf ppf "@[<0>%s %a %a =@ %a %s@ @]%a"
            (to_html "let" Keyword)
            fmt_ppr_cmp_branch_prefix cD'
            (fmt_ppr_cmp_meta_obj 0) m0
            (fmt_ppr_cmp_exp_syn 0) i
            (to_html "in" Keyword)
            (fmt_ppr_cmp_exp_chk 0) e
       | Comp.Branch (_, cD', pat, e) ->
          fprintf ppf "@[%s %a %a=@ %a %s@ @]%a"
            (to_html "let" Keyword)
            fmt_ppr_cmp_branch_prefix cD'
            (fmt_ppr_pat_obj 0) pat
            (fmt_ppr_cmp_exp_syn 0) i
            (to_html "in" Keyword)
            (fmt_ppr_cmp_exp_chk 0) e
       end

    | Comp.Case (_, prag, i, bs) ->
       let open Comp in
       fprintf ppf "%s %a %s %s%a"
         (to_html "case" Keyword)
         (fmt_ppr_cmp_exp_syn 0) i
         (to_html "of" Keyword)
         begin match prag with
         | PragmaCase -> ""
         | PragmaNotCase -> to_html " %not " Keyword
         end
         fmt_ppr_cmp_branches bs

    | Comp.Hole _ -> fprintf ppf " ? "

    | Comp.BoxHole _ -> fprintf ppf " _ "

    | Comp.Impossible (_, i) ->
      fprintf ppf "%s %a"
        (to_html "impossible" Keyword)
        (fmt_ppr_cmp_exp_syn 0) i

  and fmt_ppr_cmp_exp_syn lvl ppf : Comp.exp_syn -> unit =
    function
    | Comp.Name (_, x) ->
       fprintf ppf "%s"
         (to_html (Id.render_name x) LinkOption)

    | Comp.Apply (_, i, e) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a %a%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_exp_syn 1) i
         (fmt_ppr_cmp_exp_chk 2) e
         (r_paren_if cond)

    | Comp.BoxVal (_, m0) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_meta_obj 0) m0
         (r_paren_if cond)

    | Comp.PairVal (_, i1, i2) ->
       fprintf ppf "(%a , %a)"
         (fmt_ppr_cmp_exp_syn 1) i1
         (fmt_ppr_cmp_exp_syn 1) i2


  and fmt_ppr_cmp_branch_prefix ppf : LF.mctx -> unit =
    function
    | LF.Empty -> ()
    | other ->
       let rec fmt_ppr_ctyp_decls' ppf =
         function
         | LF.Dec (LF.Empty, decl) ->
            fprintf ppf "%a"
              fmt_ppr_lf_ctyp_decl decl
         | LF.Dec (cD, decl) ->
            fprintf ppf "%a@ %a"
              fmt_ppr_ctyp_decls' cD
              fmt_ppr_lf_ctyp_decl decl
       in
       fprintf ppf "@[%a@] " (fmt_ppr_ctyp_decls') other

  and fmt_ppr_cmp_branches ppf : Comp.branch list -> unit =
    function
    | [] -> ()

    | b :: [] ->
       fprintf ppf "%a"
         fmt_ppr_cmp_branch b

    | b :: bs ->
       fprintf ppf "%a%a"
         fmt_ppr_cmp_branch b
         fmt_ppr_cmp_branches bs

  and fmt_ppr_cmp_fbranches lvl ppf =
    function
    | Comp.NilFBranch _ -> ()
    | Comp.ConsFBranch (_, (ps, e), Comp.NilFBranch _) ->
       fprintf ppf "%a%s@[%a@]"
         (fmt_ppr_pat_spine lvl) ps
         (symbol_to_html DblRArr)
         (fmt_ppr_cmp_exp_chk lvl) e
    | Comp.ConsFBranch (_, (ps, e), br) ->
       fprintf ppf "%a%s@[%a@]@\n@[<hov2>| %a"
         (fmt_ppr_pat_spine lvl) ps
         (symbol_to_html DblRArr)
         (fmt_ppr_cmp_exp_chk lvl) e
         (fmt_ppr_cmp_fbranches lvl) br

  and fmt_ppr_patternOpt ppf =
    function
    | Some tM -> fmt_ppr_lf_normal 0 ppf tM
    | None ->fprintf ppf "@[{}@]"

  and fmt_ppr_cmp_branch ppf : Comp.branch -> unit =
    function
    | Comp.Branch (_, cD1', Comp.PatMetaObj (_, mO), e) ->
       fprintf ppf "@\n@[<hov2>| %a%a %s@ @[<v>%a@]@]"
         fmt_ppr_cmp_branch_prefix cD1'
         (fmt_ppr_cmp_meta_obj 0) mO
         (* NOTE: Technically: |- cG ctx and
          *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1|
          * -bp
          *)
         (symbol_to_html DblRArr)
         (fmt_ppr_cmp_exp_chk 0) e

    | Comp.Branch (_, cD1', pat, e) ->
       fprintf ppf "@\n@[<hov2>| %a%a %s@ @[<v>%a@]@]"
         fmt_ppr_cmp_branch_prefix cD1'
         (fmt_ppr_pat_obj 0) pat
         (symbol_to_html DblRArr)
         (fmt_ppr_cmp_exp_chk 0) e

  (*
    and fmt_ppr_cmp_gctx cD lvl ppf = function
    | LF.Empty ->
    fprintf ppf "."

    | LF.Dec (cG, LF.TypDecl (x, tau)) ->
    fprintf ppf "%a, %s: %a"
    (fmt_ppr_cmp_gctx cD 0) cG
    (Id.render_name x)
    (fmt_ppr_lf_typ cD LF.Null lvl) tau
   *)

  let fmt_ppr_mrec prefix lvl ppf =
    function
    | Sgn.Typ (_, n, kA) ->
       fprintf ppf "%s %s : %a = "
         (to_html prefix Keyword)
         (to_html (Id.render_name n) (ID Typ))
         (fmt_ppr_lf_kind 0) kA
    | Sgn.Const (_, n, tA) ->
       fprintf ppf "@\n| %s : %a"
         (to_html (Id.render_name n) (ID Constructor))
         (fmt_ppr_lf_typ 0)  tA
    | Sgn.CompTyp (_, n, kA, _)
      | Sgn.CompCotyp (_, n, kA) ->
       fprintf ppf "%s %s : %a = "
         (to_html prefix Keyword)
         (to_html (Id.render_name n) (ID Typ))
         (fmt_ppr_cmp_kind 1) kA
    | Sgn.CompConst (_, n, tA) ->
       fprintf ppf "@\n| %s : %a"
         (to_html (Id.render_name n) (ID Constructor))
         (fmt_ppr_cmp_typ 1)  tA
    | Sgn.CompDest
      { identifier=n
      ; mctx=cD
      ; observation_typ=tA
      ; return_typ=tA'
      ; _
      } ->
       fprintf ppf "@\n| (%s : %a) :: %a"
         (to_html (Id.render_name n) (ID Constructor))
         (fmt_ppr_cmp_typ 1)  tA
         (fmt_ppr_cmp_typ 1)  tA'
    | _ -> ()

  (* TODO: Refactor this *)
  let fl_to_prefix =
    function
    | Sgn.CompTyp (_, _, _, _) -> "inductive"
    | Sgn.CompCotyp (_, _, _) -> "coinductive"
    | Sgn.Typ (_, _, _) -> "LF"

  let fmt_ppr_mrec' lvl ppf (k, body) =
    fmt_ppr_mrec (fl_to_prefix k) lvl ppf k;
    List.iter (fun d -> fmt_ppr_mrec "" lvl ppf d) body

  let rec fmt_ppr_mrecs lvl ppf =
    function
    | [h] -> fmt_ppr_mrec' lvl ppf h; fprintf ppf ";@\n"
    | h :: t -> fmt_ppr_mrec' lvl ppf h;
              fprintf ppf "@\n%s " (to_html "and" Keyword);
              fmt_ppr_mrecs lvl ppf t

  let rec fmt_ppr_sgn_decl ppf =
    function
    | Sgn.Const (_, x, a) ->
       fprintf ppf "@[<h>%s : %a.@]@\n"
         (to_html (Id.render_name x) (ID Constructor))
         (fmt_ppr_lf_typ l0)  a

    | Sgn.Typ (_, x, k) ->
       fprintf ppf "@[<h>%s : %a.@]@\n"
         (to_html (Id.render_name x) (ID Typ))
         (fmt_ppr_lf_kind l0) k

    | Sgn.CompConst (_, x, a) ->
       fprintf ppf "@[<h>| %s : %a@]@\n"
         (to_html (Id.render_name x) (ID Constructor))
         (fmt_ppr_cmp_typ l0)  a

    | Sgn.CompTypAbbrev (_, x, k, a) ->
       fprintf ppf "@[<v>%s %s : %a =@ %a;@]@\n"
         (to_html "datatype" Keyword)
         (Id.render_name  x)
         (fmt_ppr_cmp_kind 0) k
         (fmt_ppr_cmp_typ 0)  a

    | Sgn.CompTyp (_, x, k, _) ->
       fprintf ppf "@[<v>%s %s : %a = @]@\n"
         (to_html "datatype" Keyword)
         (to_html (Id.render_name x) (ID Typ))
         (fmt_ppr_cmp_kind 0) k

    | Sgn.Schema (_, x, schema) ->
       fprintf ppf "@[<h>%s %s = %a;@]@\n"
         (to_html "schema" Keyword)
         (to_html (Id.render_name  x) (ID Schema))
         (fmt_ppr_lf_schema 0) schema

    | Sgn.Pragma (_, Sgn.NamePrag (name, s, s_opt)) ->
       fprintf ppf "@[<h>%s %s %s %s@]@\n"
         (to_html "%name" Keyword)
         (Id.render_name name)
         s
         begin match s_opt with
         | None -> ""
         | Some x -> x
         end

    | Sgn.Val (_, x, None, i) ->
       fprintf ppf "@[%s %s = %a;@]@\n"
         (to_html "let" Keyword)
         (Id.render_name  x)
         (fmt_ppr_cmp_exp_syn l0) i

    | Sgn.Val (_, x, Some tA, i) ->
       fprintf ppf "@[%s %s : %a =@ %a;@]@\n"
         (to_html "let" Keyword)
         (Id.render_name  x)
         (fmt_ppr_cmp_typ 0) tA
         (fmt_ppr_cmp_exp_syn l0) i

    | Sgn.Query _ ->
       fprintf ppf "%s"
         (to_html "query" Keyword)

    | Sgn.Module (_, name, decls) ->
       let aux ppf t = List.iter (fmt_ppr_sgn_decl ppf) t in
       fprintf ppf "@[%s %s = %s@ @[<v2>%a@]@ %s;@]@\n"
         (to_html "module" Keyword) (name) (to_html "struct" Keyword) (aux) decls (to_html "end" Keyword)
    | Sgn.MRecTyp (l, decls) ->
       fmt_ppr_mrecs 0 ppf decls
    | _ -> ()

  let fmt_ppr_sgn ppf sgn = List.iter (fmt_ppr_sgn_decl ppf) sgn
end (* Ext.Make *)

(* Default Error Pretty Printer Functor Instantiation *)
module DefaultPrinter = Make (Store.Cid.NamedRenderer)
