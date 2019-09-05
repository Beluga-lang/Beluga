(** Pretty printing for external syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html
*)

open Support
open Format
open Syntax.Ext

  (* 
  (* External Syntax Printer Signature *)
  module type PRINTER = sig

    (* Contextual Format Based Pretty Printers *)
    val fmt_ppr_sgn_decl      : lvl -> formatter -> Sgn.decl  -> unit
    val fmt_ppr_lf_kind       : LF.dctx -> lvl -> formatter -> LF.kind      -> unit
    val fmt_ppr_lf_ctyp_decl  : LF.mctx -> lvl -> formatter -> LF.ctyp_decl -> unit
    val fmt_ppr_lf_typ_rec    : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ_rec    -> unit

    val fmt_ppr_lf_typ        : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.typ        -> unit
    val fmt_ppr_lf_normal     : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.normal     -> unit
    val fmt_ppr_lf_head       : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.head       -> unit
    val fmt_ppr_lf_spine      : LF.mctx -> LF.dctx -> lvl -> formatter -> LF.spine      -> unit
    val fmt_ppr_lf_sub        : ?pp_empty:(Format.formatter -> unit -> bool) ->
                                LF.mctx -> LF.dctx -> lvl -> formatter -> LF.sub        -> unit

    val fmt_ppr_lf_schema     : lvl -> formatter -> LF.schema     -> unit
    val fmt_ppr_lf_sch_elem   : lvl -> formatter -> LF.sch_elem   -> unit

    val fmt_ppr_lf_psi_hat    : LF.mctx -> lvl -> formatter -> LF.dctx  -> unit
    val fmt_ppr_lf_dctx       : LF.mctx -> lvl -> formatter -> LF.dctx  -> unit

    val fmt_ppr_lf_mctx       : ?sep:(formatter -> unit -> unit) ->
                                lvl -> formatter -> LF.mctx     -> unit
    val fmt_ppr_cmp_kind      : LF.mctx -> lvl -> formatter -> Comp.kind -> unit
    val fmt_ppr_cmp_typ       : LF.mctx -> lvl -> formatter -> Comp.typ -> unit
    val fmt_ppr_cmp_exp_chk   : LF.mctx -> lvl -> formatter -> Comp.exp_chk -> unit
    val fmt_ppr_cmp_exp_syn   : LF.mctx -> lvl -> formatter -> Comp.exp_syn -> unit
    val fmt_ppr_cmp_branches  : LF.mctx -> lvl -> formatter -> Comp.branch list -> unit
    val fmt_ppr_cmp_branch    : LF.mctx -> lvl -> formatter -> Comp.branch -> unit
    val fmt_ppr_pat_obj       : LF.mctx -> lvl -> formatter -> Comp.pattern -> unit
      (*
    val fmt_ppr_cmp_gctx      : LF.mctx -> lvl -> formatter -> Comp.gctx -> unit
       *)

    val fmt_ppr_patternOpt    : LF.mctx -> LF.dctx -> formatter -> LF.normal option -> unit

  end (* Ext.PRINTER *)
                        *)

(* External Syntax Pretty Printer Functor *)
module Make (R : Store.Cid.RENDERER) : Printer.Ext.T = struct
  include Prettycom

  type lvl = int
  let l0 = 0
        
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
    let paren s = lvl > 0 && true in
    begin match head with
    | LF.PVar (_,  x, s) ->
       fprintf ppf "%s#%s%a%s"
         (l_paren_if (paren s))
         (Id.render_name x)
         (Maybe.print
            (fun ppf sub ->
              fprintf ppf "[%a]"
                (fmt_ppr_lf_sub cD cPsi 0) sub))
         s
         (r_paren_if (paren s))
      
    | LF.Name(_, x, s) ->
       fprintf ppf "%s%a"
         (to_html (Id.render_name x) LinkOption)
         (Maybe.print
            (fun ppf sub ->
              fprintf ppf "[%a]"
                (fmt_ppr_lf_sub cD cPsi 0) sub))
         s
      
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
         (fmt_ppr_lf_sub_opt  cD cPsi lvl) s
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
      
  (** Renders the given substitution in brackets, if it exists.
      Otherwise prints nothing.
   *)
  and fmt_ppr_lf_sub_opt cD cPsi lvl ppf so =
    Maybe.print
      (fun ppf sub ->
        fprintf ppf "[%a]"
          (fmt_ppr_lf_sub cD cPsi lvl) sub)
      ppf
      so
    
  (** Prints a substitution.
      `pp_empty' is a printing function that prints the empty
      substitution. By default this prints nothing, and returns
      false. However, if you want to print the empty substitution as
      something else, e.g. `^', then you can override this and
      return true.
   *)
  and fmt_ppr_lf_sub ?(pp_empty = fun _ _ -> false) (cD : LF.mctx) (cPsi : LF.dctx) lvl (ppf : Format.formatter) (start, tms : LF.sub) =
    
	  let print_tm = fmt_ppr_lf_normal cD cPsi 1 in
    let print_svar s s_opt =
      fprintf ppf "#%s%a"
        (Id.render_name s)
        (Maybe.print
           (fun ppf sub ->
             fprintf ppf "[%a]"
               (fmt_ppr_lf_sub ~pp_empty: (fun ppf () -> fprintf ppf "^"; true) cD cPsi 0) sub))
        s_opt
    in
    let go ppf () =
      let nonempty =
        (* print the beginning of the substitution and give a boolean
           indicating whether some output was actually generated.
           This is so after we can correctly generate a comma.
         *)
        match start with
        | LF.EmptySub _ -> pp_empty ppf ()
        | LF.Id _ -> fprintf ppf "%s" (symbol_to_html Dots); true
        | LF.SVar (_, s, sub') -> print_svar s sub'; true
      in
      
      (* then check if the list of terms is nonempty;
         if it is: print a comma, then each term comma-separated.
         else, just print each term comma-separated *)
      
      if nonempty && Misc.List.nonempty tms then  
        Fmt.comma ppf ();
      
      pp_print_list ~pp_sep: Fmt.comma
        print_tm ppf tms;
    in
    
    fprintf ppf "@[<h>%a@]" go ();
    
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
      
  and fmt_ppr_lf_mctx ?(sep = Fmt.comma) lvl ppf = function
    | LF.Empty ->
       fprintf ppf "."
      
    | _ as cD ->
       fprintf ppf "%a"
         (pp_print_list ~pp_sep: sep
            (fun ppf (cD, d) -> fmt_ppr_lf_ctyp_decl cD lvl ppf d))
         (Context.to_sublist_rev cD);
       
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
    | Comp.ClObj (cPsi, ms) ->
       let cond = lvl > 1 in
       fprintf ppf "%s[%a %s %a]%s"
         (l_paren_if cond)
         (fmt_ppr_lf_dctx cD 0) cPsi
         (symbol_to_html Turnstile)
         (fmt_ppr_lf_sub cD cPsi 0) ms
         (r_paren_if cond)
       
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
       
  let rec fmt_ppr_pat_spine cD lvl ppf = function
    | Comp.PatNil _ -> fprintf ppf ""
    | Comp.PatApp (_, pat, pat_spine) ->
       fprintf ppf "%a %a"
         (fmt_ppr_pat_obj cD (lvl+1)) pat
         (fmt_ppr_pat_spine cD lvl) pat_spine
    | Comp.PatObs (_, x, pat_spine) ->
       fprintf ppf "%s %a"
         (Id.render_name x)
         (fmt_ppr_pat_spine cD lvl) pat_spine
      
      
  and fmt_ppr_pat_obj cD lvl ppf = function
    | Comp.PatMetaObj (_, mO) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a%s"
         (l_paren_if cond)
         (fmt_ppr_meta_obj cD 0) mO
         (r_paren_if cond)
    | Comp.PatName (_, x, pat_spine) ->
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
    | Comp.PatAnn (_, pat, tau) ->
       fprintf ppf "%a : %a"
         (fmt_ppr_pat_obj cD 0) pat
         (fmt_ppr_cmp_typ cD 0) tau
      
      
  let rec fmt_ppr_cmp_exp_chk cD lvl ppf = function
    | Comp.Syn (_, i) ->
       fmt_ppr_cmp_exp_syn cD lvl ppf i
      
    | Comp.Fn (_, x, e) ->
       let cond = lvl > 0 in
       fprintf ppf "%s%s %s %s %a%s"
         (l_paren_if cond)
         (to_html "fn" Keyword)
	       (Id.render_name x)
         (symbol_to_html DblRArr)
         (fmt_ppr_cmp_exp_chk cD 0) e
         (r_paren_if cond);
       
    | Comp.Fun (_, b) ->
       fprintf ppf "%s @[%a@]"
         (to_html "fun" Keyword)
         (fmt_ppr_cmp_fbranches cD lvl) b
      
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
       fprintf ppf "%a"
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
       | Comp.EmptyBranch(_, _, _) ->
          fprintf ppf "%s %a"
            (to_html "impossible" Keyword)
            (fmt_ppr_cmp_exp_syn cD 0) i
       end
      
    | Comp.Case (_, prag, i, bs) ->
       fprintf ppf "%s %a %s %s%a"
         (to_html "case" Keyword)
         (fmt_ppr_cmp_exp_syn cD 0) i
         (to_html "of" Keyword)
         (match prag with Pragma.RegularCase -> "" | Pragma.PragmaNotCase -> (to_html " %not " Keyword))
         (fmt_ppr_cmp_branches cD 0) bs
      
    | Comp.Hole (_) -> fprintf ppf " ? "
                     
  and fmt_ppr_cmp_exp_syn cD lvl ppf = function
    | Comp.Name(_, x) ->
       fprintf ppf "%s"
         (to_html (Id.render_name x) LinkOption)
      
    | Comp.Apply (_, i, e) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a %a%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_exp_syn cD 1) i
         (fmt_ppr_cmp_exp_chk cD 2) e
         (r_paren_if cond)
       
    | Comp.BoxVal (_, m0) ->
       let cond = lvl > 1 in
       fprintf ppf "%s%a%s"
         (l_paren_if cond)
         (fmt_ppr_meta_obj cD 0) m0
         (r_paren_if cond)
       
    | Comp.PairVal(_, i1, i2) ->
       fprintf ppf "(%a , %a)"
         (fmt_ppr_cmp_exp_syn cD 1) i1
         (fmt_ppr_cmp_exp_syn cD 1) i2
      
      
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
      
  and fmt_ppr_cmp_fbranches cD lvl ppf = function
    | Comp.NilFBranch _ -> ()
    | Comp.ConsFBranch (_, (ps, e), Comp.NilFBranch _) ->
       fprintf ppf "%a%s@[%a@]"
         (fmt_ppr_pat_spine cD lvl) ps
         (symbol_to_html DblRArr)
         (fmt_ppr_cmp_exp_chk cD lvl) e
    | Comp.ConsFBranch (_, (ps, e), br) ->
       fprintf ppf "%a%s@[%a@]@\n@[<hov2>| %a"
         (fmt_ppr_pat_spine cD lvl) ps
         (symbol_to_html DblRArr)
         (fmt_ppr_cmp_exp_chk cD lvl) e
         (fmt_ppr_cmp_fbranches cD lvl) br
      
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
      
  let total_to_string tdec = match tdec with
    | None -> ""
    | Some (Comp.Trust _) -> "/ trust /"
    | Some (Comp.Total (_ , order, f, args)) ->
       let rec args_to_string args = match args with
         | [] -> ""
         | Some n :: args' -> Id.render_name n ^ " " ^ args_to_string args'
         | None :: args' -> " _ " ^ args_to_string args'
       in
       let rec order_to_string order = match order with
         | Comp.Arg n -> Id.render_name n
         | Comp.Lex orders ->
            "{" ^ String.concat " " (List.map order_to_string orders) ^ "}"
       in
       "/ total " ^
         (match order with
          | Some order -> order_to_string order
          | None -> ""
         )
         ^ " ( " ^ Id.render_name f ^ " " ^ args_to_string args ^ ") /"
       
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
    | Sgn.CompConst(_, n, tA) -> 
       fprintf ppf "@\n| %s : %a"
         (to_html (Id.render_name n) (ID Constructor))
         (fmt_ppr_cmp_typ LF.Empty 1)  tA
    | Sgn.CompDest(_, n, cD, tA, tA') ->
       fprintf ppf "@\n| (%s : %a) :: %a"
         (to_html (Id.render_name n) (ID Constructor))
         (fmt_ppr_cmp_typ cD 1)  tA
         (fmt_ppr_cmp_typ cD 1)  tA'
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
	            fprintf ppf "@\n%s " (to_html "and" Keyword);
	            fmt_ppr_mrecs lvl ppf t
              
  let rec fmt_ppr_sgn_decl ppf = function
    | Sgn.Const (_, x, a) ->
       fprintf ppf "@[<h>%s : %a.@]@\n"
         (to_html (Id.render_name x) (ID Constructor))
         (fmt_ppr_lf_typ LF.Empty LF.Null l0)  a
      
    | Sgn.Typ (_, x, k) ->
       fprintf ppf "@[<h>%s : %a.@]@\n"
         (to_html (Id.render_name x) (ID Typ))
         (fmt_ppr_lf_kind LF.Null l0) k
      
    | Sgn.CompConst (_, x, a) ->
       fprintf ppf "@[<h>| %s : %a@]@\n"
         (to_html (Id.render_name x) (ID Constructor))
         (fmt_ppr_cmp_typ LF.Empty l0)  a
      
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
       (fmt_ppr_rec l0 ppf) lrec
      
    | Sgn.Pragma (_, Sgn.NamePrag(name, s, s_opt)) ->
       fprintf ppf "@[<h>%s %s %s %s@]@\n"
         (to_html "%name" Keyword) (Id.render_name name)
         s (match s_opt with None -> "" | Some x -> x)
      
    | Sgn.Val (_, x, None, i) ->
       fprintf ppf "@[%s %s = %a;@]@\n"
         (to_html "let" Keyword)
         (Id.render_name  x)
         (fmt_ppr_cmp_exp_syn LF.Empty l0) i
      
    | Sgn.Val (_, x, Some(tA), i) ->
       fprintf ppf "@[%s %s : %a =@ %a;@]@\n"
         (to_html "let" Keyword)
         (Id.render_name  x)
         (fmt_ppr_cmp_typ LF.Empty 0) tA
         (fmt_ppr_cmp_exp_syn LF.Empty l0) i
      
    | Sgn.Query _ ->
       fprintf ppf "%s"
         (to_html "query" Keyword)
      
    | Sgn.Module(_, name, decls) ->
       let aux ppf t = List.iter (fmt_ppr_sgn_decl ppf) t in
       fprintf ppf "@[%s %s = %s@ @[<v2>%a@]@ %s;@]@\n"
         (to_html "module" Keyword) (name) (to_html "struct" Keyword) (aux) decls (to_html "end" Keyword)
    | Sgn.MRecTyp(l, decls) ->
       fmt_ppr_mrecs 0 ppf decls
    | _ -> ()

  let fmt_ppr_sgn ppf sgn = List.iter (fmt_ppr_sgn_decl ppf) sgn
end (* Ext.Make *)
                                                     
(* Default Error Pretty Printer Functor Instantiation *)
module DefaultPrinter = Make (Store.Cid.NamedRenderer)
