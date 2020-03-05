open Support
open Format
open Syntax
open Int

let (_, _, dprnt) = Debug.(makeFunctions' (toFlags [17]))

module TermS = Store.Cid.Term
module CompS = Store.Cid.Comp

module PC = Printer.Control

(* Internal Syntax Pretty Printer Functor *)
module Make (R : Store.Cid.RENDERER) : Printer.Int.T = struct
  include Prettycom

  type lvl = int
  let l0 = 0

  module InstHashedType = struct
    type t    = LF.iterm option ref
    let equal = (==)
    let hash  = Hashtbl.hash
  end

  module MInstHashtbl = Hashtbl.Make (InstHashedType)
  module SInstHashtbl = Hashtbl.Make (InstHashedType)
  module PInstHashtbl = Hashtbl.Make (InstHashedType)

  let minst_hashtbl : string MInstHashtbl.t = MInstHashtbl.create 0
  let sinst_hashtbl : string SInstHashtbl.t = SInstHashtbl.create 0
  let pinst_hashtbl : string PInstHashtbl.t = PInstHashtbl.create 0

  (* Fresh name generation *)

  let rec get_names_dctx : LF.dctx -> Id.name list = function
    | LF.Null -> []
    | LF.CtxVar psi -> []
    | LF.DDec (cPsi', LF.TypDecl (n, _))
      | LF.DDec (cPsi', LF.TypDeclOpt n) -> n :: get_names_dctx cPsi'

  let rec get_names_mctx : LF.mctx -> Id.name list = function
    | LF.Empty -> []
    | LF.Dec (cD', LF.Decl (n, _, _))
      | LF.Dec (cD', LF.DeclOpt n) -> n :: get_names_mctx cD'

  let rec get_names_gctx : Comp.gctx -> Id.name list = function
    | LF.Empty -> []
    | LF.Dec (cG', Comp.CTypDecl (n, _, _ ))
      | LF.Dec (cG', Comp.CTypDeclOpt n) -> n :: get_names_gctx cG'

  let fresh_name_dctx (cPsi : LF.dctx) : Id.name -> Id.name =
    Id.gen_fresh_name (get_names_dctx cPsi)
  let fresh_name_mctx (cD : LF.mctx) : Id.name -> Id.name =
    Id.gen_fresh_name (get_names_mctx cD)
  let fresh_name_gctx (cG : Comp.gctx) : Id.name -> Id.name  =
    Id.gen_fresh_name (get_names_gctx cG)

  let fresh_name_ctyp_decl (cD: LF.mctx) : LF.ctyp_decl -> LF.ctyp_decl = function
    | LF.Decl (n, ct, dep) ->
       let n' = fresh_name_mctx cD n in LF.Decl (n', ct, dep)
    | LF.DeclOpt n ->
       let n' = fresh_name_mctx cD n in LF.DeclOpt n'

  (** Prints a context.
      Prints each element of the context from left to right with the
      given separator between entries, and using the provided function
      to print an entry.
      The given predicate decides whether an entry should be printed.
      The given printing function receives the subcontext (to the left
      of the entry) plus the entry itself.
   *)
  let fmt_ppr_ctx_filter : type a. ?sep:(formatter -> unit -> unit) -> (a LF.ctx * a -> bool) -> (formatter -> a LF.ctx * a -> unit) -> formatter -> a LF.ctx -> unit =
    (* the type has to be written in this horrible way to keep OCaml
       from unnecessarily monomorphizing it. *)
    fun ?(sep = pp_print_space) p f ppf ctx ->
    pp_print_list ~pp_sep: sep f ppf (Context.to_sublist ctx |> List.filter p)

  (* Contextual Format Based Pretty Printers
   *
   * We assume types, terms, etc are all in normal form.
   *)

  let rec fmt_ppr_lf_typ cD cPsi lvl ppf = function
    | LF.Atom (_, a, LF.Nil) ->
       fprintf ppf "%s"
         (R.render_cid_typ a)

    | LF.Atom (_, a, ms) ->
       let cond = lvl > 1 in
       let Store.Cid.Typ.Entry.({ implicit_arguments = k; _ }) = Store.Cid.Typ.get a in
       let ms =
         (* drop implicits *)
         if !PC.printImplicit then ms else LF.drop_spine k ms
       in
       fprintf ppf "%s@[<hov 2>%s@ @[<hov>%a@]@]%s"
         (l_paren_if cond)
         (R.render_cid_typ a)
         (fmt_ppr_lf_spine cD cPsi 2) ms
         (r_paren_if cond)

    | LF.PiTyp ((LF.TypDecl (x, a), LF.Maybe), b) ->
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "@[<1>%s{%s : %a} @ %a%s@]"
         (l_paren_if cond)
         (Id.render_name x)
         (fmt_ppr_lf_typ cD cPsi 0) a
         (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, a))) 0) b
         (r_paren_if cond)

    | LF.PiTyp ((LF.TypDecl (x, a), LF.No), b) ->
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "@[<1>%s%a -> %a%s@]"
         (l_paren_if cond)
         (fmt_ppr_lf_typ cD cPsi 1) a
         (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, a))) 0) b
         (r_paren_if cond)

    | LF.Sigma typRec ->
       fprintf ppf "@[<hv 2>block (@,@[%a@]@])"
         (fmt_ppr_lf_typ_rec cD cPsi lvl) typRec

    | LF.TClo (typ, s) ->
       fprintf ppf "TClo(%a,@ %a)"
         (fmt_ppr_lf_typ cD cPsi lvl) typ
         (fmt_ppr_lf_sub cD cPsi lvl) s

  and fmt_ppr_lf_tuple cD cPsi lvl ppf = function
    | LF.Last tM ->
       fmt_ppr_lf_normal cD cPsi lvl ppf tM

    | LF.Cons(tM, rest) ->
       fprintf ppf "%a, %a"
         (fmt_ppr_lf_normal cD cPsi lvl) tM
         (fmt_ppr_lf_tuple cD cPsi lvl) rest

  and fmt_ppr_lf_operator cD cPsi ppf (fixity, name, spine) =
    match fixity with
    | Ext.Sgn.Prefix ->
       fmt_ppr_lf_prefix_operator cD cPsi ppf (name, spine)
    | Ext.Sgn.Postfix ->
       fmt_ppr_lf_postfix_operator cD cPsi ppf (name, spine)
    | Ext.Sgn.Infix ->
       fmt_ppr_lf_infix_operator cD cPsi ppf (name, spine)

  and fmt_ppr_lf_prefix_operator cD cPsi ppf = function
    | name, LF.(App (m, Nil)) ->
       fprintf ppf "%a %a"
         Id.print name
         (fmt_ppr_lf_normal cD cPsi 2) m
    | _ ->
       Error.violation
         "[fmt_ppr_lf_prefix_operator] spine length <> 1"

  and fmt_ppr_lf_postfix_operator cD cPsi ppf = function
    | name, LF.(App (m, Nil)) ->
       fprintf ppf "%a %a"
         (fmt_ppr_lf_normal cD cPsi 2) m
         Id.print name
    | _ ->
       Error.violation
         "[fmt_ppr_lf_postfix_operator] spine length <> 1"

  and fmt_ppr_lf_infix_operator cD cPsi ppf = function
    | name, LF.(App (m1, App (m2, Nil))) ->
       fprintf ppf "%a %a %a"
         (fmt_ppr_lf_normal cD cPsi 2) m1
         Id.print name
         (fmt_ppr_lf_normal cD cPsi 2) m2
    | _ ->
       Error.violation
         "[fmt_ppr_lf_infix_operator] spine length <> 2"

  and fmt_ppr_lf_normal cD cPsi lvl ppf =
    let deimplicitize_spine h ms = match h with
      | _ when !PC.printImplicit -> ms
      | LF.Const c ->
         LF.drop_spine (Store.Cid.Term.get_implicit_arguments c) ms
      | _ -> ms
    in
    function
       | LF.Lam (_, x, m) ->
          let x = fresh_name_dctx cPsi x in
          let cond = lvl > 0 in
          fprintf ppf "%s@[<hov 2>\\%s.@ @[%a@]@]%s"
            (l_paren_if cond)
            (Id.render_name x)
            (fmt_ppr_lf_normal cD (LF.DDec(cPsi, LF.TypDeclOpt x)) 0) m
            (r_paren_if cond)
       | LF.LFHole (_, id, name) ->
          let open Holes in
          let open HoleId in
          let name =
            match name with
            | Anonymous -> ""
            | Named s -> s
          in
          begin match get (by_id id) with
          | None -> fprintf ppf "?%s" name
          | Some (_, Exists (w, h)) ->
             match w with
             | CompInfo -> Error.violation "expected LFHole; got comp hole"
             | LFInfo ->
                let { lfSolution; cPsi; _ } = h.info in
                match lfSolution with
                | None ->
                   fprintf ppf "?%s" name
                | Some sM ->
                   fprintf ppf "%a" (fmt_ppr_lf_normal cD cPsi l0) (Whnf.norm sM)
          end
       | LF.Tuple (_, tuple) ->
          fprintf ppf "<%a>"
            (fmt_ppr_lf_tuple cD cPsi lvl) tuple

       | LF.Root (_, h, LF.Nil) ->
          fprintf ppf "%a"
            (fmt_ppr_lf_head cD cPsi lvl) h

       | LF.Clo(tM, s) -> fmt_ppr_lf_normal cD cPsi lvl ppf (Whnf.norm (tM, s))

       | LF.(Root (_, (Const cid as h), ms))  ->
          let ms = deimplicitize_spine h ms in
          let TermS.Entry.({ name; _ }) = TermS.get cid in
          begin match Store.OpPragmas.getPragma name with
          | Some p ->
             (* TODO limit the printing of parens for operators *)
             fprintf ppf "(%a)"
               (fmt_ppr_lf_operator cD cPsi)
               (Store.OpPragmas.(p.fix), name, ms)
          | _ ->
             let cond = lvl > 1 in
             fprintf ppf "%s%a %a%s"
               (l_paren_if cond)
               (fmt_ppr_lf_head cD cPsi lvl) h
               (fmt_ppr_lf_spine cD cPsi 2)  ms
               (r_paren_if cond)
          end
       | LF.Root (_, h, ms) ->
          let ms = deimplicitize_spine h ms in
          let cond = lvl > 1 in
          fprintf ppf "%s%a %a%s"
            (l_paren_if cond)
            (fmt_ppr_lf_head cD cPsi lvl) h
            (fmt_ppr_lf_spine cD cPsi 2)  ms
            (r_paren_if cond)

  and fmt_ppr_lf_head cD cPsi lvl ppf head =
    let paren s =
      not (PC.db()) && lvl > 0
      && match s with
         | LF.EmptySub | LF.Undefs -> false
         | LF.Shift _ when not (Context.hasCtxVar cPsi) -> false
         | _ -> true
    in
    let rec fmt_head_with proj = function
      | LF.HClo (h, s, sigma) ->
         fprintf ppf "%s[%a[%a]]"
           (R.render_bvar cPsi h)
           (fmt_ppr_lf_offset cD) s
           (fmt_ppr_lf_sub cD cPsi lvl) sigma
      | LF.HMClo (h, ((s, theta),sigma)) ->
         fprintf ppf "%s[%a[%a ; %a]]"
           (R.render_bvar cPsi h)
           (fmt_ppr_lf_mmvar lvl) s
           (fmt_ppr_lf_msub  cD lvl) theta
           (fmt_ppr_lf_sub cD cPsi lvl) sigma
      | LF.BVar x  ->
         fprintf ppf "%s%s"
           (R.render_bvar cPsi x)
           proj

      | LF.Const c ->
         fprintf ppf "%s%s"
           (R.render_cid_term c)
           proj

      | LF.MMVar ((c, ms), s) ->
         fprintf ppf "%s%a%s[@[%a@]][@[%a@]]%s"
           (l_paren_if (paren s))
           (fmt_ppr_lf_mmvar lvl) c
           proj
           (fmt_ppr_lf_msub cD lvl) ms
           (fmt_ppr_lf_sub  cD cPsi lvl) s
           (r_paren_if (paren s))

      | LF.MPVar ((c, ms), s) ->
         fprintf ppf "%s%a%s[%a]%a%s"
           (l_paren_if (paren s))
           (fmt_ppr_lf_mmvar lvl) c
           proj
           (fmt_ppr_lf_msub cD lvl) ms
           (fmt_ppr_lf_sub  cD cPsi lvl) s
           (r_paren_if (paren s))

      | LF.MVar(c, LF.Undefs)
        | LF.MVar(c, LF.EmptySub) ->
         let f =
           if Context.is_null cPsi then
             fun _ () -> ()
           else
             fun ppf () -> fprintf ppf "[]"
         in
         begin match !PC.substitutionStyle with
         | PC.Natural ->
            fprintf ppf "%a%a%s"
              (fmt_ppr_lf_cvar cD) c
              f ()
              proj
         | PC.DeBruijn ->
            fprintf ppf "%a%s[e]"
              (fmt_ppr_lf_cvar cD) c
              proj
         end

      | LF.MVar (c, s) ->
         if Substitution.LF.isId s then
           fprintf ppf "%a%s"
             (fmt_ppr_lf_cvar cD) c
             proj
         else
           fprintf ppf "%s%a%s[@[%a@]]%s"
             (l_paren_if (paren s))
             (fmt_ppr_lf_cvar cD) c
             proj
             (fmt_ppr_lf_sub cD cPsi lvl) s
             (r_paren_if (paren s))

      | LF.PVar (c, s) ->
         if Substitution.LF.isId s then
           fprintf ppf "%a%s"
             (fmt_ppr_lf_offset cD) c
             proj
         else
           fprintf ppf "%s%a%s[%a]%s"
             (l_paren_if (paren s))
             (fmt_ppr_lf_offset cD) c
             proj
             (fmt_ppr_lf_sub  cD cPsi lvl) s
             (r_paren_if (paren s))

      | LF.FVar x ->
         fprintf ppf "%s%s"
           (Id.render_name x)
           proj

      | LF.FMVar (u, s) ->
         fprintf ppf "FMV %s%s%s[%a]%s"
           (l_paren_if (paren s))
           (Id.render_name u)
           proj
           (fmt_ppr_lf_sub cD cPsi lvl) s
           (r_paren_if (paren s))

      | LF.FPVar (p, s) ->
         fprintf ppf "%sFPV %s%s[%a]%s"
           (l_paren_if (paren s))
           (Id.render_name p)
           proj
           (fmt_ppr_lf_sub cD cPsi lvl) s
           (r_paren_if (paren s))

      | LF.Proj (head, k) ->
         fmt_head_with ("." ^ string_of_int k) head

    in
    fmt_head_with "" head


  and fmt_ppr_lf_spine cD cPsi lvl ppf = function
    | LF.Nil -> ()
    | LF.App(m, LF.Nil) ->
       fprintf ppf "@[%a@]"
         (fmt_ppr_lf_normal  cD cPsi (lvl + 1)) m
    | LF.App (m, ms) ->
       fprintf ppf "@[%a@]@ @[%a@]"
         (fmt_ppr_lf_normal  cD cPsi (lvl + 1)) m
         (fmt_ppr_lf_spine   cD cPsi lvl) ms
    | LF.SClo (ms, s) ->
       let ms' = Whnf.normSpine (ms, s) in
       fprintf ppf "%a"
         (fmt_ppr_lf_spine cD cPsi lvl) ms'

  and fmt_ppr_lf_sub_typing ppf (cD, cPsi, s, cPsi') =
    fprintf ppf "@[@[%a@] ;@ @[%a@]@] |-@ @[@[%a@] :@ @[%a@]@]"
      (fmt_ppr_lf_mctx l0) cD
      (fmt_ppr_lf_dctx cD l0) cPsi
      (fmt_ppr_lf_sub cD cPsi l0) s
      (fmt_ppr_lf_dctx cD l0) cPsi'

  and fmt_ppr_lf_sub cD cPsi lvl ppf s =
    match !Printer.Control.substitutionStyle with
    | Printer.Control.Natural -> fmt_ppr_lf_sub_natural cD cPsi lvl ppf s
    | Printer.Control.DeBruijn -> fmt_ppr_lf_sub_deBruijn cD cPsi lvl ppf s

  and fmt_ppr_lf_sub_natural cD cPsi lvl ppf s =
    let s = Whnf.normSub s in
    let cPsi = Whnf.normDCtx cPsi in
    let print_front = fmt_ppr_lf_front cD cPsi 1 in
    (* XXX O(n^2) algorithm below.
       The following algorithm for printing the substitution
       effectively converts it to a list of items, so these items can
       be printed using pp_print_list with a comma separator.
       These items are printing functions of type
           formatter -> unit -> unit
       I build the list by appending to the end with `@ [foo]`, so
       overall this algorithm is O(n^2).
       This can be improved by building the list in reverse and then
       printing it in reverse, to recover O(n) performance.
     *)
    let rec prepare_lf_sub_id cPsi =
      match cPsi with
      | LF.Null ->
         []
      | LF.CtxVar _ ->
         [fun ppf _ -> fprintf ppf ".."]
      | LF.(DDec (Null, (TypDecl (x, _) | TypDeclOpt x))) ->
         [fun ppf _ -> Id.print ppf x]
      | LF.DDec (cPsi', LF.TypDecl (x, _))
        | LF.DDec (cPsi', LF.TypDeclOpt x) ->
         prepare_lf_sub_id cPsi' @ [fun ppf _ -> Id.print ppf x]
    in
    let rec fmt_ppr_lf_sub_shift ppf (cPsi,n) = match cPsi, n with
      | _, 0 -> prepare_lf_sub_id cPsi
      | LF.DDec (cPsi', _), n -> fmt_ppr_lf_sub_shift ppf (cPsi', n-1)
    in
    let rec self lvl =
      function
      | LF.(EmptySub | Undefs) -> []
      | LF.Shift n -> fmt_ppr_lf_sub_shift ppf (cPsi, n)
      | LF.FSVar (_, (s_name, s)) ->
         [fun ppf _ ->
          fprintf ppf "|- FSV %s[%a]"
            (Id.render_name s_name )
            (fmt_ppr_lf_sub cD cPsi lvl) s]

      | LF.SVar (c, _, s) ->
         [fun ppf _ ->
          fprintf ppf "%a[@[%a@]]"
            (fmt_ppr_lf_offset cD) c
            (fmt_ppr_lf_sub_natural cD cPsi lvl) s]

      | LF.MSVar (_, ((_sigma, t),s)) ->
         [fun ppf _ ->
          fprintf ppf "$?S[@[%a@];@ @[%a@]]"
           (fmt_ppr_lf_msub cD lvl) t
           (fmt_ppr_lf_sub_natural cD cPsi lvl) s]

      | LF.Dot (f, s) ->
         self lvl s @ [fun ppf _ -> print_front ppf f]
    in
    match s with
    | LF.Shift _ when not (Context.hasCtxVar cPsi) ->
       (* Print nothing at all, because the user would have written nothing at all *)
       ()
    | _ ->  (* For anything else, print a space first *)
       fprintf ppf "%a"
         (pp_print_list ~pp_sep: Fmt.comma
            (fun ppf f -> f ppf ()))
         (self lvl s)

  and fmt_ppr_lf_sub_deBruijn cD cPsi lvl ppf s =
    let rec self lvl ppf = function
      | LF.EmptySub -> fprintf ppf "EmptySub"
      | LF.Undefs -> fprintf ppf "Undefs"
      | LF.Shift n ->
         fprintf ppf "^%s"
           (R.render_offset n)

      | LF.FSVar (n, (s_name, s)) ->
         fprintf ppf
           "^%s FSV %s[%a]"
           (R.render_offset n)
           (Id.render_name s_name)
           (self lvl) s

      | LF.SVar (c, n, s) ->
         fprintf ppf
           "^%s %a[%a]"
           (R.render_offset n)
           (fmt_ppr_lf_offset cD) c
           (self lvl) s

      | LF.MSVar (n , ((_sigma, t),s)) ->
         fprintf ppf
           "^%s $?S [%a][|%a|]"
           (R.render_offset n)
           (self lvl) s
           (fmt_ppr_lf_msub cD 0) t

      | LF.Dot (f, s) ->
         fprintf ppf "%a,  %a"
           (fmt_ppr_lf_front cD cPsi 1) f
           (self lvl) s
    in
    fprintf ppf " %a"
      (self lvl) s


  and fmt_ppr_lf_front cD cPsi lvl ppf = function
    | LF.Head h ->
       fprintf ppf "%a"
         (fmt_ppr_lf_head cD cPsi lvl) h

    | LF.Obj m ->
       fprintf ppf "%a"
         (fmt_ppr_lf_normal cD cPsi lvl) m

    | LF.Undef ->
       fprintf ppf "undef"

  and fmt_ppr_lf_msub cD lvl ppf = function
    | LF.MShift k ->
       fprintf ppf "^%s" (string_of_int k)

    | LF.MDot (f, s) ->
       fprintf ppf "@[%a@],@ @[%a@]"
         (fmt_ppr_lf_msub cD lvl) s
         (fmt_ppr_lf_mfront cD 1) f

  and fmt_ppr_lf_clobj cD lvl cPsi ppf = function
    | LF.MObj m -> fmt_ppr_lf_normal cD cPsi lvl ppf m
    | LF.SObj s -> fmt_ppr_lf_sub cD cPsi lvl ppf s
    | LF.PObj h -> fprintf ppf "%a" (fmt_ppr_lf_head cD cPsi lvl) h


  and fmt_ppr_lf_mfront' cD ppf = function
    | LF.CObj cPsi ->
       fprintf ppf "@[%a@]"
         (fmt_ppr_lf_dctx cD 0) cPsi
    | LF.ClObj (phat, tM) ->
       let cPsi = Context.hatToDCtx phat in
       fprintf ppf "@[<hov 2>@[%a@] |-@ @[%a@]@]"
         (fmt_ppr_lf_dctx_hat cD 0) cPsi
         (fmt_ppr_lf_clobj cD 0 cPsi) tM
    | LF.MV k ->
       fprintf ppf "%s"
         (R.render_cvar cD k)
    | LF.MUndef ->
       fprintf ppf "UNDEF"

  and fmt_ppr_lf_mfront cD lvl ppf mO =
    fprintf ppf "[%a]" (fmt_ppr_lf_mfront' cD) mO

  and fmt_ppr_lf_mfront_typed cD lvl ppf = function
    | LF.(ClObj (_, tM), ClTyp (_, cPsi)) ->
       fprintf ppf "@[<hov 2>@[%a@] |-@ @[%a@]@]"
         (fmt_ppr_lf_dctx cD 0) cPsi
         (fmt_ppr_lf_clobj cD 0 cPsi) tM
    | (cM, _) -> fmt_ppr_lf_mfront' cD ppf cM

  and fmt_ppr_cmp_meta_obj cD lvl ppf (_, mO) =
    fmt_ppr_lf_mfront cD lvl ppf mO

  and fmt_ppr_cmp_meta_obj_typed cD lvl ppf ( (_, cM), cU ) =
    fprintf ppf "[%a]"
      (fmt_ppr_lf_mfront_typed cD lvl) (cM, cU)

  and fmt_ppr_lf_mmvar_uninstantiated ppf (u, typ, dep) =
    match typ with
    | LF.(ClTyp (PTyp tA, _)) ->
       begin
         try
           fprintf ppf "?#%s"
             (PInstHashtbl.find pinst_hashtbl u)
         with
         | Not_found ->
            let sym = match Store.Cid.Typ.gen_mvar_name tA with
              | Some vGen -> vGen ()
              | None -> Gensym.MVarData.gensym ()
            in
            PInstHashtbl.replace pinst_hashtbl u sym;
            fprintf ppf "?#%s" sym
       end
    | LF.(ClTyp (MTyp tA, _)) ->
       begin
         try
           fprintf ppf "?%s%a"
             (MInstHashtbl.find minst_hashtbl u)
             fmt_ppr_lf_depend dep
         with
         | Not_found ->
            (* (* Should probably create a sep. generator for this -dwm *)
               let sym = String.uppercase (Gensym.VarData.gensym ()) in
             *)
            (* Not working -bp *)
            let sym =
              match Store.Cid.Typ.gen_mvar_name tA with
              | Some vGen -> vGen ()
              | None -> Gensym.MVarData.gensym ()
            in
            MInstHashtbl.replace minst_hashtbl u sym;
            fprintf ppf "?%s" sym
       end
    | LF.(ClTyp (STyp (_, cPsi), _)) ->
       begin
         try
           fprintf ppf "?%s"
             (SInstHashtbl.find sinst_hashtbl u)
         with
         | Not_found ->
            (* (* Should probably create a sep. generator for this -dwm *)
               let sym = String.uppercase (Gensym.VarData.gensym ()) in
             *)
            (* Not working -bp *)
            let sym = Gensym.MVarData.gensym ()
            in
            SInstHashtbl.replace sinst_hashtbl u sym
            ; fprintf ppf "#?%s" sym
       end

  and fmt_ppr_lf_mmvar lvl ppf mmvar =
    (* check whether the mmvar is instantiated or not before proceeding to print *)
    let u = LF.(mmvar.instantiation) in
    match !u with
    | None ->
       fmt_ppr_lf_mmvar_uninstantiated ppf LF.(u, mmvar.typ, mmvar.depend)
    | Some it ->
       match LF.(mmvar.typ) with
       | LF.ClTyp (_, cPsi) ->
          fmt_ppr_lf_iterm LF.(mmvar.cD) cPsi lvl ppf it

  and fmt_ppr_lf_offset cD ppf n =
    fprintf ppf "%s" (R.render_cvar cD n)

  and fmt_ppr_lf_cvar cD ppf = function
    | LF.Offset n -> fmt_ppr_lf_offset cD ppf n

    | LF.Inst mmvar ->
       let u = LF.(mmvar.instantiation) in
       let open LF in
       match !u with
       | Some it ->
          let ClTyp (_, cPsi) = mmvar.typ in
          fmt_ppr_lf_iterm mmvar.cD cPsi 0 ppf it
       | None ->
          fmt_ppr_lf_mmvar_uninstantiated ppf (u, mmvar.typ, mmvar.depend)

  and fmt_ppr_lf_ctx_var cD ppf = function
    | LF.CInst (mmvar, theta) ->
       let g = LF.(mmvar.instantiation) in
       begin match !g with
       | None ->
          fprintf ppf "?%a[%a]"
            Id.print LF.(mmvar.name)
            (fmt_ppr_lf_msub cD 0) theta

       | Some (LF.ICtx cPsi) ->
          fprintf ppf "%a"
            (fmt_ppr_lf_dctx LF.(mmvar.cD) 0) (Whnf.cnormDCtx (cPsi, theta))
       end

    | LF.CtxOffset psi ->
       fprintf ppf "%s"
         (R.render_ctx_var cD psi)
    | LF.CtxName psi ->
       fprintf ppf "%s"
         (Id.render_name psi)

  and fmt_ppr_lf_typ_rec cD cPsi _lvl ppf typrec =
    let ppr_element cD cPsi ppf = function
      | (x, tA) ->
         fprintf ppf "@[<hv>%s :@ @[%a@]@]"
           (Id.render_name x)
           (fmt_ppr_lf_typ cD cPsi 0) tA
    in
    let rec ppr_elements cD cPsi ppf = function
      | LF.SigmaLast (None, tA) -> fmt_ppr_lf_typ cD cPsi 0 ppf tA
      | LF.SigmaLast (Some x, tA) ->  ppr_element cD cPsi ppf (x, tA)
      (*          | LF.SigmaElem (x, tA1, LF.SigmaLast tA2) ->
                  begin
                  ppr_element cD cPsi  ppf ". " (x, tA1);
                  fprintf ppf "%a" (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, tA1))) 0) tA2
                  end *)
      | LF.SigmaElem (x, tA, tRec)  ->
         let x = fresh_name_dctx cPsi x in
         fprintf ppf "%a,@ %a"
           (ppr_element cD cPsi) (x, tA)
           (ppr_elements cD (LF.DDec(cPsi, LF.TypDecl (x, tA)))) tRec
    in
    fprintf ppf "@[<hv>%a@]" (ppr_elements cD cPsi) typrec

  and projectCtxIntoDctx = function
    |  LF.Empty -> LF.Null
    |  LF.Dec (rest, last) -> LF.DDec (projectCtxIntoDctx rest, last)

  and fmt_ppr_lf_schema ?(useName=true) lvl ppf s =
    let print_without_name (LF.Schema elems) =
      fprintf ppf "@[<hv>%a@]"
        (pp_print_list ~pp_sep: (fun ppf _ -> fprintf ppf " +@ ")
           (fmt_ppr_lf_sch_elem l0))
        elems
    in
    (* Reversing the names is fundamentally unsafe because multiple
       schemas with different names could have the same name.
       For now, we will just print the full schema, until there is a
       more reliable way of getting the schema name back.
       -je *)
    (*
    if useName then
      try
        fprintf ppf "%s" (Id.render_name (Store.Cid.Schema.get_name_from_schema s))
      with
      | Not_found -> print_without_name s

    else *) print_without_name s

  and frugal_block cD cPsi lvl ppf = function
    | LF.SigmaLast(_,  tA) -> fmt_ppr_lf_typ cD cPsi 0 ppf tA
    | other -> fprintf ppf "block (%a)" (fmt_ppr_lf_typ_rec cD cPsi lvl) other

  and fmt_ppr_lf_sch_elem lvl ppf = function
    | LF.SchElem (LF.Empty, sgmDecl) ->
       fprintf ppf "%a"
         (frugal_block LF.Empty LF.Null lvl) sgmDecl

    | LF.SchElem (typDecls, sgmDecl) ->
       let cPsi = projectCtxIntoDctx typDecls in
       fprintf ppf "@[some [%a] %a@]"
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


  and fmt_ppr_lf_dctx_hat cD _lvl ppf = function
    | LF.Null   -> fprintf ppf ""

    | LF.CtxVar ctx_var ->
       fmt_ppr_lf_ctx_var cD ppf ctx_var

    | LF.DDec (LF.Null, LF.TypDeclOpt x) ->
       fprintf ppf "%s"
         (Id.render_name x)

    | LF.DDec (cPsi, LF.TypDeclOpt x) ->
       fprintf ppf "%a, %s"
         (fmt_ppr_lf_dctx_hat cD 0) cPsi
         (Id.render_name x)

    | LF.DDec (LF.Null, LF.TypDecl(x, _ )) ->
       fprintf ppf "%s"
         (Id.render_name x)

    | LF.DDec (cPsi, LF.TypDecl(x, _ )) ->
       fprintf ppf "%a, %s"
         (fmt_ppr_lf_dctx_hat cD 0) cPsi
         (Id.render_name x)

  and fmt_ppr_lf_dctx' cD ppf = function
    | LF.Null ->
       fprintf ppf ""

    | LF.CtxVar ctx_var ->
       fmt_ppr_lf_ctx_var cD ppf ctx_var

    | LF.DDec (LF.Null, LF.TypDecl (x, tA)) ->
       fprintf ppf "@[<hv 2>%s :@ @[%a@]@]"
         (Id.render_name x)
         (fmt_ppr_lf_typ cD LF.Null 0) tA

    | LF.DDec (LF.Null, LF.TypDeclOpt x) ->
       fprintf ppf "%s : _"
         (Id.render_name x)

    | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
       fprintf ppf "@[%a@],@ @[<hv 2>%s :@ @[%a@]@]"
         (fmt_ppr_lf_dctx' cD) cPsi
         (Id.render_name x)
         (fmt_ppr_lf_typ cD cPsi 0) tA

    | LF.DDec (cPsi, LF.TypDeclOpt x) ->
       fprintf ppf "%a,@ %s : _"
         (fmt_ppr_lf_dctx' cD) cPsi
         (Id.render_name x)

  and fmt_ppr_lf_dctx cD lvl ppf cPsi =
    fprintf ppf "@[<hv>%a@]" (fmt_ppr_lf_dctx' cD) cPsi

  and fmt_ppr_lf_mctx ?(all = false) ?(sep = Fmt.comma) lvl ppf cD =
    let should_print =
      if all then
        fun _ -> true
      else
        function
        | (_, LF.Decl (_, _, dep)) ->
           not !Printer.Control.printNormal && (!Printer.Control.printImplicit || not (isImplicit dep))
        | _ -> true
    in
    fmt_ppr_ctx_filter ~sep: sep should_print
      (fun ppf (cD', d) ->
        fprintf ppf "%a"
          (fmt_ppr_lf_ctyp_decl cD') d)
      ppf
      cD

  and fmt_ppr_lf_kind cPsi lvl ppf = function
    | LF.Typ ->
       fprintf ppf "type"

    | LF.PiKind ((LF.TypDecl (x, a), LF.Maybe), k) ->
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "@[<2>%s{@[%s :@ @[%a@]@]}@ @[%a@]%s@]"
         (l_paren_if cond)
         (Id.render_name   x)
         (fmt_ppr_lf_typ LF.Empty cPsi  0) a
         (fmt_ppr_lf_kind (LF.DDec(cPsi, LF.TypDeclOpt  x)) 0) k
         (r_paren_if cond)

    | LF.PiKind ((LF.TypDecl (x, a), LF.No), k) ->
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "%s@[<2>@[%a@] ->@ @[%a@]%s@]"
         (l_paren_if cond)
         (fmt_ppr_lf_typ LF.Empty cPsi  1) a
         (fmt_ppr_lf_kind (LF.DDec(cPsi, LF.TypDeclOpt  x)) 0) k
         (r_paren_if cond)

  and fmt_ppr_lf_mtyp' cD (pre, post) ppf = function
    | LF.ClTyp (LF.MTyp tA, cPsi) ->
       fprintf ppf "%s@[<hov 2>@[%a@] |-@ @[%a@]@]%s"
         pre
         (fmt_ppr_lf_dctx cD 0) cPsi
         (fmt_ppr_lf_typ cD cPsi 0) tA
         post

    | LF.ClTyp (LF.PTyp tA, cPsi) ->
       fprintf ppf "#%s@[<hov 2>@[%a@] |-@ @[%a@]@]%s"
         pre
         (fmt_ppr_lf_dctx cD 0) cPsi
         (fmt_ppr_lf_typ cD cPsi 0) tA
         post

    | LF.ClTyp (LF.STyp (cl, cPhi), cPsi) ->
       fprintf ppf "$%s@[<hov 2>@[%a@] |- %a@ @[%a@]@]%s"
         pre
         (fmt_ppr_lf_dctx cD 0) cPsi
         fmt_ppr_lf_svar_class cl
         (fmt_ppr_lf_dctx cD 0) cPhi
         post
    | LF.CTyp (Some cid) ->
       let x = Store.Cid.Schema.get_name cid in
       fprintf ppf "%a"
         Id.print x
    | LF.CTyp None -> fprintf ppf "CTX"

  and fmt_ppr_lf_mtyp cD ppf = fmt_ppr_lf_mtyp' cD ("[", "]") ppf

  (* If a declaration is implicit and you don't want to print it, then
     it's *YOUR* responsibility to check the plicity of the
     declaration and skip calling this function. Otherwise, it is
     impossible to get the spacing to work correctly in the printed
     material. *)
  and fmt_ppr_lf_ctyp_decl ?(fmt_ppr_depend = fmt_ppr_lf_depend_clean) cD ppf = function
    | LF.Decl (u, mtyp,dep) ->
       fprintf ppf "@[<2>%a%a :@ @[%a@]@]"
         Id.print u
         fmt_ppr_depend dep
         (fmt_ppr_lf_mtyp' cD ("(", ")")) mtyp

    | LF.DeclOpt name ->
       fprintf ppf "%s : _"
         (Id.render_name name)

  and fmt_ppr_lf_ctyp_decl_harpoon cD ppf = function
    | LF.Decl (_, _, dep) as d ->
       let f =
         match dep with
         | LF.Maybe -> fun ppf _ -> fprintf ppf " (not in scope)"
         | _ -> fun _ _ -> ()
       in
       fprintf ppf "@[%a%a@]"
         (fmt_ppr_lf_ctyp_decl cD) d
         f ()
    | LF.DeclOpt _ ->
       Error.violation "[fmt_ppr_lf_ctyp_decl_harpoon] DeclOpt impossible"

  and isImplicit = function
    | LF.Maybe -> true
    | LF.(No | Inductive) -> false

  and isImplicitDecl = function
    | LF.Decl (_, _, dep) when isImplicit dep -> true
    | _ -> false

  and fmt_ppr_lf_iterm cD cPsi lvl ppf = function
    | LF.INorm tM -> fmt_ppr_lf_normal cD cPsi lvl ppf tM
    | LF.IHead h -> fmt_ppr_lf_head cD cPsi lvl ppf h
    | LF.ISub s -> fmt_ppr_lf_sub cD cPsi lvl ppf s
    | LF.ICtx _ -> failwith "printing ICtx is weird because a dctx was also passed in."

  let fmt_ppr_lf_typ_typing ppf (cD, cPsi, tA) =
    fprintf ppf "@[<2>@[@[<hv>%a@] ;@ @[<hv>%a@]@] |-@ @[%a@]@ : type@]"
      (fmt_ppr_lf_mctx l0) cD
      (fmt_ppr_lf_dctx cD l0) cPsi
      (fmt_ppr_lf_typ cD cPsi l0) tA

  let fmt_ppr_lf_msub_typing ppf (cD', t, cD) =
    fprintf ppf "@[<hv>%a@] |-@ @[%a@]@ : @[<hv>%a@]"
      (fmt_ppr_lf_mctx ~all: true l0) cD'
      (fmt_ppr_lf_msub cD' l0) t
      (fmt_ppr_lf_mctx ~all: true l0) cD

  let fmt_ppr_lf_constraint ppf =
    let open Format in
    function
    | LF.Queued id ->
       fprintf ppf "@[QUEUED %d@]" id
    | LF.(Eqn (id, cD, cPsi, INorm tM1, INorm tM2)) ->
       fprintf ppf "@[%d.@ @[<v>@[%a@]@ =@ @[%a@]@]@]"
         id
         (fmt_ppr_lf_normal cD cPsi l0) tM1
         (fmt_ppr_lf_normal cD cPsi l0) tM2
    | LF.(Eqn (id, cD, cPsi, IHead h1, IHead h2)) ->
       fprintf ppf "@[%d.@ @[<v>@[%a@]@ =@ @[%a@]@]@]"
         id
         (fmt_ppr_lf_head cD cPsi l0) h1
         (fmt_ppr_lf_head cD cPsi l0) h2

  let fmt_ppr_lf_constraints ppf =
    let open Format in
    fprintf ppf "@[<v>%a@]"
      (pp_print_list
         ~pp_sep: pp_print_cut
         (fun ppf x -> fmt_ppr_lf_constraint ppf !x))

  (* Computation-level *)
  let rec fmt_ppr_cmp_kind cD lvl ppf = function
    | Comp.Ctype _ -> fprintf ppf "ctype"
    | Comp.PiKind (_, ctyp_decl, cK) ->
       let ctyp_decl = fresh_name_ctyp_decl cD ctyp_decl in
       let cond = lvl > 0 in
       begin
         fprintf ppf "%s@[<2>{@[<2>%a@]}@ %a%s@]"
           (l_paren_if cond)
           (fmt_ppr_lf_ctyp_decl cD) ctyp_decl
           (fmt_ppr_cmp_kind (LF.Dec(cD, ctyp_decl)) 1) cK
           (r_paren_if cond)
       end

  let fmt_ppr_cmp_meta_typ cD ppf = fmt_ppr_lf_mtyp cD ppf

  let rec fmt_ppr_cmp_meta_spine cD lvl ppf = function
    | Comp.MetaNil ->
       fprintf ppf ""
    | Comp.MetaApp (mO, mS) ->
       fprintf ppf "@ @[%a@]%a"
         (fmt_ppr_cmp_meta_obj  cD (lvl + 1)) mO
         (fmt_ppr_cmp_meta_spine   cD lvl) mS

  let rec fmt_ppr_cmp_typ cD lvl ppf = function
    | Comp.TypBase (_, c, mS)->
       let cond = lvl > 10 in
       fprintf ppf "%s@[<2>%s@[%a@]@]%s"
         (l_paren_if cond)
         (R.render_cid_comp_typ c)
         (fmt_ppr_cmp_meta_spine cD lvl) mS
         (r_paren_if cond)
    | Comp.TypCobase (_, c, mS)->
       let cond = lvl > 10 in
       fprintf ppf "%s%s@[%a@]%s"
         (l_paren_if cond)
         (R.render_cid_comp_cotyp c)
         (fmt_ppr_cmp_meta_spine cD lvl) mS
         (r_paren_if cond)
    | Comp.TypBox (_, mT) ->
       fprintf ppf "@[%a@]"
         (fmt_ppr_cmp_meta_typ cD) mT

    | Comp.TypArr (_, tau1, tau2) ->
       let cond = lvl > 1 in
       fprintf ppf "%s@[<2>%a ->@ %a@]%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_typ cD 2) tau1
         (fmt_ppr_cmp_typ cD 1) tau2
         (r_paren_if cond)

    | Comp.TypCross (_, tau1, tau2) ->
       let cond = lvl > 0 in
       fprintf ppf "%s@[<2>@[%a@]@ * @[%a@]@]%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_typ cD 1) tau1
         (fmt_ppr_cmp_typ cD 0) tau2
         (r_paren_if cond)

    (* Special case for printing implicit context variable
       quantifiers; these can never be omitted, and are printed with
       parentheses instead of curly braces. *)
    | Comp.TypPiBox (_, LF.(Decl (_, CTyp _, Maybe) as d), tau) ->
       let cond = lvl > 1 in
       fprintf ppf "%s@[<2>(@[<2>%a@])@ @[%a@]%s@]"
         (l_paren_if cond)
         (fmt_ppr_lf_ctyp_decl cD) d
         (fmt_ppr_cmp_typ (LF.Dec(cD, d)) 1) tau
         (r_paren_if cond)

    | Comp.TypPiBox (_, ctyp_decl, tau) ->
       let ctyp_decl = fresh_name_ctyp_decl cD ctyp_decl in
       if not !PC.printImplicit && isImplicitDecl ctyp_decl then
         fprintf ppf "%a" (fmt_ppr_cmp_typ (LF.Dec (cD, ctyp_decl)) 1) tau
       else
         let cond = lvl > 1 in
         fprintf ppf "%s@[<2>{@[<2>%a@]}@ @[%a@]%s@]"
           (l_paren_if cond)
           (fmt_ppr_lf_ctyp_decl cD) ctyp_decl
           (fmt_ppr_cmp_typ (LF.Dec(cD, ctyp_decl)) 1) tau
           (r_paren_if cond)

    | Comp.TypClo (_, _ ) ->
       fprintf ppf "TypClo!"

    | Comp.TypInd tau ->
       if !PC.printImplicit then
         fprintf ppf "@[%a@]*"
           (fmt_ppr_cmp_typ cD 10) tau
       else
         fmt_ppr_cmp_typ cD lvl ppf tau

  let rec fmt_ppr_pat_spine cD cG lvl ppf = function
    | Comp.PatNil -> fprintf ppf ""
    | Comp.PatApp (_, pat, pat_spine) ->
       fprintf ppf "@[%a@]@ @[%a@]"
         (fmt_ppr_cmp_pattern cD cG (lvl+1)) pat
         (fmt_ppr_pat_spine cD cG lvl) pat_spine

  and fmt_ppr_cmp_pattern cD cG lvl ppf =
    let rec dropSpineLeft ms n = match (ms, n) with
      | (_, 0) -> ms
      | (Comp.PatNil, _) -> ms
      | (Comp.PatApp (_l,_p,rest), n) -> dropSpineLeft rest (n-1)
    in
    let deimplicitize_spine c ms =
      let ia =
        if !Printer.Control.printImplicit
        then 0
        else Store.Cid.CompConst.get_implicit_arguments c
      in
      dropSpineLeft ms ia
    in
    function
    | Comp.PatMetaObj (_, mO) ->
       fprintf ppf "@[%a@]"
         (fmt_ppr_cmp_meta_obj cD 0) mO
    | Comp.PatConst (_, c, pat_spine) ->
       let pat_spine = deimplicitize_spine c pat_spine in
       let cond = lvl > 1 in
       fprintf ppf "%s%s @[%a@]%s"
         (l_paren_if cond)
         (R.render_cid_comp_const c)
         (fmt_ppr_pat_spine cD cG 2) pat_spine
         (r_paren_if cond)

    | Comp.PatPair (_, pat1, pat2) ->
       fprintf ppf "(%a , %a)"
         (fmt_ppr_cmp_pattern cD cG 0) pat1
         (fmt_ppr_cmp_pattern cD cG 0) pat2
    | Comp.PatAnn (_, pat, _, `implicit) ->
       fmt_ppr_cmp_pattern cD cG 0 ppf pat

    | Comp.PatAnn (_, pat, tau, `explicit) ->
       fprintf ppf "(%a : %a)"
         (fmt_ppr_cmp_pattern cD cG 0) pat
         (fmt_ppr_cmp_typ cD 0) tau

    | Comp.PatVar (_, offset ) ->
       fprintf ppf "%s"
         (R.render_var cG offset)

    | Comp.PatFVar (_, name ) ->
       fprintf ppf "%s"
         (Id.render_name name)

  let rec fmt_ppr_cmp_numeric_order ppf =
    let print_list (left, right) ppf os =
      fprintf ppf "%s@[<hov>%a@]%s"
        left
        (pp_print_list ~pp_sep: pp_print_space
           fmt_ppr_cmp_numeric_order)
        os
        right
    in
    function
    | Comp.Arg x -> pp_print_int ppf x
    | Comp.Lex os ->
       print_list ("{", "}") ppf os
    | Comp.Simul os ->
       print_list ("[", "]") ppf os

  let fmt_ppr_cmp_total_dec_kind ppf = function
    | `trust -> fprintf ppf "trust"
    | `partial -> fprintf ppf "partial"
    | `not_recursive -> fprintf ppf "notrec"
    | `inductive order -> fprintf ppf "total @[%a@]"
         fmt_ppr_cmp_numeric_order order

  (** Prints a totality declaration for *debugging*.
      This does not generate syntactically valid Beluga.
   *)
  let fmt_ppr_cmp_total_dec ppf = function
    | { Comp.name; tau; order } ->
       fprintf ppf "@[<hov 2>@[%a@]:@ @[<hv 2>%a :@ @[%a@]@]@]"
         fmt_ppr_cmp_total_dec_kind order
         Id.print name
         (fmt_ppr_cmp_typ LF.Empty l0) tau

  let fmt_ppr_cmp_meta_branch_label ppf = function
    | `ctor cid -> fprintf ppf "%s" (R.render_cid_term cid)
    | `pvar k ->
       fprintf ppf "#%a"
         (Maybe.print (fun ppf -> fprintf ppf ".%d"))
         k
    | `bvar -> fprintf ppf "head variable"

  let rec fmt_ppr_cmp_exp_chk cD cG lvl ppf = function
    | Comp.Syn (_, i) ->
       fmt_ppr_cmp_exp_syn cD cG lvl ppf i

    | Comp.Fn (_, x, e) ->
       let x = fresh_name_gctx cG x in
       let cond = lvl > 0 in
       (*            fprintf ppf "@[<2>%sfn %s =>@ %a%s@]" *)
       fprintf ppf "%sfn %s =>@ "
         (l_paren_if cond)
         (Id.render_name x);

       fprintf ppf "%a%s"
         (fmt_ppr_cmp_exp_chk cD (LF.Dec(cG, Comp.CTypDeclOpt x))  0) e
         (r_paren_if cond);

    | Comp.Fun (_, fbr) -> fprintf ppf "Some fun"
    (* let cD1 = Context.append cD cD' in *)
    (* let cG1 = Context.append cG cG' in *)
    (*           let cond = lvl > 0 in *)
    (* (\*            fprintf ppf "@[<2>%sfun %s =>@ %a%s@]" *\) *)
    (*             fprintf ppf "%sfun %a =>@ " *)
    (*               (l_paren_if cond) *)
    (*               (fmt_ppr_pat_spine cD' cG' lvl) ps; *)

    (*             fprintf ppf "%a%s" *)
    (*               (fmt_ppr_cmp_exp_chk cD' cG' 0) e *)
    (*               (r_paren_if cond); *)


    | Comp.MLam (_, x, e) ->
       let x = fresh_name_mctx cD x in
       let cond = lvl > 0 in
       fprintf ppf "%smlam %s =>@ "
         (l_paren_if cond)
         (Id.render_name x);
       fprintf ppf "%a%s"
         (fmt_ppr_cmp_exp_chk (LF.Dec(cD, LF.DeclOpt x)) (Whnf.cnormGCtx (cG, LF.MShift 1)) 0) e
         (r_paren_if cond);

    | Comp.Pair (_, e1, e2) ->
       fprintf ppf "(%a , %a)"
         (fmt_ppr_cmp_exp_chk cD cG 0) e1
         (fmt_ppr_cmp_exp_chk cD cG 0) e2


    | Comp.LetPair(_, i, (x, y, e)) ->
       let x = fresh_name_gctx cG x in
       let y = fresh_name_gctx cG y in
       let cond = lvl > 1 in
       fprintf ppf "@[<2>%slet <%s,%s> = %a@ in %a%s@]"
         (l_paren_if cond)
         (Id.render_name x)
         (Id.render_name y)
         (fmt_ppr_cmp_exp_syn cD cG 0) i
         (fmt_ppr_cmp_exp_chk cD (LF.Dec(LF.Dec(cG, Comp.CTypDeclOpt x), Comp.CTypDeclOpt y)) 0) e
         (r_paren_if cond)


    | Comp.Let(_, i, (x, e)) ->
       let x = fresh_name_gctx cG x in
       let cond = lvl > 1 in
       fprintf ppf "%s@[@[<hv 2>let %s =@ @[%a@]@]@ in@ @[%a@]@]%s"
         (l_paren_if cond)
         (Id.render_name x)
         (fmt_ppr_cmp_exp_syn cD cG 0) i
         (fmt_ppr_cmp_exp_chk cD (LF.Dec(cG, Comp.CTypDeclOpt x)) 0) e
         (r_paren_if cond)

    | Comp.Box (_ , cM, cU) ->
       fmt_ppr_cmp_meta_obj_typed cD 0 ppf (cM, cU)

    | Comp.Impossible (_, i) ->
       let cond = lvl > 0 in
       fprintf ppf "%simpossible @[%a@]%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_exp_syn cD cG 0) i
         (r_paren_if cond)

    | Comp.Case (_, prag, i, bs) ->
       begin match bs with
       | [] ->
          let cond = lvl > 0 in
          fprintf ppf "%simpossible @[%a@]%s"
            (l_paren_if cond)
            (fmt_ppr_cmp_exp_syn cD cG 0) i
            (r_paren_if cond)
       | [Comp.Branch (_, cD_prefix, (cD_b, cG_b), pat, t, e)] ->
          let cond = lvl > 1 in
          fprintf ppf "%s@[<hv>@[<hv>let @[%a@[<h>%a@] =@ @[%a@]@]@ @]in@ @[%a@]@]%s"
            (l_paren_if cond)
            (fmt_ppr_lf_mctx ~sep: pp_print_space l0) cD_prefix
            (fmt_ppr_cmp_pattern cD_b cG_b 0) pat
            (fmt_ppr_cmp_exp_syn cD cG 0) i
            (fmt_ppr_cmp_exp_chk cD_b (Context.append cG cG_b) 0) e
            (r_paren_if cond)
       | bs ->
          let open Comp in
          let cond = lvl > 0 in
          fprintf ppf "%s@[<v>case @[%a@] of%s@,@[%a@]@]%s"
            (l_paren_if cond)
            (fmt_ppr_cmp_exp_syn cD cG 0) i
            (match prag with PragmaCase -> "" | PragmaNotCase -> " --not")
            (fmt_ppr_cmp_branches cG) bs
            (r_paren_if cond)
       end

    | Comp.Hole (loc, id, name) ->
       let name =
         let open HoleId in
         match name with
         | Named n -> n
         | Anonymous -> "" in
       try
         fprintf ppf "?%s" name
       with
       | _ -> fprintf ppf "?%s" name

  and fmt_ppr_cmp_exp_syn cD cG lvl ppf = function
    | Comp.Var (_, x) ->
       fprintf ppf "%s"
         (R.render_var cG x)

    | Comp.Const (_ ,prog) ->
       fprintf ppf "%s"
         (R.render_cid_prog prog)

    | Comp.DataConst (_, c) ->
       fprintf ppf "%s"
         (R.render_cid_comp_const c)

    | Comp.Obs (_, e, t, obs) ->
       fprintf ppf "%a.%s"
         (fmt_ppr_cmp_exp_chk cD cG 1) e
         (R.render_cid_comp_dest obs)

    | Comp.Apply (_, i, e) ->
       let cond = lvl > 1 in
       fprintf ppf "%s@[<2>@[%a@]@ @[%a@]@]%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_exp_syn cD cG 1) i
         (fmt_ppr_cmp_exp_chk cD cG 2) e
         (r_paren_if cond)

    | Comp.MApp (_, i, cM, cU, pl) ->
       let cond = lvl > 1 in
       if !PC.printImplicit || Comp.is_explicit pl then
         fprintf ppf "%s@[<2>@[%a@]@ @[%a@]@]%s"
           (l_paren_if cond)
           (fmt_ppr_cmp_exp_syn cD cG 1) i
           (fmt_ppr_cmp_meta_obj_typed cD 0) (cM, cU)
           (r_paren_if cond)
       else
         fmt_ppr_cmp_exp_syn cD cG lvl ppf i (* not printing implicits *)

    | Comp.PairVal (loc, i1, i2) ->
       fprintf ppf "@[( %a@,, %a)@]"
         (fmt_ppr_cmp_exp_syn cD cG 0) i1
         (fmt_ppr_cmp_exp_syn cD cG 0) i2

    | Comp.AnnBox (cM, cT) ->
       fmt_ppr_cmp_meta_obj_typed cD 1 ppf (cM, cT)

  and fmt_ppr_cmp_value lvl ppf =
    function
    | Comp.FunValue _ -> fprintf ppf " fn "
    | Comp.ThmValue _ -> fprintf ppf " rec "
    | Comp.MLamValue _ -> fprintf ppf " mlam "
    | Comp.CtxValue _ -> fprintf ppf " mlam "
    | Comp.BoxValue mC -> fprintf ppf "%a"  (fmt_ppr_cmp_meta_obj LF.Empty 0) mC
    | Comp.ConstValue _ -> fprintf ppf " const "
    | Comp.PairValue (v1, v2) ->
       fprintf ppf "(%a , %a)"
         (fmt_ppr_cmp_value 0) v1
         (fmt_ppr_cmp_value 0) v2
    | Comp.DataValue (c, spine) ->
       (* Note: Arguments in data spines are accumulated in reverse order, to
          allow applications of data values in constant time. *)
       let k = if !Printer.Control.printImplicit then 0
               else Store.Cid.CompConst.get_implicit_arguments c in
       (* the function drop and print_spine can probably be combined
          to avoid traversing the spine twice.
        *)
       let rec drop ms = match ms with
         | Comp.DataNil -> (Comp.DataNil, 0)
         | Comp.DataApp (v, spine) ->
            let (ms', k') = drop spine in
            if k' < k then (ms', k'+1)
            else (Comp.DataApp (v, ms'), k'+1)
       in
       let rec print_spine ppf = function
         | Comp.DataNil -> ()
         | Comp.DataApp (v, spine) ->
            print_spine ppf spine;
            fprintf ppf " %a" (fmt_ppr_cmp_value 1 ) v
       in
       let (pat_spine, k') = drop spine in (* k = length of original spine *)


       let cond = lvl > 0 &&  (k' - k) > 1 in
       fprintf ppf "%s%s%a%s"
         (l_paren_if cond)
         (R.render_cid_comp_const c) print_spine pat_spine
         (r_paren_if cond)

  and fmt_ppr_cmp_branches cG ppf bs =
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut (fmt_ppr_cmp_branch cG))
      bs

  and fmt_ppr_cmp_branch cG ppf = function
    | Comp.Branch (_, cD_prefix, (cD1', cG_p), pat, t, e) ->
       fprintf ppf "@[<v2>| @[%a@]@[%a@] =>@ @[%a@]@]"
         (fmt_ppr_lf_mctx 0) cD_prefix
         (fmt_ppr_cmp_pattern cD1' cG_p 0) pat
         (* NOTE: Technically: cD |- cG ctx and
          *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1|
          * -bp
          *)
         (fmt_ppr_cmp_exp_chk cD1' (Context.append cG cG_p) 1) e

  and fmt_ppr_cmp_subgoal_path cD cG ppf path =
    let rec format_path =
      let open Comp.SubgoalPath in
      function
      | Here -> []
      | Suffices (i, k, p) ->
         let f ppf () =
           fprintf ppf "premise %d of @[%a@]" k
             (fmt_ppr_cmp_exp_syn cD cG l0) i
         in
         f :: format_path p
      | Intros p ->
         (fun ppf () -> fprintf ppf "intros") :: format_path p
      | MetaSplit (i, lbl, p) ->
         let f ppf () =
           fprintf ppf "split @[%a@] (case @[%a@])"
             (fmt_ppr_cmp_exp_syn cD cG l0) i
             fmt_ppr_cmp_meta_branch_label lbl
         in
         f :: format_path p
      | CompSplit (i, c, p) ->
         let f ppf () =
           fprintf ppf "split @[%a@] (case %s)"
             (fmt_ppr_cmp_exp_syn cD cG l0) i
             (R.render_cid_comp_const c)
         in
         f :: format_path p
      | ContextSplit (i, Comp.EmptyContext _, p) ->
         let f ppf () =
           fprintf ppf "split @[%a@] (case empty context)"
             (fmt_ppr_cmp_exp_syn cD cG l0) i
         in
         f :: format_path p
      | ContextSplit (i, Comp.ExtendedBy (_, k), p) ->
         let f ppf () =
           fprintf ppf "split @[%a@] (case extended by %d)"
             (fmt_ppr_cmp_exp_syn cD cG l0) i
             k
         in
         f :: format_path p
    in
    let fs = format_path path in
    fprintf ppf "@[<hv 2>%a@]"
      (pp_print_list ~pp_sep: (fun ppf () -> fprintf ppf " <-@ ")
         (fun ppf f -> f ppf ()))
      fs

  and fmt_ppr_cmp_proof_state ppf =
    let print_line ppf () = for _ = 1 to 80 do fprintf ppf "-" done in
    let open Comp in
    fun { context = {cD; cG; _} as ctx ; goal; solution; label } ->
    fprintf ppf
      "@[<v>%a\
       @,%a\
       @,%a\
       @,%a
       @]"
      (fmt_ppr_cmp_subgoal_path cD cG) (label SubgoalPath.Here)
      fmt_ppr_cmp_hypotheses_listing ctx
      print_line ()
      (fmt_ppr_cmp_typ cD l0) (Whnf.cnormCTyp goal)

  and fmt_ppr_cmp_proof cD cG ppf =
    let open Comp in
    function
    | Incomplete (_, g) ->
       begin
         match ! (g.solution) with
         | None -> fprintf ppf "?"
         | Some proof ->
            dprnt "[fmt_ppr_cmp_proof] chasing pointer!";
            fmt_ppr_cmp_proof cD cG ppf proof
       end
    | Command ( stmt, proof ) ->
       fprintf ppf "%a"
         (fmt_ppr_cmp_command_and_proof cD cG) (stmt, proof)
    | Directive d ->
       fmt_ppr_cmp_directive cD cG ppf d

  and fmt_ppr_cmp_command cD cG ppf cmd =
    let open Comp in
    match cmd with
    | Unbox (i, name, _) ->
       fprintf ppf "@[<hv>by @[%a@]@ as %a unboxed@]"
         (fmt_ppr_cmp_exp_syn cD cG l0) i
         Id.print name
    | By (i, name, _) ->
       fprintf ppf "@[<hv 2>by @[%a@]@ as %a@]"
         (fmt_ppr_cmp_exp_syn cD cG l0) i
         Id.print name

  and fmt_ppr_cmp_command_and_proof cD cG ppf (c, p) =
    let (cD', cG', _) = Whnf.apply_command_to_context (cD, cG) c in
    fprintf ppf
      "@[%a@];@,%a"
      (fmt_ppr_cmp_command cD cG) c
      (fmt_ppr_cmp_proof cD' cG') p

  (** Pretty-prints a Harpoon split branch who's case label is of the
      abstract type `b` using the supplied printing function.
   *)
  and fmt_ppr_cmp_split_branch :
        type b. LF.mctx -> Comp.gctx -> (Format.formatter -> b -> unit) ->
        Format.formatter ->
        b Comp.split_branch -> unit =
    fun cD cG f ppf ->
    let open Comp in
    function
    | SplitBranch (c, _, _, h) ->
       let Hypothetical (hyp, _) = h in
       fprintf ppf "@[<v>case %a:@,%a@]"
         f c
         (fmt_ppr_cmp_hypothetical cD cG) h

  and fmt_ppr_cmp_directive cD cG ppf : Comp.directive -> unit =
    let open Comp in
    let print_split ppf i bs f =
      fprintf ppf "@[split@ @[%a@] as@]@,@[<v>%a@]"
        (fmt_ppr_cmp_exp_syn cD cG l0) i
         (pp_print_list ~pp_sep: pp_print_cut
            (fmt_ppr_cmp_split_branch cD cG f))
         bs
    in
    function
    | Intros h -> fprintf ppf "intros@,%a" (fmt_ppr_cmp_hypothetical cD cG) h
    | Suffices (i, ps) ->
       fprintf ppf "@[<v>@[<2>suffices by@ @[%a@]@] toshow@,@[<v>%a@]@]"
         (Printer.fmt_ppr_implicits false
            (fmt_ppr_cmp_exp_syn cD cG l0))
         i
         (pp_print_list ~pp_sep: pp_print_cut
            (fun ppf (_, tau, p) ->
              fprintf ppf "@[<v 2>@[%a@] {@,@[<v>%a@]@]@,}"
                (fmt_ppr_cmp_typ cD l0) tau
                (fmt_ppr_cmp_proof cD cG) p))
         ps
    | ImpossibleSplit i ->
       fprintf ppf "impossible @[%a@]"
         (Printer.fmt_ppr_implicits false
            (fmt_ppr_cmp_exp_syn cD cG l0))
         i

    | MetaSplit (i, _, bs) ->
       print_split ppf i bs fmt_ppr_cmp_meta_branch_label

    | CompSplit (i, _, bs) ->
       print_split ppf i bs
         (fun ppf c -> fprintf ppf "%s" (R.render_cid_comp_const c))

    | ContextSplit (i, _, bs) ->
       print_split ppf i bs fmt_ppr_cmp_context_case

    | Solve t ->
       fprintf ppf "@[<hov 2>solve@ @[%a@]@]"
         (Printer.fmt_ppr_implicits false
            (fmt_ppr_cmp_exp_chk cD cG l0))
         t;

  and fmt_ppr_cmp_hypotheses_listing ppf =
    let open Comp in
    fun { cD; cG; _ } ->
    fprintf ppf
      "@[<v>Meta-context:\
       @,  @[<v>%a@]\
       @,Computational context:\
       @,  @[<v>%a@]
       @]"
      (pp_print_list ~pp_sep: pp_print_cut
         (fun ppf (cD, d) ->
           fprintf ppf "@[<hv 2>%a@]" (fmt_ppr_lf_ctyp_decl_harpoon cD) d))
      (Context.to_sublist cD)
      (pp_print_list ~pp_sep: pp_print_cut
         (fun ppf d ->
           fprintf ppf "@[<hv 2>%a@]" (fmt_ppr_cmp_ctyp_decl cD l0) d))
      (Context.to_list cG)

  and fmt_ppr_cmp_hypothetical cD cG ppf =
    let open Comp in
    function
    | Hypothetical (h, proof) ->
       fprintf ppf "@[<v>{ %a @[<v>%a@]@,}@]"
         fmt_ppr_cmp_hypotheses h
         (fmt_ppr_cmp_proof h.cD h.cG) proof;

  and fmt_ppr_cmp_hypotheses ppf =
    let open Comp in
    let comma_sep_by fmt l = pp_print_list ~pp_sep: Fmt.comma fmt l in
    fun { cD; cG; _ } ->
    fprintf ppf "@[<hv>%a@]@,| @[<hv>%a@]@,;"
      (comma_sep_by
         begin fun ppf (cD, x) ->
         fprintf ppf "@[<hov 2>%a@]" (fmt_ppr_lf_ctyp_decl cD) x
         end)
      (Context.to_sublist cD)
      (comma_sep_by (fmt_ppr_cmp_ctyp_decl cD l0))
      (Context.to_list cG)

  and fmt_ppr_cmp_ih_arg cD ppf = function
    | Comp.M m_obj -> fmt_ppr_cmp_meta_obj cD l0 ppf m_obj
    | Comp.V k -> fprintf ppf "(offset %d)" k
    | Comp.DC -> fprintf ppf "_"
    | Comp.E -> Misc.not_implemented "IH E printing"

  and fmt_ppr_cmp_ctyp_decl cD lvl ppf = function
    | Comp.CTypDecl (x, tau, tag) ->
       fprintf ppf "@[<hov 2>%a@[%a@] :@ @[%a@]@]"
         Id.print x
         print_wf_tag (tag && !PC.printImplicit)
         (fmt_ppr_cmp_typ cD lvl) tau

    | Comp.CTypDeclOpt x ->
       fprintf ppf "%a : _" Id.print x

  and fmt_ppr_cmp_gctx ?(sep = Fmt.comma) cD lvl ppf cG =
    fmt_ppr_ctx_filter ~sep: sep
      (Misc.const true)
      (fun ppf (_, d) -> fmt_ppr_cmp_ctyp_decl cD l0 ppf d)
      ppf
      cG

  let fmt_ppr_cmp_gctx_typing ppf (cD, cG) =
    fprintf ppf "@[%a@] |-@ @[%a@]"
      (fmt_ppr_lf_mctx l0) cD
      (fmt_ppr_cmp_gctx cD l0) cG

  let fmt_ppr_cmp_typ_typing ppf (cD, tau) =
    fprintf ppf "@[%a@] |-@ @[%a@]"
    (fmt_ppr_lf_mctx l0) cD
    (fmt_ppr_cmp_typ cD l0) tau

  let fmt_ppr_cmp_comp_prog_info ppf e =
    let {CompS.Entry.name; implicit_arguments; typ; prog; mutual_group; hidden} = e in
    let ds = CompS.lookup_mutual_group mutual_group in
    fprintf ppf
      "@[<v>name: @[%a@]\
       @,@[<hv 2>type:@ @[%a@]@]\
       @,implicit parameters: %d\
       @,hidden: %b\
       @,mutual_group: @[%a@]\
       @,@[<hv 2>total_decs:@ @[%a@]@]\
       @,@[<hv 2>definition:@ @[%a@]@]\
       @,@]"
      Id.print name
      (fmt_ppr_cmp_typ LF.Empty l0) typ
      implicit_arguments
      hidden
      CompS.fmt_ppr_mutual_group_id mutual_group
      (Maybe.print (pp_print_list ~pp_sep: pp_print_cut fmt_ppr_cmp_total_dec)) ds
      (Maybe.print (fmt_ppr_cmp_value l0)) prog

  let fmt_ppr_cmp_thm ppf = function
    (* should cG contain a Dec for the theorem itself? *)
    | Comp.Program e ->
       fmt_ppr_cmp_exp_chk LF.Empty LF.Empty 0 ppf e
    | Comp.Proof p ->
       fmt_ppr_cmp_proof LF.Empty LF.Empty ppf p

  let fmt_ppr_cmp_thm_prefix ppf = function
    | Comp.Program _ -> fprintf ppf "rec"
    | Comp.Proof _ -> fprintf ppf "proof"


  let fmt_ppr_cmp_ih_args cD cG ppf : Comp.ih_arg list -> unit =
    pp_print_list ~pp_sep: pp_print_space (fmt_ppr_cmp_ih_arg cD) ppf

  let fmt_ppr_cmp_ih cD cG ppf (Comp.WfRec (f, args, tau)) =
    fprintf ppf "@[<hv 2>@[%a@] @[%a@] :@ @[%a@]@]"
      Id.print f
      (fmt_ppr_cmp_ih_args cD cG) args
      (fmt_ppr_cmp_typ cD l0) tau

  let fmt_ppr_cmp_ihctx cD cG ppf cIH =
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut (fmt_ppr_cmp_ih cD cG))
      (Context.to_list cIH)

  let fmt_ppr_sgn_thm_decl ppf = function
    | Sgn.({ thm_name; thm_typ; thm_body; thm_loc }) ->
       fprintf ppf "%a %s : %a =@ @[<v2>%a;@]"
         fmt_ppr_cmp_thm_prefix thm_body
         (R.render_cid_prog thm_name)
         (fmt_ppr_cmp_typ LF.Empty 0) thm_typ
         fmt_ppr_cmp_thm thm_body

  let rec fmt_ppr_sgn_decl ppf = function
    | Sgn.CompTypAbbrev (_,_,_,_) -> ()
    | Sgn.Const (_, c, a) ->
       fprintf ppf "%s : %a.@\n"
         (R.render_cid_term c)
         (fmt_ppr_lf_typ LF.Empty  LF.Null l0)  a

    | Sgn.Typ (_, a, k) ->
       fprintf ppf "%s : %a.@\n"
         (R.render_cid_typ  a)
         (fmt_ppr_lf_kind LF.Null l0) k

    | Sgn.CompTyp (_, a, cK, _) ->
       fprintf ppf "@\ndatatype %s : @[%a@] = @\n"
         (Id.render_name a)
         (fmt_ppr_cmp_kind LF.Empty l0) cK

    | Sgn.CompCotyp (_, a, cK) ->
       fprintf ppf "@\ncodatatype %s : @[%a@] = @\n"
         (Id.render_name a)
         (fmt_ppr_cmp_kind LF.Empty l0) cK

    | Sgn.CompDest (_, c, cD, tau0, tau1) ->
       fprintf ppf "@ | (%s : @[%a@] :: @[%a@]@\n"
         (Id.render_name c)
         (fmt_ppr_cmp_typ cD l0) tau0
         (fmt_ppr_cmp_typ cD l0) tau1
    | Sgn.CompConst (_, c, tau) ->
       fprintf ppf "@ | %s : @[%a@]@\n"
         (Id.render_name c)
         (fmt_ppr_cmp_typ LF.Empty l0) tau

    | Sgn.MRecTyp(_, l) -> List.iter (fmt_ppr_sgn_decl ppf) (List.flatten l)

    | Sgn.Val (_, x, tau, i, None) ->
       fprintf ppf "@\nlet %s : %a = %a@\n"
         (Id.render_name x)
         (fmt_ppr_cmp_typ LF.Empty l0) tau
         (fmt_ppr_cmp_exp_chk LF.Empty LF.Empty l0) i

    | Sgn.Val (_, x, tau, i, Some v) ->
       fprintf ppf "@\nlet %s : %a = %a@\n   ===> %a@\n"
         (Id.render_name x)
         (fmt_ppr_cmp_typ LF.Empty l0) tau
         (fmt_ppr_cmp_exp_chk LF.Empty LF.Empty l0) i
         (fmt_ppr_cmp_value l0) v

    | Sgn.Schema (w, schema) ->
       fprintf ppf "@\nschema %s = @[%a@];@\n"
         (R.render_cid_schema  w)
         (fmt_ppr_lf_schema ~useName:false l0) schema

    | Sgn.Theorem thms ->
       fprintf ppf "@[<v>%a@]"
         (pp_print_list ~pp_sep: (fun ppf _ -> fprintf ppf "@,and ")
            (fun ppf x ->
              fprintf ppf "@[%a@]"
                fmt_ppr_sgn_thm_decl x))
         thms

      (*
    | Sgn.Rec (((f, _, _ ) as h)::t) ->
       let total = if (Store.Cid.Comp.get f).Store.Cid.Comp.total
                   then " total" else ""
       in
       fmt_ppr_rec l0 ppf ("rec"^total) h;
       List.iter (fmt_ppr_rec l0 ppf ("and"^total)) t
       *)

    | Sgn.Pragma (LF.OpenPrag n) ->
       let n' = Store.Modules.name_of_id n in
       let _ = Store.Modules.open_module n' in
       fprintf ppf "@\n--open %s@\n" (String.concat "." n')

    | Sgn.Pragma _ -> ()

    | Sgn.Module(_, name, decls) ->
       let aux fmt t = List.iter (fun x -> (fmt_ppr_sgn_decl fmt x)) t in

       (* Necessary to enforce correct printing *)
       let ((_, origName, _, _) as state) = Store.Modules.getState () in
       let newName = origName@[name] in
       let _ = Store.Modules.current := (Store.Modules.id_of_name newName) in
       let _ = Store.Modules.currentName := newName in
       let _ = fprintf ppf "@\nmodule %s = struct@\n@[<v2>%a@]@\nend;@\n"
                 (name) (aux) decls in
       Store.Modules.setState state

    |  _ -> ()

  let fmt_ppr_sgn ppf sgn = List.iter (fmt_ppr_sgn_decl ppf) sgn
end (* Int.Make *)

(* Default Error Pretty Printer Functor Instantiation *)
module DefaultPrinter = Make (Store.Cid.NamedRenderer)
