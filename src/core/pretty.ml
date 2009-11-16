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


module Control = struct
  type substitution_style = Natural | DeBruijn

  let substitutionStyle = ref Natural
  let printImplicit = ref true

  let db() = !substitutionStyle = DeBruijn
end (* Control *)



module type CID_RENDERER = sig

  open Id
  open Syntax.Int

  val render_name         : name         -> string
  val render_cid_typ      : cid_typ      -> string
  val render_cid_term     : cid_term     -> string
  val render_cid_schema   : cid_schema   -> string
  val render_cid_coercion : cid_coercion -> string
  val render_cid_prog     : cid_prog     -> string
  val render_offset       : offset       -> string

  val render_ctx_var      : LF.mctx    -> offset   -> string
  val render_cvar         : LF.mctx    -> offset   -> string
  val render_bvar         : LF.dctx    -> offset   -> string
  val render_var          : Comp.gctx  -> var      -> string

end


module Int = struct

  open Id
  open Syntax.Int

  (* Internal Syntax Printer Signature *)
  module type PRINTER = sig

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

    val fmt_ppr_lf_coercion   : lvl -> formatter -> LF.coercion     -> unit

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

    val ppr_lf_coercion   : LF.coercion      -> unit

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
    val octxToString      : LF.mctx -> string

    val schemaToString    : LF.schema     -> string 
    val coercionToString  : LF.coercion   -> string 
    val gctxToString      : LF.mctx -> LF.mctx -> Comp.gctx  -> string
    val expChkToString    : LF.mctx -> LF.mctx -> Comp.gctx  -> Comp.exp_chk  -> string
    val expSynToString    : LF.mctx -> LF.mctx -> Comp.gctx  -> Comp.exp_syn  -> string
    val branchToString    : LF.mctx -> LF.mctx -> Comp.gctx  -> Comp.branch   -> string
    val compTypToString   : LF.mctx -> LF.mctx -> Comp.typ      -> string
    val msubToString      : LF.mctx -> LF.mctx -> LF.msub     -> string

  end (* Int.PRINTER *)

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

    let rec phatToDCtx phat = match phat with 
      | (None,      0) -> LF.Null
      | (Some psi , 0) -> LF.CtxVar psi
      | (ctx_v    , k) -> 
         LF.DDec (phatToDCtx (ctx_v, k-1), LF.TypDeclOpt (Id.mk_name Id.NoName)) 
        

    (* Contextual Format Based Pretty Printers 
     *
     * We assume types, terms, etc are all in normal form.
     *)
    let rec fmt_ppr_lf_typ cO cD cPsi lvl ppf = function
      | LF.Atom (_, a, LF.Nil) ->
          fprintf ppf "%s"
            (R.render_cid_typ a)

      | LF.Atom (_, a, ms) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%s%a%s"
              (l_paren_if cond)
              (R.render_cid_typ a)
              (fmt_ppr_lf_spine cO cD cPsi 2) ms
              (r_paren_if cond)

      | LF.PiTyp ((LF.TypDecl (x, a), LF.Maybe), b) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a} @ %a%s@]"
              (l_paren_if cond)
              (R.render_name  x)
              (fmt_ppr_lf_typ cO cD cPsi 0) a
              (fmt_ppr_lf_typ cO cD (LF.DDec(cPsi, LF.TypDecl(x, a))) 0) b
              (r_paren_if cond)

      | LF.PiTyp ((LF.TypDecl (x, a), LF.No), b) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s%a -> %a%s@]"
              (l_paren_if cond)
              (fmt_ppr_lf_typ cO cD cPsi 1) a
              (fmt_ppr_lf_typ cO cD (LF.DDec(cPsi, LF.TypDecl(x, a))) 0) b
              (r_paren_if cond)

      | LF.Sigma typRec ->
          fprintf ppf "%sblock %a%s"
            (l_paren_if (lvl > 0))
            (fmt_ppr_lf_typ_rec cO cD cPsi lvl) typRec
            (r_paren_if (lvl > 0))

    and fmt_ppr_tuple cO cD cPsi lvl ppf = function
      | LF.Last tM ->
           fmt_ppr_lf_normal cO cD cPsi lvl ppf tM

      | LF.Cons(tM, rest) ->
           fprintf ppf "%a, %a"
             (fmt_ppr_lf_normal cO cD cPsi lvl) tM
             (fmt_ppr_tuple cO cD cPsi lvl) rest

    and fmt_ppr_lf_normal cO cD cPsi lvl ppf =
      let rec dropSpineLeft ms n = match (ms, n) with
          (_, 0) -> ms
        | (LF.Nil, _) -> ms
        | (LF.App (_m, rest), n) -> dropSpineLeft rest (n - 1)

      in let deimplicitize_spine h ms = match h with
        | LF.Const c ->
            let implicit_arguments = if !Control.printImplicit
                                     then 0
                                     else Store.Cid.Term.get_implicit_arguments c
            in
              dropSpineLeft ms implicit_arguments

        | LF.MVar _
        | LF.BVar _
        | LF.PVar _
        | LF.FMVar _
        | LF.FPVar _
        | LF.Proj _  
        | LF.FVar _
        | LF.AnnH _ ->
            ms

      in function
        | LF.Lam (_, x, m) ->
            let cond = lvl > 0 in
              fprintf ppf "%s\\%s. %a%s"
                (l_paren_if cond)
                (R.render_name x)
                (fmt_ppr_lf_normal cO cD (LF.DDec(cPsi, LF.TypDeclOpt x)) 0) m
                (r_paren_if cond)

        | LF.Tuple (_, tuple) ->
           fprintf ppf "<%a>"
             (fmt_ppr_tuple cO cD cPsi lvl) tuple

        | LF.Root (_, h, LF.Nil) ->
            fprintf ppf "%a"
              (fmt_ppr_lf_head cO cD cPsi lvl) h

        | LF.Root (_, h, ms)  ->
            let cond = lvl > 1 in
            let ms = deimplicitize_spine h ms in
              fprintf ppf "%s%a%a%s"
                (l_paren_if cond)
                (fmt_ppr_lf_head cO cD cPsi lvl) h
                (fmt_ppr_lf_spine cO cD cPsi 2)  ms
                (r_paren_if cond)

        | LF.Clo(tM, s) -> fmt_ppr_lf_normal cO cD cPsi lvl ppf (Whnf.norm (tM, s))

    and fmt_ppr_lf_head cO cD cPsi lvl ppf head = 
      let paren s = not (Control.db()) && lvl > 0 && (match s with
        | LF.Shift _ when not (Context.hasCtxVar cPsi) -> false
        | _ -> true)
      in
      let rec fmt_head_with proj = function
      | LF.BVar x  ->
          fprintf ppf "%s%s"
            (R.render_bvar cPsi x)
            proj

      | LF.Const c ->
          fprintf ppf "%s%s"
            (R.render_cid_term c)
            proj

      | LF.MMVar (c, (ms, s)) ->
          fprintf ppf "%s?%a%s[%a]%a%s"
            (l_paren_if (paren s))
            (fmt_ppr_lf_mmvar cO lvl) c
            proj
            (fmt_ppr_lf_msub cO cD lvl) ms
            (fmt_ppr_lf_sub  cO cD cPsi lvl) s
            (r_paren_if (paren s))

      | LF.MVar (c, s) ->
          fprintf ppf "%s%a%s%a%s"
            (l_paren_if (paren s))
            (fmt_ppr_lf_cvar cO cD lvl) c
            proj
            (fmt_ppr_lf_sub  cO cD cPsi lvl) s
            (r_paren_if (paren s))

      | LF.PVar (c, s) ->
          fprintf ppf "%s#%a%s%a%s"
            (l_paren_if (paren s))
            (fmt_ppr_lf_cvar cO cD lvl) c
            proj
            (fmt_ppr_lf_sub  cO cD cPsi lvl) s
            (r_paren_if (paren s))

      | LF.FVar x ->
          fprintf ppf "%s%s"
            (R.render_name x)
            proj

      | LF.FMVar (u, s) ->
          fprintf ppf "%s%s%s%a%s"
            (l_paren_if (paren s))
            (R.render_name u)
            proj
            (fmt_ppr_lf_sub cO cD cPsi lvl) s
            (r_paren_if (paren s))

      | LF.FPVar (p, s) ->
          fprintf ppf "%s#%s%s%a%s"
            (l_paren_if (paren s))
            (R.render_name p)
            proj
            (fmt_ppr_lf_sub cO cD cPsi lvl) s
            (r_paren_if (paren s))

      | LF.Proj (head, k) ->
          fmt_head_with ("." ^ string_of_int k) head

      | LF.CoPVar (co_cid, p, k, s) ->
          fprintf ppf "%s%s#%a%s.%s%a"
            (R.render_cid_coercion co_cid)
            (l_paren_if (paren s))
            (fmt_ppr_lf_cvar cO cD lvl) p
            (r_paren_if (paren s))
            (string_of_int k)
            (fmt_ppr_lf_sub  cO cD cPsi lvl) s

      in
        fmt_head_with "" head


    and fmt_ppr_lf_spine cO cD cPsi lvl ppf = function
      | LF.Nil ->
          fprintf ppf ""

      | LF.App (m, ms) ->
          fprintf ppf " %a%a"
            (fmt_ppr_lf_normal  cO cD cPsi lvl) m
            (fmt_ppr_lf_spine   cO cD cPsi lvl) ms

    and fmt_ppr_lf_sub cO cD cPsi lvl ppf s =
      match !Control.substitutionStyle with
        | Control.Natural -> fmt_ppr_lf_sub_natural cO cD cPsi lvl ppf s
        | Control.DeBruijn -> fmt_ppr_lf_sub_deBruijn cO cD cPsi lvl ppf s

    and fmt_ppr_lf_sub_natural cO cD cPsi lvl ppf s=
      let print_front = fmt_ppr_lf_front cO cD cPsi 1 in
      let hasCtxVar = match Context.ctxVar cPsi with Some _ -> true | None -> false in
      let rec self lvl ppf =
        function
       (* Print ".." for a Shift when there is a context variable present,
          and nothing otherwise *)
        | LF.Shift _ when hasCtxVar     ->    fprintf ppf ".."
        | LF.Shift _ when not hasCtxVar  ->    () 

        | LF.CoShift (LF.Coe co_cid, _ , _ )  ->    
                fprintf ppf "%s(..)" 
                  (R.render_cid_coercion co_cid)
(*          fprintf ppf " <<<<<<<    %a    >>>>>>>"
            (fmt_ppr_lf_dctx cO cD lvl) cPsi
*)
        | LF.CoShift (LF.InvCoe co_cid , _ , _ )   ->    
                fprintf ppf "-%s(..)" 
                  (R.render_cid_coercion co_cid)
        | LF.SVar (c, s) ->
            fprintf ppf "%a[%a]"
              (fmt_ppr_lf_cvar cO cD lvl) c
              (self lvl) s
              
        | LF.Dot (f, s) when hasCtxVar ->
            fprintf ppf "%a %a"
              (self lvl) s
              print_front f
              
        | LF.Dot (f, LF.Shift _) when not hasCtxVar ->       (* No context variable, so just print the front *)
            fprintf ppf "%a"
              print_front f
              
        | LF.Dot (f, s) when not hasCtxVar ->
            fprintf ppf "%a %a"
              (self lvl) s
              print_front f
      in
        match s with
          | LF.Shift _ when not hasCtxVar ->  (* Print nothing at all, because the user would have written nothing at all *)
              ()
          | _ ->  (* For anything else, print a space first *)
              fprintf ppf " %a"
                (self lvl) s

    and fmt_ppr_lf_sub_deBruijn cO cD cPsi lvl ppf s =
      let rec self lvl ppf = function
        | LF.CoShift (LF.Coe co_cid, LF.NoCtxShift,n) ->

            fprintf ppf "co(%s)^%s"
              (R.render_cid_coercion co_cid)
              (R.render_offset n)


        | LF.CoShift (LF.InvCoe co_cid, LF.NoCtxShift,n) ->

            fprintf ppf "co(-%s)^%s"
              (R.render_cid_coercion co_cid)
              (R.render_offset n)

        | LF.Shift (LF.NoCtxShift,n) ->
            fprintf ppf "^%s"
              (R.render_offset n)

        | LF.Shift (LF.CtxShift (LF.CtxOffset psi), n) -> 
            fprintf ppf "^(ctxShift (%s) + %s)"
              (R.render_ctx_var cO psi)
              (R.render_offset n)

        | LF.Shift (LF.NegCtxShift (LF.CtxOffset psi), n) -> 
            fprintf ppf "^(NegShift(%s) + %s)"
              (R.render_ctx_var cO psi)
              (R.render_offset n)

        | LF.SVar (c, s) ->
            fprintf ppf "%a[%a]"
              (fmt_ppr_lf_cvar cO cD lvl) c
              (self lvl) s

        | LF.Dot (f, s) ->
            fprintf ppf "%a . %a"
              (fmt_ppr_lf_front cO cD cPsi 1) f
              (self lvl) s
      in
        fprintf ppf "[%a]"
          (self lvl) s


    and fmt_ppr_lf_front cO cD cPsi lvl ppf = function
      | LF.Head h ->
          fprintf ppf "%a"
            (fmt_ppr_lf_head cO cD cPsi lvl) h

      | LF.Block (h, index) -> 
          fprintf ppf "(block %a,%s)"
            (fmt_ppr_lf_head cO cD cPsi lvl) h
            (string_of_int index)

      | LF.Obj m ->
          fprintf ppf "%a"
            (fmt_ppr_lf_normal cO cD cPsi lvl) m

      | LF.Undef ->
          fprintf ppf "_"


    and fmt_ppr_lf_msub cO cD lvl ppf = function
      | LF.MShift k ->
          fprintf ppf "^%s" (string_of_int k)

      | LF.MDot (f, s) ->
          fprintf ppf "%a@ ,@ %a"
            (fmt_ppr_lf_mfront cO cD 1) f
            (fmt_ppr_lf_msub cO cD lvl) s


    and fmt_ppr_lf_mfront cO cD lvl ppf = function
      | LF.MObj (psihat, m) ->
          let cPsi = phatToDCtx psihat in 
          fprintf ppf "M (%a . %a)"
            (fmt_ppr_lf_psi_hat cO lvl) cPsi
            (fmt_ppr_lf_normal cO cD cPsi lvl) m

      | LF.PObj (psihat, h) ->
          let cPsi = phatToDCtx psihat in 
          fprintf ppf "P (%a . %a)"
            (fmt_ppr_lf_psi_hat cO lvl) cPsi
            (fmt_ppr_lf_head cO cD cPsi lvl) h

      | LF.MV k ->
          fprintf ppf "MV %s "
            (R.render_cvar cD k)

      | LF.MUndef -> 
          fprintf ppf "_ "

    and fmt_ppr_lf_mmvar cO lvl ppf = function
      | LF.MInst ({ contents = None } as u, _, _, tA, _) ->
          begin
            try
              fprintf ppf "?%s"
                (InstHashtbl.find inst_hashtbl u)
            with
              | Not_found ->
                  (* (* Should probably create a sep. generator for this -dwm *)
                  let sym = String.uppercase (Gensym.VarData.gensym ()) in
                  *)
                  (* Not working -bp *)
                  let sym = match Store.Cid.Typ.gen_mvar_name tA with 
                              | Some vGen -> vGen ()
                              | None -> Gensym.MVarData.gensym ()
                  in 
                      InstHashtbl.replace inst_hashtbl u sym
                    ; fprintf ppf "?%s" sym
          end
       
      | LF.MInst ({ contents = Some m}, cD, cPsi, _, _) ->
          fprintf ppf "MMV SOME %a"
            (fmt_ppr_lf_normal cO cD cPsi lvl) m

    and fmt_ppr_lf_cvar _cO cD _lvl ppf = function
      | LF.Offset n ->
          fprintf ppf "%s"
            (R.render_cvar cD n)

      | LF.Inst ({ contents = None } as u, _, tA, _) ->
          begin
            try
              fprintf ppf "?%s"
                (InstHashtbl.find inst_hashtbl u)
            with
              | Not_found ->
                  (* (* Should probably create a sep. generator for this -dwm *)
                  let sym = String.uppercase (Gensym.VarData.gensym ()) in
                  *)
                  (* Not working -bp *)
                  let sym = match Store.Cid.Typ.gen_mvar_name tA with 
                              | Some vGen -> vGen ()
                              | None -> Gensym.MVarData.gensym ()
                  in 
                      InstHashtbl.replace inst_hashtbl u sym
                    ; fprintf ppf "?%s" sym
          end

      | LF.PInst ({ contents = None } as p, _, _, _) ->
          begin
            try
              fprintf ppf "?%s"
                (PInstHashtbl.find pinst_hashtbl p)
            with
              | Not_found ->
                  (* Should probably create a sep. generator for this -dwm *)
                  let sym = String.lowercase (Gensym.VarData.gensym ()) in
                      PInstHashtbl.replace pinst_hashtbl p sym
                    ; fprintf ppf "%s" sym
          end



    and fmt_ppr_lf_ctx_var cO ppf = function
      | LF.CtxOffset psi ->
          fprintf ppf "%s"
            (R.render_ctx_var cO psi)
      | LF.CtxName psi ->
          fprintf ppf "%s"
            (R.render_name psi)

      | LF.CoCtx (co, c_var) -> 
          fprintf ppf "%s(%a)"
            (R.render_cid_coercion co)
            (fmt_ppr_lf_ctx_var cO) c_var


    and fmt_ppr_lf_typ_rec cO cD cPsi _lvl ppf typrec = 
       let ppr_element cO cD cPsi ppf suffix = function
       | (x, tA) ->
              fprintf ppf "%s:%a%s"
                (R.render_name x)
                (fmt_ppr_lf_typ cO cD cPsi 0) tA
               suffix
       in 
       let rec ppr_elements cO cD cPsi ppf = function
         | LF.SigmaLast tA -> fprintf ppf "%a" (fmt_ppr_lf_typ cO cD cPsi 0) tA
         | LF.SigmaElem (x, tA1, LF.SigmaLast tA2) -> 
             begin 
               ppr_element cO cD cPsi  ppf ". " (x, tA1); 
               fprintf ppf "%a" (fmt_ppr_lf_typ cO cD (LF.DDec(cPsi, LF.TypDecl(x, tA1))) 0) tA2 
             end
         | LF.SigmaElem (x, tA, tAs)  -> 
             begin 
               ppr_element cO cD cPsi ppf ", " (x, tA); 
               ppr_elements cO cD (LF.DDec(cPsi, LF.TypDecl (x, tA))) ppf  tAs 
             end
(*             | tA :: tAs -> *)
(*                   fprintf ppf "%a,@ %a" *)
(*                     (fmt_ppr_lf_typ cD cPsi 0) tA *)
(*                     ppr_typ_rec        tAs *)
(*                fprintf ppf "Sigma %a. %a" *)
       in
         fprintf ppf "%a"
           (ppr_elements cO cD cPsi) typrec

    and projectCtxIntoDctx = function
         |  LF.Empty -> LF.Null
         |  LF.Dec (rest, last) -> LF.DDec (projectCtxIntoDctx rest, last)

    and fmt_ppr_lf_schema lvl ppf = function
      | LF.Schema [] -> ()

      | LF.Schema (f :: []) ->
            fprintf ppf "%a"
              (fmt_ppr_lf_sch_elem lvl) f

      | LF.Schema (f :: fs) ->
            fprintf ppf "%a@ + "
              (fmt_ppr_lf_sch_elem lvl) f
          ; fmt_ppr_lf_schema lvl ppf (LF.Schema fs)

    and fmt_ppr_lf_sch_elem lvl ppf = function
      | LF.SchElem (typDecls, sgmDecl) ->
          let cPsi = projectCtxIntoDctx typDecls in 
            fprintf ppf "some [%a] block %a"
              (ppr_typ_decl_dctx  LF.Empty)  cPsi
              (fmt_ppr_lf_typ_rec LF.Empty LF.Empty cPsi lvl) sgmDecl


    and ppr_typ_decl_dctx cD ppf = function
      | LF.Null ->  
          fprintf ppf "" 
            
      | LF.DDec (LF.Null, LF.TypDecl (x, tA)) ->
          fprintf ppf "., %s : %a"
            (R.render_name x)
            (fmt_ppr_lf_typ LF.Empty cD LF.Null 0) tA 
            
      | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
          fprintf ppf "%a, %s : %a"
            (ppr_typ_decl_dctx cD) cPsi
            (R.render_name x)
            (fmt_ppr_lf_typ LF.Empty cD cPsi 0) tA

    and fmt_ppr_lf_coercion lvl ppf = function
      | [LF.CoBranch (t_ctx, trec1, Some trec2)] ->
          let cPsi = projectCtxIntoDctx t_ctx in 
          fprintf ppf " some [%a] block %a => %a"
            (ppr_typ_decl_dctx  LF.Empty)  cPsi
            (fmt_ppr_lf_typ_rec LF.Empty LF.Empty cPsi 0) trec1
            (fmt_ppr_lf_typ_rec LF.Empty LF.Empty cPsi 0) trec2

      | [LF.CoBranch (t_ctx, trec1, None)] ->
          let cPsi = projectCtxIntoDctx t_ctx in 
          fprintf ppf " some [%a] block %a => _"
            (ppr_typ_decl_dctx  LF.Empty)  cPsi
            (fmt_ppr_lf_typ_rec LF.Empty LF.Empty cPsi 0) trec1

      | LF.CoBranch (t_ctx, trec1, Some trec2) :: c_list -> 
          let cPsi = projectCtxIntoDctx t_ctx in 
          fprintf ppf "some [%a] block %a => %a @ @[<0>|%a@]"
            (ppr_typ_decl_dctx  LF.Empty)  cPsi
            (fmt_ppr_lf_typ_rec LF.Empty LF.Empty cPsi 0) trec1
            (fmt_ppr_lf_typ_rec LF.Empty LF.Empty cPsi 0) trec2
            (fmt_ppr_lf_coercion lvl) c_list

      | LF.CoBranch (t_ctx, trec1, None) :: c_list -> 
          let cPsi = projectCtxIntoDctx t_ctx in 
          fprintf ppf "some [%a] block %a => _ @ @[<0>|%a@]"
            (ppr_typ_decl_dctx  LF.Empty)  cPsi
            (fmt_ppr_lf_typ_rec LF.Empty LF.Empty cPsi 0) trec1
            (fmt_ppr_lf_coercion lvl) c_list


    and fmt_ppr_lf_psi_hat cO _lvl ppf = function
      | LF.Null   -> fprintf ppf "" 

      | LF.CtxVar ctx_var ->
          fmt_ppr_lf_ctx_var cO ppf ctx_var

      | LF.DDec (LF.Null, LF.TypDeclOpt x) ->
          fprintf ppf "%s"
            (R.render_name x)

      | LF.DDec (cPsi, LF.TypDeclOpt x) ->
          fprintf ppf "%a, %s"
            (fmt_ppr_lf_psi_hat cO 0) cPsi
            (R.render_name x)

      | LF.DDec (LF.Null, LF.TypDecl(x, _ )) ->
          fprintf ppf "%s"
            (R.render_name x)

      | LF.DDec (cPsi, LF.TypDecl(x, _ )) ->
          fprintf ppf "%a, %s"
            (fmt_ppr_lf_psi_hat cO 0) cPsi
            (R.render_name x)

    and fmt_ppr_lf_dctx cO cD _lvl ppf = function
      | LF.Null ->
          fprintf ppf ""

      | LF.CtxVar ctx_var ->
          fmt_ppr_lf_ctx_var cO ppf ctx_var

      | LF.DDec (LF.Null, LF.TypDecl (x, tA)) ->
          fprintf ppf "%s : %a"
            (R.render_name x)
            (fmt_ppr_lf_typ cO cD LF.Null 0) tA

      | LF.DDec (LF.Null, LF.TypDeclOpt x) ->
          fprintf ppf "%s : _"
            (R.render_name x)

      | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
          fprintf ppf "%a, %s : %a"
            (fmt_ppr_lf_dctx cO cD 0) cPsi
            (R.render_name x)
            (fmt_ppr_lf_typ cO cD cPsi 0) tA

      | LF.DDec (cPsi, LF.TypDeclOpt x) ->
          fprintf ppf "%a, %s : _"
            (fmt_ppr_lf_dctx cO cD 0) cPsi
            (R.render_name x)

    and fmt_ppr_lf_mctx cO lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cD, ctyp_decl) ->
          fprintf ppf "%a, %a"
            (fmt_ppr_lf_mctx cO 0) cD
            (fmt_ppr_lf_ctyp_decl cO cD lvl) ctyp_decl

    and fmt_ppr_lf_octx lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cO, ctyp_decl) ->
          fprintf ppf "%a, %a"
            (fmt_ppr_lf_octx 0) cO
            (fmt_ppr_lf_ctyp_decl LF.Empty LF.Empty lvl) ctyp_decl



    and fmt_ppr_lf_kind cPsi lvl ppf = function
      | LF.Typ ->
          fprintf ppf "type"

      | LF.PiKind ((LF.TypDecl (x, a), LF.Maybe), k) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name   x)
              (fmt_ppr_lf_typ LF.Empty LF.Empty cPsi  0) a
              (fmt_ppr_lf_kind (LF.DDec(cPsi, LF.TypDeclOpt  x)) 0) k
              (r_paren_if cond)

      | LF.PiKind ((LF.TypDecl (x, a), LF.No), k) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s%a -> %a%s@]"
              (l_paren_if cond)
              (fmt_ppr_lf_typ LF.Empty LF.Empty cPsi  1) a
              (fmt_ppr_lf_kind (LF.DDec(cPsi, LF.TypDeclOpt  x)) 0) k
              (r_paren_if cond)



    and fmt_ppr_lf_ctyp_decl cO cD _lvl ppf = function
      | LF.MDecl (u, tA, cPsi) ->
          fprintf ppf "{%s :: %a[%a]}"
            (R.render_name u)
            (fmt_ppr_lf_typ cO cD cPsi 2) tA
            (fmt_ppr_lf_dctx cO cD 0) cPsi

      | LF.PDecl (p, tA, cPsi) ->
          fprintf ppf "{#%s :: %a[%a]}"
            (R.render_name p)
            (fmt_ppr_lf_typ cO cD cPsi 2) tA
            (fmt_ppr_lf_dctx cO cD 0) cPsi

      | LF.CDecl (name, schemaName) ->
          fprintf ppf "{%s :: %a}"
            (R.render_name name)
            (fmt_ppr_lf_schema 0) (Store.Cid.Schema.get_schema schemaName)

      | LF.MDeclOpt name -> 
          fprintf ppf "{%s :: _ }"
            (R.render_name name)


      | LF.PDeclOpt name -> 
          fprintf ppf "{%s :: _ }"
            (R.render_name name)

    (* Computation-level *)

    let rec fmt_ppr_cmp_typ cO cD lvl ppf = function
      | Comp.TypBox (_, tA, cPsi) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_lf_typ cO cD cPsi 2) tA
            (fmt_ppr_lf_dctx cO cD 0) cPsi

      | Comp.TypArr (tau1, tau2) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a -> %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_typ cO cD 2) tau1
              (fmt_ppr_cmp_typ cO cD 0) tau2
              (r_paren_if cond)

      | Comp.TypCross (tau1, tau2) ->
          let cond = lvl > 0 in
            fprintf ppf "%s%a * %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_typ cO cD 1) tau1
              (fmt_ppr_cmp_typ cO cD 0) tau2
              (r_paren_if cond)

      | Comp.TypCtxPi ((psi, w), tau) ->
          let cond = lvl > 1 in
            fprintf ppf "%s{%s:(%s)*} %a%s"
              (l_paren_if cond)
              (R.render_name psi)
              (R.render_cid_schema w)
              (fmt_ppr_cmp_typ (LF.Dec(cO, LF.CDecl(psi, w))) cD 0) tau
              (r_paren_if cond)

      | Comp.TypPiBox ((ctyp_decl, _ ), tau) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_ctyp_decl cO cD 1) ctyp_decl
              (fmt_ppr_cmp_typ cO (LF.Dec(cD, ctyp_decl)) 1) tau
              (r_paren_if cond)

      | Comp.TypClo (_, _ ) ->             fprintf ppf " TypClo! "

    let rec fmt_ppr_cmp_exp_chk cO cD cG lvl ppf = function
      | Comp.Syn (_, i) ->
          fmt_ppr_cmp_exp_syn cO cD cG lvl ppf (strip_mapp_args cO cD cG i)

      | Comp.Fun (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%sfn %s =>@ %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk cO cD (LF.Dec(cG, Comp.CTypDeclOpt x))  0) e
              (r_paren_if cond)

      | Comp.CtxFun (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%sFN %s =>@ %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk (LF.Dec(cO, LF.CDeclOpt x)) cD cG 0) e
              (r_paren_if cond)

      | Comp.MLam (_, x, e) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<2>%smlam %s => @ %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (fmt_ppr_cmp_exp_chk cO (LF.Dec(cD, LF.MDeclOpt x)) cG 0) e
              (r_paren_if cond)

      | Comp.Pair (_, e1, e2) -> 
            fprintf ppf "(%a , %a)"
              (fmt_ppr_cmp_exp_chk cO cD cG 0) e1
              (fmt_ppr_cmp_exp_chk cO cD cG 0) e2


      | Comp.LetPair(_, i, (x, y, e)) -> 
          let cond = lvl > 1 in
            fprintf ppf "@[<2>%slet <%s,%s> = %a@ in %a%s@]"
              (l_paren_if cond)
              (R.render_name x)
              (R.render_name y)
              (fmt_ppr_cmp_exp_syn cO cD cG 0) (strip_mapp_args cO cD cG i)
              (fmt_ppr_cmp_exp_chk cO cD (LF.Dec(LF.Dec(cG, Comp.CTypDeclOpt x), Comp.CTypDeclOpt y)) 0) e
              (r_paren_if cond)

      | Comp.Box (_ , pHat, tM) ->
          let cond = lvl > 1 in
          let cPsi = phatToDCtx pHat in
            fprintf ppf "%s[%a] %a%s"
              (l_paren_if cond)
              (fmt_ppr_lf_psi_hat cO 0) cPsi
              (fmt_ppr_lf_normal cO cD cPsi 0) tM
              (r_paren_if cond)

      | Comp.Case (_, i, bs) ->
          let cond = lvl > 1 in
            fprintf ppf "@[<2>%scase %a @ of@[<-1>%a@]%s@]"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn cO cD cG 0) (strip_mapp_args cO cD cG i)
              (fmt_ppr_cmp_branches cO cD cG 0) bs
              (r_paren_if cond)

    and strip_mapp_args cO cD cG i = 
      if !Control.printImplicit then 
        i 
      else 
        let (i', _ ) = strip_mapp_args' cO cD cG i in i'

    and strip_mapp_args' cO cD cG i = match i with 
      | Comp.Const prog -> 
          (i,  implicitCompArg  (Store.Cid.Comp.get prog).Store.Cid.Comp.typ)
      | Comp.Var x -> 
          begin match Context.lookup cG x with
              None -> (i, 0) 
            | Some tau -> (i,  implicitCompArg tau)
          end 

      | Comp.Apply (loc, i, e) -> 
          let (i', _ ) = strip_mapp_args' cO cD cG i in 
            (Comp.Apply (loc, i', e), 0)

      | Comp.CtxApp (loc, i, cPsi) ->
          let (i', _ ) = strip_mapp_args' cO cD cG i in 
            (Comp.CtxApp (loc, i', cPsi), 0)

      | Comp.MApp (loc, i1, (phat, tM) ) -> 
          let (i', stripArg) = strip_mapp_args' cO cD cG i1 in 
            if stripArg = 0 then 
              (Comp.MApp (loc , i', (phat, tM)), 0)
            else 
              (i', stripArg - 1 )

      | Comp.Ann (e, tau) -> (Comp.Ann (e, tau), 0)


    and implicitCompArg tau = begin match tau with 
      | Comp.TypPiBox ((LF.MDecl _ , Comp.Implicit), tau) -> 
          implicitCompArg tau + 1 
      | _ -> 0
    end
        

    and fmt_ppr_cmp_exp_syn cO cD cG lvl ppf = function
      | Comp.Var x ->
          fprintf ppf "%s"
            (R.render_var cG x)

      | Comp.Const prog ->
          fprintf ppf "%s"
            (R.render_cid_prog prog)

      | Comp.Apply (_, i, e) ->
          let cond = lvl > 1 in
            fprintf ppf "%s@[<2>%a @ %a@]%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn cO cD cG 1) i
              (fmt_ppr_cmp_exp_chk cO cD cG 2) e
              (r_paren_if cond)

      | Comp.CtxApp (_, i, cPsi) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a @ [%a]%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn cO cD cG 1) i
              (fmt_ppr_lf_dctx cO cD 0) cPsi
              (r_paren_if cond)

      | Comp.MApp (_, i, (pHat, tM)) ->
          let cond = lvl > 1 in
          let cPsi = phatToDCtx pHat in
            fprintf ppf "%s%a @ < %a. %a > %s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_syn cO cD cG 1) i
              (fmt_ppr_lf_psi_hat cO 0) cPsi
              (fmt_ppr_lf_normal cO cD cPsi 0) tM
              (r_paren_if cond)

      | Comp.Ann (e, tau) ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a : %a%s"
              (l_paren_if cond)
              (fmt_ppr_cmp_exp_chk cO cD cG 1) e
              (fmt_ppr_cmp_typ cO cD 2) (Whnf.cnormCTyp (tau, Whnf.m_id))
              (r_paren_if cond)


    and fmt_ppr_cmp_branches cO cD cG lvl ppf = function
      | [] -> ()

      | b :: [] ->
          fprintf ppf "%a"
            (fmt_ppr_cmp_branch cO cD cG 0) b

      | b :: bs ->
          fprintf ppf "%a @ @[<0>|%a@]"
            (fmt_ppr_cmp_branch cO cD cG 0) b
            (fmt_ppr_cmp_branches cO cD cG lvl) bs


    and fmt_ppr_cmp_branch cO cD cG _lvl ppf = function
      | Comp.BranchBox (cD1', (phat, tM, t), e) ->
          let rec ppr_ctyp_decls cO ppf = function
            | LF.Empty             -> fprintf ppf ""

            | LF.Dec (cD, decl) ->
                fprintf ppf "%a @ %a"
                  (ppr_ctyp_decls cO) cD
                  (fmt_ppr_lf_ctyp_decl cO cD 1) decl
          in
          let cPsi = phatToDCtx phat in
(*            fprintf ppf "%a @ [%a] %a : %a[%a] => @ @[<2>%a@]@ " *)
            fprintf ppf "%a @ ([%a] %a) @ : %a  => @ @[<2>%a@]@ "
              (ppr_ctyp_decls cO) cD1'
              (fmt_ppr_lf_psi_hat cO 0) cPsi
              (fmt_ppr_lf_normal cO cD1' cPsi 0) tM
              (* (fmt_ppr_lf_msub cO cD1' 2) t   *)
              (fmt_ppr_refinement cO cD1' cD 2) t
              (* NOTE: Technically: cD |- cG ctx and 
               *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1|
               * -bp
               *) 
              (fmt_ppr_cmp_exp_chk cO cD1' (Whnf.cnormCtx (cG, t)) 1) e


    (* cD |- t : cD'  *)

    and fmt_ppr_refinement cO cD cD0 lvl ppf t = begin match (t, cD0) with
      | (LF.MShift _, _ ) ->
          fprintf ppf "" 

      | (LF.MDot (f, s), LF.Dec(cD', decl)) -> 
          fprintf ppf "%a@ ,@ %a"
            (fmt_ppr_refine_elem cO cD decl 1) f
            (fmt_ppr_refinement cO cD cD' lvl) s
    end


    and fmt_ppr_refine_elem cO cD decl lvl ppf = function 
      | LF.MObj (psihat, m) ->
          let cPsi = phatToDCtx psihat in 
          let u    = 
            begin match decl with 
              | LF.MDecl(u, _ , _ ) -> u 
              | LF.MDeclOpt u -> u 
            end in
          fprintf ppf "%a . %a = %s"           
            (fmt_ppr_lf_psi_hat cO lvl) cPsi
            (fmt_ppr_lf_normal cO cD cPsi lvl) m
            (R.render_name u)

      | LF.PObj (psihat, h) ->
          let cPsi = phatToDCtx psihat in 
          let p = 
            begin match decl with 
              | LF.PDecl(p, _ , _ ) -> p 
              | LF.PDeclOpt p -> p 
            end in
          fprintf ppf "%a . %a = #%s"
            (fmt_ppr_lf_psi_hat cO lvl) cPsi
            (fmt_ppr_lf_head cO cD cPsi lvl) h
            (R.render_name p)


    let rec fmt_ppr_cmp_gctx cO cD lvl ppf = function
      | LF.Empty ->
          fprintf ppf "."

      | LF.Dec (cG, Comp.CTypDecl (x, tau)) ->
          fprintf ppf "%a, %s: %a"
            (fmt_ppr_cmp_gctx cO cD 0) cG
            (R.render_name x)
            (fmt_ppr_cmp_typ cO cD lvl) tau



    let rec fmt_ppr_sgn_decl lvl ppf = function
      | Sgn.Const (c, a) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_cid_term c)
            (fmt_ppr_lf_typ LF.Empty LF.Empty LF.Null lvl)  a

      | Sgn.Typ (a, k) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_cid_typ  a)
            (fmt_ppr_lf_kind LF.Null lvl) k

      | Sgn.Schema (w, schema) ->
          fprintf ppf "schema %s : %a;@.@?"
            (R.render_cid_schema  w)
            (fmt_ppr_lf_schema lvl) schema

      | Sgn.Rec (f, tau, e) ->
          fprintf ppf "rec %s : %a = @ %a ;@.@?"
            (R.render_cid_prog  f)
            (fmt_ppr_cmp_typ LF.Empty LF.Empty lvl) tau
            (fmt_ppr_cmp_exp_chk LF.Empty LF.Empty 
               (LF.Dec(LF.Empty, Comp.CTypDecl ((Store.Cid.Comp.get f).Store.Cid.Comp.name ,  tau)))  lvl) e

      | Sgn.Pragma (LF.NamePrag _cid_tp) ->  ()
 
 

    (* Regular Pretty Printers *)
    let ppr_sgn_decl              = fmt_ppr_sgn_decl              std_lvl std_formatter 
    let ppr_lf_ctyp_decl  cO cD   = fmt_ppr_lf_ctyp_decl cO cD    std_lvl std_formatter 
    let ppr_lf_kind cPsi          = fmt_ppr_lf_kind cPsi          std_lvl std_formatter
    let ppr_lf_typ  cO cD cPsi    = fmt_ppr_lf_typ cO cD cPsi     std_lvl std_formatter
    let ppr_lf_normal cO cD cPsi  = fmt_ppr_lf_normal cO cD cPsi  std_lvl std_formatter
    let ppr_tuple cO cD cPsi      = fmt_ppr_tuple cO cD cPsi      std_lvl std_formatter
    let ppr_lf_head cO cD cPsi    = fmt_ppr_lf_head cO cD cPsi    std_lvl std_formatter
    let ppr_lf_spine cO cD cPsi   = fmt_ppr_lf_spine cO cD cPsi   std_lvl std_formatter
    let ppr_lf_sub cO cD cPsi     = fmt_ppr_lf_sub cO cD cPsi     std_lvl std_formatter
    let ppr_lf_front cO cD cPsi   = fmt_ppr_lf_front cO cD cPsi   std_lvl std_formatter
    let ppr_lf_msub cO  cD        = fmt_ppr_lf_msub cO cD         std_lvl std_formatter
    let ppr_lf_mfront cO cD       = fmt_ppr_lf_mfront cO cD       std_lvl std_formatter

    let ppr_lf_cvar cO cD         = fmt_ppr_lf_cvar cO cD         std_lvl std_formatter

    let ppr_lf_schema             = fmt_ppr_lf_schema             std_lvl std_formatter
    let ppr_lf_sch_elem           = fmt_ppr_lf_sch_elem           std_lvl std_formatter
    let ppr_lf_coercion           = fmt_ppr_lf_coercion           std_lvl std_formatter

    let ppr_lf_typ_rec cO cD cPsi = fmt_ppr_lf_typ_rec cO cD cPsi std_lvl std_formatter

    let ppr_lf_psi_hat cO         = fmt_ppr_lf_psi_hat cO         std_lvl std_formatter
    let ppr_lf_dctx cO cD         = fmt_ppr_lf_dctx cO cD         std_lvl std_formatter
    let ppr_lf_mctx cO            = fmt_ppr_lf_mctx cO            std_lvl std_formatter
    let ppr_lf_octx               = fmt_ppr_lf_octx               std_lvl std_formatter
    let ppr_cmp_gctx cO cD        = fmt_ppr_cmp_gctx cO cD        std_lvl std_formatter
    let ppr_cmp_typ cO cD         = fmt_ppr_cmp_typ cO cD         std_lvl std_formatter
    let ppr_cmp_exp_chk cO cD cG  = fmt_ppr_cmp_exp_chk cO cD cG  std_lvl std_formatter
    let ppr_cmp_exp_syn cO cD cG  = fmt_ppr_cmp_exp_syn cO cD cG  std_lvl std_formatter
    let ppr_cmp_branches cO cD cG = fmt_ppr_cmp_branches cO cD cG std_lvl std_formatter
    let ppr_cmp_branch cO cD cG   = fmt_ppr_cmp_branch cO cD cG   std_lvl std_formatter

    let subToString cO cD cPsi s'  = 
      let s = Whnf.normSub s' in 
        fmt_ppr_lf_sub cO cD cPsi std_lvl str_formatter s
        ; flush_str_formatter ()

    let spineToString cO cD cPsi sS  = 
      let tS = Whnf.normSpine sS in 
        fmt_ppr_lf_spine cO cD cPsi std_lvl str_formatter tS
        ; flush_str_formatter ()

    let typToString cO cD cPsi sA    = 
      let tA = Whnf.normTyp sA in 
        fmt_ppr_lf_typ cO cD cPsi std_lvl str_formatter tA
        ; flush_str_formatter ()

    let typRecToString cO cD cPsi typrec_clo = 
      let typrec = Whnf.normTypRec typrec_clo in 
      fmt_ppr_lf_typ_rec cO cD cPsi std_lvl str_formatter typrec
      ; flush_str_formatter () 

    let kindToString cPsi sK   = 
      let tK = Whnf.normKind sK in 
      fmt_ppr_lf_kind cPsi std_lvl str_formatter tK
      ; flush_str_formatter ()

    let tupleToString cO cD cPsi tuple = 
      fmt_ppr_tuple cO cD cPsi std_lvl str_formatter tuple
      ; flush_str_formatter ()

    let headToString cO cD cPsi h = 
      fmt_ppr_lf_head cO cD cPsi std_lvl str_formatter h
      ; flush_str_formatter ()

    let normalToString cO cD cPsi sM = 
      let tM = Whnf.norm sM in 
        fmt_ppr_lf_normal cO cD cPsi std_lvl str_formatter tM
        ; flush_str_formatter ()


    let dctxToString cO cD cPsi = 
      let cPsi' = Whnf.normDCtx cPsi in 
        fmt_ppr_lf_dctx cO cD std_lvl str_formatter cPsi'
        ; flush_str_formatter ()

    let mctxToString cO cD = 
      let cD' = Whnf.normMCtx cD in 
      fmt_ppr_lf_mctx cO std_lvl str_formatter cD'
        ; flush_str_formatter ()

    let octxToString cO  = 
      fmt_ppr_lf_octx std_lvl str_formatter cO
        ; flush_str_formatter ()

    let schemaToString schema = 
      fmt_ppr_lf_schema std_lvl str_formatter schema
      ; flush_str_formatter ()

    let coercionToString coercion = 
      fmt_ppr_lf_coercion std_lvl str_formatter coercion
      ; flush_str_formatter ()

    let gctxToString cO cD cG = 
      let cG' = Whnf.normCtx cG in 
        fmt_ppr_cmp_gctx cO cD std_lvl str_formatter cG'
        ; flush_str_formatter ()

    let expChkToString cO cD cG e    = 
      let e' = Whnf.cnormExp (e , Whnf.m_id) in 
       fmt_ppr_cmp_exp_chk cO cD cG std_lvl str_formatter e'
      ; flush_str_formatter ()

    let expSynToString cO cD cG i   = 
      fmt_ppr_cmp_exp_syn cO cD cG std_lvl str_formatter i
      ; flush_str_formatter ()

    let branchToString cO cD cG  b    = 
      fmt_ppr_cmp_branch cO cD cG std_lvl str_formatter b
      ; flush_str_formatter ()

    let compTypToString cO cD tau  = 
      let tau' = Whnf.normCTyp tau in 
        fmt_ppr_cmp_typ cO cD std_lvl str_formatter tau'
        ; flush_str_formatter ()

    let msubToString cO cD   s    = 
      fmt_ppr_lf_msub cO cD std_lvl str_formatter s
      ; flush_str_formatter ()

  end (* Int.Make *)

  (* Default CID_RENDERER for Internal Syntax using de Buijn indices *)
  module DefaultCidRenderer = struct

    open Store.Cid

    let render_name       n    = n.string_of_name
    let render_cid_typ    a    = render_name (Typ .get a).Typ .name
    let render_cid_term   c    = render_name (Term.get c).Term.name
    let render_cid_schema w    = render_name (Schema.get w).Schema.name
    let render_cid_coercion w  = render_name (Coercion.get w).Coercion.name
    let render_cid_prog   f    = render_name (Comp.get f).Comp.name
    let render_ctx_var _cO g   =  string_of_int g
    let render_cvar    _cD u   = "mvar " ^ string_of_int u
    let render_bvar  _cPsi i   = string_of_int i
    let render_offset      i   = string_of_int i
    let render_var   _cG   x   = string_of_int x

  end (* Int.DefaultCidRenderer *)

 
 (* RENDERER for Internal Syntax using names *)
  module NamedRenderer = struct

    open Store.Cid
    open Store

    let render_name        n   = n.string_of_name
    let render_cid_typ     a   = render_name (Typ .get a).Typ .name
    let render_cid_term    c   = render_name (Term.get c).Term.name
    let render_cid_schema  w   = render_name (Schema.get w).Schema.name
    let render_cid_coercion w  = render_name (Coercion.get w).Coercion.name
    let render_cid_prog    f   = render_name (Comp.get f).Comp.name
    let render_ctx_var cO g    =      
      begin try
        render_name (Context.getNameMCtx cO g)
      with
          _ -> "FREE CtxVar " ^ (string_of_int g)
      end 

    let render_cvar    cD u    = 
      begin try
        render_name (Context.getNameMCtx cD u)
      with 
          _ -> "FREE MVar " ^ (string_of_int u)
      end 
    let render_bvar  cPsi i    = 
      begin try 
        render_name (Context.getNameDCtx cPsi i)
      with
          _ -> "FREE BVar " ^ (string_of_int i)
      end 

    let render_offset     i   = string_of_int i

    let render_var   cG   x   = 
      begin try
        render_name (Context.getNameCtx cG x)
      with 
          _ -> "FREE Var " ^ (string_of_int x)
      end

  end (* Int.NamedRenderer *)


  (* Default Internal Syntax Pretty Printer Functor Instantiation *)
   (* module DefaultPrinter = Make (DefaultCidRenderer)   *)
    module DefaultPrinter = Make (NamedRenderer)   

end (* Int *)


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

    let print_typeVariant = function
      | Cross -> "'A * 'B"
      | Arrow -> "'A -> 'B"
      | CtxPi -> "{_:schema} 'A"
      | PiBox -> "{_::'A} 'B"
      | Box   -> "[ ] A"

    (* Format Based Pretty Printers for Error messages *)
    let fmt_ppr ppf = function
      | UnboundName n ->
          fprintf ppf "unbound data-level variable (ordinary or meta-variable) or constructor: %s" (R.render_name n)

      | UnboundCoName n ->
          fprintf ppf "unbound context coercion: %s" (R.render_name n)

      | UnboundCtxName n ->
          fprintf ppf "unbound context variable: %s" (R.render_name n)

      | UnboundCtxSchemaName n ->
          fprintf ppf "unbound context schema: %s" (R.render_name n)

      | UnboundCompName n ->
          fprintf ppf "unbound computation-level variable: %s" (R.render_name n)

      | UnknownCidTyp n ->
          fprintf ppf "unbound type constructor: %s" (R.render_cid_typ n)

      | CtxVarMismatch (cO, var, expected) ->
          fprintf ppf "Context variable %a doesn't check against schema %a"
            (IP.fmt_ppr_lf_ctx_var cO) var
            (IP.fmt_ppr_lf_schema 0) expected

      | SigmaIllTyped (_cO, _cD, _cPsi, (_tArec, _s1), (_tBrec, _s2)) ->
          fprintf ppf "Sigma Type mismatch" (* TODO *)

      | KindMismatch (cD, cPsi, sS, sK) ->
          fprintf ppf "ill-kinded type\n  expected kind %s \n  for spine: %a \n  in context:\n    %a"
            (IP.kindToString cPsi sK)
            (IP.fmt_ppr_lf_spine LF.Empty cD cPsi std_lvl) (Whnf.normSpine sS)
            (IP.fmt_ppr_lf_dctx LF.Empty cD std_lvl) cPsi

      | TypMismatch (cO, cD, cPsi, sM, sA1, sA2) ->
          fprintf ppf
            "ill-typed expression\n  expected: %a\n  inferred: %a\n  for expression: %a\n "
            (IP.fmt_ppr_lf_typ cO cD cPsi    std_lvl) (Whnf.normTyp sA1)
            (IP.fmt_ppr_lf_typ cO cD cPsi    std_lvl) (Whnf.normTyp sA2)
            (IP.fmt_ppr_lf_normal cO cD cPsi std_lvl) (Whnf.norm sM)
            (* (IP.fmt_ppr_lf_dctx cO cD std_lvl)        (Whnf.normDCtx cPsi) *)


      | TypMismatchElab (cO, cD, cPsi, sA1, sA2) ->
          fprintf ppf
            "ill-typed expression\n  expected: %a\n  inferred: %a\n \n "
            (IP.fmt_ppr_lf_typ cO cD cPsi    std_lvl) (Whnf.normTyp sA1)
            (IP.fmt_ppr_lf_typ cO cD cPsi    std_lvl) (Whnf.normTyp sA2)
            (* (IP.fmt_ppr_lf_dctx cO cD std_lvl)        (Whnf.normDCtx cPsi) *)


      | IllTyped (cO, cD, cPsi, sM, sA) ->
          fprintf ppf
            "ill-typed expression\n  expected type: %a\n  for expression:\n    %a\n "
            (IP.fmt_ppr_lf_typ cO cD cPsi std_lvl) (Whnf.normTyp sA)
            (IP.fmt_ppr_lf_normal cO cD cPsi std_lvl) (Whnf.norm sM)
            (* (IP.fmt_ppr_lf_dctx cO cD std_lvl) cPsi  *)

      | IllTypedElab (cO, cD, cPsi, sA) ->
          fprintf ppf
            "ill-typed expression\n  inferred type: %a \n "
            (IP.fmt_ppr_lf_typ cO cD cPsi std_lvl) (Whnf.normTyp sA)



      | EtaExpandBV (offset, cO, cD, cPsi, sA) -> 
          fprintf ppf
            "bound variable %s to has type %a \n and should be eta-expanded\n"
            (R.render_offset offset)
            (IP.fmt_ppr_lf_typ cO cD cPsi std_lvl) (Whnf.normTyp sA)


      | EtaExpandFMV (offset, cO, cD, cPsi, sA) -> 
          fprintf ppf
            "meta-variable %s to has type %a \n and should be eta-expanded\n"
            (R.render_name offset)
            (IP.fmt_ppr_lf_typ cO cD cPsi std_lvl) (Whnf.normTyp sA)

      | EtaExpandFV (offset, cO, cD, cPsi, sA) -> 
          fprintf ppf
            "variable %s to has type %a \n and should be eta-expanded\n"
            (R.render_name offset)
            (IP.fmt_ppr_lf_typ cO cD cPsi std_lvl) (Whnf.normTyp sA)


      | SpineIllTyped -> 
          fprintf ppf
            "ill-typed spine---not enough arguments supplied"

      | LeftoverConstraints x ->
          fprintf ppf
            "cannot reconstruct a type for free variable %s (leftover constraints)"
            (R.render_name x)

      | IllTypedIdSub ->
          fprintf ppf "ill-typed substitution" (* TODO *)

      | ValueRestriction (cO, cD, cG, i, theta_tau) ->
          fprintf ppf
            "value restriction [pattern matching]\n  expected: boxed type\n  inferred: %a\n  for expression: %a\n  in context:\n    %s"
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau)
            (IP.fmt_ppr_cmp_exp_syn cO cD cG std_lvl) i
            "[no comp-level context printing yet]" (* TODO print context? *)

      | CompIllTyped (cO, cD, cG, e, theta_tau (* expected *),  theta_tau' (* inferred *)) ->
          fprintf ppf
            "ill-typed expression\n  expected: %a\n  for expression: %a\n  inferred:%a    \n"
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau) 
            (IP.fmt_ppr_cmp_exp_chk cO cD cG std_lvl) e
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau') 

      | CompMismatch (cO, cD, cG, i, variant, theta_tau) ->
          fprintf ppf
            "ill-typed expression\n  expected: %s\n  inferred: %a\n  for expression: %a\n  in context:\n    %s"
            (print_typeVariant variant)
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau)
            (IP.fmt_ppr_cmp_exp_syn cO cD cG std_lvl) i
            "[no comp-level context printing yet]" (* TODO print context? *)


      | CompPattMismatch ((cO, cD, cPsi, tM, sA) , (cO', cD', cPsi', sA')) ->
          fprintf ppf
            "ill-typed pattern\n  expected: %a[%a] \n  inferred: %a[%a]\n  for expression: [%a] %a\n"  
            (IP.fmt_ppr_lf_typ cO' cD' cPsi' std_lvl) (Whnf.normTyp sA')
            (IP.fmt_ppr_lf_dctx cO' cD' std_lvl) (Whnf.normDCtx cPsi')
            (IP.fmt_ppr_lf_typ cO cD cPsi std_lvl) (Whnf.normTyp sA)
            (IP.fmt_ppr_lf_dctx cO' cD' std_lvl) (Whnf.normDCtx cPsi)
            (IP.fmt_ppr_lf_dctx cO' cD' std_lvl) (Whnf.normDCtx cPsi)
            (IP.fmt_ppr_lf_normal cO cD cPsi std_lvl) tM

      | CompBoxCtxMismatch (cO, cD, cPsi, (phat, tM)) ->
          fprintf ppf
            "Expected: %a \n  in context %a \n Used in context %a\n "  
            (IP.fmt_ppr_lf_normal cO cD cPsi std_lvl) tM 
            (IP.fmt_ppr_lf_dctx cO cD std_lvl) (Whnf.normDCtx cPsi)
            (IP.fmt_ppr_lf_psi_hat cO std_lvl) (Context.hatToDCtx phat)



      | CompFreeMVar u -> 
          fprintf ppf "Encountered free meta-variables %s \n"
            (R.render_name u)

      | CompScrutineeTyp (cO, cD, cG, i, sP, cPsi) -> 
          fprintf ppf "Type %a[%a] of scrutinee %a is not closed\n"
            (IP.fmt_ppr_lf_typ cO cD cPsi std_lvl) (Whnf.normTyp sP)
            (IP.fmt_ppr_lf_dctx cO cD std_lvl) cPsi
            (IP.fmt_ppr_cmp_exp_syn cO cD cG std_lvl) i


      | CompCtxFunMismatch (cO, cD, _cG, theta_tau) -> 
          fprintf ppf "Expected Pictx type ; Found %a \n"
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau)

      | CompFunMismatch (cO, cD, _cG, theta_tau) -> 
          fprintf ppf "Expected arrow type ; Found %a \n"
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau)

      | CompMLamMismatch (cO, cD, _cG, theta_tau) -> 
          fprintf ppf "Expected Pibox type ; Found %a \n"
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau)

      | CompBoxMismatch (cO, cD, _cG, theta_tau) -> 
          fprintf ppf "Expected box type ; Found %a \n"
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau)

      | CompPairMismatch (cO, cD, _cG, theta_tau) -> 
          fprintf ppf "Expected product type ; Found %a \n"
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau)

      | CompSynMismatch (cO, cD, theta_tau, theta_tau') ->
          fprintf ppf
            "Expected type : %a \n Inferred type  %a \n  "  
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau)
            (IP.fmt_ppr_cmp_typ cO cD std_lvl) (Whnf.cnormCTyp theta_tau')

      | CompTypAnn -> 
          fprintf ppf "Type synthesis of term failed (use typing annotation)" 

      | ConstraintsLeft ->
          fprintf ppf "Constraints of functional type are not simplified" (* TODO *)

      | NotPatSub ->
          fprintf ppf "Not a pattern substitution" (* TODO *)

      | LeftoverUndef ->
          fprintf ppf "Undef left after unification" (* FIXME this is a beluga error *)

      | SubIllTyped ->
          fprintf ppf "Substitution not well-typed"  (* TODO *)

      | UnboundIdSub ->
          fprintf ppf "identity substitution used without context variable"

    (* Regular Pretty Printers *)
    let ppr = fmt_ppr std_formatter

  end


  (* Default CID_RENDERER for Errors *)
   (* module DefaultCidRenderer = Int.DefaultCidRenderer  *)
      module DefaultCidRenderer = Int.NamedRenderer 



  (* Default Error Pretty Printer Functor Instantiation *)
  module DefaultPrinter = Make (DefaultCidRenderer)

end (* Error *)

