include Format

let enabled = ref false
let testing = ref false

module Printer =
struct
  open Syntax.Int
  module R = Store.Cid.NamedRenderer


  module InstHashedType = struct
    type t    = LF.iterm option ref
    let equal = (==)
    let hash  = Hashtbl.hash
  end

  module InstHashtbl = Hashtbl.Make (InstHashedType)

  let inst_hashtbl : string InstHashtbl.t = InstHashtbl.create 0

  module MInstHashedType = struct
    type t    = LF.iterm option ref
    let equal = (==)
    let hash  = Hashtbl.hash
  end

  module MInstHashtbl = Hashtbl.Make (MInstHashedType)

  let minst_hashtbl : string MInstHashtbl.t = MInstHashtbl.create 0

  module SInstHashedType = struct
    type t    = LF.iterm option ref
    let equal = (==)
    let hash  = Hashtbl.hash
  end

  module SInstHashtbl = Hashtbl.Make (SInstHashedType)

  let sinst_hashtbl : string SInstHashtbl.t = SInstHashtbl.create 0

  module PInstHashedType = struct
    type t    = LF.iterm option ref
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

  let string_of_depend = function
    | LF.No -> "No"
    | LF.Maybe -> "Maybe"
    | LF.Inductive -> "Inductive"

  let rec sexp_lf_typ cD cPsi ppf = function
    | LF.Atom (_, a, LF.Nil) ->
      fprintf ppf "(Atom %s)"
        (R.render_cid_typ a)

    | LF.Atom (_, a, ms) ->
      fprintf ppf "(Atom %s %a)"
        (R.render_cid_typ a)
        (sexp_lf_spine cD cPsi) ms

    | LF.PiTyp ((LF.TypDecl (x, a), dep), b) ->
      fprintf ppf "(Pi (%s . %a) %s %a)"
        (Id.render_name x)
        (sexp_lf_typ cD cPsi) a
	(string_of_depend dep)
        (sexp_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, a)))) b

    | LF.Sigma typRec ->
      fprintf ppf "(Sigma %a)"
        (sexp_lf_typ_rec cD cPsi) typRec

    | LF.TClo (typ, s) ->
      fprintf ppf "(TClo %a  %a)"
        (sexp_lf_typ cD cPsi) typ
        (sexp_lf_sub cD cPsi) s

  and sexp_lf_tuple cD cPsi ppf = function
    | LF.Last tM ->
      fprintf ppf "(Last %a)"
	(sexp_lf_normal cD cPsi) tM

    | LF.Cons(tM, rest) ->
      fprintf ppf "(Cons %a %a)"
        (sexp_lf_normal cD cPsi) tM
        (sexp_lf_tuple cD cPsi) rest

  and sexp_lf_normal cD cPsi ppf = function
      | LF.Lam (_, x, m) ->
        fprintf ppf "(Lam %s %a)"
          (Id.render_name x)
          (sexp_lf_normal cD (LF.DDec(cPsi, LF.TypDeclOpt x))) m
      | LF.LFHole _ ->
        fprintf ppf "?"
      | LF.Tuple (_, tuple) ->
         fprintf ppf "%a"
           (sexp_lf_tuple cD cPsi) tuple
      | LF.Root (_, h, LF.Nil) ->
        fprintf ppf "%a"
        (sexp_lf_head cD cPsi) h
      | LF.Root (_, h, ms) ->
           fprintf ppf "(Root %a %a)"
             (sexp_lf_head cD cPsi) h
             (sexp_lf_spine cD cPsi)  ms
      | LF.Clo(tM, s) ->
	sexp_lf_normal cD cPsi ppf (Whnf.norm (tM, s))

  and sexp_lf_head cD cPsi ppf = function
      | LF.HClo (h, s, sigma) ->
        fprintf ppf "(HClo %s %a %a)"
          (R.render_bvar cPsi h)
          (sexp_lf_offset cD) s
          (sexp_lf_sub  cD cPsi) sigma

      | LF.HMClo (h, ((s, theta),sigma)) ->
        fprintf ppf "(HMClo %s %a %a %a)"
          (R.render_bvar cPsi h)
          (sexp_lf_mmvar) s
          (sexp_lf_msub cD) theta
          (sexp_lf_sub cD cPsi) sigma

      | LF.BVar x  ->
        fprintf ppf "%s"
          (R.render_bvar cPsi x)

      | LF.Const c ->
        fprintf ppf "%s"
          (R.render_cid_term c)

      | LF.MMVar ((c, ms), s) ->
        fprintf ppf "(MMVar %a %a %a)"
          sexp_lf_mmvar c
          (sexp_lf_msub cD) ms
          (sexp_lf_sub  cD cPsi) s

      | LF.MPVar ((c, ms), s) ->
        fprintf ppf "(MPVar %a %a %a)"
          (sexp_lf_mmvar) c
          (sexp_lf_msub cD) ms
          (sexp_lf_sub  cD cPsi) s

      | LF.MVar (c, s) ->
        fprintf ppf "(MVar %a %a)"
          (sexp_lf_cvar cD ) c
          (sexp_lf_sub  cD cPsi) s

      | LF.PVar (c, s) ->
        fprintf ppf "(PVar %a %a)"
          (sexp_lf_offset cD) c
          (sexp_lf_sub  cD cPsi) s

      | LF.FVar x ->
        fprintf ppf "%s"
          (Id.render_name x)

      | LF.FMVar (u, s) ->
        fprintf ppf "(FMVar %s %a)"
          (Id.render_name u)
          (sexp_lf_sub cD cPsi) s

      | LF.FPVar (p, s) ->
        fprintf ppf "(FPVar %s %a)"
          (Id.render_name p)
          (sexp_lf_sub cD cPsi) s

      | LF.Proj (head, k) ->
	fprintf ppf "(Proj %d %a)"
	  k
	  (sexp_lf_head cD cPsi) head


  and sexp_lf_spine cD cPsi ppf = function
    | LF.Nil ->
      fprintf ppf "Nil"
    | LF.App(m, LF.Nil) ->
      fprintf ppf "%a"
        (sexp_lf_normal  cD cPsi) m
    | LF.App (m, ms) ->
      fprintf ppf "(Sp %a %a)"
        (sexp_lf_normal cD cPsi) m
        (sexp_lf_spine  cD cPsi) ms

  and sexp_lf_sub cD cPsi ppf = function
      | LF.EmptySub -> fprintf ppf "EmptySub"
      | LF.Undefs -> fprintf ppf "Undefs"
      | LF.Shift n ->
        fprintf ppf "(Shift %s)"
          (R.render_offset n)

      | LF.FSVar (n, (s_name, s)) ->
        fprintf ppf
          "(FSVar #^%s %s %a)"
          (R.render_offset n)
          (Id.render_name s_name)
          (sexp_lf_sub cD cPsi) s

      | LF.SVar (c, n, s) ->
    	fprintf ppf
          "(SVar #^%s %a %a)"
          (R.render_offset n)
          (sexp_lf_offset cD) c
          (sexp_lf_sub cD cPsi) s

      | LF.MSVar (n , ((_sigma, t),s)) ->
        fprintf ppf
          "(MSVar #^%s %a %a)"
          (R.render_offset n)
          (sexp_lf_sub cD cPsi) s
          (sexp_lf_msub cD) t

      | LF.Dot (f, s) ->
        fprintf ppf "%a  %a"
          (sexp_lf_front cD cPsi) f
          (sexp_lf_sub cD cPsi) s

  and sexp_lf_front cD cPsi ppf = function
    | LF.Head h ->
      fprintf ppf "%a"
        (sexp_lf_head cD cPsi) h

    | LF.Obj m ->
      fprintf ppf "%a"
        (sexp_lf_normal cD cPsi) m

    | LF.Undef ->
      fprintf ppf "Undef"

  and sexp_lf_msub cD ppf = function
    | LF.MShift k ->
      fprintf ppf "(Shift %d)" k

    | LF.MDot (f, s) ->
      fprintf ppf "(MDot %a %a)"
        (sexp_lf_mfront cD) f
        (sexp_lf_msub cD) s

  and sexp_lf_clobj cD cPsi ppf = function
    | LF.MObj m ->
      sexp_lf_normal cD cPsi ppf m
    | LF.SObj s ->
      sexp_lf_sub cD cPsi ppf s
    | LF.PObj h ->
      sexp_lf_head cD cPsi ppf h


  and sexp_lf_mfront cD ppf = function
    | LF.CObj cPsi ->
      fprintf ppf "(CObj %a)"
        (sexp_lf_dctx cD) cPsi
    | LF.ClObj (phat, tM) ->
      let cPsi = phatToDCtx phat in
      fprintf ppf "(ClObj %a %a)"
        (sexp_lf_psi_hat cD) cPsi
        (sexp_lf_clobj cD cPsi) tM
    | LF.MV k ->
      fprintf ppf "%s"
        (R.render_cvar cD k)
    | LF.MUndef ->
      fprintf ppf "MUndef"


  and sexp_meta_obj cD ppf (_loc, mO) =
    sexp_lf_mfront cD ppf mO

  and sexp_lf_mmvar ppf = function
    | {LF.instantiation = { contents = None } as u; typ = LF.ClTyp (LF.PTyp tA, _); _} ->
      begin
        try
          fprintf ppf "(MMVar-1 %s)"
            (PInstHashtbl.find pinst_hashtbl u)
        with
        | Not_found ->
           let sym = match Store.Cid.Typ.gen_mvar_name tA with
             | Some vGen -> vGen ()
             | None -> Gensym.MVarData.gensym ()
           in
           PInstHashtbl.replace pinst_hashtbl u sym;
           fprintf ppf "(MMVar-2 %s)" sym
      end
    | {LF.instantiation = {contents = Some (LF.IHead h) }; LF.cD; LF.typ = LF.ClTyp (LF.PTyp _, cPsi); _} ->
      fprintf ppf " %a"
        (sexp_lf_head cD cPsi) h

    | {LF.instantiation = {contents = None } as u; LF.typ = LF.ClTyp (LF.MTyp tA,_); LF.depend; _} ->
      let s = (match depend with LF.No -> "No" | LF.Maybe -> "Maybe" | LF.Inductive -> "Inductive") in
      begin
        try
          fprintf ppf "(MMVar-3 (?%s . %s))"
            (MInstHashtbl.find minst_hashtbl u) s
        with
          | Not_found ->
            let sym = match Store.Cid.Typ.gen_mvar_name tA with
              | Some vGen -> vGen ()
              | None -> Gensym.MVarData.gensym ()
            in
            MInstHashtbl.replace minst_hashtbl u sym
            ; fprintf ppf "(MMVar-4 %s)" sym
      end

    | {LF.instantiation = { contents = Some (LF.INorm m)}; LF.cD; LF.typ = LF.ClTyp (LF.MTyp _,cPsi); _} ->
       fprintf ppf " %a"
         (sexp_lf_normal cD cPsi) m

    | {LF.instantiation = { contents = None } as u; LF.typ = LF.ClTyp (LF.STyp (_, cPsi),_); _} ->
       begin
         try
           fprintf ppf "(MMVar-5 %s)"
             (SInstHashtbl.find sinst_hashtbl u)
         with
         | Not_found ->
            let sym = Gensym.MVarData.gensym ()
            in
            SInstHashtbl.replace sinst_hashtbl u sym;
            fprintf ppf "(MMVar-6 %s)" sym
       end

    | {LF.instantiation = { contents = Some (LF.ISub s) }; LF.cD; LF.typ = LF.ClTyp (LF.STyp _,cPsi); _} ->
      fprintf ppf " #%a"
        (sexp_lf_sub cD cPsi) s

  and sexp_lf_offset cD ppf n =
    fprintf ppf "%s" (R.render_cvar cD n)

  and sexp_lf_cvar cD ppf = function
    | LF.Offset n ->
      sexp_lf_offset cD ppf n

    | LF.Inst { LF.instantiation = {contents = None} as u; typ = LF.ClTyp (LF.MTyp tA, _); _} ->
      begin
        try
          fprintf ppf "?%s"
            (InstHashtbl.find inst_hashtbl u)
        with
          | Not_found ->
            let sym = match Store.Cid.Typ.gen_mvar_name tA with
              | Some vGen -> vGen ()
              | None -> Gensym.MVarData.gensym ()
            in
            InstHashtbl.replace inst_hashtbl u sym
            ; fprintf ppf "?%s" sym
      end

    | LF.Inst _ ->
      fprintf ppf "(?INST _)"

  and sexp_lf_ctx_var cD ppf = function
    | LF.CInst ({LF.name; LF.instantiation = {contents = None}; _}, theta) ->
      fprintf ppf "(CInst %s %a)"
        (Id.render_name name)
        (sexp_lf_msub cD) theta

    | LF.CInst ({LF.instantiation = {contents = Some (LF.ICtx cPsi)}; LF.cD; _}, theta) ->
      fprintf ppf "%a"
        (sexp_lf_dctx cD) (Whnf.cnormDCtx (cPsi, theta))

    | LF.CtxOffset psi ->
      fprintf ppf "%s"
        (R.render_ctx_var cD psi)
    | LF.CtxName psi ->
      fprintf ppf "%s"
        (Id.render_name psi)

  and sexp_lf_typ_rec cD cPsi ppf = function
      | LF.SigmaLast (x, tA) ->
	fprintf ppf "(Last %s %a)"
	  (match x with None -> "_" | Some x -> (Id.render_name x))
	  (sexp_lf_typ cD cPsi) tA
      | LF.SigmaElem (x, tA, tAs)  ->
	fprintf ppf "(Elem %s %a %a)"
	  (Id.render_name x)
	  (sexp_lf_typ cD cPsi) tA
          (sexp_lf_typ_rec cD (LF.DDec(cPsi, LF.TypDecl (x, tA))))  tAs

   and sexp_lf_schema ppf = function
      | LF.Schema [] ->
	fprintf ppf "Nil"

      | LF.Schema (f :: fs) ->
        fprintf ppf "(Cons %a %a)"
          sexp_lf_sch_elem f
          sexp_lf_schema (LF.Schema fs)

  and sexp_lf_sch_elem ppf =
    let rec projectCtxIntoDctx = function
    |  LF.Empty -> LF.Null
    |  LF.Dec (rest, last) -> LF.DDec (projectCtxIntoDctx rest, last)
    in function
    | LF.SchElem (typDecls, sgmDecl) ->
      let cPsi = projectCtxIntoDctx typDecls in
      fprintf ppf "(SchElem %a %a)"
        (ppr_typ_decl_dctx  LF.Empty)  cPsi
        (sexp_lf_typ_rec LF.Empty cPsi) sgmDecl



  and ppr_typ_decl_dctx cD ppf = function
    | LF.Null ->
      fprintf ppf "Null"

    | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
      fprintf ppf "(DDec %a (%s . %a))"
        (ppr_typ_decl_dctx cD) cPsi
        (Id.render_name x)
        (sexp_lf_typ cD cPsi) tA


  and sexp_lf_psi_hat cD ppf = function
    | LF.Null   -> fprintf ppf "Null"

    | LF.CtxVar ctx_var ->
      sexp_lf_ctx_var cD ppf ctx_var

    | LF.DDec (cPsi, LF.TypDeclOpt x) ->
      fprintf ppf "(DDec %a (Opt %s))"
        (sexp_lf_psi_hat cD) cPsi
        (Id.render_name x)

    | LF.DDec (cPsi, LF.TypDecl(x, _ )) ->
      fprintf ppf "(DDec %a %s)"
        (sexp_lf_psi_hat cD) cPsi
        (Id.render_name x)

  and sexp_lf_dctx cD ppf =
    function
    | LF.Null ->
      fprintf ppf "Null"

    | LF.CtxVar ctx_var ->
      sexp_lf_ctx_var cD ppf ctx_var

    | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
      fprintf ppf "(DDec %a (%s . %a))"
        (sexp_lf_dctx cD) cPsi
        (Id.render_name x)
        (sexp_lf_typ cD cPsi) tA

    | LF.DDec (cPsi, LF.TypDeclOpt x) ->
      fprintf ppf "(DDec %a (Opt %s))"
        (sexp_lf_dctx cD) cPsi
        (Id.render_name x)

  and sexp_lf_mctx ppf =
    function
    | LF.Empty ->
      fprintf ppf "Empty"

    | LF.Dec (cD, ctyp_decl) ->
      fprintf ppf "(Dec %a %a)"
    	sexp_lf_mctx cD
    	(sexp_lf_ctyp_decl cD) ctyp_decl

  and sexp_lf_kind cPsi ppf =  function
    | LF.Typ ->
      fprintf ppf "Type"

    | LF.PiKind ((LF.TypDecl (x, a), dep), k) ->
      fprintf ppf "(Pi (%s . %a) %s %a)"
        (Id.render_name   x)
        (sexp_lf_typ LF.Empty cPsi) a
	(string_of_depend dep)
        (sexp_lf_kind (LF.DDec(cPsi, LF.TypDeclOpt  x))) k

  and sexp_lf_mtyp cD ppf =
    function
    | LF.ClTyp (LF.MTyp tA, cPsi) ->
      fprintf ppf "(ClTyp (MTyp %a %a))"
        (sexp_lf_dctx cD) cPsi
        (sexp_lf_typ cD cPsi) tA

    | LF.ClTyp (LF.PTyp tA, cPsi) ->
      fprintf ppf "(ClTyp (PTyp %a %a))"
        (sexp_lf_dctx cD) cPsi
        (sexp_lf_typ cD cPsi) tA

    | LF.ClTyp (LF.STyp (cl, cPhi), cPsi) ->
      fprintf ppf "(ClTyp (STyp %a  (%s . %a)))"
        (sexp_lf_dctx cD) cPsi
    	(match cl with LF.Ren -> "Ren" | LF.Subst -> "Subst")
        (sexp_lf_dctx cD) cPhi
    | LF.CTyp (Some schemaName) ->
      fprintf ppf "(CTyp %a)"
        (sexp_lf_schema) (Store.Cid.Schema.get_schema schemaName)
    | LF.CTyp None -> fprintf ppf "CTX"

  and sexp_lf_ctyp_decl cD ppf =
    function
    | LF.Decl (u, mtyp,dep) ->
        fprintf ppf "(Decl %s  %a)"
          (Id.render_name u)
          (sexp_lf_mtyp cD) mtyp

    | LF.DeclOpt name ->
      fprintf ppf "(Decl %s  _)"
        (Id.render_name name)

  (* Computation-level *)
  let rec sexp_cmp_kind cD ppf =
    function
    | Comp.Ctype _ -> fprintf ppf "ctype"
    | Comp.PiKind (_, ctyp_decl, cK) ->
        fprintf ppf "(Pi %a %a)"
          (sexp_lf_ctyp_decl cD) ctyp_decl
          (sexp_cmp_kind (LF.Dec(cD, ctyp_decl))) cK

  let sexp_meta_typ cD ppf = sexp_lf_mtyp cD ppf

  let rec sexp_meta_spine cD ppf =
    function
    | Comp.MetaNil ->
      fprintf ppf "MetaNil"
    | Comp.MetaApp (mO, mS) ->
      fprintf ppf " MetaApp %a %a"
        (sexp_meta_obj cD) mO
        (sexp_meta_spine cD) mS

  and sexp_iterm cD cPsi ppf =
    function
    | LF.INorm tM -> sexp_lf_normal cD cPsi ppf tM
    | LF.IHead h -> sexp_lf_head cD cPsi ppf h
    | LF.ISub s -> sexp_lf_sub cD cPsi ppf s

  let rec sexp_cmp_typ cD ppf =
    function
    | Comp.TypBase (_, c, mS)->
      fprintf ppf "(TypBase %s %a)"
        (R.render_cid_comp_typ c)
        (sexp_meta_spine cD) mS

    | Comp.TypCobase (_, c, mS)->
      fprintf ppf "(TypCobase %s%a)"
        (R.render_cid_comp_cotyp c)
        (sexp_meta_spine cD) mS

    | Comp.TypBox (_, mT) ->
      fprintf ppf "%a"
    	(sexp_meta_typ cD) mT

    | Comp.TypArr (tau1, tau2) ->
      fprintf ppf "(TypArr %a  %a)"
        (sexp_cmp_typ cD) tau1
        (sexp_cmp_typ cD) tau2

    | Comp.TypCross (tau1, tau2) ->
      fprintf ppf "(TypCross %a %a)"
        (sexp_cmp_typ cD) tau1
        (sexp_cmp_typ cD) tau2

    | Comp.TypPiBox (ctyp_decl, tau) ->
      fprintf ppf "(Pi %a %a)"
        (sexp_lf_ctyp_decl cD) ctyp_decl
        (sexp_cmp_typ (LF.Dec(cD, ctyp_decl))) tau

    | Comp.TypClo (_, _ ) -> fprintf ppf "TypClo"

    | Comp.TypInd tau ->
      fprintf ppf "(TypInd %a)"
        (sexp_cmp_typ cD) tau

  let rec sexp_pat_spine cD cG ppf =
    function
    | Comp.PatNil -> fprintf ppf "Nil"
    | Comp.PatApp (_, pat, pat_spine) ->
      fprintf ppf "(PatApp %a %a)"
        (sexp_pat_obj cD cG) pat
        (sexp_pat_spine cD cG) pat_spine

  and sexp_pat_obj cD cG ppf =
    function
      | Comp.PatMetaObj (_, mO) ->
        fprintf ppf "(PatMetaObj %a)"
          (sexp_meta_obj cD) mO

      | Comp.PatConst (_, c, pat_spine) ->
        fprintf ppf "(PatConst %s %a)"
          (R.render_cid_comp_const c)
          (sexp_pat_spine cD cG) pat_spine

      | Comp.PatPair (_, pat1, pat2) ->
        fprintf ppf "(PatPair %a %a)"
          (sexp_pat_obj cD cG) pat1
          (sexp_pat_obj cD cG) pat2

      | Comp.PatAnn (_, pat, tau) ->
        fprintf ppf "(PatAnn %a %a)"
          (sexp_pat_obj cD cG) pat
          (sexp_cmp_typ cD) tau

      | Comp.PatVar (_, offset ) ->
        fprintf ppf "(PatVar %s)"
          (R.render_var cG offset)

      | Comp.PatFVar (_, name ) ->
        fprintf ppf "(PatFVar %s)"
          (Id.render_name name)

  let rec sexp_cmp_exp_chk cD cG ppf =
    function
    | Comp.Syn (_, i) ->
      sexp_cmp_exp_syn cD cG ppf i

    | Comp.Fn (_, x, e) ->
      fprintf ppf "(Fun %s %a)"
        (Id.render_name x)
        (sexp_cmp_exp_chk cD (LF.Dec(cG, Comp.CTypDeclOpt x))) e

    | Comp.Fun (_, br) ->
      fprintf ppf "FunNoPP"

    | Comp.MLam (_, x, e) ->
      fprintf ppf "(MLam %s %a) "
        (Id.render_name x)
        (sexp_cmp_exp_chk (LF.Dec(cD, LF.DeclOpt x)) (Whnf.cnormCtx (cG, LF.MShift 1))) e

    | Comp.Pair (_, e1, e2) ->
      fprintf ppf "(Pair %a %a)"
        (sexp_cmp_exp_chk cD cG) e1
        (sexp_cmp_exp_chk cD cG) e2

    | Comp.LetPair(_, i, (x, y, e)) ->
      fprintf ppf "(Let (%s . %s) %a %a)"
        (Id.render_name x)
        (Id.render_name y)
        (sexp_cmp_exp_syn cD cG) i
        (sexp_cmp_exp_chk cD (LF.Dec(LF.Dec(cG, Comp.CTypDeclOpt x), Comp.CTypDeclOpt y))) e

    | Comp.Let(_, i, (x, e)) ->
      fprintf ppf "(let %s %a %a)"
        (Id.render_name x)
        (sexp_cmp_exp_syn cD cG) i
        (sexp_cmp_exp_chk cD (LF.Dec(cG, Comp.CTypDeclOpt x))) e

    | Comp.Box (_ , cM) ->
      fprintf ppf "(Box %a)"
        (sexp_meta_obj cD) cM

    | Comp.Case (_, prag, i, bs) ->
       let open Comp in
       fprintf ppf "(Case %a%s%a)"
         (sexp_cmp_exp_syn cD cG) i
         (match prag with PragmaCase -> " " | PragmaNotCase -> " PragmaNot ")
         (sexp_cmp_branches cD cG) bs

    | Comp.Hole (_, _, name_opt) ->
       let name =
         let open HoleId in
         match name_opt with
         | Named n -> " " ^ n
         | Anonymous -> ""
       in
       begin
         try
           fprintf ppf "(Hole%s)" name
         with
         | _ -> fprintf ppf "(Hole %s_)" name
       end

    (* I'm not sure this sexp representation is acceptable or not...
     *)
    | Comp.Impossible (_, i) ->
      fprintf ppf "(Impossible %a)"
        (sexp_cmp_exp_syn cD cG) i

  and sexp_cmp_exp_syn cD cG ppf =
    function
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
      fprintf ppf "(Obs %a %s)"
        (sexp_cmp_exp_chk cD cG) e
        (R.render_cid_comp_dest obs)

    | Comp.Apply (_, i, e) ->
      fprintf ppf "(Apply %a %a)"
        (sexp_cmp_exp_syn cD cG) i
        (sexp_cmp_exp_chk cD cG) e

    | Comp.MApp (_, i, mC) ->
      fprintf ppf "(MApp %a %a)"
        (sexp_cmp_exp_syn cD cG) i
        (sexp_meta_obj cD) mC

    | Comp.PairVal (loc, i1, i2) ->
      fprintf ppf "(PairVal %a %a)"
        (sexp_cmp_exp_syn cD cG) i1
        (sexp_cmp_exp_syn cD cG) i2

    | Comp.AnnBox (cM, _tau) ->
      fprintf ppf "%a"
        (sexp_meta_obj cD) cM

  and sexp_cmp_value ppf =
    function
      | Comp.FunValue _ -> fprintf ppf "FunValue"
      | Comp.ThmValue _ -> fprintf ppf "ThmValue"
      | Comp.MLamValue _ -> fprintf ppf "MLamValue"
      | Comp.CtxValue _ -> fprintf ppf "MLamValue"
      | Comp.BoxValue mC -> fprintf ppf "(BoxValue %a)"  (sexp_meta_obj LF.Empty) mC
      | Comp.ConstValue _ -> fprintf ppf "ConstValue"
      | Comp.PairValue (v1, v2) ->
        fprintf ppf "(PairValue %a %a)"
          sexp_cmp_value v1
          sexp_cmp_value v2
      | Comp.DataValue (c, spine) ->
    	 (* Note: Arguments in data spines are accumulated in reverse order, to
            allow applications of data values in constant time. *)
        let rec print_spine ppf = function
          | Comp.DataNil ->
	    fprintf ppf "Nil"

          | Comp.DataApp (v, spine) ->
            fprintf ppf "(DataApp %a %a)"
	      print_spine spine
	      sexp_cmp_value v
        in
        fprintf ppf "(DataValue %s %a)"
    	  (R.render_cid_comp_const c) print_spine spine


  and sexp_cmp_branch_prefix ppf =
    function
    | LF.Empty -> ()
    | other ->
      begin
	let rec sexp_ctyp_decls ppf = function
          | LF.Dec (LF.Empty, decl) ->
            fprintf ppf "%a"
              (sexp_lf_ctyp_decl LF.Empty) decl
          | LF.Dec (cD, decl) ->
            fprintf ppf "%a %a"
              sexp_ctyp_decls cD
              (sexp_lf_ctyp_decl cD) decl
	in
	fprintf ppf "(Prefix %a)" sexp_ctyp_decls other
      end

  and sexp_cmp_branches cD cG ppf =
    function
    | [] -> ()

    | b :: bs ->
      fprintf ppf "%a %a"
        (sexp_cmp_branch cD cG) b
        (sexp_cmp_branches cD cG) bs


  and sexp_cmp_branch cD cG ppf =
    function
    | Comp.Branch (_, cD1', cG', pat, t, e) ->
      let cG_t = cG (* Whnf.cnormCtx (cG, t) *) in
      let cG_ext = Context.append cG_t cG' in
        fprintf ppf "(Branch %a %a %a  %a %a)"
          (sexp_cmp_branch_prefix) cD1'
          (sexp_cmp_gctx cD1') cG'
          (sexp_pat_obj cD1' cG') pat
          (sexp_refinement cD1' cD) t
          (sexp_cmp_exp_chk cD1' cG_ext) e

  and sexp_refinement cD cD0 ppf t =
    begin match (t, cD0) with
    | (LF.MShift k, _ ) ->
        fprintf ppf "(MShift %d)" k

    | (LF.MDot (f, s), LF.Dec(cD', decl)) ->
      fprintf ppf "(MDot %a %a)"
        (sexp_refine_elem cD decl) f
        (sexp_refinement cD cD') s

    | _ -> raise (Error.Violation "Cannot print refinement, invalid context for subsitution")
  end

  and sexp_refine_elem cD decl ppf m =
    let name = begin match decl with
      | LF.Decl(name,_,_) -> name
      | LF.DeclOpt name -> name
    end in
    fprintf ppf "(%a . %s)"
      (sexp_lf_mfront cD) m
      (Id.render_name name)

  and sexp_cmp_gctx cD ppf =
    function
    | LF.Empty ->
      fprintf ppf "Nil"

    | LF.Dec (cG, Comp.CTypDecl (x, tau, _)) ->
      fprintf ppf "(Dec %a (%s . %a))"
        (sexp_cmp_gctx cD) cG
        (Id.render_name x)
        (sexp_cmp_typ cD) tau

  let sexp_thm ppf total d (* (f, tau, e) *) =
    (* do not currently support sexp formatting of Harpoon proofs *)
    let Sgn.({ thm_name; thm_typ; thm_body = Comp.Program e; _ }) = d in
    fprintf ppf "(%s %s %a %a)"
      (if total then "RecTotal" else "Rec")
      (R.render_cid_prog thm_name)
      (sexp_cmp_typ LF.Empty) thm_typ
      (sexp_cmp_exp_chk  LF.Empty
         (LF.Dec(LF.Empty, Comp.CTypDecl ((Store.Cid.Comp.get thm_name).Store.Cid.Comp.name, thm_typ, false)))) e

  let rec sexp_sgn_decl ppf =
    function
    (* Type abbreviations are not dumped since they are not even pretty printed) *)
    | Sgn.CompTypAbbrev (_,_,_,_) -> ()

    | Sgn.Const (_, c, a) ->
      fprintf ppf "(Const %s %a)"
        (R.render_cid_term c)
        (sexp_lf_typ LF.Empty  LF.Null)  a

    | Sgn.Typ (_, a, k) ->
      fprintf ppf "(Typ %s %a)"
        (R.render_cid_typ  a)
        (sexp_lf_kind LF.Null) k

    | Sgn.CompTyp (_, a, cK, _) ->
      fprintf ppf "(CompTyp %s %a)"
        (Id.render_name a)
        (sexp_cmp_kind LF.Empty) cK

    | Sgn.CompCotyp (_, a, cK) ->
      fprintf ppf "(CompCotyp %s %a)"
        (Id.render_name a)
        (sexp_cmp_kind LF.Empty) cK

    | Sgn.CompDest (_, c, cD, tau0, tau1) ->
      fprintf ppf "(CompDest %s %a %a)"
        (Id.render_name c)
        (sexp_cmp_typ cD) tau0
        (sexp_cmp_typ cD) tau1

    | Sgn.CompConst (_, c, tau) ->
      fprintf ppf "(CompConst %s %a)"
        (Id.render_name c)
        (sexp_cmp_typ LF.Empty) tau

    | Sgn.MRecTyp(_, l) ->
      List.iter (sexp_sgn_decl ppf) (List.flatten l)

    | Sgn.Val (_, x, tau, i, None) ->
      fprintf ppf "(Val %s %a %a None)"
        (Id.render_name x)
        (sexp_cmp_typ LF.Empty) tau
        (sexp_cmp_exp_chk LF.Empty LF.Empty) i

    | Sgn.Val (_, x, tau, i, Some v) ->
      fprintf ppf "(Val %s %a %a (Some %a))"
        (Id.render_name x)
        (sexp_cmp_typ LF.Empty) tau
        (sexp_cmp_exp_chk LF.Empty LF.Empty) i
        sexp_cmp_value v

    | Sgn.Schema (w, schema) ->
      fprintf ppf "(Schema %s %a)"
        (R.render_cid_schema  w)
        sexp_lf_schema schema

    | Sgn.Theorem (thm :: t as ts) ->
       let total =
         Store.Cid.Comp.((get Sgn.(thm.thm_name)).total)
       in
      List.iter (sexp_thm ppf total) ts

    (* Pragmas are not dumped for now *)
    (* | Sgn.Pragma (LF.OpenPrag n) -> *)
    (*   let n' = Store.Modules.name_of_id n in *)
    (*   let _ = Store.Modules.open_module n' in *)
    (*   fprintf ppf "@\n%%open %s@\n" (String.concat "." n') *)
    | Sgn.Pragma _ -> ()

    (* Modules are not dumped, since the current implementation uses
       state and terrifying things *)
    (* | Sgn.Module(_, name, decls) -> *)
    (*   let aux fmt t = List.iter (fun x -> (sexp_sgn_decl fmt x)) t in *)

    (*       (\* Necessary to enforce correct printing *\) *)
    (*   let ((_, origName, _, _) as state) = Store.Modules.getState () in *)
    (*   let newName = origName@[name] in *)
    (*   let _ = Store.Modules.current := (Store.Modules.id_of_name newName) in *)
    (*   let _ = Store.Modules.currentName := newName in *)
    (*   let _ = fprintf ppf "@\nmodule %s = struct@\n@[<v2>%a@]@\nend;@\n" *)
    (*     (name) (aux) decls in *)
    (*   Store.Modules.setState state *)

    |  _ -> ()

  let sexp_sgn_decls ppf sgn =
    fprintf ppf "(Decls %a)"
    (fun ppf -> List.iter (sexp_sgn_decl ppf)) sgn
end
