include Format

let enabled = ref false

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

  let pending ppf = fprintf ppf "Ellipsis"
  let fpending ppf _ = fprintf ppf "Ellipsis"

  let rec sexp_lf_typ cD cPsi ppf = function
    | LF.Atom (_, a, LF.Nil) ->
      fprintf ppf "(Atom %s)"
        (R.render_cid_typ a)

    | LF.Atom (_, a, ms) ->
      fprintf ppf "(Atom %s %a)"
        (R.render_cid_typ a)
        (sexp_lf_spine cD cPsi) ms

    | LF.PiTyp ((LF.TypDecl (x, a), _), b) ->
      fprintf ppf "(Pi (%s . %a) %a)"
        (R.render_name x)
        (sexp_lf_typ cD cPsi) a
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
          (R.render_name x)
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
          (R.render_name x)

      | LF.FMVar (u, s) ->
        fprintf ppf "(FMVar %s %a)"
          (R.render_name u)
          (sexp_lf_sub cD cPsi) s

      | LF.FPVar (p, s) ->
        fprintf ppf "(FPVar %s %a)"
          (R.render_name p)
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
          (R.render_name s_name)
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
    | LF.MObj m -> pending ppf
      (* sexp_lf_normal cD cPsi ppf m *)
    | LF.SObj s -> pending ppf
      (* sexp_lf_sub cD cPsi ppf s *)
    | LF.PObj h -> pending ppf
      (* sexp_lf_head cD cPsi ppf h *)


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


  (* and sexp_meta_obj cD ppf (loc,mO) = pending ppf *)
  (*   (\* sexp_lf_mfront cD ppf mO *\) *)

  and sexp_lf_mmvar ppf = function
    | (_, ({ contents = None } as u), _, LF.ClTyp (LF.PTyp tA,_), _, mDep) ->
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
            PInstHashtbl.replace pinst_hashtbl u sym
            ; fprintf ppf "?#%s" sym
      end
    | (_, {contents = Some (LF.IHead h)}, cD, LF.ClTyp (LF.PTyp _,cPsi), _, mDep) ->
      fprintf ppf " %a"
        (sexp_lf_head cD cPsi) h

    | (_, ({ contents = None } as u), _, LF.ClTyp (LF.MTyp tA,_), _, mDep) ->
      let s = (match mDep with LF.No -> "No" | LF.Maybe -> "Maybe" | LF.Inductive -> "Inductive") in
      begin
        try
          fprintf ppf "(?%s . %s)"
            (MInstHashtbl.find minst_hashtbl u) s
        with
          | Not_found ->
            let sym = match Store.Cid.Typ.gen_mvar_name tA with
              | Some vGen -> vGen ()
              | None -> Gensym.MVarData.gensym ()
            in
            MInstHashtbl.replace minst_hashtbl u sym
            ; fprintf ppf "?%s" sym
      end

    | (_, {contents = Some (LF.INorm m)}, cD, LF.ClTyp (LF.MTyp _,cPsi), _, _) ->
      fprintf ppf " %a"
        (sexp_lf_normal cD cPsi) m

    | (_, ({ contents = None } as u), _, LF.ClTyp (LF.STyp (_, cPsi),_), _, mDep) ->
      begin
        try
          fprintf ppf "?%s"
            (SInstHashtbl.find sinst_hashtbl u)
        with
          | Not_found ->
            let sym = Gensym.MVarData.gensym ()
            in
            SInstHashtbl.replace sinst_hashtbl u sym
            ; fprintf ppf "#?%s" sym
      end

    | (_, {contents = Some (LF.ISub s)}, cD, LF.ClTyp (LF.STyp _,cPsi), _, mDep) ->
      fprintf ppf " #%a"
        (sexp_lf_sub cD cPsi) s

  and sexp_lf_offset cD ppf n =
    fprintf ppf "%s" (R.render_cvar cD n)

  and sexp_lf_cvar cD ppf = function
    | LF.Offset n ->
      sexp_lf_offset cD ppf n

    | LF.Inst (_, ({ contents = None } as u), _, LF.ClTyp (LF.MTyp tA,_), _, _) ->
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
    | LF.CInst ((n, {contents = None}, _cD, _schema, _cnstr,_dep), theta) ->
      fprintf ppf "(CInst %s %a)"
        (R.render_name n)
        (sexp_lf_msub cD) theta

    | LF.CInst ((_n, {contents = Some (LF.ICtx cPsi)}, cD', _schema, _cnstr, _dep), theta) ->
      fprintf ppf "%a"
        (sexp_lf_dctx cD') (Whnf.cnormDCtx (cPsi, theta))

    | LF.CtxOffset psi ->
      fprintf ppf "%s"
        (R.render_ctx_var cD psi)
    | LF.CtxName psi ->
      fprintf ppf "%s"
        (R.render_name psi)

  and sexp_lf_typ_rec cD cPsi ppf = function
      | LF.SigmaLast (x, tA) ->
	fprintf ppf "(Last %s %a)"
	  (match x with None -> "_" | Some x -> (R.render_name x))
	  (sexp_lf_typ cD cPsi) tA
      | LF.SigmaElem (x, tA, tAs)  ->
	fprintf ppf "(Elem %s %a %a)"
	  (R.render_name x)
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

    (* | LF.DDec (LF.Null, LF.TypDecl (x, tA)) -> pending ppf *)
    (*   (\* fprintf ppf "%s : %a" *\) *)
    (*   (\*   (R.render_name x) *\) *)
    (*   (\*   (sexp_lf_typ cD LF.Null 0) tA *\) *)

    | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
      fprintf ppf "(DDec %a (%s . %a))"
        (ppr_typ_decl_dctx cD) cPsi
        (R.render_name x)
        (sexp_lf_typ cD cPsi) tA


  and sexp_lf_psi_hat cD ppf = function
    | LF.Null   -> fprintf ppf "Null"

    | LF.CtxVar ctx_var ->
      sexp_lf_ctx_var cD ppf ctx_var

    | LF.DDec (cPsi, LF.TypDeclOpt x) ->
      fprintf ppf "(DDec %a (Opt %s))"
        (sexp_lf_psi_hat cD) cPsi
        (R.render_name x)

    | LF.DDec (cPsi, LF.TypDecl(x, _ )) ->
      fprintf ppf "(DDec %a %s)"
        (sexp_lf_psi_hat cD) cPsi
        (R.render_name x)

  and sexp_lf_dctx cD ppf =
    function
    | LF.Null ->
      fprintf ppf "Null"

    | LF.CtxVar ctx_var ->
      sexp_lf_ctx_var cD ppf ctx_var

    | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
      fprintf ppf "(DDec %a (%s . %a))"
        (sexp_lf_dctx cD) cPsi
        (R.render_name x)
        (sexp_lf_typ cD cPsi) tA

    | LF.DDec (cPsi, LF.TypDeclOpt x) ->
      fprintf ppf "(DDec %a (Opt %s))"
        (sexp_lf_dctx cD) cPsi
        (R.render_name x)

  and sexp_lf_mctx ppf = pending ppf
    (* function *)
    (* | LF.Empty -> *)
    (*   fprintf ppf "." *)

    (* | LF.Dec (cD, ctyp_decl) -> *)
    (*   (match ctyp_decl with *)
    (* 	| LF.Decl (_, _, dep) -> *)
    (* 	  if ((not !Control.printImplicit) && (isImplicit dep)|| *)
    (* 		 (!Control.printNormal)) then *)
    (* 	    fprintf ppf "%a" (sexp_lf_mctx 0) cD *)
    (* 	  else *)
    (* 	    fprintf ppf "%a, %a" *)
    (* 	      (sexp_lf_mctx 0) cD *)
    (* 	      (sexp_lf_ctyp_decl cD lvl) ctyp_decl *)
    (* 	| _ -> *)
    (* 	  fprintf ppf "%a, %a" *)
    (* 	    (sexp_lf_mctx 0) cD *)
    (* 	    (sexp_lf_ctyp_decl cD lvl) ctyp_decl *)
    (*   ) *)
  and sexp_lf_kind cPsi ppf =  function
    | LF.Typ ->
      fprintf ppf "Type"

    | LF.PiKind ((LF.TypDecl (x, a), _), k) ->
      fprintf ppf "(Pi (%s . %a) %a)"
        (R.render_name   x)
        (sexp_lf_typ LF.Empty cPsi) a
        (sexp_lf_kind (LF.DDec(cPsi, LF.TypDeclOpt  x))) k

  and sexp_lf_mtyp' cD lvl ppf = pending ppf
    (* function *)
    (* | LF.ClTyp (LF.MTyp tA, cPsi) -> *)
    (*   fprintf ppf "[%a |- %a]" *)
    (*     (sexp_lf_dctx cD lvl) cPsi *)
    (*     (sexp_lf_typ cD cPsi lvl) tA *)

    (* | LF.ClTyp (LF.PTyp tA, cPsi) -> *)
    (*   fprintf ppf "#[%a |- %a]" *)
    (*     (sexp_lf_dctx cD lvl) cPsi *)
    (*     (sexp_lf_typ cD cPsi lvl) tA *)

    (* | LF.ClTyp (LF.STyp (cl, cPhi), cPsi) -> *)
    (*   fprintf ppf "[%a |- %s  %a]" *)
    (*     (sexp_lf_dctx cD lvl) cPsi *)
    (* 	(match cl with LF.Ren -> "#" | LF.Subst -> "") *)
    (*     (sexp_lf_dctx cD lvl) cPhi *)
    (* | LF.CTyp (Some schemaName) -> *)
    (*   fprintf ppf "%a" *)
    (*     (sexp_lf_schema lvl) (Store.Cid.Schema.get_schema schemaName) *)
    (* | LF.CTyp None -> fprintf ppf "CTX" *)

  and sexp_lf_mtyp cD ppf = sexp_lf_mtyp' cD 0 ppf

  and sexp_lf_ctyp_decl ?(printing_holes=false) cD ppf = pending ppf
    (* function *)
    (* | LF.Decl (u, mtyp,dep) -> *)

    (* 	  (\* Note: I'm not sure, in meta-context printing, implicit arguements should always be printed or not *\) *)
    (* 	  (\* This modification won't print it if Control.printImplicit is false*\) *)

    (*   if ((not !Control.printImplicit) && (isImplicit dep)|| (!Control.printNormal)) then () else begin *)
    (*     fprintf ppf "{%s : %a}%s" *)
    (*       (if printing_holes then Store.Cid.NamedHoles.getName ~tA:(getTyp mtyp) u else R.render_name u) *)
    (*       (sexp_lf_mtyp cD) mtyp *)
    (*       (if !Control.printImplicit then *)
    (* 	      dependent_string dep *)
    (* 	   else inductive_string dep) end *)

    (* | LF.DeclOpt name -> *)
    (*   fprintf ppf "{%s : _ }" *)
    (*     (R.render_name name) *)

  (* and getTyp = function *)
  (*   | LF.ClTyp (LF.MTyp tA, _) *)
  (*   | LF.ClTyp (LF.PTyp tA, _) -> Some tA *)
  (*   | _ -> None *)

  (* and isImplicit = function *)
  (*   | LF.No -> false *)
  (*   | LF.Maybe -> true *)
  (*   | LF.Inductive -> false *)
  (* and dependent_string = function *)
  (*   | LF.No -> "^e" *)
  (*   | LF.Maybe -> "^i" *)
  (*   | LF.Inductive -> "*" *)

  (* and inductive_string dep = *)
  (*   begin match dep with *)
  (*     | LF.No -> "" *)
  (*     | LF.Maybe -> "" *)
  (*     | LF.Inductive -> "*" *)
  (*   end *)

    (* Computation-level *)
  let sexp_cmp_kind cD lvl ppf = pending ppf
    (* function *)
    (* | Comp.Ctype _ -> fprintf ppf "ctype" *)
    (* | Comp.PiKind (_, ctyp_decl, cK) -> *)
    (*   let cond = lvl > 0 in *)
    (*   begin *)
    (*     fprintf ppf "@[<1>%s%a@ %a%s@]" *)
    (*       (l_paren_if cond) *)
    (*       (sexp_lf_ctyp_decl cD 1) ctyp_decl *)
    (*       (sexp_cmp_kind (LF.Dec(cD, ctyp_decl)) 1) cK *)
    (*       (r_paren_if cond) *)
    (*   end *)

  let sexp_meta_typ cD lvl ppf = sexp_lf_mtyp' cD lvl ppf

  let sexp_meta_spine cD lvl ppf = pending ppf
    (* function *)
    (* | Comp.MetaNil -> *)
    (*   fprintf ppf "" *)
    (* | Comp.MetaApp (mO, mS) -> *)
    (*   fprintf ppf " %a%a" *)
    (*     (sexp_meta_obj  cD (lvl + 1)) mO *)
    (*     (sexp_meta_spine   cD lvl) mS *)

  and sexp_iterm cD cPsi ppf = pending ppf
    (* function *)
    (* | LF.INorm tM -> sexp_lf_normal cD cPsi 0 ppf tM *)
    (* | LF.IHead h -> sexp_lf_head cD cPsi 0 ppf h *)
    (* | LF.ISub s -> sexp_lf_sub cD cPsi 0 ppf s *)

  let sexp_cmp_typ cD lvl ppf = pending ppf
    (* function *)
    (* | Comp.TypBase (_, c, mS)-> *)
    (*   let cond = lvl > 1 in *)
    (*   fprintf ppf "%s%s%a%s" *)
    (*     (l_paren_if cond) *)
    (*     (R.render_cid_comp_typ c) *)
    (*     (sexp_meta_spine cD lvl) mS *)
    (*     (r_paren_if cond) *)
    (* | Comp.TypCobase (_, c, mS)-> *)
    (*   let cond = lvl > 1 in *)
    (*   fprintf ppf "%s%s%a%s" *)
    (*     (l_paren_if cond) *)
    (*     (R.render_cid_comp_cotyp c) *)
    (*     (sexp_meta_spine cD lvl) mS *)
    (*     (r_paren_if cond) *)
    (* | Comp.TypBox (_, mT) -> *)
    (*   fprintf ppf "%a" *)
    (* 	(sexp_meta_typ cD 0) mT *)

    (* | Comp.TypArr (tau1, tau2) -> *)
    (*   let cond = lvl > 1 in *)
    (*   fprintf ppf "%s%a -> %a%s" *)
    (*     (l_paren_if cond) *)
    (*     (sexp_cmp_typ cD 0) tau1 *)
    (*     (sexp_cmp_typ cD 0) tau2 *)
    (*     (r_paren_if cond) *)

    (* | Comp.TypCross (tau1, tau2) -> *)
    (*   let cond = lvl > 0 in *)
    (*   fprintf ppf "%s%a * %a%s" *)
    (*     (l_paren_if cond) *)
    (*     (sexp_cmp_typ cD 1) tau1 *)
    (*     (sexp_cmp_typ cD 0) tau2 *)
    (*     (r_paren_if cond) *)

    (* | Comp.TypPiBox (ctyp_decl, tau) -> *)
    (*   let cond = lvl > 1 in *)
    (*   fprintf ppf "%s%a %a%s" *)
    (*     (l_paren_if cond) *)
    (*     (sexp_lf_ctyp_decl cD 1) ctyp_decl *)
    (*     (sexp_cmp_typ (LF.Dec(cD, ctyp_decl)) 1) tau *)
    (*     (r_paren_if cond) *)

    (* | Comp.TypClo (_, _ ) ->             fprintf ppf " TypClo! " *)

    (* | Comp.TypBool -> fprintf ppf "Bool" *)

    (* | Comp.TypInd tau -> *)
    (*   fprintf ppf "(%a)*" *)
    (*     (sexp_cmp_typ cD 1) tau *)

  let sexp_pat_spine cD cG lvl ppf = pending ppf
    (* (function *)
    (* | Comp.PatNil -> fprintf ppf "" *)
    (* | Comp.PatApp (_, pat, pat_spine) -> *)
    (*   fprintf ppf "%a %a" *)
    (*     (sexp_pat_obj cD cG (lvl+1)) pat *)
    (*     (sexp_pat_spine cD cG lvl) pat_spine) *)

  and sexp_pat_obj cD cG lvl ppf = pending ppf
    (* let rec dropSpineLeft ms n = match (ms, n) with *)
    (*   | (_, 0) -> ms *)
    (*   | (Comp.PatNil, _) -> ms *)
    (*   | (Comp.PatApp (_l,_p,rest), n) -> dropSpineLeft rest (n-1) *)
    (* in let deimplicitize_spine c ms = *)
    (*      let ia = if !Control.printImplicit *)
    (*        then 0 *)
    (*        else Store.Cid.CompConst.get_implicit_arguments c in *)
    (* 	 dropSpineLeft ms ia in *)
    (*    function *)
    (* 	 | Comp.PatEmpty (_, cPsi) -> *)
    (*        fprintf ppf "[%a |- {}]" *)
    (*          (sexp_lf_dctx cD 0) cPsi *)
    (* 	 | Comp.PatMetaObj (_, mO) -> *)
    (*        let cond = lvl > 1 in *)
    (*        fprintf ppf "%s%a%s" *)
    (*          (l_paren_if cond) *)
    (*          (sexp_meta_obj cD 0) mO *)
    (*          (r_paren_if cond) *)
    (* 	 | Comp.PatConst (_, c, pat_spine) -> *)
    (*        let pat_spine = deimplicitize_spine c pat_spine in *)
    (*        let cond = lvl > 1 in *)
    (*        fprintf ppf "%s%s %a%s" *)
    (*          (l_paren_if cond) *)
    (*          (R.render_cid_comp_const c) *)
    (*          (sexp_pat_spine cD cG 2) pat_spine *)
    (*          (r_paren_if cond) *)

    (* 	 | Comp.PatPair (_, pat1, pat2) -> *)
    (*        fprintf ppf "(%a , %a)" *)
    (*          (sexp_pat_obj cD cG 0) pat1 *)
    (*          (sexp_pat_obj cD cG 0) pat2 *)
    (* 	 | Comp.PatTrue _ -> fprintf ppf "ttrue" *)
    (* 	 | Comp.PatFalse _ -> fprintf ppf "ffalse" *)
    (* 	 | Comp.PatAnn (_, pat, tau) -> *)
    (*        fprintf ppf "(%a : %a)" *)
    (*          (sexp_pat_obj cD cG 0) pat *)
    (*          (sexp_cmp_typ cD 0) tau *)

    (* 	 | Comp.PatVar (_, offset ) -> *)
    (*        fprintf ppf "%s" *)
    (*          (R.render_var cG offset) *)

    (* 	 | Comp.PatFVar (_, name ) -> *)
    (*        fprintf ppf "%s" *)
    (*          (R.render_name name) *)


  let sexp_cmp_exp_chk cD cG lvl ppf = pending ppf
  (*   function *)
  (*   | Comp.Syn (_, i) -> *)
  (*     sexp_cmp_exp_syn cD cG lvl ppf (strip_mapp_args cD cG i ) *)

  (*   | Comp.Fun (_, x, e) -> *)
  (*     let cond = lvl > 0 in *)
  (*     fprintf ppf "%sfn %s =>@ " *)
  (*       (l_paren_if cond) *)
  (*       (R.render_name x); *)

  (*     fprintf ppf "%a%s" *)
  (*       (sexp_cmp_exp_chk cD (LF.Dec(cG, Comp.CTypDeclOpt x))  0) e *)
  (*       (r_paren_if cond); *)

  (*   | Comp.Cofun (_, bs) -> *)
  (*     let cond = lvl > 0 in *)
  (*     fprintf ppf "%sSome cofun%s" *)
  (*       (l_paren_if cond) *)
  (*       (r_paren_if cond) *)

  (*   | Comp.MLam (_, x, e) -> *)
  (*     let cond = lvl > 0 in *)
  (*     fprintf ppf "%smlam %s =>@ " *)
  (*       (l_paren_if cond) *)
  (*       (R.render_name x); *)
  (*     fprintf ppf "%a%s" *)
  (*       (sexp_cmp_exp_chk (LF.Dec(cD, LF.DeclOpt x)) (Whnf.cnormCtx (cG, LF.MShift 1)) 0) e *)
  (*       (r_paren_if cond); *)

  (*   | Comp.Pair (_, e1, e2) -> *)
  (*     fprintf ppf "(%a , %a)" *)
  (*       (sexp_cmp_exp_chk cD cG 0) e1 *)
  (*       (sexp_cmp_exp_chk cD cG 0) e2 *)


  (*   | Comp.LetPair(_, i, (x, y, e)) -> *)
  (*     let cond = lvl > 1 in *)
  (*     fprintf ppf "@[<2>%slet <%s,%s> = %a@ in %a%s@]" *)
  (*       (l_paren_if cond) *)
  (*       (R.render_name x) *)
  (*       (R.render_name y) *)
  (*       (sexp_cmp_exp_syn cD cG 0) (strip_mapp_args cD cG i) *)
  (*       (sexp_cmp_exp_chk cD (LF.Dec(LF.Dec(cG, Comp.CTypDeclOpt x), Comp.CTypDeclOpt y)) 0) e *)
  (*       (r_paren_if cond) *)


  (*   | Comp.Let(_, i, (x, e)) -> *)
  (*     let cond = lvl > 1 in *)
  (*     fprintf ppf "@[<2>%slet %s = %a@ in %a%s@]" *)
  (*       (l_paren_if cond) *)
  (*       (R.render_name x) *)
  (*       (sexp_cmp_exp_syn cD cG 0) (strip_mapp_args cD cG i) *)
  (*       (sexp_cmp_exp_chk cD (LF.Dec(cG, Comp.CTypDeclOpt x)) 0) e *)
  (*       (r_paren_if cond) *)

  (*   | Comp.Box (_ , cM) -> *)
  (*     let cond = lvl > 1 in *)
  (*     fprintf ppf "%s%a%s" *)
  (*       (l_paren_if cond) *)
  (*       (sexp_meta_obj cD 0) cM *)
  (*       (r_paren_if cond) *)

  (*   | Comp.Case (_, prag, i, ([] as bs)) -> *)
  (*     let cond = lvl > 0 in *)
  (*     if !Control.printNormal then *)
  (*       fprintf ppf "impossible %a" *)
  (*         (sexp_cmp_exp_syn cD cG 0) (strip_mapp_args cD cG i) *)
  (*     else *)
  (*       fprintf ppf "@ %s@[<v>case @[%a@] of%s%a@]@,%s" *)
  (*         (l_paren_if cond) *)
  (*         (sexp_cmp_exp_syn cD cG 0) (strip_mapp_args cD cG i) *)
  (*         (match prag with Pragma.RegularCase -> " " | Pragma.PragmaNotCase -> " %not ") *)
  (*         (sexp_cmp_branches cD cG 0) bs *)
  (*         (r_paren_if cond) *)



  (*   | Comp.Case (_, prag, i, bs) -> *)
  (*     let cond = lvl > 0 in *)
  (*     fprintf ppf "@ %s@[<v>case @[%a@] of%s%a@]@,%s" *)
  (*       (l_paren_if cond) *)
  (*       (sexp_cmp_exp_syn cD cG 0) (strip_mapp_args cD cG i) *)
  (*       (match prag with Pragma.RegularCase -> " " | Pragma.PragmaNotCase -> " %not ") *)
  (*       (sexp_cmp_branches cD cG 0) bs *)
  (*       (r_paren_if cond) *)

  (*   | Comp.If (_, i, e1, e2) -> *)
  (*     let cond = lvl > 1 in *)
  (*     fprintf ppf "@[<2>%sif %a @[<-1>then %a @]else %a%s@]" *)
  (*       (l_paren_if cond) *)
  (*       (sexp_cmp_exp_syn cD cG 0) (strip_mapp_args cD cG i) *)
  (*       (sexp_cmp_exp_chk cD cG 0) e1 *)
  (*       (sexp_cmp_exp_chk cD cG 0) e2 *)
  (*       (r_paren_if cond) *)

  (*   | Comp.Hole (loc, f) -> *)
  (*     try *)
  (*       let x = f () in *)
  (*       fprintf ppf " ? %%{ %d }%%" x *)
  (*     with *)
  (*       | _ -> fprintf ppf " ? " *)

  (* and strip_mapp_args cD cG i = *)
  (*   if !Control.printImplicit then *)
  (*     i *)
  (*   else *)
  (*     let (i', _ ) = strip_mapp_args' cD cG i in i' *)
  (* and strip_mapp_args' cD cG i = match i with *)
  (*   | Comp.Const (_, prog) -> *)
  (*     (i,  implicitCompArg  (Store.Cid.Comp.get prog).Store.Cid.Comp.typ) *)
  (*   | Comp.DataConst (_, c) -> *)
  (*     (i,  implicitCompArg  (Store.Cid.CompConst.get c).Store.Cid.CompConst.typ) *)
  (*   | Comp.Var (_, x) -> *)
  (*     begin match Context.lookup cG x with *)
  (*         None -> (i, []) *)
  (*       | Some tau -> (i,  implicitCompArg tau) *)
  (*     end *)
  (*   | Comp.Apply (loc, i, e) -> *)
  (*     let (i', _) = strip_mapp_args' cD cG i in *)
  (*     (Comp.Apply (loc, i', e), []) *)

  (*   | Comp.MApp (loc, i1, mC) -> *)
  (*     let (i', stripArg) = strip_mapp_args' cD cG i1 in *)
  (*     (match stripArg with *)
  (*       | false :: sA -> (i', sA) *)
  (*       | true  :: sA -> (Comp.MApp (loc , i', mC), sA) *)
  (*       | []          -> (i', [])                ) *)
  (*   | Comp.PairVal (loc, i1, i2) -> *)
  (*     let (i1', _) = strip_mapp_args' cD cG i1 in *)
  (*     let (i2', _) = strip_mapp_args' cD cG i2 in *)
  (*     (Comp.PairVal (loc, i1', i2') , []) *)
  (*   | Comp.Equal (loc, i1, i2) -> *)
  (*     let (i1', _) = strip_mapp_args' cD cG i1 in *)
  (*     let (i2', _) = strip_mapp_args' cD cG i2 in *)
  (*     (Comp.Equal (loc, i1', i2'), []) *)
  (*   | _ -> (i, []) *)
  (* and implicitCompArg tau = begin match tau with *)
  (*   | Comp.TypPiBox ((LF.Decl (_, LF.ClTyp (LF.MTyp _,_), LF.Maybe)), tau) -> *)
  (*     (false)::(implicitCompArg tau) *)
  (*   | Comp.TypPiBox (_ , tau) -> *)
  (*     (true)::(implicitCompArg tau) *)
  (*   | _ -> [] *)
  (* end *)
  and sexp_cmp_exp_syn cD cG lvl ppf = pending ppf
    (* function *)
    (* | Comp.Var (_, x) -> *)
    (*   fprintf ppf "%s" *)
    (*     (R.render_var cG x) *)

    (* | Comp.Const (_ ,prog) -> *)
    (*   fprintf ppf "%s" *)
    (*     (R.render_cid_prog prog) *)

    (* | Comp.DataConst (_, c) -> *)
    (*   fprintf ppf "%s" *)
    (*     (R.render_cid_comp_const c) *)

    (* | Comp.DataDest (_, c) -> *)
    (*   fprintf ppf "%s" *)
    (*     (R.render_cid_comp_dest c) *)

    (* | Comp.Apply (_, i, e) -> *)
    (*   let cond = lvl > 1 in *)
    (*   fprintf ppf "%s@[<2>%a@ %a@]%s" *)
    (*     (l_paren_if cond) *)
    (*     (sexp_cmp_exp_syn cD cG 1) i *)
    (*     (sexp_cmp_exp_chk cD cG 2) e *)
    (*     (r_paren_if cond) *)

    (* | Comp.MApp (_, i, mC) -> *)
    (*   let cond = lvl > 1 in *)
    (*   fprintf ppf "%s%a@ %a%s" *)
    (*     (l_paren_if cond) *)
    (*     (sexp_cmp_exp_syn cD cG 1) i *)
    (*     (sexp_meta_obj cD 0) mC *)
    (*     (r_paren_if cond) *)

    (* | Comp.PairVal (loc, i1, i2) -> *)
    (*   fprintf ppf "(%a , %a)" *)
    (*     (sexp_cmp_exp_syn cD cG 1) i1 *)
    (*     (sexp_cmp_exp_syn cD cG 1) i2 *)

    (* | Comp.Ann (e, _tau) -> *)
    (*   let cond = lvl > 1 in *)
    (*   fprintf ppf "%s%a%s" *)
    (*     (l_paren_if cond) *)
    (*     (sexp_cmp_exp_chk cD cG 1) e *)
    (*     (r_paren_if cond) *)
    (* | Comp.Equal (_, i1, i2) -> *)
    (*   fprintf ppf "%a == %a" *)
    (*     (sexp_cmp_exp_syn cD cG 1) i1 *)
    (*     (sexp_cmp_exp_syn cD cG 1) i2 *)

    (* | Comp.Boolean true -> *)
    (*   fprintf ppf "ttrue" *)

    (* | Comp.Boolean false -> *)
    (*   fprintf ppf "ffalse" *)

  and sexp_cmp_value lvl ppf = pending ppf
    (* function *)
    (*   | Comp.FunValue _ -> fprintf ppf " fn " *)
    (*   | Comp.RecValue _ -> fprintf ppf " rec " *)
    (*   | Comp.MLamValue _ -> fprintf ppf " mlam " *)
    (*   | Comp.CtxValue _ -> fprintf ppf " mlam " *)
    (*   | Comp.BoxValue mC -> fprintf ppf "[%a]"  (sexp_meta_obj LF.Empty 0) mC *)
    (*   | Comp.ConstValue _ -> fprintf ppf " const " *)
    (*   | Comp.BoolValue true -> fprintf ppf "ttrue" *)
    (*   | Comp.BoolValue false -> fprintf ppf "ffalse" *)
    (*   | Comp.PairValue (v1, v2) -> *)
    (*     fprintf ppf "(%a , %a)" *)
    (*       (sexp_cmp_value 0) v1 *)
    (*       (sexp_cmp_value 0) v2 *)
    (*   | Comp.DataValue (c, spine) -> *)
    (* 	 (\* Note: Arguments in data spines are accumulated in reverse order, to *)
    (*         allow applications of data values in constant time. *\) *)
    (* 	let k = if !Control.printImplicit then 0 *)
    (* 	  else Store.Cid.CompConst.get_implicit_arguments c in *)
    (*      (\* the function drop and print_spine can probably be combined *)
    (*         to avoid traversing the spine twice. *)
    (* 	 *\) *)
    (* 	let rec drop ms = match ms with *)
    (* 	  | Comp.DataNil -> (Comp.DataNil, 0) *)
    (* 	  | Comp.DataApp (v, spine) -> *)
    (* 	    let (ms', k') = drop spine in *)
    (* 	    if k' < k then (ms', k'+1) *)
    (* 	    else (Comp.DataApp (v, ms'), k'+1) *)
    (* 	in *)
    (*     let rec print_spine ppf = function *)
    (*       | Comp.DataNil -> () *)
    (*       | Comp.DataApp (v, spine) -> *)
    (*         print_spine ppf spine; *)
    (*         fprintf ppf " %a" (sexp_cmp_value 1 ) v *)
    (*     in *)
    (* 	let (pat_spine, k') = drop spine in *)


    (* 	let cond = lvl > 0 &&  (k' - k) > 1 in *)
    (*     fprintf ppf "%s%s%a%s" *)
    (* 	  (l_paren_if cond) *)
    (* 	  (R.render_cid_comp_const c) print_spine pat_spine *)
    (* 	  (r_paren_if cond) *)

    (*   | Comp.CodataValue (cid, spine) -> fprintf ppf "%s" (R.render_cid_comp_dest cid) *)
    (*   | Comp.CofunValue _ -> fprintf ppf " cofun " *)



  and sexp_cmp_branch_prefix ppf = fpending ppf
    (* function *)
    (* | LF.Empty -> () *)
    (* | other -> *)
    (*   (let rec sexp_ctyp_decls' ppf = function *)
    (*     | LF.Dec (LF.Empty, decl) -> *)
    (*       fprintf ppf "%a" *)
    (*         (sexp_lf_ctyp_decl LF.Empty 1) decl *)
    (*     | LF.Dec (cD, decl) -> *)
    (*       fprintf ppf "%a %a" *)
    (*         (sexp_ctyp_decls') cD *)
    (*         (sexp_lf_ctyp_decl cD 1) decl *)
    (*    in *)
    (*    fprintf ppf "@[%a@]@ " (sexp_ctyp_decls') other *)
    (*   ) *)

  and sexp_cmp_branches cD cG lvl ppf = fpending ppf
    (* function *)
    (* | [] -> () *)

    (* | b :: [] -> *)
    (*   fprintf ppf "%a" *)
    (*     (sexp_cmp_branch cD cG 0) b *)

    (* | b :: bs -> *)
    (*   fprintf ppf "%a%a" *)
    (*     (sexp_cmp_branch cD cG 0) b *)
    (*     (sexp_cmp_branches cD cG lvl) bs *)


  and sexp_cmp_branch cD cG ppf = fpending ppf
    (* function *)
    (* | Comp.EmptyBranch (_, cD1, pat, t) -> *)
    (*   if !Control.printNormal then *)
    (*     fprintf ppf "@ @[<v2>| @[<v0>%a@[%a@]@]@ " *)
    (*       (sexp_cmp_branch_prefix  0) cD1 *)
    (*       (sexp_pat_obj cD1 LF.Empty 0) pat *)
    (*   else *)
    (*     fprintf ppf "@ @[<v2>| @[<v0>%a@[ %a : %a  @]  @]@ " *)
    (*       (sexp_cmp_branch_prefix  0) cD1 *)
    (*       (sexp_pat_obj cD1 LF.Empty 0) pat *)
    (*       (sexp_refinement cD1 cD 2) t *)


    (* | Comp.Branch (_, cD1', _cG, Comp.PatMetaObj (_, mO), t, e) -> *)
    (*   if !Control.printNormal then *)
    (* 	(match e with *)
    (* 	  | Comp.Hole (loc, _ ) -> *)
    (* 	    fprintf ppf "\n | %a %a => %a" *)
    (* 	      (sexp_cmp_branch_prefix  0) cD1' *)
    (* 	      (sexp_meta_obj cD1' 0) mO *)
    (* 	      (sexp_cmp_exp_chk cD1' cG 1) e *)
    (* 	  | _ -> *)
    (* 	    fprintf ppf "@ @[<v2>| @[<v0>%a@[%a@  => @]@ @[<2>@ %a@]@]@ " *)
    (* 	      (sexp_cmp_branch_prefix  0) cD1' *)
    (* 	      (sexp_meta_obj cD1' 0) mO *)
    (*         (\* NOTE: Technically: cD |- cG ctx and *)
    (*          *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1| *)
    (*          * -bp *)
    (*          *\) *)
    (*           (sexp_cmp_exp_chk cD1' cG 1) e) *)
    (*   else *)
    (*     fprintf ppf "@ @[<v2>| @[<v0>%a@[%a : %a  @]  => @]@ @[<2>@ %a@]@]@ " *)
    (*       (sexp_cmp_branch_prefix  0) cD1' *)
    (*       (sexp_meta_obj cD1' 0) mO *)
    (*         (\* this point is where the " : " is in the string above *\) *)
    (*       (sexp_refinement cD1' cD 2) t *)
    (*         (\* NOTE: Technically: cD |- cG ctx and *)
    (*          *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1| *)
    (*          * -bp *)
    (*          *\) *)
    (*       (sexp_cmp_exp_chk cD1' cG 1) e *)

    (* | Comp.Branch (_, cD1', cG', pat, t, e) -> *)
    (*   let cG_t = cG (\* Whnf.cnormCtx (cG, t) *\) in *)
    (*   let cG_ext = Context.append cG_t cG' in *)

    (*   if !Control.printNormal then *)
    (*     fprintf ppf "@ @[<v2>| @[<v0>%a ; %a@[ |- %a  @]  => @]@ @[<2>@ %a@]@]@ " *)
    (*       (sexp_cmp_branch_prefix  0) cD1' *)
    (*       (sexp_cmp_gctx cD1' 0) cG' *)
    (*       (sexp_pat_obj cD1' cG' 0) pat *)
    (*             (\* NOTE: Technically: cD |- cG ctx and *)
    (*              *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1| *)
    (*              * -bp *)
    (*              *\) *)
    (*       (sexp_cmp_exp_chk cD1' cG_ext 1) e *)
    (*   else *)
    (*     fprintf ppf "@ @[<v2>| @[<v0>%a ; %a@[ |- %a  : %a  @]  => @]@ @[<2>@ %a@]@]@ " *)
    (*       (sexp_cmp_branch_prefix  0) cD1' *)
    (*       (sexp_cmp_gctx cD1' 0) cG' *)
    (*       (sexp_pat_obj cD1' cG' 0) pat *)
    (*           (\* this point is where the " : " is in the string a *)
    (* 		 bove *\) *)
    (*       (sexp_refinement cD1' cD 2) t *)
    (*           (\* NOTE: Technically: cD |- cG ctx and *)
    (*            *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1| *)
    (*            * -bp *)
    (*            *\) *)
    (*       (sexp_cmp_exp_chk cD1' cG_ext 1) e *)

  and sexp_refinement cD cD0 lvl ppf t = pending ppf
  (*   begin match (t, cD0) with *)
  (*   | (LF.MShift k, _ ) -> *)
  (*     (match !Control.substitutionStyle with *)
  (*       | Control.Natural -> fprintf ppf "" *)
  (*       | Control.DeBruijn -> fprintf ppf "^%s" (string_of_int k)) *)

  (*   | (LF.MDot (f, LF.MShift k), LF.Dec(cD', decl)) -> *)
  (*     (match !Control.substitutionStyle with *)
  (*       | Control.Natural -> *)
  (*         fprintf ppf "%a" *)
  (*           (sexp_refine_elem cD decl 1) f *)
  (*       | Control.DeBruijn -> *)
  (*         fprintf ppf "%a@ ,@ ^%s" *)
  (*           (sexp_refine_elem cD decl 1) f *)
  (*           (string_of_int k)) *)


  (*   | (LF.MDot (f, s), LF.Dec(cD', decl)) -> *)
  (*     fprintf ppf "%a@ ,@ %a" *)
  (*       (sexp_refine_elem cD decl 1) f *)
  (*       (sexp_refinement cD cD' lvl) s *)
  (*   | _ -> fprintf ppf "No match" *)
  (* end *)


  and sexp_refine_elem cD decl lvl ppf m = pending ppf
    (* let name = begin match decl with *)
    (*   | LF.Decl(name,_,_) -> name *)
    (*   | LF.DeclOpt name -> name *)
    (* end  in *)
    (* fprintf ppf "%a = %s" *)
    (*   (sexp_lf_mfront cD lvl) m *)
    (*   (R.render_name name) *)

  and sexp_cmp_gctx cD lvl ppf = fpending ppf
    (* function *)
    (* | LF.Empty -> *)
    (*   fprintf ppf "." *)

    (* | LF.Dec (cG, Comp.CTypDecl (x, tau)) -> *)
    (*   fprintf ppf "%a, %s: %a" *)
    (*     (sexp_cmp_gctx cD 0) cG *)
    (*     (R.render_name x) *)
    (*     (sexp_cmp_typ cD lvl) tau *)

  let sexp_rec ppf total (f, _tau, _e) =
    fprintf ppf "(%s %s Dots)"  (* ": %a =@ @[<2>%a ;@]@\n" *)
      (if total then "RecTotal" else "Rec")
      (R.render_cid_prog  f)
      (* (sexp_cmp_typ LF.Empty lvl) tau *)
      (* (sexp_cmp_exp_chk  LF.Empty *)
      (*    (LF.Dec(LF.Empty, Comp.CTypDecl ((Store.Cid.Comp.get f).Store.Cid.Comp.name ,  tau)))  lvl) e *)

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

    | Sgn.CompTyp (_, a, _cK, _) ->
      fprintf ppf "(CompTyp %s Dots)" (R.render_name a)
      (* fprintf ppf "@\ndatatype %s : @[%a@] = @\n" *)
      (*   (R.render_name a) *)
      (*   (sexp_cmp_kind LF.Empty lvl) cK *)

    | Sgn.CompCotyp (_, a, _cK) ->
      fprintf ppf "(CompCotyp %s Dots)" (R.render_name a)
      (* fprintf ppf "@\ncodatatype %s : @[%a@] = @\n" *)
      (*   (R.render_name a) *)
      (*   (sexp_cmp_kind LF.Empty lvl) cK *)

    | Sgn.CompDest (_, c, tau)
    | Sgn.CompConst (_, c, tau) ->
      fprintf ppf "(CompDest %s Dots)" (*" : @[%a@]@\n" *)
        (R.render_name c)
        (* (sexp_cmp_typ LF.Empty lvl) tau *)

    | Sgn.MRecTyp(_, l) ->
      List.iter (sexp_sgn_decl ppf) (List.flatten l)

    | Sgn.Val (_, x, _tau, _i, None) ->
      fprintf ppf "(Val %s Dots)" (R.render_name x)
      (* fprintf ppf "@\nlet %s : %a = %a@\n" *)
      (*   (R.render_name x) *)
      (*   (sexp_cmp_typ LF.Empty lvl) tau *)
      (*   (sexp_cmp_exp_chk LF.Empty LF.Empty lvl) i *)

    | Sgn.Val (_, x, tau, i, Some v) ->
      fprintf ppf "(Val %s Dots)" (R.render_name x)
      (* fprintf ppf "@\nlet %s : %a = %a@\n   ===> %a@\n" *)
      (*   (R.render_name x) *)
      (*   (sexp_cmp_typ LF.Empty lvl) tau *)
      (*   (sexp_cmp_exp_chk LF.Empty LF.Empty lvl) i *)
      (*   (sexp_cmp_value lvl) v *)

    | Sgn.Schema (w, schema) ->
      fprintf ppf "(Schema %s %a)"
        (R.render_cid_schema  w)
        sexp_lf_schema schema

    | Sgn.Rec (((f, _, _ ) as h)::t) ->
      let total = (Store.Cid.Comp.get f).Store.Cid.Comp.total  in
      sexp_rec ppf total h;
      List.iter (sexp_rec ppf total) t

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
