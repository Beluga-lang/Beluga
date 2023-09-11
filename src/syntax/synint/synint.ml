(** Internal Syntax *)

open Support.Equality
open Support
open Syncom

open Id

(* Internal LF Syntax *)
module LF = struct
  type 'a ctx =                          (* Generic context declaration    *)
    | Empty                              (* C ::= Empty                    *)
    | Dec of 'a ctx * 'a                 (*   | C, x:'a                    *)

  type svar_class = Ren | Subst

  type kind =
    | Typ
    | PiKind of (typ_decl * Depend.t * Plicity.t) * kind

  and typ_decl =                                (* LF Declarations                *)
    | TypDecl of Name.t * typ                   (* D ::= x:A                      *)
    | TypDeclOpt of Name.t                      (*   |  x:_                       *)

  (** Right-hand side of the turnstile for meta-types *)
  and cltyp =
    | MTyp of typ
    | PTyp of typ
    | STyp of svar_class * dctx

  (** Meta-types *)
  and ctyp =
    | ClTyp of cltyp * dctx
    | CTyp of cid_schema option

  and ctyp_decl =                               (* Contextual Declarations        *)
    | Decl of
        { name : Name.t
        ; typ : ctyp
        ; plicity : Plicity.t
        ; inductivity : Inductivity.t
        } (* TODO: Annotate with [Depend.t]*)
    | DeclOpt of
        { name : Name.t
        ; plicity : Plicity.t
        } (* TODO: Annotate with [Depend.t]*)

  and typ =                                                (* LF level                       *)
    | Atom of Location.t * cid_typ * spine                 (* A ::= a M1 ... Mn              *)
    | PiTyp of (typ_decl * Depend.t * Plicity.t) * typ     (*   | Pi x:A.B                   *)
    | Sigma of typ_rec
    | TClo of (typ * sub)                                  (*   | TClo(A,s)                  *)


  (* The plicity annotation is set to `implicit when reconstructing an
     a hole (_) so that when printing, it can be reproduced correctly.
   *)
  and normal =                                       (* normal terms                   *)
    | Lam of Location.t * Name.t * normal            (* M ::= \x.M                     *)
    | Root of Location.t * head * spine * Plicity.t  (*   | h . S                      *)
    | LFHole of Location.t * HoleId.t * HoleId.name
    | Clo of (normal * sub)                          (*   | Clo(N,s)                   *)
    | Tuple of Location.t * tuple

  (* TODO: Heads ought to carry their location.
     Erasure currently needs to invent / pretend that a different
     location is the correct one.
   *)
  and head =
    | BVar of offset                            (* H ::= x                        *)
    | Const of cid_term                         (*   | c                          *)
    | MMVar of mm_var_inst                      (*   | u[t ; s]                   *)
    | MPVar of mm_var_inst                      (*   | p[t ; s]                   *)
    | MVar of (cvar * sub)                      (*   | u[s]                       *)
    | PVar of (offset * sub)                    (*   | p[s]                       *)
    | AnnH of head * typ                        (*   | (H:A)                      *)
    | Proj of head * int                        (*   | x.k | #p.k s               *)

    | FVar of Name.t                            (* free variable for type
                                                   reconstruction                 *)
    | FMVar of fvarsub                          (* free meta-variable for type
                                                   reconstruction                 *)
    | FPVar of fvarsub                          (* free parameter variable for type
                                                   reconstruction                 *)
    | HClo of offset * offset * sub             (*   | HClo(x, #S[sigma])         *)
    | HMClo of offset * mm_var_inst             (*   | HMClo(x, #S[theta;sigma])  *)

  and fvarsub = Name.t * sub
  and spine =                                   (* spine                          *)
    | Nil                                       (* S ::= Nil                      *)
    | App of normal * spine                     (*   | M . S                      *)
    | SClo of (spine * sub)                     (*   | SClo(S,s)                  *)

  and sub =
    | Shift of offset                           (* sigma ::= ^(psi,n)             *)
    | SVar of offset * int * sub (* BEWARE: offset and int are both ints,
                                     and in the opposite order compared to FSVar and MSVar.
                                     offset is the index into Delta and describes the SVar.
                                     This is a pain to fix *)
    | FSVar of offset * fvarsub                 (*   | s[sigma]                   *)
    | Dot of front * sub                        (*   | Ft . s                     *)
    | MSVar of offset * mm_var_inst             (*   | u[t ; s]                   *)
    | EmptySub
    | Undefs

  and front =                                   (* Fronts:                        *)
    | Head of head                              (* Ft ::= H                       *)
    | Obj of normal                             (*    | N                         *)
    | Undef                                     (*    | _                         *)

                                                (* Contextual substitutions       *)
  and mfront =                                  (* Fronts:                        *)
    | ClObj of dctx_hat * clobj
    | CObj of dctx                              (*    | Psi                       *)
    | MV of offset                              (*    | u//u | p//p | psi/psi     *)
    | MUndef (* This shouldn't be here, we should use a different datastructure for
               partial inverse substitutions *)

  and clobj =                                   (* ContextuaL objects *)
    | MObj of normal                            (* Mft::= Psihat.N                *)
    | PObj of head                              (*    | Psihat.p[s] | Psihat.x    *)
    | SObj of sub

  and msub =                                    (* Contextual substitutions       *)
    | MShift of int                             (* theta ::= ^n                   *)
    | MDot of mfront * msub                     (*       | MFt . theta            *)

  and cvar =                                    (* Contextual Variables                  *)
    | Offset of offset                          (* Bound Variables                       *)
    | Inst of mm_var                            (* D ; Psi |- M <= A provided constraint *)

  and mm_var =
    { name : Name.t
    ; instantiation : iterm option ref
    ; cD : mctx
    ; mmvar_id : int (* unique to each MMVar *)
    ; typ : ctyp
    ; constraints : cnstr list ref (* not really used *)
    ; plicity : Plicity.t
    ; inductivity : Inductivity.t
    }

  and mm_var_inst' = mm_var * msub
  and mm_var_inst = mm_var_inst' * sub

  and iterm =
    | INorm of normal
    | IHead of head
    | ISub of sub
    | ICtx of dctx

  and tvar =
    | TInst of typ option ref * dctx * kind * cnstr list ref

  (* unique identifiers attached to constraints, used for debugging *)
  and constrnt_id = int

  and constrnt =                                       (* Constraint                            *)
    | Queued of constrnt_id                            (* constraint ::= Queued                 *)
    | Eqn of constrnt_id * mctx * dctx * iterm * iterm (*            | Delta; Psi |-(M1 == M2)  *)

  and cnstr = constrnt ref

  and dctx =                               (* LF Context                      *)
    | Null                                 (* Psi ::= .                       *)
    | CtxVar of ctx_var                    (*     | psi                       *)
    | DDec of dctx * typ_decl              (*     | Psi, x:A   or x:block ... *)

  and ctx_var =
    | CtxName of Name.t
    | CtxOffset of offset
    | CInst of mm_var_inst'
       (* D |- Psi : schema   *)

  and sch_elem =                           (* Schema Element                 *)
    | SchElem of typ_decl ctx * typ_rec    (* Pi    x1:A1 ... xn:An.
                                              Sigma y1:B1 ... yk:Bk. B       *)
                                           (* Sigma-types not allowed in Ai  *)

  and schema =
    | Schema of sch_elem list

  and dctx_hat = ctx_var option * offset   (* Psihat ::=         *)
                                           (*        | psi       *)
                                           (*        | .         *)
                                           (*        | Psihat, x *)


  and typ_rec =                            (* Sigma x1:A1 ... xn:An. B *)
    |  SigmaLast of Name.t option * typ    (* ... . B *)
    |  SigmaElem of Name.t * typ * typ_rec (* xk : Ak, ... *)

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and mctx = ctyp_decl ctx                 (* Modal Context  D: CDec ctx     *)

  let map_plicity f =
    function
    | Root (loc, tH, tS, plicity) ->
       Root (loc, tH, tS, f plicity)
    | tM -> tM

  let proj_maybe (h : head) : int option -> head =
    function
    | None -> h
    | Some k -> Proj (h, k)

  (** Helper for forming TClo LF types, which avoids doing so if the
      substitution is the identity.
   *)
  let tclo tA s =
    match s with
    | Shift 0 -> tA
    | _ -> TClo (tA, s)

  (** Forms an MMVar instantiation by attaching an LF substitution and
      a meta-substituation to the variable.
   *)
  let mm_var_inst (u : mm_var) (t : msub) (s : sub): mm_var_inst = (u, t), s

  let is_mmvar_instantiated mmvar = Option.is_some (mmvar.instantiation.contents)
  let type_of_mmvar_instantiated mmvar =  (mmvar.typ)
  let rename_ctyp_decl f =
    function
    | Decl d -> Decl { d with name = f d.name }
    | DeclOpt d -> DeclOpt { d with name = f d.name }

  (** Embeds a head into a normal by using an empty spine.
      Very useful for constructing variables as normals.
      Note that the normal will have a ghost location, as heads don't
      carry a location.
   *)
  let head (tH : head) : normal =
    Root (Location.ghost, tH, Nil, Plicity.explicit)

  let mvar cvar sub : head =
    MVar (cvar, sub)

  let mmvar inst = MMVar inst

  let mpvar inst = MPVar inst

  (** Assert that the contextual type declaration be a real Decl, and
      not a DeclOpt.
      Raises a violation if it is a DeclOpt.
   *)
  let require_decl : ctyp_decl -> Name.t * ctyp * Plicity.t * Inductivity.t =
    function
    | Decl { name = u; typ = cU; plicity; inductivity } -> (u, cU, plicity, inductivity)
    | DeclOpt _ ->
       Error.raise_violation "[require_decl] DeclOpt is forbidden"

  (* Hatted version of LF.Null *)
  let null_hat : dctx_hat = (None, 0)

  let rec loc_of_normal =
    function
    | Lam (loc, _, _) -> loc
    | Root (loc, _, _, _) -> loc
    | LFHole (loc, _, _) -> loc
    | Clo (tM, _) -> loc_of_normal tM
    | Tuple (loc, _) -> loc

  (**********************)
  (* Type Abbreviations *)
  (**********************)

  type nclo = normal * sub               (* Ns = [s]N                      *)
  type sclo = spine * sub                (* Ss = [s]S                      *)
  type tclo = typ * sub                  (* As = [s]A                      *)
  type trec_clo = typ_rec * sub          (* [s]Arec                        *)

  (**********************)
  (* Helpers            *)
  (**********************)

  let rec blockLength =
    function
    | SigmaLast _ -> 1
    | SigmaElem(_x, _tA, recA) -> 1 + blockLength recA

  (* getType traverses the typ_rec from left to right;
     target is relative to the remaining suffix of the type

     getType head s_recA target j = (tA, s')

     if  Psi(head) = Sigma recA'
         and [s]recA is a suffix of recA'
     then
         Psi |- [s']tA  <= type

    val getType : head -> trec_clo -> int -> tclo
  *)
  let getType =
    let rec getType head s_recA target j =
      match (s_recA, target) with
      | ((SigmaLast (_, lastA), s), 1) ->
          (lastA, s)

      | ((SigmaElem (_x, tA, _recA), s), 1) ->
          (tA, s)

      | ((SigmaElem (_x, _tA, recA), s), target) ->
          let tPj = Proj (head, j) in
          getType head (recA, Dot (Head tPj, s)) (target - 1) (j + 1)

      | _ -> raise Not_found
    in
    fun head s_recA target -> getType head s_recA target 1

  (* getIndex traverses the typ_rec from left to right;
     target is the name of the projection we're looking for
  *)
  let getIndex =
    let rec getIndex' trec target acc =
      match trec with
      | SigmaLast (None, _) -> raise Not_found
      | ( SigmaLast (Some name, _)
        | SigmaElem (name, _, _)
        ) when Name.(name = target) -> acc
      | SigmaLast (Some _, _) -> failwith "Projection Not found"
      | SigmaElem (_, _, trec') -> getIndex' trec' target (acc + 1)
    in fun trec target -> getIndex' trec target 1

  let is_explicit =
    function
    | Decl { inductivity = Inductivity.Inductive; _ }
    | Decl { plicity = Plicity.Explicit; _ } -> true
    | _ -> false

  let name_of_ctyp_decl (d : ctyp_decl) =
    match d with
    | Decl d -> d.name
    | DeclOpt d -> d.name

  (** Decides whether the given mfront is a variable,
      viz. [projection of a] pattern variable, metavariable, or
      context variable.
      Returns the offset of the variable, and optionally the
      projection offset.
   *)
  let variable_of_mfront (mf : mfront) : (offset * offset option) option =
    match mf with
    | ClObj (_, MObj (Root (_, MVar (Offset x, _), _, _)))
      | CObj (CtxVar (CtxOffset x))
      | ClObj (_ , MObj (Root (_, PVar (x, _), _, _)))
      | ClObj (_ , PObj (PVar (x, _)))  ->
       Some (x, None)

    | ClObj (_, MObj (Root (_, Proj (PVar (x, _), k ), _, _)))
      | ClObj (_, PObj (Proj (PVar (x, _), k))) ->
       Some (x, Some k)

    | _ -> None

  let get_constraint_id =
    function
    | Eqn (id, _, _, _, _) -> id
    | Queued id -> id

  let rec drop_spine k =
    function
    | tS when k = 0 -> tS
    | Nil -> Nil
    | App (_, tS') -> drop_spine (k - 1) tS'
    | SClo (tS', _) -> drop_spine (k - 1) tS'
end

(* Internal Computation Syntax *)
module Comp = struct
  type unbox_modifier =
    [ `Strengthened
    ]

  type case_pragma = PragmaCase | PragmaNotCase

  type context_case =
    | EmptyContext of Location.t
    | ExtendedBy of Location.t * int (* specifies a schema element *)

  type case_label =
    | Lf_constant of Location.t * Name.t * Id.cid_term
    | Comp_constant of Location.t * Name.t * Id.cid_comp_const
    | BVarCase of Location.t
    | ContextCase of context_case
    | PVarCase
      of Location.t
         * int (* schema element number (1-based) *)
         * int option (* the number of the projection, if any (1-based) *)

  type 'a generic_order =
    | Arg of 'a                                    (* O ::= x                    *)
    | Lex of 'a generic_order list                 (*     | {O1 .. On}           *)
    | Simul of 'a generic_order list               (*     | [O1 .. On]           *)
  (* Note: Simul is currently unused. It doesn't even have a parser. -je *)

  (** Type specified in an interactive use of `suffices` *)
  type 'a generic_suffices_typ =
    [ `exact of 'a (* user specified an exact type annotation *)
    | `infer of Location.t (* user specified `_` and expects the type to be known *)
    ]

  let map_suffices_typ (f : 'a -> 'b) : 'a generic_suffices_typ -> 'b generic_suffices_typ =
    function
    | `exact x -> `exact (f x)
    | `infer loc -> `infer loc

  let rec map_order (f : 'a -> 'b) : 'a generic_order -> 'b generic_order =
    function
    | Arg x -> Arg (f x)
    | Lex xs -> Lex (List.map (map_order f) xs)
    | Simul xs -> Simul (List.map (map_order f) xs)

  type kind =
    | Ctype of Location.t
    | PiKind of Location.t * LF.ctyp_decl * kind

  type meta_typ = LF.ctyp

  type meta_obj = Location.t * LF.mfront

  type meta_spine =
    | MetaNil
    | MetaApp of meta_obj * meta_typ (* annotation for pretty printing*)
                 * meta_spine * Plicity.t

  type typ =
    | TypBase of Location.t * cid_comp_typ * meta_spine
    | TypCobase of Location.t * cid_comp_cotyp * meta_spine
    | TypDef of Location.t * cid_comp_typ * meta_spine
    | TypBox of Location.t * meta_typ
    | TypArr of Location.t * typ * typ
    | TypCross of Location.t * typ List2.t
    | TypPiBox of Location.t * LF.ctyp_decl * typ
    | TypClo of typ *  LF.msub
    | TypInd of typ

  type suffices_typ = typ generic_suffices_typ

  let rec loc_of_typ : typ -> Location.t =
    function
    | TypBase (l, _, _) | TypCobase (l, _, _) | TypDef (l, _, _)
      | TypBox (l, _) | TypArr (l, _, _) | TypCross (l, _)
      | TypPiBox (l, _, _) ->
       l
    | TypClo (tau, _) | TypInd tau -> loc_of_typ tau

  let loc_of_suffices_typ : suffices_typ -> Location.t =
    function
    | `exact tau -> loc_of_typ tau
    | `infer loc -> loc

  type ih_arg =
    | M of meta_obj * meta_typ
    | V of offset
    | E (* what is E? -je *)
    | DC
  (* ^ For arguments that not constrained in the IH call. Stands
     for don't care. *)

  type wf_tag = bool  (* indicates whether the argument is smaller *)

  type ctyp_decl =
    | CTypDecl of Name.t * typ * wf_tag

    (** Used during pretty-printing when going under lambdas. *)
    | CTypDeclOpt of Name.t

  type ih_decl =
    | WfRec of Name.t * ih_arg list * typ

  let rename_ctyp_decl f =
    function
    | CTypDecl (x, tau, tag) -> CTypDecl (f x, tau, tag)
    | CTypDeclOpt x -> CTypDeclOpt (f x)

  type gctx = ctyp_decl LF.ctx

  type ihctx = ih_decl LF.ctx

  (** Normal computational terms *)
  and exp =                                                                               (* e :=                                              *)
    | Fn         of Location.t * Name.t * exp                                             (* | \x. e'                                          *)
    | Fun        of Location.t * fun_branches                                             (* | b_1...b_k                                       *)
    | MLam       of Location.t * Name.t * exp * Plicity.t                                 (* | Pi X.e'                                         *)
    | Tuple      of Location.t * exp List2.t                                              (* | (e1, e2, ..., en)                               *)
    | LetTuple   of Location.t * exp * (Name.t List2.t * exp)                             (* | let (x1=i.1, x2=i.2, ..., xn=i.n) = i in e      *)
    | Let        of Location.t * exp * (Name.t * exp)                                     (* | let x = e' in e''                               *)
    | Box        of Location.t * meta_obj * meta_typ (* for printing *)                   (* | Box (C) : [U]                                   *)
    | Case       of Location.t * case_pragma * exp * branch list                          (* | case e of branches                              *)
    | Impossible of Location.t * exp                                                      (* | impossible e                                    *)
    | Hole       of Location.t * HoleId.t * HoleId.name                                   (* | _                                               *)
    | Var        of Location.t * offset                                                   (* | x:tau in cG                                     *)
    | DataConst  of Location.t * cid_comp_const                                           (* | c:tau in Comp. Sig.                             *)
    | Obs        of Location.t * exp * LF.msub * cid_comp_dest                            (* | observation (e, ms, destructor={typ, ret_typ}   *)
    | Const      of Location.t * cid_prog                                                 (* | theorem cp                                      *)
    | Apply      of Location.t * exp * exp                                                (* | (n:tau_1 -> tau_2) (e:tau_1)                    *)
    | MApp       of Location.t * exp * meta_obj * meta_typ (* for printing *) * Plicity.t (* | (Pi X:U. e': tau) (C : U)                       *)
    | AnnBox     of Location.t * meta_obj * meta_typ                                      (* | [cPsihat |- tM] : [cPsi |- tA]                  *)

  and pattern =
    | PatMetaObj of Location.t * meta_obj
    | PatConst of Location.t * cid_comp_const * pattern_spine
    | PatFVar of Location.t * Name.t (* used only _internally_ by coverage *)
    | PatVar of Location.t * offset
    | PatTuple of Location.t * pattern List2.t
    | PatAnn of Location.t * pattern * typ * Plicity.t

  and pattern_spine =
    | PatNil
    | PatApp of Location.t * pattern * pattern_spine
    | PatObs of Location.t * cid_comp_dest * LF.msub * pattern_spine

  and branch =
    | Branch
      of Location.t
         * LF.mctx (* branch prefix *)
         * (LF.mctx * gctx) (* branch contexts *)
         * pattern
         * LF.msub (* refinement substitution for the branch *)
         * exp

  and fun_branches =
   | NilFBranch  of Location.t
   | ConsFBranch of Location.t * (LF.mctx * gctx * pattern_spine * exp) * fun_branches

  type tclo = typ * LF.msub

  type order = int generic_order

  type 'order total_dec_kind =
    [ `inductive of 'order
    | `not_recursive
    | `trust (* trusted *)
    | `partial (* not total *)
    ]

  let map_total_dec_kind (f : 'o1 -> 'o2) : 'o1 total_dec_kind -> 'o2 total_dec_kind =
    function
    | `inductive o -> `inductive (f o)
    | x -> x

  let option_of_total_dec_kind =
    function
    | `inductive o -> Some o
    | _ -> None

  (** Applies a spine of checkable terms to a synthesizable term, from
      left to right. *)
  let rec apply_many i =
    function
    | [] -> i
    | e :: es -> apply_many (Apply (Location.ghost, i, e)) es

  let loc_of_exp =
    function
    | Fn (loc, _, _)
    | Fun (loc, _)
    | MLam (loc, _, _, _)
    | Tuple (loc, _)
    | LetTuple (loc, _, _)
    | Let (loc, _, _)
    | Box (loc, _, _)
    | Case (loc, _, _, _)
    | Impossible (loc, _)
    | Hole (loc, _, _)
    | Var (loc, _)
    | DataConst (loc, _)
    | Obs (loc, _, _, _)
    | Const (loc, _)
    | Apply (loc, _, _)
    | MApp (loc, _, _, _, _)
    | AnnBox (loc, _, _) -> loc

  type total_dec =
    { name : Name.t
    ; tau  : typ
    ; order: order total_dec_kind
    }

  let make_total_dec name tau order =
    { name; tau; order }

  (** Decides whether this synthesizable expression is actually an
      annotated box.
   *)
  let is_meta_obj : exp -> meta_obj option =
    function
    | AnnBox (_, m, _)  -> Some m
    | _ -> None

  let head_of_meta_obj : meta_obj -> (LF.dctx_hat * LF.head) option =
    let open LF in
    function
    | (_, ClObj (phat, MObj (Root (_, h, _, _)))) -> Some (phat, h)
    | _ -> None

  let itermToClObj =
    function
    | LF.INorm n -> LF.MObj n
    | LF.IHead h -> LF.PObj h
    | LF.ISub s -> LF.SObj s
    | _ -> failwith "can't convert iterm to clobj"

  let metaObjToMFront (_loc, x) = x

  (** Finds the head of an application. Chases meta-applications and
      computation applications.
   *)
  let rec head_of_application : exp -> exp =
    function
    | Apply (_, i, _) -> head_of_application i
    | MApp (_, i, _, _, _) -> head_of_application i
    | i -> i

  (** Removes all type annotations from a pattern. *)
  let rec strip_pattern : pattern -> pattern =
    function
    | PatTuple (loc, ps) ->
       PatTuple (loc, List2.map strip_pattern ps)
    | PatAnn (loc, p, _, _) -> p
    | PatConst (loc, c, pS) ->
       PatConst (loc, c, strip_pattern_spine pS)
    | p -> p (* no subpatterns *)

  and strip_pattern_spine : pattern_spine -> pattern_spine =
    function
    | PatNil -> PatNil
    | PatApp (loc, p, pS) ->
       PatApp (loc, strip_pattern p, strip_pattern_spine pS)

  type defer_kind =
    [ `subgoal
    | `theorem
    ]

  type invoke_kind =
    [ `ih
    | `lemma
    ]

  type split_kind =
    [ `split
    | `invert
    | `impossible
    ]

  type level =
    [ `meta
    | `comp
    ]

  (* Bundle of LF and computational hypotheses. *)
  type hypotheses =
    { cD : LF.mctx (* Delta / meta context / LF assumptions *)
    ; cG : gctx    (* Gamma / computation assumptions *)
    ; cIH : ihctx   (* Generated induction hypotheses. *)
    }

  let no_hypotheses = { cD = LF.Empty; cG = LF.Empty; cIH = LF.Empty }

  type meta_branch_label =
    [ `ctor of cid_term
    | `pvar of int option

    (* used when matching on a pvar in a nonempty context; this means
       the pvar is actually the head variable in the context. *)
    | `bvar
    ]

  module SubgoalPath = struct
    type t =
      | Here
      | Intros       of t
      | Suffices     of exp * int * t
      | MetaSplit    of exp * meta_branch_label * t
      | CompSplit    of exp * cid_comp_const * t
      | ContextSplit of exp * context_case * t

    let equals p1 p2 = assert false

    type builder = t -> t
    let start = fun p -> p
    let append (b1 : builder) (b2 : builder) : builder =
      fun p -> b1 (b2 p)

    let build_here (b : builder) : t =
      b Here

    let build_intros = fun p -> Intros p
    let build_suffices i k = fun p -> Suffices (i, k, p)
    let build_meta_split i lbl = fun p -> MetaSplit (i, lbl, p)
    let build_comp_split i lbl = fun p -> CompSplit (i, lbl, p)
    let build_context_split i lbl = fun p -> ContextSplit (i, lbl, p)
  end

  (* A proof is a sequence of statements ending either as a complete proof or an incomplete proof.*)
  type proof =
    | Incomplete (* hole *)
      of Location.t * proof_state
    | Command of command * proof
    | Directive of directive (* which can end proofs or split into subgoals *)

  and command =
    | By    of exp * Name.t * typ
    | Unbox of exp * Name.t * LF.ctyp * unbox_modifier option
  (* ^ The stored ctyp is the type synthesized for the exp, BEFORE
     the application of any unbox_modifier *)

  and proof_state =
    { context : hypotheses (* all the assumptions *)
    (* The full context in scope at this point. *)

    ; label : SubgoalPath.builder
    (* A list of labels representing where we are in the proof.
       Used to generate a label for the state by assembling them. *)

    ; goal : tclo
    (* The goal of this proof state. Contains a type with a delayed msub. *)

    ; solution : proof option ref
    (* The solution to this proof obligation. Filled in by a tactic later. *)
    }

  and directive =
    | Intros (* Prove a function type by a hypothetical derivation. *)
      of hypothetical
    | Solve (* End the proof with the given term *)
      of exp
    | ImpossibleSplit
      of exp
    | Suffices
      of exp (* i -- the function to invoke *)
         * suffices_arg list
         (* ^ the arguments of the function *)

    | MetaSplit (* Splitting on an LF object *)
      of exp (* The object to split on *)
         * typ (* The type of the object that we're splitting on *)
         * meta_branch list
    | CompSplit (* Splitting on an inductive type *)
      of exp (* THe computational term to split on *)
         * typ (* The type of the object to split on *)
         * comp_branch list
    | ContextSplit (* Splitting on a context *)
      of exp (* The scrutinee *)
         * typ (* The type of the scrutinee *)
         * context_branch list

  and suffices_arg = Location.t * typ * proof

  and context_branch = context_case split_branch
  and meta_branch = meta_branch_label split_branch
  and comp_branch = cid_comp_const split_branch

  (** A general branch of a case analysis. *)
  and 'b split_branch =
    | SplitBranch
         (* the case label for this branch *)
      of 'b

         (* the full pattern generated for this branch *)
         * (gctx * pattern)

         (* refinement substitution for this branch *)
         * LF.msub

         (* the derivation for this case *)
         * hypothetical

  (* Suppose cD and cG are the contexts when checking a split.
     Suppose we have a branch b = SplitBranch (lbl, t, { cD = cD_b; cG = cG_b; _ }).
     Then cD_b |- t : cD
     and the context cG_b to use to check inside the branch is obtained
     from cG' = [t]cG
   *)

 (** A hypothetical derivation lists meta-hypotheses and hypotheses,
     then proceeds with a proof.
  *)
  and hypothetical =
    Hypothetical
    of Location.t
       * hypotheses (* the full contexts *)
       * proof (* the proof; should make sense in `hypotheses`. *)

  (** An open subgoal is a proof state together with a reference ot the
      theorem in which it occurs.
   *)
  type open_subgoal = Location.t * cid_prog * proof_state

  (** Generates a unsolved subgoal with the given goal in an empty
      context, with no label.
   *)
  let make_proof_state label (t : tclo) : proof_state =
    { context = no_hypotheses
    ; goal = t
    ; label
    ; solution = ref None
    }

  (** Smart constructor for an unfinished proof ending. *)
  let incomplete_proof (l : Location.t) (s : proof_state) : proof =
    Incomplete (l, s)

  (** Smart constructor for the intros directive. *)
  let intros (h : hypotheses) (proof : proof) : proof =
    Directive (Intros (Hypothetical (Location.ghost, h, proof)))

  let suffices (i : exp) (ps : suffices_arg list) : proof =
    Directive (Suffices (i, ps))

  let proof_cons (stmt : command) (proof : proof) = Command (stmt, proof)

  let solve (t : exp) : proof =
    Directive (Solve t)

  let context_split (i : exp) (tau : typ) (bs : context_branch list)
      : proof =
    Directive (ContextSplit (i, tau, bs))

  let context_branch (c : context_case) (cG_p, pat) (t : LF.msub) (h : hypotheses) (p : proof)
      : context_branch =
    SplitBranch (c, (cG_p, pat), t, (Hypothetical (Location.ghost, h, p)))

  let meta_split (m : exp) (a : typ) (bs : meta_branch list)
      : proof =
    Directive (MetaSplit (m, a, bs))

  let impossible_split (i : exp) : proof =
    Directive (ImpossibleSplit i)

  let meta_branch
        (c : meta_branch_label)
        (cG_p, pat)
        (t : LF.msub)
        (h : hypotheses)
        (p : proof)
      : meta_branch =
    SplitBranch (c, (cG_p, pat), t, (Hypothetical (Location.ghost, h, p)))

  let comp_split (t : exp) (tau : typ) (bs : comp_branch list)
      : proof =
    Directive (CompSplit (t, tau, bs))

  let comp_branch
        (c : cid_comp_const)
        (cG_p, pat)
        (t : LF.msub)
        (h : hypotheses)
        (d : proof)
      : comp_branch =
    SplitBranch (c, (cG_p, pat), t, (Hypothetical (Location.ghost, h, d)))

  (** Gives a more convenient way of writing complex proofs by using list syntax. *)
  let prepend_commands (cmds : command list) (proof : proof)
      : proof =
    List.fold_right proof_cons cmds proof

  let name_of_ctyp_decl =
    function
    | CTypDecl (name, _, _) -> name
    | CTypDeclOpt name -> name

  (** Decides whether the computational term is actually a variable
      index object.
      See `LF.variable_of_mfront`.
   *)
  let metavariable_of_exp : exp -> (offset * offset option) option =
    function
    | AnnBox (_, (_, mf), _) -> LF.variable_of_mfront mf
    | _ -> None

  (* Decides whether the given term is a computational variable.
     Returns the offset of the variable.
   *)
  let variable_of_exp : exp -> offset option =
    function
    | Var (_, k) -> Some k
    | _ -> None

  type thm =
    | Proof of proof
    | Program of exp

  type env =
    | Empty
    | Cons of value * env

  (* Syntax of values, used by the operational semantics *)

  and value =
    | FnValue    of Name.t * exp * LF.msub * env
    | FunValue   of fun_branches_value
    | ThmValue   of cid_prog * thm * LF.msub * env
    | MLamValue  of Name.t * exp * LF.msub * env
    | CtxValue   of Name.t * exp * LF.msub * env
    | BoxValue   of meta_obj
    | ConstValue of cid_prog
    | DataValue  of cid_comp_const * data_spine
    | TupleValue of value List2.t

  (* Arguments in data spines are accumulated in reverse order, to
     allow applications of data values in constant time. *)
  and data_spine =
    | DataNil
    | DataApp of value * data_spine

  and fun_branches_value =
    | NilValBranch
    | ConsValBranch of (pattern_spine * exp * LF.msub * env) * fun_branches_value
end


(* Internal Signature Syntax *)
module Sgn = struct
  type global_prag =
    | No_strengthening of { location : Location.t }
    | Warn_on_coverage_error of { location : Location.t }
    | Initiate_coverage_checking of { location : Location.t }

  type prag =
    | NamePrag of
        { location : Location.t
        ; constant : Qualified_identifier.t
        ; meta_variable_base : Identifier.t
        ; computation_variable_base : Identifier.t Option.t
        }
    | NotPrag of { location : Location.t }
    | OpenPrag  of
        { location : Location.t
        ; module_identifier : Qualified_identifier.t
        }
    | DefaultAssocPrag of
        { location : Location.t
        ; associativity : Associativity.t
        }
    | PrefixFixityPrag of
        { location : Location.t
        ; constant : Qualified_identifier.t
        ; precedence : Int.t Option.t
        ; postponed : Bool.t
        }
    | InfixFixityPrag of
        { location : Location.t
        ; constant : Qualified_identifier.t
        ; precedence : Int.t Option.t
        ; associativity : Associativity.t Option.t
        ; postponed : Bool.t
        }
    | PostfixFixityPrag of
        { location : Location.t
        ; constant : Qualified_identifier.t
        ; precedence : Int.t Option.t
        ; postponed : Bool.t
        }
    | AbbrevPrag of
        { location : Location.t
        ; module_identifier : Qualified_identifier.t
        ; abbreviation : Identifier.t
        }
        (** [AbbrevPrag { module_identifier; abbreviation; _ }] is the
            pragma [--abbrev module_identifier abbreviation.] for defining
            the alias [abbreviation] for the module [module_identifier]. *)
    | Query of
        { location : Location.t
        ; name : Identifier.t Option.t
        ; typ : LF.typ * Id.offset
        ; expected_solutions : Int.t Option.t
        ; maximum_tries : Int.t Option.t
        }  (** Logic programming query on LF type *)

  type positivity_flag =
    | Nocheck
    | Positivity
    | Stratify of  Location.t * int
    | StratifyAll of Location.t

  (** Reconstructed signature element *)
  type decl =
    | Typ of
        { location: Location.t
        ; cid : Id.cid_typ
        ; identifier: Identifier.t
        ; kind: LF.kind
        } (** LF type family declaration *)

    | Const of
        { location: Location.t
        ; cid : Id.cid_term
        ; identifier: Identifier.t
        ; typ: LF.typ
        } (** LF type constant declaration *)

    | CompTyp of
        { location: Location.t
        ; cid : Id.cid_comp_typ
        ; identifier: Identifier.t
        ; kind: Comp.kind
        ; positivity_flag: positivity_flag
        } (** Computation-level data type constant declaration *)

    | CompCotyp of
        { location: Location.t
        ; cid : Id.cid_comp_cotyp
        ; identifier: Identifier.t
        ; kind: Comp.kind
        } (** Computation-level codata type constant declaration *)

    | CompConst of
        { location: Location.t
        ; cid : Id.cid_comp_const
        ; identifier: Identifier.t
        ; typ: Comp.typ
        } (** Computation-level type constructor declaration *)

    | CompDest of
        { location: Location.t
        ; cid : Id.cid_comp_dest
        ; identifier: Identifier.t
        ; mctx: LF.mctx
        ; observation_typ: Comp.typ
        ; return_typ: Comp.typ
        } (** Computation-level type destructor declaration *)

    | CompTypAbbrev of
        { location: Location.t
        ; cid : Id.cid_comp_typdef
        ; identifier: Identifier.t
        ; kind: Comp.kind
        ; typ: Comp.typ
        } (** Synonym declaration for computation-level type *)

    | Schema of
        { location: Location.t
        ; cid: cid_schema
        ; identifier : Identifier.t
        ; schema: LF.schema
        } (** Declaration of a specification for a set of contexts *)

    | Val of
        { location: Location.t
        ; cid : Id.cid_prog
        ; identifier: Identifier.t
        ; typ: Comp.typ
        ; expression: Comp.exp
        ; expression_value: Comp.value option
        } (** Computation-level value declaration *)

    | Recursive_declarations of
        { location: Location.t
        ; declarations: decl List1.t
        } (** Mutually-recursive declarations *)

    | Theorem of
        { identifier : Identifier.t
        ; cid : cid_prog
        ; typ : Comp.typ
        ; body : Comp.thm
        ; location : Location.t
        } (** Theorem declaration *)

    | Module of
        { location: Location.t
        ; cid : Id.module_id
        ; identifier: Identifier.t
        ; entries: entry list
        } (** Namespace declaration for other declarations *)

  and entry =
    | Pragma of
        { location : Location.t
        ; pragma : prag
        }
    | Declaration of
        { location : Location.t
        ; declaration : decl
        }
    | Comment of
        { location : Location.t
        ; content : String.t
        } (** Documentation comment *)

  type sgn_file =
    { location : Location.t
    ; global_pragmas : global_prag list
    ; entries : entry list
    }

  (** Reconstructed Beluga project *)
  type sgn = sgn_file List1.t
end
