open Support.Equality
(* Internal Syntax *)
open Support

open Id

module Loc = Location

(* Internal LF Syntax *)
module LF = struct
  include Syncom.LF

  type kind =
    | Typ
    | PiKind of (typ_decl * depend) * kind

  and typ_decl =                              (* LF Declarations                *)
    | TypDecl of name * typ                   (* D := x:A                       *)
    | TypDeclOpt of name                      (*   |  x:_                       *)

  and cltyp =
    | MTyp of typ
    | PTyp of typ
    | STyp of svar_class * dctx

  and ctyp =
    | ClTyp of cltyp * dctx
    | CTyp of cid_schema option

  and ctyp_decl =                             (* Contextual Declarations        *)
    | Decl of name * ctyp * depend
    | DeclOpt of name * plicity

  and typ =                                   (* LF level                       *)
    | Atom  of Loc.t * cid_typ * spine        (* A ::= a M1 ... Mn              *)
    | PiTyp of (typ_decl * depend) * typ      (*   | Pi x:A.B                   *)
    | Sigma of typ_rec
    | TClo  of (typ * sub)                    (*   | TClo(A,s)                  *)


  (* The plicity annotation is set to `implicit when reconstructing an
     a hole (_) so that when printing, it can be reproduced correctly.
   *)
  and normal =                                (* normal terms                   *)
    | Lam  of Loc.t * name * normal           (* M ::= \x.M                     *)
    | Root of Loc.t * head * spine * plicity  (*   | h . S                      *)
    | LFHole of Loc.t * HoleId.t * HoleId.name
    | Clo  of (normal * sub)                  (*   | Clo(N,s)                   *)
    | Tuple of Loc.t * tuple

  (* TODO: Heads ought to carry their location.
     Erasure currently needs to invent / pretend that a different
     location is the correct one.
   *)
  and head =
    | BVar  of offset                         (* H ::= x                        *)
    | Const of cid_term                       (*   | c                          *)
    | MMVar of mm_var_inst                    (*   | u[t ; s]                   *)
    | MPVar of mm_var_inst                    (*   | p[t ; s]                   *)
    | MVar  of (cvar * sub)                   (*   | u[s]                       *)
    | PVar  of (offset * sub)                 (*   | p[s]                       *)
    | AnnH  of head * typ                     (*   | (H:A)                      *)
    | Proj  of head * int                     (*   | x.k | #p.k s               *)

    | FVar  of name                           (* free variable for type
                                                 reconstruction                 *)
    | FMVar of fvarsub                        (* free meta-variable for type
                                                 reconstruction                 *)
    | FPVar of fvarsub                        (* free parameter variable for type
                                                 reconstruction                 *)
    | HClo  of offset * offset * sub          (*   | HClo(x, #S[sigma])         *)
    | HMClo of offset * mm_var_inst           (*   | HMClo(x, #S[theta;sigma])  *)

  and fvarsub = name * sub
  and spine =                                 (* spine                          *)
    | Nil                                     (* S ::= Nil                      *)
    | App  of normal * spine                  (*   | M . S                      *)
    | SClo of (spine * sub)                   (*   | SClo(S,s)                  *)

  and sub =
    | Shift of offset                         (* sigma ::= ^(psi,n)             *)
    | SVar  of offset * int * sub (* BEWARE: offset and int are both ints,
                                     and in the opposite order compared to FSVar and MSVar.
                                     offset is the index into Delta and describes the SVar.
                                     This is a pain to fix *)
    | FSVar of offset * fvarsub               (*   | s[sigma]                   *)
    | Dot   of front * sub                    (*   | Ft . s                     *)
    | MSVar of offset * mm_var_inst           (*   | u[t ; s]                   *)
    | EmptySub
    | Undefs

  and front =                                 (* Fronts:                        *)
    | Head of head                            (* Ft ::= H                       *)
    | Obj  of normal                          (*    | N                         *)
    | Undef                                   (*    | _                         *)

                                              (* Contextual substitutions       *)
  and mfront =                                (* Fronts:                        *)
    | ClObj of dctx_hat * clobj
    | CObj of dctx                            (*    | Psi                       *)
    | MV   of offset                          (*    | u//u | p//p | psi/psi     *)
    | MUndef (* This shouldn't be here, we should use a different datastructure for
               partial inverse substitutions *)

  and clobj =                                 (* ContextuaL objects *)
    | MObj of normal                          (* Mft::= Psihat.N                *)
    | PObj of head                            (*    | Psihat.p[s] | Psihat.x    *)
    | SObj of sub

  and msub =                                  (* Contextual substitutions       *)
    | MShift of int                           (* theta ::= ^n                   *)
    | MDot   of mfront * msub                 (*       | MFt . theta            *)

  and cvar =                                  (* Contextual Variables           *)
    | Offset of offset                        (* Bound Variables                *)
    | Inst   of mm_var                 (* D ; Psi |- M <= A provided constraint *)

  and mm_var =
    { name : name
    ; instantiation : iterm option ref
    ; cD : mctx
    ; typ : ctyp
    ; constraints : cnstr list ref (* not really used *)
    ; depend : depend
    }

  and mm_var_inst' = mm_var * msub
  and mm_var_inst = mm_var_inst' * sub

  and iterm =
    | INorm of normal
    | IHead of head
    | ISub of sub
    | ICtx of dctx

  and tvar =
    | TInst   of typ option ref * dctx * kind * cnstr list ref

  and typ_free_var = Type of typ | TypVar of tvar

  (* unique identifiers attached to constraints, used for debugging *)
  and constrnt_id = int

  and constrnt =                                       (* Constraint                     *)
    | Queued of constrnt_id                            (* constraint ::= Queued          *)
    | Eqn of constrnt_id * mctx * dctx * iterm * iterm (*            | Delta; Psi |-(M1 == M2)  *)

  and cnstr = constrnt ref

  and dctx =                                 (* LF Context                     *)
    | Null                                   (* Psi ::= .                      *)
    | CtxVar   of ctx_var                    (* | psi                          *)
    | DDec     of dctx * typ_decl            (* | Psi, x:A   or x:block ...    *)

  and ctx_var =
    | CtxName   of name
    | CtxOffset of offset
    | CInst  of mm_var_inst'
        (* D |- Psi : schema   *)

  and sch_elem =                         (* Schema Element                 *)
    | SchElem of typ_decl ctx * typ_rec    (* Pi    x1:A1 ... xn:An.
                                            Sigma y1:B1 ... yk:Bk. B       *)
                                         (* Sigma-types not allowed in Ai  *)

  and schema =
    | Schema of sch_elem list

  and dctx_hat = ctx_var option * offset  (* Psihat ::=         *)
                                          (*        | psi       *)
                                          (*        | .         *)
                                          (*        | Psihat, x *)


  and typ_rec =    (* Sigma x1:A1 ... xn:An. B *)
    |  SigmaLast of name option * typ                        (* ... . B *)
    |  SigmaElem of name * typ * typ_rec                (* xk : Ak, ... *)

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and mctx = ctyp_decl ctx          (* Modal Context  D: CDec ctx     *)

  let map_plicity f = function
    | Root (loc, tH, tS, plicity) ->
       Root (loc, tH, tS, f plicity)
    | _ as tM -> tM

  let proj_maybe (h : head) : int option -> head = function
    | None -> h
    | Some k -> Proj (h, k)

  (** Helper for forming TClo LF types, which avoids doing so if the
      substitution is the identity.
   *)
  let tclo tA s = match s with
    | Shift 0 -> tA
    | _ -> TClo (tA, s)

  (** Forms an MMVar instantiation by attaching an LF substitution and
      a meta-substituation to the variable.
   *)
  let mm_var_inst (u : mm_var) (t : msub) (s : sub): mm_var_inst = (u, t), s

  let is_mmvar_instantiated mmvar = Maybe.is_some (mmvar.instantiation.contents)

  let rename_ctyp_decl f = function
    | Decl (x, tA, ind) -> Decl (f x, tA, ind)
    | DeclOpt (x, plicity) -> DeclOpt (f x, plicity)

  (** Embeds a head into a normal by using an empty spine.
      Very useful for constructing variables as normals.
      Note that the normal will have a ghost location, as heads don't
      carry a location.
   *)
  let head (tH : head) : normal =
    Root (Loc.ghost, tH, Nil, `explicit)

  let mvar cvar sub : head =
    MVar (cvar, sub)

  (* Hatted version of LF.Null *)
  let null_hat : dctx_hat = (None, 0)

  let rec loc_of_normal = function
    | Lam (loc, _, _) -> loc
    | Root (loc, _, _, _) -> loc
    | LFHole (loc, _, _) -> loc
    | Clo (tM, _) -> loc_of_normal tM
    | Tuple (loc, _) -> loc

  (**********************)
  (* Type Abbreviations *)
  (**********************)

  type nclo     = normal  * sub          (* Ns = [s]N                      *)
  type sclo     = spine   * sub          (* Ss = [s]S                      *)
  type tclo     = typ     * sub          (* As = [s]A                      *)
  type trec_clo = typ_rec * sub          (* [s]Arec                        *)

  type assoc = Left | Right | NoAssoc
  type fix = Prefix | Postfix | Infix
  type prag =
    | NamePrag of cid_typ
    | NotPrag
    | OpenPrag of module_id
    | DefaultAssocPrag of assoc
    | FixPrag of name * fix * int * assoc option
    | AbbrevPrag of string list * string

  (**********************)
  (* Helpers            *)
  (**********************)

  (* val blockLength : typ_rec -> int *)
  let rec blockLength = function
    | SigmaLast _ -> 1
    | SigmaElem(_x, _tA, recA) -> 1 + blockLength recA

  (* getType traverses the typ_rec from left to right;
     target is relative to the remaining suffix of the type

     getType head s_recA target j = (tA, s')

     if  Psi(head) = Sigma recA'
         and [s]recA is a suffix of recA'
     then
         Psi |- [s']tA  <= type

     CLIENTS: pass 1 for the last argument j

    (* getType head s_recA target 1 *)
    val getType : head -> trec_clo -> int -> int -> tclo
  *)
  let rec getType head s_recA target j = match (s_recA, target) with
    | ((SigmaLast (_, lastA), s), 1) ->
        (lastA, s)

    | ((SigmaElem (_x, tA, _recA), s), 1) ->
        (tA, s)

    | ((SigmaElem (_x, _tA, recA), s), target) ->
        let tPj = Proj (head, j) in
          getType head (recA, Dot (Head tPj, s)) (target - 1) (j + 1)

    | _ -> raise Not_found

  (* getIndex traverses the typ_rec from left to right;
     target is the name of the projection we're looking for

    Precondition: acc is 1 when the function is 1st called
     acc is an accumulator set to 1 when the function is called

  *)
  let rec getIndex' trec target acc =
    match trec with
    | SigmaLast(None, _) -> raise Not_found
    | SigmaLast(Some name, _) ->
       if String.compare (string_of_name name) (string_of_name target) == 0
       then acc
       else failwith "Projection Not found"
    | SigmaElem(name, _, trec') ->
       if String.compare (string_of_name name) (string_of_name target) == 0
       then acc
       else getIndex' trec' target (acc + 1)

  let getIndex trec target = getIndex' trec target 1

  let is_explicit =
    function
    | Decl(_, _, dep) ->
       begin
         match dep with
         | No -> true
         | Maybe -> false
         | Inductive -> true
       end
    | _ -> true

  let name_of_ctyp_decl (d : ctyp_decl) =
    match d with
    | Decl (n, _, _) -> n
    | DeclOpt (n, _) -> n

  (** Decides whether the given mfront is a variable,
      viz. [projection of a] pattern variable, metavariable, or
      context variable.
      Returns the offset of the variable, and optionally the
      projection offset.
   *)
  let variable_of_mfront (mf : mfront) : (offset * offset option) option =
    match mf with
    | ClObj (_, MObj (Root (_, MVar (Offset x,_), _, _)))
      | CObj (CtxVar (CtxOffset x))
      | ClObj (_ , MObj (Root (_,PVar (x,_), _, _)))
      | ClObj (_ , PObj (PVar (x,_)))  ->
       Some (x, None)

    | ClObj (_, MObj (Root (_, Proj (PVar (x, _), k ),_, _)))
      | ClObj (_, PObj (Proj (PVar (x,_), k))) ->
       Some (x, Some k)

    | _ -> None

  let get_constraint_id = function
    | Eqn (id, _, _, _, _) -> id
    | Queued id -> id

  let rec drop_spine k = function
    | tS when k = 0 -> tS
    | Nil -> Nil
    | App (_, tS') -> drop_spine (k-1) tS'
end

(* Internal Computation Syntax *)
module Comp = struct
  include Syncom.Harpoon
  include Syncom.Comp

  type kind =
    | Ctype of Loc.t
    | PiKind  of Loc.t * LF.ctyp_decl * kind

  type meta_typ = LF.ctyp

  type meta_obj = Loc.t * LF.mfront

  type meta_spine =
    | MetaNil
    | MetaApp of meta_obj * meta_spine

  type typ =
    | TypBase   of Loc.t * cid_comp_typ * meta_spine
    | TypCobase of Loc.t * cid_comp_cotyp * meta_spine
    | TypDef    of Loc.t * cid_comp_typ * meta_spine
    | TypBox of Loc.t * meta_typ
    | TypArr    of Loc.t * typ * typ
    | TypCross  of Loc.t * typ * typ
    | TypPiBox  of Loc.t * LF.ctyp_decl * typ
    | TypClo    of typ *  LF.msub
    | TypInd of typ

  let rec loc_of_typ : typ -> Loc.t = function
    | TypBase (l, _, _) | TypCobase (l, _, _) | TypDef (l, _, _)
      | TypBox (l, _) | TypArr (l, _, _) | TypCross (l, _, _)
      | TypPiBox (l, _, _) ->
       l
    | TypClo (tau, _) | TypInd tau -> loc_of_typ tau

  type ih_arg =
    | M  of meta_obj
    | V  of offset
    | E (* what is E? -je *)
    | DC
  (* ^ For arguments that not constrained in the IH call. Stands
     for don't care. *)

  type wf_tag = bool  (* indicates whether the argument is smaller *)

  type ctyp_decl =
    | CTypDecl    of name * typ * wf_tag

    (** Used during pretty-printing when going under lambdas. *)
    | CTypDeclOpt of name

  type ih_decl =
    | WfRec of name * ih_arg list * typ

  let rename_ctyp_decl f = function
    | CTypDecl (x, tau, tag) -> CTypDecl (f x, tau, tag)
    | CTypDeclOpt x -> CTypDeclOpt (f x)

  type gctx = ctyp_decl LF.ctx

  type ihctx = ih_decl LF.ctx

  and exp_chk =
    | Syn        of Loc.t * exp_syn
    | Fn         of Loc.t * name * exp_chk
    | Fun        of Loc.t * fun_branches
    | MLam       of Loc.t * name * exp_chk * plicity
    | Pair       of Loc.t * exp_chk * exp_chk
    | LetPair    of Loc.t * exp_syn * (name * name * exp_chk)
    | Let        of Loc.t * exp_syn * (name * exp_chk)
    | Box        of Loc.t * meta_obj * meta_typ (* type annotation used for pretty-printing *)
    | Case       of Loc.t * case_pragma * exp_syn * branch list
    | Impossible of Loc.t * exp_syn
    | Hole       of Loc.t * HoleId.t * HoleId.name

  and exp_syn =
    | Var       of Loc.t * offset
    | DataConst of Loc.t * cid_comp_const
    | Obs       of Loc.t * exp_chk * LF.msub * cid_comp_dest
    | Const     of Loc.t * cid_prog
    | Apply     of Loc.t * exp_syn * exp_chk
    | MApp      of Loc.t * exp_syn * meta_obj * meta_typ (* annotation for printing *)
                   * plicity
    | AnnBox    of meta_obj * meta_typ
    | PairVal   of Loc.t * exp_syn * exp_syn

  and pattern =
    | PatMetaObj of Loc.t * meta_obj
    | PatConst of Loc.t * cid_comp_const * pattern_spine
    | PatFVar   of Loc.t * name (* used only _internally_ by coverage *)
    | PatVar   of Loc.t * offset
    | PatPair  of Loc.t * pattern * pattern
    | PatAnn   of Loc.t * pattern * typ * plicity

  and pattern_spine =
    | PatNil
    | PatApp of Loc.t * pattern * pattern_spine
    | PatObs of Loc.t * cid_comp_dest * LF.msub * pattern_spine

  and branch =
    | Branch of
        Loc.t
        * LF.mctx (* branch prefix *)
        * (LF.mctx * gctx) (* branch contexts *)
        * pattern
        * LF.msub (* refinement substitution for the branch *)
        * exp_chk

  and fun_branches =
   | NilFBranch of Loc.t
   | ConsFBranch of Loc.t * (LF.mctx * gctx * pattern_spine * exp_chk) * fun_branches

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

  let option_of_total_dec_kind = function
    | `inductive o -> Some o
    | _ -> None

  (** Applies a spine of checkable terms to a synthesizable term, from
      left to right. *)
  let rec apply_many i = function
    | [] -> i
    | e :: es -> apply_many (Apply (Loc.ghost, i, e)) es

  type total_dec =
    { name : Id.name
    ; tau  : typ
    ; order: order total_dec_kind
    }

  let make_total_dec name tau order =
    { name; tau; order }

  (** Decides whether this synthesizable expression is actually an
      annotated box.
   *)
  let is_meta_obj : exp_syn -> meta_obj option =
    function
    | AnnBox (m, _)  -> Some m
    | _ -> None

  let head_of_meta_obj : meta_obj -> (LF.dctx_hat * LF.head) option =
    let open LF in
    function
    | (_, ClObj (phat, MObj (Root (_, h, _, _)))) -> Some (phat, h)
    | _ -> None

  let itermToClObj = function
    | LF.INorm n -> LF.MObj n
    | LF.IHead h -> LF.PObj h
    | LF.ISub s -> LF.SObj s
    | _ -> failwith "can't convert iterm to clobj"

  let metaObjToMFront (_loc, x) = x

  (** Finds the head of an application. Chases meta-applications and
      computation applications.
   *)
  let rec head_of_application : exp_syn -> exp_syn = function
    | Apply (_, i, _) -> head_of_application i
    | MApp (_, i, _, _, _) -> head_of_application i
    | _ as i -> i

  (** Removes all type annotations from a pattern. *)
  let rec strip_pattern : pattern -> pattern = function
    | PatPair (loc, p1, p2) ->
       PatPair (loc, strip_pattern p1, strip_pattern p2)
    | PatAnn (loc, p, _, _) -> p
    | PatConst (loc, c, pS) ->
       PatConst (loc, c, strip_pattern_spine pS)
    | p -> p (* no subpatterns *)

  and strip_pattern_spine : pattern_spine -> pattern_spine = function
    | PatNil -> PatNil
    | PatApp (loc, p, pS) ->
       PatApp (loc, strip_pattern p, strip_pattern_spine pS)

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
      | Intros of t
      | Suffices of exp_syn * int * t
      | MetaSplit of exp_syn * meta_branch_label * t
      | CompSplit of exp_syn * cid_comp_const * t
      | ContextSplit of exp_syn * context_case * t

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
      of Loc.t * proof_state
    | Command of command * proof
    | Directive of directive (* which can end proofs or split into subgoals *)

  and command =
    | By of exp_syn * name * typ
    | Unbox of exp_syn * name * LF.ctyp * unbox_modifier option
  (* ^ The stored ctyp is the type synthesized for the exp_syn, BEFORE
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
      of exp_chk
    | ImpossibleSplit
      of exp_syn
    | Suffices
      of exp_syn (* i -- the function to invoke *)
         * suffices_arg list
         (* ^ the arguments of the function *)

    | MetaSplit (* Splitting on an LF object *)
      of exp_syn (* The object to split on *)
         * typ (* The type of the object that we're splitting on *)
         * meta_branch list
    | CompSplit (* Splitting on an inductive type *)
      of exp_syn (* THe computational term to split on *)
         * typ (* The type of the object to split on *)
         * comp_branch list
    | ContextSplit (* Splitting on a context *)
      of exp_syn (* The scrutinee *)
         * typ (* The type of the scrutinee *)
         * context_branch list

  and suffices_arg = Loc.t * typ * proof

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
    Hypothetical of
      hypotheses (* the full contexts *)
      * proof (* the proof; should make sense in `hypotheses`. *)

  (** An open subgoal is a proof state together with a reference ot the
      theorem in which it occurs.
   *)
  type open_subgoal = cid_comp_const * proof_state

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
  let incomplete_proof (l : Loc.t) (s : proof_state) : proof =
    Incomplete (l, s)

  (** Smart constructor for the intros directive. *)
  let intros (h : hypotheses) (proof : proof) : proof =
    Directive (Intros (Hypothetical (h, proof)))

  let suffices (i : exp_syn) (ps : suffices_arg list) : proof =
    Directive (Suffices (i, ps))

  let proof_cons (stmt : command) (proof : proof) = Command (stmt, proof)

  let solve (t : exp_chk) : proof =
    Directive (Solve t)

  let context_split (i : exp_syn) (tau : typ) (bs : context_branch list)
      : proof =
    Directive (ContextSplit (i, tau, bs))

  let context_branch (c : context_case) (cG_p, pat) (t : LF.msub) (h : hypotheses) (p : proof)
      : context_branch =
    SplitBranch (c, (cG_p, pat), t, (Hypothetical (h, p)))

  let meta_split (m : exp_syn) (a : typ) (bs : meta_branch list)
      : proof =
    Directive (MetaSplit (m, a, bs))

  let impossible_split (i : exp_syn) : proof =
    Directive (ImpossibleSplit i)

  let meta_branch
        (c : meta_branch_label)
        (cG_p, pat)
        (t : LF.msub)
        (h : hypotheses)
        (p : proof)
      : meta_branch =
    SplitBranch (c, (cG_p, pat), t, (Hypothetical (h, p)))

  let comp_split (t : exp_syn) (tau : typ) (bs : comp_branch list)
      : proof =
    Directive (CompSplit (t, tau, bs))

  let comp_branch
        (c : cid_comp_const)
        (cG_p, pat)
        (t : LF.msub)
        (h : hypotheses)
        (d : proof)
      : comp_branch =
    SplitBranch (c, (cG_p, pat), t, (Hypothetical (h, d)))

  (** Gives a more convenient way of writing complex proofs by using list syntax. *)
  let prepend_commands (cmds : command list) (proof : proof)
      : proof =
    List.fold_right proof_cons cmds proof

  let name_of_ctyp_decl (d : ctyp_decl) =
    match d with
    | CTypDecl (name, _, _) -> name
    | CTypDeclOpt name -> name

  (** Decides whether the computational term is actually a variable
      index object.
      See `LF.variable_of_mfront`.
   *)
  let metavariable_of_exp (t : exp_syn) : (offset * offset option) option =
    match t with
    | AnnBox ((_, mf), _) -> LF.variable_of_mfront mf
    | _ -> None

  (* Decides whether the given term is a computational variable.
     Returns the offset of the variable.
   *)
  let variable_of_exp (t : exp_syn) : offset option =
    match t with
    | Var (_, k) -> Some k
    | _ -> None

  type thm =
    | Proof of proof
    | Program of exp_chk

  type env =
    | Empty
    | Cons of value * env

  (* Syntax of values, used by the operational semantics *)

  and value =
    | FnValue    of name * exp_chk * LF.msub * env
    | FunValue   of fun_branches_value
    | ThmValue   of cid_prog * thm * LF.msub * env
    | MLamValue  of name * exp_chk * LF.msub * env
    | CtxValue   of name * exp_chk * LF.msub * env
    | BoxValue   of meta_obj
    | ConstValue of cid_prog
    | DataValue  of cid_comp_const * data_spine
    | PairValue  of value * value

  (* Arguments in data spines are accumulated in reverse order, to
     allow applications of data values in constant time. *)
  and data_spine =
    | DataNil
    | DataApp of value * data_spine

  and fun_branches_value =
  | NilValBranch
  | ConsValBranch of (pattern_spine * exp_chk * LF.msub * env) * fun_branches_value
end


(* Internal Signature Syntax *)
module Sgn = struct

  (* type positivity_flag =  *)
  (*   | Noflag *)
  (*   | Positivity *)
  (*   | Stratify of Loc.t * Comp.order * name * (name option) list  *)


  type positivity_flag =
    | Nocheck
    | Positivity
    | Stratify of  Loc.t * int
    | StratifyAll of Loc.t

  type thm_decl =
    { thm_name : cid_prog
    ; thm_typ : Comp.typ
    ; thm_body : Comp.thm
    ; thm_loc : Loc.t
    }

  type decl =
    | Typ           of Loc.t * cid_typ  * LF.kind
    | Const         of Loc.t * cid_term * LF.typ
    | CompTyp       of Loc.t * name * Comp.kind  *  positivity_flag
    | CompCotyp     of Loc.t * name * Comp.kind
    | CompConst     of Loc.t * name * Comp.typ
    | CompDest      of Loc.t * name * LF.mctx * Comp.typ * Comp.typ
    | CompTypAbbrev of Loc.t * name * Comp.kind * Comp.typ
    | Schema        of cid_schema * LF.schema
    | Theorem       of thm_decl list
    | Proof         of Comp.typ * Comp.proof
    | Pragma        of LF.prag
    | Val           of Loc.t * name * Comp.typ * Comp.exp_chk * Comp.value option
    | MRecTyp       of Loc.t * decl list list
    | Module        of Loc.t * string * decl list
    | Query         of Loc.t * name option * (LF.typ  * Id.offset) * int option * int option
    | Comment       of Loc.t * string

  type sgn = decl list

end
