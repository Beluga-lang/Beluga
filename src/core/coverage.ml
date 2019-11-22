(** Coverage checker

    @author Brigitte Pientka
 *)

open Support
open Syntax.Int

module Loc = Syntax.Loc
module Types = Store.Cid.Typ
module Const = Store.Cid.Term
module S = Substitution
module U = Unify.EmptyTrail
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.NamedRenderer

let dprintf, dprint, _ = Debug.makeFunctions' (Debug.toFlags [29])
open Debug.Fmt

type error =
  | NoCover of string
  | MatchError of string
  | NothingToRefine
  | NoCoverageGoalsGenerated

exception Error of Loc.t * error

let _ =
  Error.register_printer
    begin fun (Error (loc, e)) ->
    Error.print_with_location loc
      begin fun ppf ->
      match e with
      | NoCover s ->
         Format.fprintf ppf "\n######   COVERAGE FAILURE: Case expression doesn't cover: ######\n##       %s\n##"
           s
      | MatchError s ->
         Format.fprintf ppf "\n######   COVERAGE FAILURE: Case expression doesn't cover: ######\n##       Matching fails due to %s."
           s
      | NothingToRefine ->
         Format.pp_print_string ppf "Nothing to refine"
      | NoCoverageGoalsGenerated ->
         Format.pp_print_string ppf "No coverage goals generated"
      end
    end

(**
Generating meta-variable, parameter variable and pattern variable names
*)
module NameGenerator : sig
  val new_parameter_name : string -> Id.name
  val new_bvar_name : string -> Id.name
  val new_patvar_name : unit -> Id.name

  val reset_generator : unit -> unit
end = struct
  (** suffix for meta-variable and parameter variable names,
      e.g. for Obj-no-split (MVars)
   *)
  let counter = ref 0
  let pv_counter = ref 0

  let new_name_of_scheme cnt scheme =
    cnt := !cnt + 1;
    Id.mk_name (Id.SomeString (scheme (string_of_int !cnt)))

  let new_parameter_name string =
    new_name_of_scheme counter (fun suffix -> string ^ suffix)

  let new_bvar_name string =
    new_name_of_scheme counter (fun suffix -> string ^ suffix)

  let new_patvar_name () =
    new_name_of_scheme pv_counter (fun suffix -> "v" ^ suffix)

  let reset_generator () =
    (counter := 0; pv_counter := 0)
end

(* ****************************************************************************** *)
(* Coverage problem *)
type gctx = (Id.name * Comp.typ * Comp.wf_tag) list

let lookup (cG : gctx) x =
  let _, tau, _ =
    List.find (fun (y, _, _) -> x = y) cG
  in
  tau

type problem =
  { loc : Loc.t
  ; prag : Comp.case_pragma (* indicates if % not appeared after ``case...of'' *)
  ; cD : LF.mctx
  ; cG : gctx
  ; branches : Comp.branch list
  ; ctype : Comp.typ (* type and context of scrutinee *)
  ; m_obj : Comp.meta_obj option
    (* The normal LF object begin analyzed by the case.
     This is used as the initial term to split on in
     order to avoid considering certain impossible
     branches.
     *)
  }

(* Make a coverage problem *)
let make loc prag cD branches ctype m_obj =
  { loc
  ; prag
  ; cD
  ; cG = []
  ; branches
  ; ctype
  ; m_obj
  }


(* Final Coverage Result *)
type coverage_result =
  | Success
  | Failure of string

(* ****************************************************************************** *)
(* Rigid matching algorithm : pre-matching algorithm which will generate
   candidates*)

type depend =
  | Atomic
  | Dependent

type cov_goal =
  | CovGoal of LF.dctx * LF.normal * LF.tclo (*  cPsi |- tR <= sP *)
  | CovCtx of LF.dctx
  | CovSub of LF.dctx * LF.sub * LF.cltyp
  | CovPatt of gctx * Comp.pattern * Comp.tclo

type pattern =
  | MetaPatt of LF.dctx * LF.normal * LF.tclo
  | MetaCtx of LF.dctx
  | MetaSub of LF.dctx * LF.sub * LF.cltyp
  | GenPatt of Comp.gctx * Comp.pattern * Comp.tclo

type eqn =
  | Eqn of cov_goal * pattern
  | EqnCtx of LF.dctx * LF.dctx

type split =
  | Split of cov_goal * pattern
  | SplitCtx of LF.dctx * LF.dctx
  | SplitPat of (Comp.pattern * Comp.tclo) * (Comp.pattern * Comp.tclo)

type candidate =
  | Cand of
      LF.mctx (* meta-context of pattern *)
      * Comp.gctx
      * eqn list
      * split list

type candidates = candidate list

type cov_problem =
  LF.mctx * gctx * candidates * Comp.pattern

type cov_problems = cov_problem list

type open_cov_problem =
  LF.mctx * gctx * Comp.pattern

type open_cov_problems = open_cov_problem list

let open_cov_problems = ref ([] : open_cov_problems)

let reset_open_cov_problems () = open_cov_problems := []

type solved =
  | Solved
  | NotSolvable
  | PossSolvable of candidate

type refinement_candidate =
  | TermCandidate of (LF.mctx * cov_goal * LF.msub)
  | CtxCandidate of (LF.mctx * LF.dctx * LF.msub)
(*  | PatCandidate of (LF.mctx * gctx * cov_goal * LF.msub * Comp.pattern list) *)

type refinement_cands =
  | NoCandidate
  | SomeTermCands of depend * (refinement_candidate list)
  | SomeCtxCands of refinement_candidate list
(*  | SomePatCands of refinement_candidate list *)


let rec lower cPsi sA =
  match sA with
  | LF.Atom _, _ -> (cPsi, Whnf.whnfTyp sA)
  | LF.PiTyp ((decl, _), tB), s -> lower (LF.DDec (cPsi, S.LF.decSub decl s)) (tB, S.LF.dot1 s)


let gen_str cD cPsi (LF.Atom (_, a, _) as tP) =
  let cPhi, conv_list = ConvSigma.flattenDCtx cD cPsi in
  let s_proj = ConvSigma.gen_conv_sub conv_list in
  let s_tup = ConvSigma.gen_conv_sub' conv_list in
  (* cPsi |- s_proj          : cPhi
     cPhi |- s_tup           : cPsi
     cPhi |- tQ                       where cPsi |- tP !! tQ = [s_tup]tP !! *)
  let tQ = Whnf.normTyp (tP, s_tup) in
  let ss', cPhi' = Subord.thin' cD a cPhi in
  (* cPhi  |- ss'             : cPhi' *)
  let ssi' = S.LF.invert ss' in
  (* cPhi' |- ssi             : cPhi  *)
  (* cPhi' |- [ssi]tQ                 *)
  (* cPhi  |- ss'             : cPhi'
     cPsi  |- s_proj          : cPhi
     cPsi  |- comp ss' s_proj : cPhi' *)
  let ss_proj = S.LF.comp ss' s_proj in
  (ss_proj, (cPhi', LF.tclo tQ ssi'))

let eta_expand (tH, tA) =
  let rec eta (tA, s) tS =
    match tA, s with
    | LF.Atom _, s -> LF.Root (Loc.ghost, tH, tS)
    | LF.PiTyp ((LF.TypDecl (x, tB0), _), tB), s ->
       let tM = eta (tB0, s) LF.Nil in
       LF.Lam (Loc.ghost, x, eta (tB, S.LF.dot1 s) (LF.App (tM, tS))) in
  eta (tA, S.LF.id) LF.Nil

(* etaExpandMVstr cPsi sA = tN

   cPsi  |- [s]A <= typ
   cPsi  |- ss   <= cPsi'
   cPsi' |- tN   <= [s'][s]A
 *)
let rec etaExpandMVstr cD cPsi sA =
  etaExpandMVstr' cD cPsi (Whnf.whnfTyp sA)

and etaExpandMVstr' cD cPsi =
  function
  | LF.Atom (_, a, _) as tP, s ->
     let cPhi, conv_list = ConvSigma.flattenDCtx cD cPsi in
     let s_proj = ConvSigma.gen_conv_sub conv_list in
     let s_tup = ConvSigma.gen_conv_sub' conv_list in
     (* let tQ = ConvSigma.strans_typ cD cPsi (tP, s) conv_list in *)
     let tQ = Whnf.normTyp (tP, S.LF.id) in
     (* necessary to eliminate closures *)
     let tQ = Whnf.normTyp (tQ, Substitution.LF.comp s s_tup) in
     (* cPsi |- s_proj          : cPhi
        cPhi |- s_tup           : cPsi
        cPhi |- tQ                       where cPsi |- tP !! tQ = [s_tup]tP !! *)
     let ss', cPhi' = Subord.thin' cD a cPhi in
     (* cPhi  |- ss'             : cPhi' *)
     let ssi' = S.LF.invert ss' in
     (* cPhi' |- ssi             : cPhi  *)
     (* cPhi' |- [ssi]tQ                 *)
     let u = Whnf.newMMVar None (cD, cPhi', LF.TClo (tQ, ssi')) LF.Maybe in
     (* cPhi  |- ss'             : cPhi'
        cPsi  |- s_proj          : cPhi
        cPsi  |- comp ss' s_proj : cPhi' *)
     let ss_proj = S.LF.comp ss' s_proj in
     let tM = LF.Root (Loc.ghost, LF.MMVar ((u, Whnf.m_id), ss_proj),  LF.Nil) in
     tM
  | LF.PiTyp ((LF.TypDecl (x, _) as decl, _), tB), s ->
     LF.Lam (Loc.ghost, x, etaExpandMVstr cD (LF.DDec (cPsi, S.LF.decSub decl s)) (tB, S.LF.dot1 s))

let rec compgctx_of_gctx =
  function
  | [] -> LF.Empty
  | (x, tau, flag) :: cG ->
     LF.Dec (compgctx_of_gctx cG, Comp.CTypDecl (x, tau, flag))

let rec gctx_of_compgctx =
  function
  | LF.Empty -> []
  | LF.Dec (cG, Comp.CTypDecl (x, tau, flag)) ->
     (x, tau, flag) :: gctx_of_compgctx cG

(* ****************************************************************************** *)
(** Printing for debugging

Example:

X:nat
|-  Cand ( Null , [], [ X = z     ]),
    Cand ( N:nat, [], [ X = suc N ])
 *)

module Prettycov : sig
  open Format

  val fmt_ppr_open_cov_problems : formatter -> open_cov_problems -> unit
  val fmt_ppr_open_cov_problem : formatter -> open_cov_problem -> unit
  val fmt_ppr_cov_problems : formatter -> cov_problems -> unit
  val fmt_ppr_cov_problem : formatter -> cov_problem -> unit
  val fmt_ppr_candidates : LF.mctx * Comp.gctx -> formatter -> candidates -> unit
  val fmt_ppr_candidate : LF.mctx * Comp.gctx -> formatter -> candidate -> unit
  val fmt_ppr_equations : LF.mctx -> LF.mctx -> formatter -> eqn list -> unit
  val fmt_ppr_splits : LF.mctx * Comp.gctx -> LF.mctx * Comp.gctx -> formatter -> split list -> unit
  val fmt_ppr_cov_goals : formatter -> (LF.mctx * cov_goal * LF.msub) list -> unit
  val fmt_ppr_cov_goal : LF.mctx -> formatter -> cov_goal -> unit
  val fmt_ppr_pattern : LF.mctx -> formatter -> pattern -> unit
  val fmt_ppr_mvlist : formatter -> LF.cvar list -> unit
end = struct
  let fmt_ppr_mvlist ppf (vars : LF.cvar list) : unit =
    let open Format in
    match vars with
    | [] ->
       fprintf ppf "<no mvs>"
    | _ ->
       pp_print_list ~pp_sep: Fmt.comma
         begin fun ppf ->
         function
         | LF.Offset k ->
            fprintf ppf "%d"
              k
         | _ ->
            failwith
              "[fmt_ppr_mvlist] cvar is not an offset"
         end
         ppf
         vars

  let fmt_ppr_pattern cD ppf : pattern -> unit =
    let open Format in
    function
    | MetaCtx cPsi ->
       P.fmt_ppr_lf_dctx cD P.l0 ppf cPsi
    | MetaSub (cPsi, s, LF.STyp (_, cPhi)) ->
       fprintf ppf "%a |- %a : %a"
         (P.fmt_ppr_lf_dctx cD P.l0) cPsi
         (P.fmt_ppr_lf_sub cD cPsi P.l0) s
         (P.fmt_ppr_lf_dctx cD P.l0) cPhi
    | MetaPatt (cPsi, tR, sA) ->
       fprintf ppf "%a |- %a : %a"
         (P.fmt_ppr_lf_dctx cD P.l0) cPsi
         (P.fmt_ppr_lf_normal cD cPsi P.l0) tR
         (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA)

  let fmt_ppr_cov_goal cD ppf : cov_goal -> unit =
    let open Format in
    function
    | CovCtx cPsi -> P.fmt_ppr_lf_dctx cD P.l0 ppf cPsi
    | CovSub (cPsi, s, LF.STyp (_, cPhi)) ->
       fprintf ppf "%a |- %a : %a"
         (P.fmt_ppr_lf_dctx cD P.l0) cPsi
         (P.fmt_ppr_lf_sub cD cPsi P.l0) s
         (P.fmt_ppr_lf_dctx cD P.l0) cPhi
    | CovGoal (cPsi, tR, sA) ->
       fprintf ppf "%a |- %a : %a"
         (P.fmt_ppr_lf_dctx cD P.l0) cPsi
         (P.fmt_ppr_lf_normal cD cPsi P.l0) tR
         (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA)
    | CovPatt (cG, patt, ttau) ->
       fprintf ppf "%a : %a"
         (P.fmt_ppr_cmp_pattern cD (compgctx_of_gctx cG) P.l0) patt
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)

  let fmt_ppr_cov_goals ppf (goals : (LF.mctx * cov_goal * LF.msub) list) : unit =
    let open Format in
    let f ppf (cD, cg, _) =
      fprintf ppf "-- %a |- %a"
        (P.fmt_ppr_lf_mctx P.l0) cD
        (fmt_ppr_cov_goal cD) cg
    in
    pp_print_list ~pp_sep: pp_print_cut f ppf goals

  let fmt_ppr_split (cD, cG) (cD_p, cG_p) ppf : split -> unit =
    let open Format in
    function
    | Split (cg, patt) ->
       fprintf ppf "%a == %a"
         (fmt_ppr_cov_goal cD) cg
         (fmt_ppr_pattern cD_p) patt
    | SplitCtx (cPsi, cPhi) ->
       fprintf ppf "%a == %a"
         (P.fmt_ppr_lf_dctx cD P.l0) cPsi
         (P.fmt_ppr_lf_dctx cD_p P.l0) cPhi
    | SplitPat ((patt, ttau), (patt', ttau')) ->
       fprintf ppf "%a : %a == %a : %a"
         (P.fmt_ppr_cmp_pattern cD cG P.l0) patt
         (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
         (P.fmt_ppr_cmp_pattern cD_p cG_p P.l0) patt'
         (P.fmt_ppr_cmp_typ cD_p P.l0) (Whnf.cnormCTyp ttau')

  let fmt_ppr_splits c c' ppf : split list -> unit =
    let open Format in
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut (fmt_ppr_split c c'))

  let fmt_ppr_equation cD cD_p ppf : eqn -> unit =
    let open Format in
    function
    | Eqn (cg, patt) ->
       fprintf ppf "%a == %a"
         (fmt_ppr_cov_goal cD) cg
         (fmt_ppr_pattern cD_p) patt
    | _ ->
       failwith "[fmt_ppr_eqn] not an equation"

  let fmt_ppr_equations cD cD_p ppf : eqn list -> unit =
    let open Format in
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut (fmt_ppr_equation cD cD_p))

  let fmt_ppr_candidate (cD, cG) ppf : candidate -> unit =
    let open Format in
    function
    | Cand (cD_p, cG_p, eqns, splits) ->
       fprintf ppf "@[<v>@[%a@]; @[%a@]@,@[%a@]; @[%a@] |-@,MATCHES {@,%a@,}@,SPLITS {@,%a@,}@]"
         (P.fmt_ppr_lf_mctx P.l0) cD
         (P.fmt_ppr_cmp_gctx cD P.l0) cG
         (P.fmt_ppr_lf_mctx P.l0) cD_p
         (P.fmt_ppr_cmp_gctx cD_p P.l0) cG_p
         (fmt_ppr_equations cD cD_p) eqns
         (fmt_ppr_splits (cD, cG) (cD_p, cG_p)) splits

  let fmt_ppr_candidates (cD, cG) ppf (candidates : candidate list) : unit =
    let open Format in
    match candidates with
    | [] ->
       fprintf ppf "<no candidates>"
    | _ ->
       let f ppf i c =
         fprintf ppf "@[<v 2>CANDIDATE %d:@,%a@]"
           (i + 1)
           (fmt_ppr_candidate (cD, cG)) c
       in
       fprintf ppf "@[<v>";
       List.iteri (f ppf) candidates;
       fprintf ppf "@]"

  let fmt_ppr_cov_problem ppf ((cD, cG, candidates, patt) : cov_problem) : unit =
    let cG' = compgctx_of_gctx cG in
    let open Format in
    fprintf ppf "#### @[<v>COVERAGE GOAL:@,\
                 cD = @[%a@]@,\
                 @[%a@] |- @[%a@]@,\
                 is possibly covered by:@,\
                 @[%a@]@]"
      (P.fmt_ppr_lf_mctx P.l0) cD
      (P.fmt_ppr_cmp_gctx cD P.l0) cG'
      (P.fmt_ppr_cmp_pattern cD cG' P.l0) patt
      (fmt_ppr_candidates (cD, cG')) candidates

  let fmt_ppr_cov_problems ppf : cov_problems -> unit =
    let open Format in
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut fmt_ppr_cov_problem)

  let fmt_ppr_open_cov_problem ppf ((cD, cG, patt) : open_cov_problem) : unit =
    let open Format in
    fprintf ppf "@[<2>@[@[%a@] ;@ @[%a@]@] |-@ @[%a@]@]"
      (P.fmt_ppr_lf_mctx P.l0) cD
      (P.fmt_ppr_cmp_gctx cD P.l0) (compgctx_of_gctx cG)
      (P.fmt_ppr_cmp_pattern cD (compgctx_of_gctx cG) P.l0) patt

  let fmt_ppr_open_cov_problems ppf (gs : open_cov_problems) : unit =
    let open Format in
    let f ppf i (cD, cG, patt) =
      fprintf ppf "@[(%d)@ @[%a@]@]@,"
        (i + 1)
        fmt_ppr_open_cov_problem (cD, cG, patt)
    in
    fprintf ppf "@[<v>";
    List.iteri (f ppf) gs;
    fprintf ppf "@]"
end

(* ****************************************************************************** *)

module TrivialCoverageChecker : sig
  val check : LF.ctyp_decl LF.ctx -> gctx -> Comp.typ -> Comp.branch list -> bool
end = struct
  let check_meta_obj cD (_, m0) mT =
    match m0, mT with
    | LF.CObj (LF.CtxVar _), _ -> true
    | LF.ClObj (_, clObj), LF.ClTyp (clTyp, cPsi) ->
       begin match clObj, clTyp with
       | LF.MObj (LF.Root (_, LF.MVar (LF.Offset u, s), LF.Nil)), LF.MTyp _ ->
          let _, _, cPsi' = Whnf.mctxMDec cD u in
          Whnf.convSub s S.LF.id && Whnf.convDCtx cPsi' cPsi
       | LF.PObj (LF.PVar (p, s)), LF.PTyp _ ->
          let _, _, cPsi' = Whnf.mctxPDec cD p in
          Whnf.convSub s S.LF.id && Whnf.convDCtx cPsi' cPsi
       | LF.SObj (LF.SVar (0, 0, s)), LF.STyp _ ->
          Whnf.convSub s S.LF.id
       | _ -> false
       end
    | _ -> false

  let is_id cD t cD' =
    let l = Context.length cD in
    let rec id t cD0 =
      match t with
      | LF.MShift n -> n = l
      | LF.MDot (m, t) ->
         begin match m, cD0 with
         | LF.MV _, LF.Dec (cD0, _)
           | LF.CObj (LF.CtxVar _), LF.Dec (cD0, _) ->
            id t cD0
         | LF.ClObj _, LF.Dec (cD0, LF.Decl (_, tU, _)) ->
            check_meta_obj
              cD
              (Loc.ghost, m)
              (Whnf.cnormMetaTyp (tU, t))
            && id t cD0
         | _ -> false
         end
    in
    id t cD'

  let check_branch cD cG tau_sc b =
    dprintf
      begin fun p ->
      let cG = Context.of_list_map cG (fun (x, y, z) -> Comp.CTypDecl (x, y, z)) in
      p.fmt "@[<v>[trivial check_branch] @[<v>check branch %a@]@]"
        (P.fmt_ppr_cmp_branch cD cG P.l0) b
      end;
    match b with
    | Comp.Branch (_, cD0, _, patt, t, _) ->
       begin match patt, tau_sc with
       | Comp.PatVar _, _ ->
          is_id cD0 t cD
       | Comp.PatMetaObj (_, m0), Comp.TypBox (_, mT) ->
          check_meta_obj cD0 m0 (Whnf.cnormMetaTyp (mT, t)) && is_id cD0 t cD
       | _ -> false
       end

  let check cD cG tau_sc =
    List.exists (check_branch cD cG tau_sc)
end

type result =
  | Yes of LF.tclo * LF.tclo
  | Inst
  | SplitCand
  | No
(*    | CtxSplitCand of (eqn list * split list) *)

(* pre_match_head (cPsi, tH) (cPsi', tH') = result

   - Yes (tA, tA') if tH is an instance of tH' and tH:tA and tH':tA'
   - No            if tH can never be an instance of tH'
   - Inst          if tH is claimed to be an instance of tH',
                   i.e. tH's structure matches the structure of a
                   subterm in tH', but there might be HO constraints
   - SplitCand     if tH can maybe be an instance of tH' after we split
                   tH further; this happens if tH is more general (i.e.
                   it is a meta-variable or a parameter variable) than tH'
 *)
let rec pre_match_head cD cD' (cPsi, tH) (cPsi', tH') =
  match tH, tH' with
  (*
  | LF.MVar (LF.Offset u, s), LF.MVar (LF.Offset v, s') ->
     if Whnf.convHead (tH, idSub) (tH', idSub)
     then
       let _, tA, _ = Whnf.mctxMDec cD u in
       Yes ((tA, s), (tA, s'))
     else
       Inst
   *)
  (*
   ** How to check that two terms M and N with mvars that fall outside
   the pattern fragment are identical? -
   **
   - Convertibility doesn't quite apply because cD and cD' might be different
   - Matching will fail due to unresolved constraints
   *)
  | _, LF.MVar _ -> Inst
  | LF.BVar k, LF.BVar k' ->
     if k = k'
     then
       let LF.TypDecl (_, tA) = Context.ctxDec cPsi k in
       let LF.TypDecl (_, tA') = Context.ctxDec cPsi' k' in
       Yes ((tA, S.LF.id), (tA', S.LF.id))
     else No
  | LF.PVar _, LF.BVar k -> SplitCand
  | LF.BVar k, LF.PVar _ -> Inst
  (*
  | LF.PVar (k, s), LF.PVar (n, s') ->
     if k = n
     then
       (match s, s' with
        | LF.Shift l, LF.Shift l' ->
           if l = l' then
             Inst (* could return Yes *)
           else (if l < l' then SplitCand else No)
        | LF.Shift l, LF.EmptySub -> No
          (* this would mean the written pattern is not inhabited *)
        | _, _ -> Inst
       )
     else No
   *)
  | LF.PVar (p, s), LF.PVar (q, s') ->
     let ms = Ctxsub.mctxToMMSub cD cD' in
     let cPsi_p' = Whnf.cnormDCtx (cPsi', ms) in
     let tH' = Whnf.cnormHead (tH', ms) in
     dprintf
       begin fun p ->
       p.fmt "[pre_match_head] @[<v>pvar - case@,@[@[%a@]@ |- @[%a@]@]@,@[@[%a@]@ |- @[%a@]@]@] "
         (P.fmt_ppr_lf_dctx cD P.l0) cPsi
         (P.fmt_ppr_lf_head cD cPsi P.l0) tH
         (P.fmt_ppr_lf_dctx cD' P.l0) cPsi'
         (P.fmt_ppr_lf_head cD' cPsi' P.l0) tH'
       end;

     let mC, sC = pre_match_dctx cD cD' cPsi cPsi' [] [] in
     dprintf
       begin fun p ->
       p.fmt "[pre_match_head] @[<v>pre_match_dctx yields@,sC = @[%a@]@,mC = @[%a@]@]"
         (Prettycov.fmt_ppr_splits (cD, LF.Empty) (cD', LF.Empty)) sC
         (Prettycov.fmt_ppr_equations cD cD') mC
       end;
     begin try
         U.unifyDCtx cD cPsi cPsi_p';
         U.unifyH cD (Context.dctxToHat cPsi_p') tH tH';
         let _, tA, _ = Whnf.mctxPDec cD p in
         let _, tA', _ = Whnf.mctxPDec cD' q in
         Yes ((tA, S.LF.id), (tA', S.LF.id))
       with
       | _ ->
          dprint
            begin fun _ ->
            "[pre_match_head] pvar - SplitCand"
            end;
          SplitCand
            (* CtxSplitCand (pre_match_dctx cD cD_p cPsi cPsi_p [] []) *)
     end
  | LF.Const c, LF.Const c' ->
     if c = c'
     then
       let tA = (Const.get c).Const.typ in
       Yes ((tA, S.LF.id), (tA, S.LF.id))
     else No

  | LF.Const c, LF.PVar _ -> No
  | LF.Const c, LF.BVar _ -> No
  | LF.Const c, LF.Proj _ -> No

  | LF.Proj (LF.BVar k, j), LF.Proj (LF.BVar k', j') ->
     if k = k' && j = j'
     then
       let LF.TypDecl (_, tA) = Context.ctxDec cPsi k in
       let LF.TypDecl (_, tA') = Context.ctxDec cPsi' k' in
       Yes ((tA, S.LF.id), (tA', S.LF.id))
     else No
  | LF.Proj (LF.PVar _, j), LF.Proj (LF.BVar k', j') ->
     if j == j'
     then SplitCand
     else No
  | LF.Proj (LF.BVar k, j), LF.Proj (LF.PVar _, j') ->
     if j == j'
     then Inst
     else No
  | LF.Proj (LF.PVar _, j), LF.Proj (LF.PVar _, j') ->
     if j == j'
     then Inst
     else No

  | LF.MVar _, _ -> SplitCand

  | LF.PVar _, LF.Const _ -> No
  | LF.Proj _, LF.Const _ -> No
  | LF.PVar _, LF.Proj (LF.BVar _, _) -> No (* Inst *)
  | LF.PVar _, LF.Proj (LF.PVar _, _) -> No (* Inst *)
  | LF.Proj _, LF.BVar _ -> No
  | LF.Proj _, LF.PVar _ -> No
  | _ -> No

(* pre_match (cPsi, tM, tA) (cPsi', tM', tA') matchCands splitCands = (matchCands', splitCands')

   if cD; cPsi |- tM  <= tA
      cD; cPsi |- tM' <= tA
   then
      matchCands' is an extension of matchCands containing
       atomic equations which need to be solved for tM to be an instance of tM'

      splitCands' is an extension of splitCands containing
       atomic splitting candidates, i.e. where tM and tM' currently disagree


   Effect: pre_match may raise an exception MatchError, if tM can never be an
   instance of tM' and splitting is not able to make any progress.
 *)
and pre_match cD cD_p covGoal patt matchCands splitCands =
  let CovGoal (cPsi, tM, sA) = covGoal in
  let MetaPatt (cPhi, tN, sA') = patt in
  match tM, tN with
  | LF.Lam (_, x, tM), LF.Lam (_, _, tN) ->
     let LF.PiTyp ((tdecl, _), tB), s = Whnf.whnfTyp sA in
     let LF.PiTyp ((tdecl', _), tB'), s' = Whnf.whnfTyp sA' in
     let covGoal' =
       CovGoal
         ( LF.DDec (cPsi, S.LF.decSub tdecl s)
         , tM, (tB, S.LF.dot1 s)
         )
     in
     let patt' =
       MetaPatt
         ( LF.DDec (cPhi, S.LF.decSub tdecl' s')
         , tN, (tB', S.LF.dot1 s')
         )
     in
     pre_match cD cD_p covGoal' patt' matchCands splitCands

  | LF.Root (_, tH, tS), LF.Root (loc, tH', tS') ->
     begin match pre_match_head cD cD_p (cPsi, tH) (cPhi, tH') with
     | Yes (sA, sA') ->
        pre_match_spine
          cD cD_p
          (cPsi, tS, sA)
          (cPhi, tS', sA')
          matchCands splitCands

     | No ->
        let s =
          let open Format in
          fprintf str_formatter "Head mismatch @[<v>@[%a@]@ =/=@ @[%a@]@]"
            (P.fmt_ppr_lf_head cD cPsi P.l0) tH
            (P.fmt_ppr_lf_head cD_p cPhi P.l0) tH';
          flush_str_formatter ()
        in
        raise (Error (loc, MatchError (s)))

     | Inst ->
        dprintf
          begin fun p ->
          p.fmt "[pre_match] Eqn : @[<hv>%a@ == %a@]"
            (Prettycov.fmt_ppr_cov_goal cD) covGoal
            (Prettycov.fmt_ppr_pattern cD_p) patt
          end;
        (Eqn (covGoal, patt) :: matchCands, splitCands)

     | SplitCand -> (matchCands, Split (covGoal, patt)::splitCands)
     (*
     | CtxSplitCand (mC, sC) -> (mC @ matchCands, sC @ splitCands)
      *)
     end

and pre_match_spine cD cD_p (cPsi, tS, sA) (cPsi', tS', sA') matchCands splitCands =
  match tS, tS' with
  | LF.Nil, LF.Nil -> (matchCands, splitCands)
  | LF.App (tM, tS), LF.App (tM', tS') ->
     let LF.PiTyp ((LF.TypDecl (_, tB1), _), tB2), s = Whnf.whnfTyp sA in
     let LF.PiTyp ((LF.TypDecl (_, tC1), _), tC2), s' = Whnf.whnfTyp sA' in
     let covGoal1 = CovGoal (cPsi, tM, (tB1,s)) in
     let patt1 = MetaPatt (cPsi', tM', (tC1,s')) in
     let sB2' = (tB2, LF.Dot (LF.Obj (tM), s)) in
     let sC2' = (tC2, LF.Dot (LF.Obj (tM'), s')) in
     let matchCands', splitCands' =
       pre_match cD cD_p covGoal1 patt1 matchCands splitCands
     in
     pre_match_spine cD cD_p (cPsi, tS, sB2')
       (cPsi', tS', sC2') matchCands' splitCands'

and pre_match_sub cD cD_p covGoal patt matchCands splitCands =
  let CovSub (cPsi0, s0, (LF.STyp (r0, cPhi0) as sT0)) = covGoal in
  let MetaSub (cPsi1, s1, (LF.STyp (r1, cPhi1) as sT1)) = patt in
  match (s0, cPhi0), (s1, cPhi1) with
  | (LF.EmptySub, LF.Null), (LF.EmptySub, LF.Null) -> (matchCands, splitCands)
  | (LF.Shift k, _), (LF.Shift n, _) ->
     if n = k
     then (matchCands, splitCands)
     else
       Error.violation "[coverage] [pre_match_sub] substitution mismatch"
  (*
          raise (Error (Loc.ghost,
                    MatchError ("Substitution mismatch " ^ P.subToString cD cPsi0 s0 ^ " =/= " ^ P.subToString cD_p cPsi0 s1 ^ "\n")))
   *)

  | (LF.SVar _, cPhi0), (LF.Shift 0, cPhi1) ->
     (* SplitCand *)
     let covGoal = CovSub (cPsi0, s0, LF.STyp (r0, cPhi0)) in
     let patt = MetaSub (cPsi1, s1, LF.STyp (r1, cPhi1)) in
     (matchCands, Split (covGoal, patt) :: splitCands)

  | (LF.Shift 0, cPhi0), (LF.SVar _, cPhi1) ->
     let covGoal = CovSub (cPsi0, s0, sT0) in
     let patt = MetaSub (cPsi1, s1, sT1) in
     (Eqn (covGoal, patt) :: matchCands, splitCands)

  | (LF.SVar _, _), (LF.SVar _, _) ->
     let covGoal = CovSub (cPsi0, s0, LF.STyp (r0, cPhi0)) in
     let patt = MetaSub (cPsi1, s1, LF.STyp (r1, cPhi1)) in
     (Eqn (covGoal, patt) :: matchCands, splitCands)


  | (LF.Dot (f0, s0), LF.DDec (cPhi0, tdecl0)), (LF.Dot (f1, s1), LF.DDec (cPhi1, tdecl1)) ->
     let LF.TypDecl (_, tA0) = tdecl0 in
     let LF.TypDecl (_, tA1) = tdecl1 in
     let covGoal = CovSub (cPsi0, s0, LF.STyp (r0, cPhi0)) in
     let patt = MetaSub (cPsi1, s1, LF.STyp (r1, cPhi1)) in
     let matchCands', splitCands' = pre_match_front cD cD_p (cPhi0, f0, tA0) (cPhi1, f1, tA1) matchCands splitCands in
     pre_match_sub cD cD_p covGoal patt matchCands' splitCands'

  | (LF.Shift n, _), (LF.Dot (LF.Head LF.BVar _, _), _) ->
     let s0 = LF.Dot (LF.Head (LF.BVar (n+1)), LF.Shift (n+1)) in
     let covGoal = CovSub (cPsi0, s0, LF.STyp (r0, cPhi0)) in
     pre_match_sub cD cD_p covGoal patt matchCands splitCands

  | (LF.Dot (LF.Head LF.BVar _, _), _), (LF.Shift n, _) ->
     let s1 = LF.Dot (LF.Head (LF.BVar (n+1)), LF.Shift (n+1)) in
     let patt = MetaSub (cPsi1, s1, LF.STyp (r1, cPhi1)) in
     pre_match_sub cD cD_p covGoal patt matchCands splitCands


  | (LF.EmptySub, _), _ -> (matchCands, splitCands)
  | _, (LF.EmptySub, _) -> (matchCands, splitCands)


  | (LF.SVar _, _), _ ->  (matchCands, Split (covGoal, patt) :: splitCands)

  | _, (LF.SVar _, _) -> (Eqn (covGoal, patt) :: matchCands, splitCands)

and pre_match_front cD cD_p (cPhi0, f0, tA0) (cPhi1, f1, tA1) matchCands splitCands =
  match f0, f1 with
  | LF.Head h0, LF.Head h1 ->
     let tM0 = eta_expand (h0, tA0) in
     let tM1 = eta_expand (h1, tA1) in
     let covGoal = CovGoal (cPhi0, tM0, (tA0, S.LF.id)) in
     let patt = MetaPatt (cPhi1, tM1, (tA1, S.LF.id)) in
     pre_match cD cD_p covGoal patt matchCands splitCands

  | LF.Obj tM0, LF.Obj tM1 ->
     let covGoal = CovGoal (cPhi0, tM0, (tA0, S.LF.id)) in
     let patt = MetaPatt (cPhi1, tM1, (tA1, S.LF.id)) in
     pre_match cD cD_p covGoal patt matchCands splitCands


and pre_match_typ_spine cD cD_p (cPsi, tS1, sK1) (cPsi', tS2, sK2) matchCands splitCands =
  match (tS1,sK1), (tS2, sK2) with
  | (LF.Nil, (LF.Typ, _)), (LF.Nil, (LF.Typ, _)) ->
     (matchCands, splitCands)
  | (LF.App (tM, tS), sK), (LF.App (tM', tS'), sK')->
     let LF.PiKind ((LF.TypDecl (_, tB), _), tK1), s = sK in
     let LF.PiKind ((LF.TypDecl (_, tC), _), tK2), s' = sK' in
     let covGoal1 = CovGoal (cPsi, tM, (tB, s)) in
     let patt1 = MetaPatt (cPsi', tM', (tC, s')) in
     let sK1' = (tK1, LF.Dot (LF.Obj tM, s)) in
     let sK2' = (tK2, LF.Dot (LF.Obj tM', s')) in
     let matchCands', splitCands' = pre_match cD cD_p covGoal1 patt1 matchCands splitCands in
     pre_match_typ_spine cD cD_p (cPsi, tS, sK1')
       (cPsi', tS', sK2') matchCands' splitCands'

and pre_match_typ cD cD_p (cPsi, sA) (cPhi, sB) matchCands splitCands =
  dprintf
    begin fun p ->
    p.fmt "[pre_match_typ] @[<v>sA = %a@,sB = %a@]"
      (P.fmt_ppr_lf_typ cD cPsi P.l0) (Whnf.normTyp sA)
      (P.fmt_ppr_lf_typ cD_p cPhi P.l0) (Whnf.normTyp sB)
    end;
  match Whnf.whnfTyp sA, Whnf.whnfTyp sB with
  | (LF.Atom (_, a, tS1), s1), (LF.Atom (loc, b, tS2), s2) ->
     let tK1 = (Types.get a).Types.kind in
     let tK2 = (Types.get b).Types.kind in
     let tS1' = Whnf.normSpine (tS1, s1) in
     let tS2' = Whnf.normSpine (tS2, s2) in
     if a = b then
       pre_match_typ_spine cD cD_p (cPsi, tS1', (tK1, S.LF.id)) (cPhi, tS2', (tK2, S.LF.id))
         matchCands splitCands
     else raise (Error (loc, MatchError "Type Head mismatch"))
  | (LF.PiTyp ((LF.TypDecl (x, tA1), _), tA2), s1),  (LF.PiTyp ((LF.TypDecl (y, tB1), _), tB2), s2) ->
     let matchCands', splitCands' = pre_match_typ cD cD_p (cPsi, (tA1, s1)) (cPhi, (tB1, s2))
                                        matchCands splitCands
     in
     pre_match_typ cD cD_p (LF.DDec (cPsi, LF.TypDecl (x, LF.TClo (tA1, s1))), (tA2, S.LF.dot1 s1))
       (LF.DDec (cPhi, LF.TypDecl (y, LF.TClo (tB1, s1))), (tB2, S.LF.dot1 s2))
       matchCands' splitCands'

  | (LF.Sigma trec1, s1), (LF.Sigma trec2, s2) ->
     pre_match_trec cD cD_p cPsi cPhi (trec1, s1) (trec2, s2)
       matchCands splitCands


and pre_match_trec cD cD_p cPsi cPhi srec1 srec2 matchCands splitCands =
  match srec1, srec2 with
  | (LF.SigmaLast (_, tA1), s1), (LF.SigmaLast (_, tA2), s2) ->
     pre_match_typ cD cD_p (cPsi, (tA1, s1)) (cPhi, (tA2, s2)) matchCands splitCands
  | (LF.SigmaElem (x1, tA1, trec1), s1), (LF.SigmaElem (x2, tA2, trec2), s2) ->
     let mC, sC =
       pre_match_typ
         cD cD_p
         (cPsi, (tA1, s1))
         (cPhi, (tA2, s2))
         matchCands splitCands
     in
     pre_match_trec
       cD cD_p
       (LF.DDec (cPsi, LF.TypDecl (x1, LF.TClo (tA1,s1)))) (LF.DDec (cPhi, LF.TypDecl (x2, LF.TClo (tA2,s2))))
       (trec1, S.LF.dot1 s1) (trec2, S.LF.dot1 s2)
       mC sC


and pre_match_dctx cD cD_p cPsi cPhi_patt matchCands splitCands =
  dprintf
    begin fun p ->
    let f cD = P.fmt_ppr_lf_dctx cD P.l0 in
    p.fmt "[pre_match_dctx] @[<v>cPsi = %a@,cPhi = %a@]"
      (f cD) cPsi
      (f cD_p) cPhi_patt
    end;
  match cPsi, cPhi_patt with
  | LF.Null, LF.Null ->
     (matchCands, splitCands)
  (*
  | cPsi, LF.CtxVar _ -> ((EqnCtx (cPsi, cPhi_patt) :: matchCands), splitCands)
   *)
  | cPsi, LF.CtxVar _ ->
     (matchCands, splitCands) (* will be unified as part of the contextual obj *)
  | LF.CtxVar _, cPhi_patt ->
     (matchCands, SplitCtx (cPsi, cPhi_patt) :: splitCands)
  | LF.DDec (cPsi', LF.TypDecl (_, tA)), LF.DDec (cPhi', LF.TypDecl (_, tB)) ->
     let mC, sC = pre_match_dctx cD cD_p cPsi' cPhi' matchCands splitCands in
     pre_match_typ cD cD_p (cPsi', (tA, S.LF.id)) (cPhi', (tB, S.LF.id)) mC sC
  | _ ->
     raise (Error (Loc.ghost, MatchError "Ctx mismatch"))

let match_metaobj cD cD_p ((loc, mO), mt) ((loc', mO_p), mtp) mC sC =
  match (mO, mt), (mO_p, mtp) with
  | (LF.CObj cPsi, _), (LF.CObj cPsi', _) ->
     pre_match_dctx cD cD_p cPsi cPsi' mC sC
  | (LF.ClObj (_, LF.MObj tR), LF.ClTyp (LF.MTyp tA, cPsi)),
    (LF.ClObj (_, LF.MObj tR'), LF.ClTyp (LF.MTyp tA', cPsi')) ->
     let mC0, sC0 = pre_match_dctx cD cD_p cPsi cPsi' mC sC in
     let mC1, sC1 = pre_match_typ cD cD_p (cPsi, (tA, S.LF.id)) (cPsi', (tA', S.LF.id)) mC0 sC0 in
     let covGoal = CovGoal (cPsi, tR, (tA, S.LF.id)) in
     let pat = MetaPatt (cPsi', tR', (tA', S.LF.id)) in
     dprintf
       begin fun p ->
       let f = P.fmt_ppr_lf_normal cD_p cPsi P.l0 in
       p.fmt "[match_metaobj] MObj of MTyp: @[<v>tR = @[%a@]@,tR' = @[%a@]@]"
         f tR f tR'
       end;
     pre_match cD cD_p covGoal pat mC1 sC1
  | (LF.ClObj (_, LF.MObj tR), LF.ClTyp (LF.PTyp tA, cPsi)),
    (LF.ClObj (_, LF.MObj tR'), LF.ClTyp (LF.PTyp tA', cPsi')) ->
     let mC0, sC0 = pre_match_dctx cD cD_p cPsi cPsi' mC sC in
     let mC1, sC1 = pre_match_typ cD cD_p (cPsi, (tA, S.LF.id)) (cPsi', (tA', S.LF.id)) mC0 sC0 in
     let covGoal = CovGoal (cPsi, tR, (tA, S.LF.id)) in
     let pat = MetaPatt (cPsi', tR', (tA', S.LF.id)) in
     pre_match cD cD_p covGoal pat mC1 sC1
  | (LF.ClObj (_, LF.PObj tH), LF.ClTyp (LF.PTyp tA, cPsi)),
    (LF.ClObj (_, LF.PObj tH'), LF.ClTyp (LF.PTyp tA', cPsi')) ->
     let mC0, sC0 = pre_match_dctx cD cD_p cPsi cPsi' mC sC in
     let mC1, sC1 = pre_match_typ cD cD_p (cPsi, (tA, S.LF.id)) (cPsi', (tA', S.LF.id)) mC0 sC0 in
     let covGoal = CovGoal (cPsi, LF.Root (Loc.ghost, tH, LF.Nil), (tA, S.LF.id)) in
     let pat = MetaPatt (cPsi', LF.Root (Loc.ghost, tH', LF.Nil), (tA', S.LF.id)) in
     pre_match cD cD_p covGoal pat mC1 sC1
  | (LF.ClObj (_, LF.SObj s), LF.ClTyp (sT, cPsi)),
    (LF.ClObj (_, LF.SObj s'), LF.ClTyp (sT', cPsi')) ->
     let mC1, sC1 = pre_match_dctx cD cD_p cPsi cPsi' mC sC in
     let covGoal = CovSub (cPsi, s, sT) in
     let pat = MetaSub (cPsi', s', sT') in
     pre_match_sub cD cD_p covGoal pat mC1 sC1
  | _, _ ->
     let s =
       let open Format in
       let mobj cD = P.fmt_ppr_cmp_meta_obj cD P.l0 in
       let mtyp cD = P.fmt_ppr_cmp_meta_typ cD P.l0 in
       fprintf str_formatter "[coverage] @[<v>[match_metaobj] @,\
                              Found covgoal @[%a@ : %a@]@,
                              Pattern: @[%a@ : %a@]"
         (mobj cD) (loc, mO)
         (mtyp cD) mt
         (mobj cD_p) (loc', mO_p)
         (mtyp cD_p) mtp;
       flush_str_formatter ()
     in
     Error.violation s
(*
     raise (Error (Loc.ghost, MatchError ("Meta Obj Mismatch \n" ^ "Found CovGoal: " ^ P.metaObjToString cD (loc, mO) ^ " : " ^ P.metaTypToString cD mt  ^ "\nPattern: " ^ P.metaObjToString cD_p (loc', mO_p) ^ " : " ^ P.metaTypToString cD_p mtp ^ "\n")))
 *)

let rec match_pattern (cD, cG) (cD_p, cG_p) (pat, ttau) (pat_p, ttau_p) mC sC =
  match (pat, ttau), (pat_p, ttau_p) with
  | (Comp.PatMetaObj (loc, mO), (Comp.TypBox (_, mT), t)),
    (Comp.PatMetaObj (_, mO'), (Comp.TypBox (_, mT'), t')) ->
     let mT0  = Whnf.cnormMTyp (mT, t) in
     let mT0' = Whnf.cnormMTyp (mT', t') in
     match_metaobj cD cD_p (mO, mT0) (mO', mT0') mC sC

  | (Comp.PatConst (_, c, pS), (Comp.TypBase _, t)),
    (Comp.PatConst (loc, c', pS'), (Comp.TypBase _, t')) ->
     if c = c' then
       let ttau = ((Store.Cid.CompConst.get c).Store.Cid.CompConst.typ, Whnf.m_id) in
       let ttau' = ((Store.Cid.CompConst.get c').Store.Cid.CompConst.typ, Whnf.m_id) in
       match_spines (cD, cG) (cD_p, cG_p) (pS, ttau) (pS', ttau') mC sC
     else
       raise (Error (loc, MatchError "Const mismatch"))

  (* success *)
  | (pat, ttau),
    (Comp.PatVar (_, v), ttau') ->
     (mC, sC)

  (* splitting candidate *)
  | (Comp.PatFVar (_, v), ttau),
    (pat_p, ttau') ->
     (mC, SplitPat ((pat, ttau), (pat_p, ttau')) :: sC)

  | (Comp.PatPair (_, pat1, pat2), (Comp.TypCross (tau1, tau2), t)),
    (Comp.PatPair (_, pat1', pat2'), (Comp.TypCross (tau1', tau2'), t')) ->
     let mC1, sC1 =
       match_pattern (cD, cG) (cD_p, cG_p)
         (pat1, (tau1,t)) (pat1', (tau1', t')) mC sC
     in
     match_pattern (cD, cG) (cD_p, cG_p)
       (pat2, (tau2,t)) (pat2', (tau2', t')) mC1 sC1
  | pat_ttau, (Comp.PatAnn (_, pat', tau'), (_, t')) ->
     match_pattern (cD, cG) (cD_p, cG_p) pat_ttau (pat', (tau', t')) mC sC
  | (Comp.PatAnn (_, pat', tau'), (_, t')), pat_ttau ->
     match_pattern (cD, cG) (cD_p, cG_p) (pat', (tau', t')) pat_ttau mC sC
  | _ ->
     raise (Error (Loc.ghost, MatchError "Mismatch"))

and match_spines (cD, cG) (cD_p, cG_p) pS pS' mC sC =
  match pS, pS' with
  | (Comp.PatNil, _),
    (Comp.PatNil, _) ->
     (mC, sC)
  | (Comp.PatApp (_, pat, pS), (Comp.TypArr (tau1, tau2), t)),
    (Comp.PatApp (_, pat', pS'), (Comp.TypArr (tau1', tau2'), t')) ->
     let mC1, sC1 =
       match_pattern (cD, cG) (cD_p, cG_p)
         (pat, (tau1,t)) (pat', (tau1', t')) mC sC
     in
     match_spines (cD, cG) (cD_p, cG_p)
       (pS, (tau2,t)) (pS', (tau2', t')) mC1 sC1
  | (Comp.PatApp (_, pat, pS), (Comp.TypPiBox ((LF.Decl (_, LF.ClTyp (LF.MTyp tA, cPsi), _)), tau2), t)),
    (Comp.PatApp (_, pat', pS'), (Comp.TypPiBox ((LF.Decl (_, LF.ClTyp (LF.MTyp tA', cPsi'), _)), tau2'), t')) ->
     let Comp.PatMetaObj (_, (loc, mO)) = pat in
     let Comp.PatMetaObj (_, (loc', mO')) = pat' in
     let tau1 = LF.ClTyp (LF.MTyp (Whnf.cnormTyp (tA, t)), Whnf.cnormDCtx (cPsi, t)) in
     let tau1' = LF.ClTyp (LF.MTyp (Whnf.cnormTyp (tA', t')), Whnf.cnormDCtx (cPsi', t')) in
     let t2 = LF.MDot (mO, t) in
     let t2' = LF.MDot (mO', t') in
     let mC1, sC1 = match_metaobj cD cD_p ((loc, mO), tau1) ((loc', mO'), tau1') mC sC in
     match_spines (cD, cG) (cD_p, cG_p)
       (pS, (tau2, t2)) (pS', (tau2', t2')) mC1 sC1

  | (Comp.PatApp (_, pat, pS), (Comp.TypPiBox ((LF.Decl (_, LF.CTyp w, _)), tau2), t)),
    (Comp.PatApp (_, pat', pS'), (Comp.TypPiBox ((LF.Decl (_, LF.CTyp w', _)), tau2'), t')) ->
     let Comp.PatMetaObj (_, (loc, mO)) = pat in
     let Comp.PatMetaObj (_, (loc', mO')) = pat' in
     let tau1 = LF.CTyp w in
     let tau1' = LF.CTyp w' in
     let t2 = LF.MDot (mO, t) in
     let t2' = LF.MDot (mO', t')in
     let mC1, sC1 = match_metaobj cD cD_p ((loc, mO), tau1) ((loc', mO'), tau1') mC sC in
     match_spines (cD, cG) (cD_p, cG_p)
       (pS, (tau2, t2)) (pS', (tau2', t2')) mC1 sC1

  | _, (Comp.PatApp (loc, _, _), _) ->
     raise (Error (loc, MatchError "Spine Mismatch"))
  | _ ->
     raise (Error (Loc.ghost, MatchError "Spine Mismatch"))

(* ********************************************************************************)
(* getSchemaElems : LF.mctx -> LF.dctx -> LF.sch_elem list
 * getSchemaElems cO cPsi
 *    = [F_1, ..., F_n]   if cPsi has a context variable of schema F_1 + ... + F_n
 *    = []                if cPsi has no context variable
 *)
let getSchemaElems cD cPsi =
  match Context.ctxVar cPsi with
  | None -> []
  | Some psi ->
     let LF.Schema elems =
       Store.Cid.Schema.get_schema
         (Context.lookupCtxVarSchema cD psi)
     in
     elems

(* ****************************************************************************** *)
(* Generate object tR of type tP in a context cPsi and meta-context cD            *)

(* genSpine cPsi sA tP = (cD', tS)

   if {cD}; cPsi |- sA <= typ   and FMV(sA) = {}
     {cD}; cPsi |- tP <= typ
   then
     cD'; cPsi |- tS : sA <= tP
 *)
let rec genSpine cD cPsi sA tP =
  match Whnf.whnfTyp sA with
  | (LF.PiTyp ((LF.TypDecl (_, tA), _), tB), s) ->
     (* cPsi' |- Pi x:A.B <= typ
        cPsi  |- s <= cPsi'
        cPsi  |- tN <= [s]tA
        cPsi |- tN . s <= cPsi', x:A
      *)
     (* let tN = Whnf.etaExpandMV cPsi (tA, s) S.LF.id in *)
     dprint
       begin fun _ ->
       "[genSpine] Pi-type"
       end;
     let tN = etaExpandMVstr cD cPsi (tA, s) in
     let tS = genSpine cD cPsi (tB, LF.Dot (LF.Obj (tN), s)) tP in
     LF.App (tN, tS)

  | (LF.Atom (_, a, _) as tQ, s) ->
     dprintf
       begin fun p ->
       p.fmt "[genSpine] atom type @[%a@]"
         (P.fmt_ppr_lf_typ cD cPsi P.l0) tQ
       end;
     U.unifyTyp LF.Empty cPsi (tQ, s) (tP, S.LF.id);
     LF.Nil


(* genObj (cD, cPsi, tP) (tH, tA) = (cD', CovGoal (cPsi', tR, tP'), ms)

   if cD; cPsi |- tH => tA   and
      there exists a spine tS s.t.  cD; cPsi |- tS : A > P
   then

      R = Root (tH, tS)  and  cD'; [ms]cPsi |- tR <= [ms]tP
                         and  cD' |- ms : cD

 *)
let genObj (cD, cPsi, tP) (tH, tA) =
  (* make a fresh copy of tP[cPsi] *)
  dprintf
    begin fun p ->
    p.fmt "[genObj] @[cD = %a@]"
      (P.fmt_ppr_lf_mctx P.l0) cD
    end;
  (* construct a substitution from cD that maps each contextual
     variable to an (appropriate) MMVar
   *)
  let ms = Ctxsub.mctxToMSub cD in
  let tP' = Whnf.cnormTyp (tP, ms) in
  let cPsi' = Whnf.cnormDCtx (cPsi, ms) in
  let tA' = Whnf.cnormTyp (Whnf.normTyp (tA, S.LF.id), ms) in
  let tH' = Whnf.cnormHead (tH, ms) in

  (* now tP', cPsi', tA', tH' are all "closed" but contain MMVars instead of MVars *)

  let spine = genSpine LF.Empty cPsi' (tA', S.LF.id) tP' in
  let tM = LF.Root (Loc.ghost, tH' , spine) in
  (*
    (* This print will crash Beluga sometimes, because it *seems* like
       tA doesn't always make sense in cD.
       This is probably a bug. -je
     *)
  dprintf
    begin fun p ->
    p.fmt "[genObj] @[<v>Generated Head@,\
           tH = @[%a@]@,\
           tA = @[%a@]@,\
           as suitable head for for [@[%a |-@ %a@]]@]"
      (P.fmt_ppr_lf_head cD cPsi P.l0) tH
      (P.fmt_ppr_lf_typ cD cPsi P.l0) tA
      (P.fmt_ppr_lf_dctx cD P.l0) cPsi
      (P.fmt_ppr_lf_typ cD cPsi P.l0) tP
    end;
   *)

  U.forceGlobalCnstr (!U.globalCnstrs);
  dprint
    begin fun _ ->
    "[genObj] global constraints forced!"
    end;
  let cD', cPsi', tR, tP', ms' =
    try
      Abstract.covgoal cPsi' tM tP' (Whnf.cnormMSub ms) (* cD0; cPsi0 |- tM : tP0 *)
    with
    | Abstract.Error (_, Abstract.LeftoverConstraints) as e ->
       let open Format in
       fprintf std_formatter "@[<v>WARNING: encountered leftover constraints in higher-order unification@,Coverage goal: @[%a@ : %a@]"
         (P.fmt_ppr_lf_normal LF.Empty cPsi' P.l0) tM
         (P.fmt_ppr_lf_typ LF.Empty cPsi' P.l0) tP';
       raise e
  in
  let (cPsi', tR', tP')  = (Whnf.normDCtx cPsi', Whnf.norm (tR, S.LF.id), Whnf.normTyp (tP', S.LF.id)) in
  dprintf
    begin fun p ->
    p.fmt "[genObj] @[<v>finished@,\
           meta-sub typing: @,  @[%a@]@]"
      P.fmt_ppr_lf_msub_typing (cD', ms', cD)
    end;
  (cD' , CovGoal (cPsi', tR', (tP', S.LF.id)), ms')

let rec genAllObj cg =
  function
  | [] -> []
  | tH_tA :: tHAlist ->
     let cgs = genAllObj cg tHAlist in
     begin
       try
         (genObj cg tH_tA)::cgs
       with
       | U.Failure _
         | U.GlobalCnstrFailure _ ->
          dprint
            begin fun _ ->
            "\n [genAllObj] Global Constraint Failure – no genObj generated.\n"
            end;
          cgs
     end

let genConst  ((cD, cPsi, LF.Atom (_, a, _tS)) as cg) =
  let _ = Types.freeze a in
  let constructors = (Types.get a).Types.constructors in
  (* Reverse the list so coverage will be checked in the order that the
     constructors were declared, which is more natural to the user *)
  let constructors = List.rev !constructors in
  let tH_tA_list =
    List.map
      (fun c ->
        (LF.Const c, (Const.get c).Const.typ))
      constructors
  in
  genAllObj cg tH_tA_list


let genHeads (tH, tA) =
  match Whnf.whnfTyp (tA, S.LF.id) with
  | (LF.Sigma tArec, s) ->
     let k = LF.blockLength tArec in
     let rec getComponents i =
       if i = k+1
       then []
       else (LF.Proj (tH, i), LF.TClo (LF.getType tH (tArec, s) i 1)) :: getComponents (i+1)
     in
     getComponents 1
  | _ -> [(tH, tA)]

let genBVar ((_, cPsi, _) as cg) =
  let k = Context.dctxLength cPsi in
  let rec genBVarCovGoals i =
    if i = (k+1)
    then []
    else
      let LF.TypDecl (_, tA) = Context.ctxDec cPsi i in (* x_i : tA in cPsi *)
      let tH_tA_list = genHeads (LF.BVar i, tA) in
      let cov_goals_i = genAllObj cg tH_tA_list in
      cov_goals_i @ genBVarCovGoals (i+1)
  in
  genBVarCovGoals 1


let genPVar (cD, cPsi, tP) =
  dprintf
    begin fun p ->
    p.fmt "[genPVar] for @[%a;@ %a |-@ %a@]"
      (P.fmt_ppr_lf_mctx P.l0) cD
      (P.fmt_ppr_lf_dctx cD P.l0) cPsi
      (P.fmt_ppr_lf_typ cD cPsi P.l0) tP
    end;
  match Context.ctxVar cPsi with
  | None ->
     dprint
       begin fun _ ->
       "[genPVar] No PVar cases because there is no ctx-var\n"
       end;
     []
  | Some psi ->
     dprint
       begin fun _ ->
       "[genPVar] found ctxvar, so we are generating pvar cases"
       end;
     let cvar_psi = LF.CtxVar psi in
     let selems = getSchemaElems cD cPsi in

     let rec genPVarCovGoals =
       function
       | [] -> []
       | LF.SchElem (decls, trec) :: elems ->
          let pv_list = genPVarCovGoals elems in
          let cPhi = Context.projectCtxIntoDctx decls in
          let cD', s, offset = Ctxsub.ctxToSub_mclosed cD cvar_psi cPhi in
          (* cO; cD'; psi                   |- [s]trec
             cO; cD'                        |- (cPsi, mshift offset)
             cO; cD'; (cPsi, mshift offset) |- (tP, mshift offset)
           *)
          let trec' = Whnf.normTypRec (trec, s) in
          let pdecl, tA =
            match trec' with
            | LF.SigmaLast (n, tA) ->
               (LF.Decl
                  ( NameGenerator.new_parameter_name "p"
                  , LF.ClTyp (LF.PTyp tA, Whnf.cnormDCtx (cvar_psi, LF.MShift offset))
                  , LF.Maybe
                  )
               , tA
               )
            | LF.SigmaElem _ ->
               (LF.Decl
                  ( NameGenerator.new_parameter_name "p"
                  , LF.ClTyp (LF.PTyp (LF.Sigma trec'), Whnf.cnormDCtx (cvar_psi, LF.MShift offset))
                  , LF.Maybe
                  )
               , LF.Sigma trec'
               )
          in

          let cD'_pdecl = LF.Dec (cD', pdecl) in
          let cPsi' = Whnf.cnormDCtx (cPsi, LF.MShift (offset + 1)) in
          let tP' = Whnf.cnormTyp (tP, LF.MShift (offset + 1)) in
          let cg' = (cD'_pdecl, cPsi', tP') in

          let id_psi = Substitution.LF.justCtxVar cPsi' in
          (* cO; cD_ext, pdec  ; cPsi' |- id_psi : cvar_psi  *)

          let h = LF.PVar (1, id_psi) in
          let tA' = Whnf.normTyp (Whnf.cnormTyp (tA, LF.MShift 1), id_psi) in
          (* cO; cD', pdec; cPsi'  |- p[id_psi] : [id_psi](trec[|MShift 1|])
           or to put it differently
           cO; cD', pdec; cPsi'  |- head : trec'
           *)
          let tH_tA_list = genHeads (h, tA') in
          dprint
            begin fun _ ->
            "#Generated Heads = " ^ string_of_int (List.length tH_tA_list)
            end;
          let cg_list = genAllObj cg' (tH_tA_list) in
          dprint
            begin fun _ ->
            "#Generated Obj = " ^ string_of_int (List.length cg_list)
            end;
          (* each cg in cg_list:    (cO_k, cD_k), ms_k
           where cD_k |- ms_k : cD'_pdcl
           we need however:    cD_k |- ms'_k : cD

           mcomp (MShift (offset + 1) ms_k
           *)
          let cg_list' =
            List.map
              (fun (cD', cg, ms) ->
                (cD', cg, Whnf.mcomp (LF.MShift (offset + 1)) ms)
              )
              cg_list
          in
          let all_cg = cg_list' @ pv_list in
          dprintf
            begin fun p ->
            p.fmt "[genPVar] @[<v>generated %d cases@,%a@]"
              (List.length all_cg)
              Prettycov.fmt_ppr_cov_goals all_cg
            end;
          all_cg
     in
     genPVarCovGoals selems

(* genCovGoals cD cPsi tP = cov_goal list

   - For each constant for the typeFamily (tP)
      we generate a coverage goal

   - For each bound variable in cPsi belonging to the typeFamily(tP),
     we generate a coverage goal

   - For each schema element of a context variable belonging to the typeFamily (tP),
     we generate a coverage goal.


   A coverage goal is of the following form:

     cD'; cPsi |- tR : tP  and  is represented as (cD', CovGoal (cPsi, tR, (tP, s)))

 *)

let rec genBCovGoals ((cD, cPsi, tA) as cov_problem) =
  match tA with
  | LF.Atom _ ->
     genPVar cov_problem @
       genBVar cov_problem
  | LF.Sigma trec ->
     raise Error.NotImplemented
  | LF.PiTyp ((tdecl, dep), tA) ->
     let x =
       match tdecl with
       | LF.TypDecl (x, _) -> x
       | LF.TypDeclOpt x -> x
     in
     let cg_list = genBCovGoals (cD, LF.DDec (cPsi, tdecl), tA) in
     List.map
       (fun (cD', cg, ms) ->
         let CovGoal (LF.DDec (cPsi', tdecl'), tM, sA) = cg in
         let cg' =
           CovGoal
             ( cPsi'
             , LF.Lam (Loc.ghost, x, tM)
             , (LF.PiTyp ((tdecl', dep), LF.TClo (sA)), S.LF.id)
             )
         in
         (cD', cg', ms)
       )
       cg_list


(* genCovGoals (cD, cPsi, tA) = S

   if cD; cPsi |- tA (the type we need to cover, i.e. the coverage problem)

   then S is a list of meta-context cD_i, cg_i = CovGoal (cPsi_i, tR_i, tP_i)
          and refinement substitutions ms_i s.t.

       S = { (cD_i, cg_i, ms_i) |

              cD_i |- ms_i : cD
              cD_i; cPsi_i |- tR_i : tP_i
           }
 *)
let rec genCovGoals (((cD, cPsi, tA) as cov_problem) : (LF.mctx * LF.dctx * LF.typ)) =
  match tA with
  | LF.Atom _ ->
     let g_pv = genPVar cov_problem in (* (cD', cg, ms) list *)
     dprintf
       begin fun p ->
       p.fmt "[genCovGoals] generated pvar cases: @[%a@]"
         Prettycov.fmt_ppr_cov_goals g_pv
       end;
     let g_bv = genBVar cov_problem in
     dprintf
       begin fun p ->
       p.fmt "[genCovGoals] generated bvar cases: @[%a@]"
         Prettycov.fmt_ppr_cov_goals g_bv
       end;
     let g_cv = genConst cov_problem in
     dprintf
       begin fun p ->
       p.fmt "[genCovGoals] generated const cases: @[%a@]"
         Prettycov.fmt_ppr_cov_goals g_cv
       end;
     g_pv @ g_bv @ g_cv

  | LF.PiTyp ((tdecl, dep), tB) ->
     let cov_goals = genCovGoals (cD, LF.DDec (cPsi, tdecl), tB) in
     let LF.TypDecl (x, _) = tdecl in
     List.map
       (fun (cD', cg, ms) ->
         let CovGoal (LF.DDec (cPsi', tdecl'), tM, sA) = cg in
         ( cD'
         , CovGoal
             ( cPsi'
             , LF.Lam (Loc.ghost, x, tM)
             , (LF.PiTyp ((tdecl', dep), LF.TClo (sA)), S.LF.id))
         , ms
         )
       )
       cov_goals


let rec solve' cD (matchCand, ms) cD_p mCands' sCands' =
  match matchCand with
  | [] ->
     begin match sCands' with
     | [] ->
        begin
          try
            U.forceGlobalCnstr (!U.globalCnstrs);
            dprint
              begin fun _ ->
              "[solve'] All global constraints are true."
              end;
            Solved
          with
          | U.Failure "Unresolved constraints" ->
             dprint
               begin fun _ ->
               "001 – Global constraints failed\n"
               end;
             (* PossSolvable (Cand (cD_p, LF.Empty, mCands, sCands)) *)
             NotSolvable
          | U.GlobalCnstrFailure (_, cnstr) ->
             dprint
               begin fun _ ->
               "002 – Unification of global constraint " ^ cnstr ^ " failed.\n"
               end;
             NotSolvable
        end
     | _ -> PossSolvable (Cand (cD_p, LF.Empty, mCands', sCands'))
     end
  | mc :: mCands ->
     begin match mc with
     | Eqn (CovSub (cPsi, s, sT), MetaSub (cPsi_p, s_p, sT_p)) ->
        let cT = LF.ClTyp (sT, cPsi) in
        let cT_p = LF.ClTyp (sT_p, cPsi_p) in
        let cM = (Loc.ghost, LF.ClObj (Context.dctxToHat cPsi, LF.SObj s)) in
        let cM_p = (Loc.ghost, LF.ClObj (Context.dctxToHat cPsi_p, LF.SObj s_p)) in
        begin
          try
            U.unifyMetaTyp cD (cT, Whnf.m_id) (cT_p, ms);
            U.unifyMetaObj cD (cM, Whnf.m_id) (cM_p, ms) (cT, Whnf.m_id);
            solve' cD (mCands, ms) cD_p (mc :: mCands') sCands'
          with
          | U.GlobalCnstrFailure (_, cnstr) ->
             dprint
               begin fun _ ->
               "003  UNIFY FAILURE – GLOBAL CONSTRAINT FAILURE"
               end;
             NotSolvable
          | U.Failure msg ->
             if U.unresolvedGlobalCnstrs ()
             then
               begin
                 dprint
                   begin fun _ ->
                   " UNIFY FAILURE " ^ msg ^ "\n MOVED BACK TO SPLIT CAND"
                   end;
                 let sc = Split (CovSub (cPsi, s, sT), MetaSub (cPsi_p, s_p, sT_p)) in
                 solve' cD (mCands, ms) cD_p mCands' (sc :: sCands')
               end
             else
               begin match msg with
               (* This matching on strings is really suspicious;
                         Nowhere in unify.ml is an exception raised with only the message "Pruning",
                         so it's extremely unlikely that this branch is ever hit.
                         -je *)
               | "Pruning" ->
                  (* Match Candidate is kept ? *)
                  let sc = Split (CovSub (cPsi, s, sT), MetaSub (cPsi_p, s_p, sT_p)) in
                  solve' cD (mCands, ms) cD_p (mCands') (sc::sCands')
               | _ ->
                  (* we are not trying to be clever and see if a context split would lead to progress *)
                  dprint
                    begin fun _ ->
                    "004 UNIFY FAILURE " ^ msg ^ " \n NOT SOLVABLE\n"
                    end;
                  NotSolvable
               end
        end

     | Eqn (CovGoal (cPsi, tR, sA), MetaPatt (cPsi_p, tR_p, sA_p)) ->
        let cPsi_p' = Whnf.cnormDCtx (cPsi_p, ms) in
        let tR_p' = Whnf.cnorm (tR_p, ms) in
        let tA_p' = Whnf.cnormTyp (Whnf.normTyp sA_p, ms) in
        dprintf
          begin fun p ->
          let dctx = P.fmt_ppr_lf_dctx cD P.l0 in
          let typ = P.fmt_ppr_lf_typ cD cPsi P.l0 in
          let normal = P.fmt_ppr_lf_normal cD cPsi P.l0 in
          p.fmt "[solve'] @[<v>@[%a == %a@]@,\
                 @[%a == %a@]@,\
                 @[%a == %a@]@]"
            dctx cPsi
            dctx cPsi_p'
            typ (Whnf.normTyp sA)
            typ tA_p'
            normal tR
            normal tR_p'
          end;
        begin
          try
            U.unifyDCtx cD cPsi cPsi_p';
            U.matchTyp cD cPsi sA (tA_p', S.LF.id);
            U.matchTerm cD cPsi (tR, S.LF.id) (tR_p', S.LF.id);
            solve' cD (mCands, ms) cD_p (mc::mCands') sCands'
          with
          (* should this case betaken care of during pre_match phase ? *)
          | U.GlobalCnstrFailure (_, cnstr) ->
             print_string ("005 Unification of pre-solved equation failed due to the fact the constraint " ^ cnstr ^ " cannot be solved.\n");
             NotSolvable
          | U.Failure "Context clash" ->
             print_string "Unification of pre-solved equation failed due to context mismatch - initiate context matching";
             let sc = SplitCtx (cPsi, cPsi_p) in
             dprintf
               begin fun p ->
               let dctx = P.fmt_ppr_lf_dctx cD P.l0 in
               p.fmt "Initiate context splitting: @[%a == %a@]"
                 dctx cPsi
                 dctx cPsi_p'
               end;
             solve' cD (mCands, ms) cD_p mCands' (sc::sCands')
          | U.Failure msg ->
             if U.unresolvedGlobalCnstrs ()
             then
               begin
                 dprint
                   begin fun _ ->
                   " UNIFY FAILURE " ^ msg ^ "\n MOVED BACK TO SPLIT CAND"
                   end;
                 let sc = Split (CovGoal (cPsi, tR, sA), MetaPatt (cPsi_p, tR_p, sA_p)) in
                 solve' cD (mCands, ms) cD_p mCands' (sc::sCands')
               end
             else
               begin match msg with
               | "Pruning" ->
                  (* Match Candidate is kept ? *)
                  let sc = Split (CovGoal (cPsi, tR, sA), MetaPatt (cPsi_p, tR_p, sA_p)) in
                  solve' cD (mCands, ms) cD_p (mCands') (sc::sCands')
               | _ ->
                  dprint
                    begin fun _ ->
                    "006 UNIFY FAILURE " ^ msg ^ " \n NOT SOLVABLE\n"
                    end;
                  NotSolvable
               end
        end

     | EqnCtx (cPsi, cPsi_p) ->
        let cPsi_p' = Whnf.cnormDCtx (cPsi_p, ms) in
        begin
          try
            dprintf
              begin fun p ->
              let dctx = P.fmt_ppr_lf_dctx cD P.l0 in
              p.fmt "EqnCtx @[%a == %a@]"
                dctx cPsi
                dctx cPsi_p'
              end;
            U.unifyDCtx cD cPsi cPsi_p';
            solve' cD (mCands, ms) cD_p (mc::mCands') sCands'
          with
          | U.Failure msg ->
             dprint
               begin fun _ ->
               "007 UNIFY FAILURE " ^ msg
               end;
             NotSolvable
        end
     end

let solve cD cD_p matchCand =
  match matchCand with
  | [] -> Solved
  | mc :: _ ->
     let ms = Ctxsub.mctxToMMSub cD cD_p in
     solve' cD (matchCand, ms) cD_p [] []

(* refineSplits cD cD_p matchL splitL ms = (matchL', splitL')

   if cD |- matchL
      cD |- ms : cD0
      cD0  |- splitL
   then
      cD |- matchL'    and  matchL @ matchL0 = matchL'
      cD |- splitL'    and  splitL' is the refined splitL
 *)
let rec refineSplits (cD : LF.mctx) (cD_p : LF.mctx) matchL splitL ms =
  match splitL with
  | [] -> (matchL, [])
  | Split (CovGoal (cPsi, tR, sA), patt) :: splits ->
     let matchL', splitL' = refineSplits cD cD_p matchL splits ms in
     let tA = Whnf.normTyp sA in
     let cPsi, tR, tA = (Whnf.cnormDCtx (cPsi, ms), Whnf.cnorm (tR, ms), Whnf.cnormTyp (tA, ms)) in
     let CovGoal (cPsi', tR', sA') as covG = CovGoal (cPsi, tR, (tA, S.LF.id)) in
     (* let MetaPatt (cPhi, _, sB') = patt in *)
     (* let mL', sL' = pre_match_typ cD cD_p (cPsi, sA') (cPhi, sB') matchL' splitL' in   *)
     (* let mL', sL' = pre_match_dctx cD cD_p cPsi cPhi matchL' splitL' in *)
     let result = pre_match cD cD_p covG patt matchL' splitL' in
     result
  | Split (CovSub (cPhi, s, sT), patt) :: splits ->
     let matchL', splitL' = refineSplits cD cD_p matchL splits ms in
     let covG = CovSub (Whnf.cnormDCtx (cPhi, ms), Whnf.cnormSub (s, ms), Whnf.cnormClTyp (sT, ms)) in
     pre_match_sub cD cD_p covG patt matchL' splitL'
  | SplitCtx (cPsi, cPsi_patt) :: splits ->
     let matchL', splitL' = refineSplits cD cD_p matchL splits ms in
     let cPsi' = Whnf.cnormDCtx (cPsi, ms) in
     pre_match_dctx cD cD_p cPsi' cPsi_patt matchL' splitL'
  | SplitPat ((Comp.PatFVar (loc, x), (tau, t)), pPatt_p) :: splits ->
     let matchL', splitL' = refineSplits cD cD_p matchL splits ms in
     (matchL', SplitPat ((Comp.PatFVar (loc, x), (tau, Whnf.mcomp t ms)), pPatt_p) :: splitL')

(* cnormCtx (cG, ms) = cG' *)
let rec cnormCtx (cG, ms) =
  match cG with
  | [] -> []
  | (x, tau, flag) :: cG' ->
     (x, Whnf.cnormCTyp (tau, ms), flag) :: (cnormCtx (cG', ms))

(* cnormEqn matchL ms = [ms]matchL

   if cD |- matchL
      cD' |- ms : cD
   then
      cD' |- [ms]matchL
 *)
let rec cnormEqn matchL ms =
  match matchL with
  | [] -> []
  | (Eqn (CovGoal (cPsi, tR, sA), patt) :: matchL') ->
     let tA = Whnf.normTyp sA in
     let cPsi, tR, tA = (Whnf.cnormDCtx (cPsi, ms), Whnf.cnorm (tR, ms), Whnf.cnormTyp (tA, ms)) in
     let covG0 = CovGoal (cPsi, tR, (tA, S.LF.id)) in
     let matchL0 = cnormEqn matchL' ms in
     Eqn (covG0, patt) :: matchL0

(* refine_cand (cD', cG', ms) (cD, cG, cand) = [ms]cand

   if
   cD' |- ms : cD
   cD; cG |- cand
   then
   cD'; cG' |- [ms]cand
 *)
let refine_cand (cD', cG', ms) (cD, cG, Cand (cD_p, cG_p, matchL, splitL)) =
  let matchL' = cnormEqn matchL ms in
  dprintf
    begin fun p ->
    p.fmt "[refine_cand] cD' = %a"
      (P.fmt_ppr_lf_mctx P.l0) cD'
    end;
  let matchL0, splitL0 = refineSplits cD' cD_p matchL' splitL ms in
  Cand (cD_p, cG_p, matchL0, splitL0)

let rec refine_candidates (cD', cG', ms) (cD, cG, candidates) =
  match candidates with
  | [] -> []
  | cand :: cands ->
     begin
       try
         dprintf
           begin fun p ->
           p.fmt "[refine_candidates] @[<v>REFINING candidate:@,\
                  @[%a@]@]"
             (Prettycov.fmt_ppr_candidate (cD, LF.Empty)) cand
           end;
         let cand' = refine_cand (cD', cG', ms) (cD, cG, cand) in
         dprintf
           begin fun p ->
           p.fmt "[refine_candidates] @[<v>REFINED candidate:@,\
                  @[%a@]@]"
             (Prettycov.fmt_ppr_candidate (cD', LF.Empty)) cand'
           end;
         cand' :: refine_candidates (cD', cG', ms) (cD, cG, cands)
       with
       | Error (_, MatchError _) ->
          dprintf
            begin fun p ->
            p.fmt "[refine_candidate] @[<v>irrelevant candidate:@,\
                   @[%a@]@]"
              (Prettycov.fmt_ppr_candidate (cD, LF.Empty)) cand
            end;
          refine_candidates (cD', cG', ms) (cD, cG, cands)
     end


let rec refine_pattern cov_goals ((cD, cG, candidates, patt) as cov_problem) =
  match cov_goals with
  | [] -> []
  | (TermCandidate ((cD_cg, _, ms) as cg)) :: cgs ->
     dprintf
       begin fun p ->
       p.fmt "[refine_pattern] @[<v>considering coverage goal@,  @[%a]@,\
              There are %d candidates@]"
         Prettycov.fmt_ppr_cov_goals [cg]
         (List.length candidates)
       end;
     let cG' = cnormCtx (cG, ms) in
     let candidates' = refine_candidates (cD_cg, cG', ms) (cD, cG, candidates) in
     dprint
       begin fun _ ->
       "[refine_candidates] DONE : The remaining #refined candidates = " ^ string_of_int (List.length candidates')
       end;
     let pat' = Whnf.cnormPattern (patt, ms) in
     begin match candidates' with
     | [] ->
        dprintf
          begin fun p ->
          p.fmt "[OPEN COVERAGE GOAL] %a"
            Prettycov.fmt_ppr_cov_goals [cg]
          end;
        open_cov_problems := (cD_cg, cG', pat') :: !open_cov_problems;
        refine_pattern cgs cov_problem
     | _ ->
        dprintf
          begin fun p ->
          p.fmt "[refine_pattern] @[<v>There are %d \
                 covering candidates (after refine_pattern):@,\
                 @[%a@]@]"
            (List.length candidates')
            (Prettycov.fmt_ppr_candidates (cD_cg, compgctx_of_gctx cG'))
            candidates'
          end;
        (cD_cg, cG', candidates', pat') :: refine_pattern cgs cov_problem
     end

  | CtxCandidate (cD_cg, cPhi_r, ms) :: cgs ->
     dprintf
       begin fun p ->
       p.fmt "[refine_pattern] @[<v>consider context goal @[%a@]@,\
              there are %d candidates@,\
              cD = @[%a@]@,\
              ms = @[%a@]@]"
         (P.fmt_ppr_lf_dctx cD_cg P.l0) cPhi_r
         (List.length candidates)
         (P.fmt_ppr_lf_mctx P.l0) cD
         (P.fmt_ppr_lf_msub cD_cg P.l0) ms
       end;
     let cG' = cnormCtx (cG, ms) in
     let candidates' = refine_candidates (cD_cg, cG', ms) (cD, cG, candidates) in
     dprint
       begin fun _ ->
       "[refine_pattern] DONE : "
       ^ "Remaining #refined candidates = "
       ^ string_of_int (List.length candidates')
       end;
     let pat' = Whnf.cnormPattern (patt, ms) in
     dprintf
       begin fun p ->
       p.fmt "[refine_pattern] @[cG@ = @[%a@]@]"
         (P.fmt_ppr_cmp_gctx cD P.l0) (compgctx_of_gctx cG)
       end;
     (* cD |- cPhi and cD0, cD |- ms : cD ? *)

     begin match candidates' with
     | [] ->
        dprintf
          begin fun p ->
          p.fmt "[OPEN CONTEXT GOAL] @[%a@]"
            (P.fmt_ppr_lf_dctx cD_cg P.l0) cPhi_r;
          p.fmt "[OPEN COVERAGE GOAL] @[%a@]"
            (P.fmt_ppr_cmp_pattern cD_cg (compgctx_of_gctx cG')
               P.l0)
            pat'
          end;
        open_cov_problems := (cD_cg, cG', pat') :: !open_cov_problems;
        refine_pattern cgs cov_problem
     | _ ->
        dprintf
          begin fun p ->
          p.fmt "[refine_pattern] @[<v>there are %d refined candidates@,\
                 for @[%a@]:@,@[%a@]@]"
            (List.length candidates')
            (P.fmt_ppr_cmp_pattern cD (compgctx_of_gctx cG)
               P.l0)
            patt
            (Prettycov.fmt_ppr_candidates (cD_cg, (compgctx_of_gctx cG'))) candidates'
          end;
        (cD_cg, cG', candidates', pat') :: refine_pattern cgs cov_problem
     end

(* ************************************************************************************* *)

(* TODO: Cleanup *)
(*  addToMCtx cD' (cD_tail, ms) = cD0, ms0

    if cD' |- ms : cD
    then cD',{cD_tail}   |- ms0 : cD, cD_tail
      and ms0 is ms extended with the identity for declarations in cD_tail
 *)

let rec addToMCtx cD (cD_tail, ms) =
  match cD_tail with
  | [] -> (cD, ms)
  | LF.Decl (u, LF.ClTyp (LF.MTyp tA, cPsi), dep) :: cD_tail ->
     let mdec = LF.Decl (u, LF.ClTyp (LF.MTyp (Whnf.cnormTyp (tA, ms)), Whnf.cnormDCtx (cPsi, ms)), dep) in
     addToMCtx (LF.Dec (cD, mdec)) (cD_tail, Whnf.mvar_dot1 ms)
  | LF.Decl (u, LF.ClTyp (LF.PTyp tA, cPsi), dep) :: cD_tail ->
     let pdec = LF.Decl (u, LF.ClTyp (LF.PTyp (Whnf.cnormTyp (tA, ms)), Whnf.cnormDCtx (cPsi, ms)), dep) in
     addToMCtx (LF.Dec (cD, pdec)) (cD_tail, Whnf.mvar_dot1 ms)
  | LF.Decl (u, LF.ClTyp (LF.STyp (cl, cPhi), cPsi), dep) :: cD_tail ->
     let sdec = LF.Decl (u, LF.ClTyp (LF.STyp (cl, Whnf.cnormDCtx (cPhi, ms)), Whnf.cnormDCtx (cPsi, ms)), dep) in
     addToMCtx (LF.Dec (cD, sdec)) (cD_tail, Whnf.mvar_dot1 ms)
  | cdecl :: cD_tail ->
     addToMCtx (LF.Dec (cD, cdecl)) (cD_tail, Whnf.mvar_dot1 ms)


let rec append cD =
  function
  | [] -> cD
  | dcl :: cD_tail -> append (LF.Dec (cD, dcl)) cD_tail

(* append (cO, cO_tail) cD1 (cD2 (cpsi, tB)) = (cD1, cD2')

   if cO, cO_tail |- cD2 mctx
      cO, cO_tail |- cD1 mctx
      cO, cO_tail; cD1; cpsi |- tB
   then
       cO |- cD1, [psi, x:tB / psi]cD2' mctx

 *)

(* decTomdec cD' cPhi = (cD'', s)
    where
    cD'' = cD', cD0
    cD''; cpsi |- s : cPhi
    x:A in cPhi iff x:A[cpsi] in cD0

    and cO'' |- cD'' mctx
 *)
let rec decTomdec cD' ((LF.CtxVar (LF.CtxOffset k)) as cpsi) (d, decls) =
  match decls with
  | LF.Empty -> (cD', S.LF.id)
  | LF.Dec (decls, dec) ->
     let LF.TypDecl (x, tA) = dec in
     (* .; decls |- tA : type            *)
     (*  cD'; cpsi, @x: _  |- s' : decls         *)
     let cD'', s' = decTomdec cD' cpsi (d-1, decls) in
     let cPsi, (LF.Atom (_, a, _) as tP, s) = lower (LF.CtxVar (LF.CtxOffset (k+d))) (tA, s') in
     dprintf
       begin fun p ->
       p.fmt "[decTomdec] @[<v>cPsi = @[%a@]@,\
              tP = @[%a@]@,\
              s' = @[%a@]@,@]"
         (P.fmt_ppr_lf_dctx cD'' P.l0) cPsi
         (P.fmt_ppr_lf_typ cD'' cPsi P.l0) tP
         (P.fmt_ppr_lf_sub cD'' LF.Null P.l0) s'
       end;
     (* bp : Context substitution associated with declaration is off by 1 *)
     let ss', cPsi' = Subord.thin' cD'' a cPsi in
     dprintf
       begin fun p ->
       p.fmt "[decTomdec] thinned @[ss' = @[%a@]@]"
         (P.fmt_ppr_lf_sub cD'' cPsi' P.l0) ss'
       end;
     (* cPsi |- ss' : cPsi' *)
     let ssi' = S.LF.invert ss' in
     (* cPsi' |- ssi : cPsi *)
     let ssi = S.LF.comp s ssi' in
     dprintf
       begin fun p ->
       p.fmt "[decTomdec] inverted @[ss' = @[%a@]@]"
         (P.fmt_ppr_lf_sub cD'' cPsi' P.l0) ssi;
       p.fmt "[genCtx] generated mvar of type @[%a |- %a@]"
         (P.fmt_ppr_lf_dctx cD'' P.l0) cPsi'
         (P.fmt_ppr_lf_typ cD'' cPsi' P.l0)
         (Whnf.normTyp (tP, ssi))
       end;
     let mdec = LF.Decl (x, LF.ClTyp (LF.MTyp (LF.TClo (tP, ssi)), cPsi'), LF.Maybe) in
     let mv = LF.Root (Loc.ghost, LF.MVar (LF.Offset 1, Whnf.cnormSub (ss', LF.MShift 1)), LF.Nil) in
     (LF.Dec (cD'', mdec), LF.Dot (LF.Obj mv, Whnf.cnormSub (s', LF.MShift 1)))

(* genCtx elems = ctx_goal_list

     for each ctx_goal in ctx_goal_list .
        ctx_goal = (cD_i, cPsi_i, ms_i) s.t.
        cO; cD_i |- ms_i   : cD
        cO; cD_i |- cPsi_i : ctx
 *)
let rec genCtx (LF.Dec (_, LF.Decl _) as cD) cpsi =
  function
  | [] -> [(cD, LF.Null, LF.MShift 0)]
  | LF.SchElem (decls, trec) :: elems ->
     let cPsi_list = genCtx cD cpsi elems in
     let d = Context.length decls in
     let cD0, s = decTomdec cD cpsi (d-1, decls) in
     dprintf
       begin fun p ->
       p.fmt "[genCtx] @[s =@ @[%a@]@]"
         (P.fmt_ppr_lf_sub cD0 cpsi P.l0) s
       end;
     let cpsi' = LF.CtxVar (LF.CtxOffset (d+1)) in
     (* cD0 = cD, decls *)
     let tA =
       match trec with
       | LF.SigmaLast (_, tA) -> LF.TClo (tA, s)
       | _ -> LF.TClo (LF.Sigma trec, s)
     in
     dprintf
       begin fun p ->
       p.fmt "[genCtx] @[tA =@ @[%a@]@]"
         (P.fmt_ppr_lf_typ cD0 cpsi' P.l0) tA
       end;
     (* cD0; cpsi |- tA : type *)
     (* let ms = gen_mid cD0 cD in *)
     let ms = LF.MShift (Context.length cD0 - Context.length cD) in
     (* cD0 |- ms : cD
        cD' |- cPsi' ctx *)
     let cPsi' = LF.DDec (cpsi', LF.TypDecl (NameGenerator.new_bvar_name "x", tA)) in
     dprintf
       begin fun p ->
       p.fmt "[genCtx] @[<v>cPsi' = @[%a@]@,\
              ms = @[%a@]@,\
              cD0 = @[%a@]@,\
              cD = @[%a@]@]"
         (P.fmt_ppr_lf_dctx cD0 P.l0) cPsi'
         (P.fmt_ppr_lf_msub cD0 P.l0) ms
         (P.fmt_ppr_lf_mctx P.l0) cD0
         (P.fmt_ppr_lf_mctx P.l0) cD
       end;
     (cD0, cPsi', ms) :: cPsi_list

(* genCtxGooals cD (psi:W) = goal_list

   such that
   goal-list =
   [cD, psi:schema, cD' |- psi, x:s_elem_1, ...  where cD' = FMV(s_elem1)
    cD, psi:schema, cD' |- psi, x:s_elem_n, ...  where cD' = FMV(s_elemn)
    cD                  |- .
   ]
 *)
let genCtxGoals cD (LF.Decl (x, LF.CTyp (Some schema_cid), dep)) =
  let LF.Schema elems = Store.Cid.Schema.get_schema schema_cid in
  let cD' = LF.Dec (cD, LF.Decl (x, LF.CTyp (Some schema_cid), dep)) in
  genCtx cD' (LF.CtxVar (LF.CtxOffset 1)) elems

let genContextGoals cD ctx_schema =
  let cgs = genCtxGoals cD ctx_schema in
  List.map (fun (cD, cPsi, ms) -> (cD, CovCtx cPsi, ms)) cgs

(* Find mvar to split on *)
let genSVCovGoals (cD, (cPsi, LF.STyp (r0, cPhi))) (* cov_problem *) =
  match cPhi with
  | LF.Null -> [(cD, CovSub (cPsi, LF.EmptySub, LF.STyp (r0, cPhi)),  LF.MShift 0)]
  | LF.CtxVar _ -> []  (* Split on the context variable first *)
  | LF.DDec (cPhi', decl) ->
     let LF.TypDecl (x, tA) = decl in
     let s = LF.SVar (2, 0, S.LF.id) in
     let mT = LF.ClTyp (LF.STyp (r0, cPhi'), cPsi) in
     let cD' = LF.Dec (cD, LF.Decl (Id.mk_name (Whnf.newMTypName mT), mT, LF.No)) in
     (* if ren = renaming, generate parameter variable *)
     let tM = LF.Root (Loc.ghost, LF.MVar (LF.Offset 1, S.LF.id), LF.Nil) in
     let tA0 = Whnf.cnormTyp (tA, LF.MShift 1) in
     let cPhi0 = Whnf.cnormDCtx (cPhi', LF.MShift 1) in
     let mT' = LF.ClTyp (LF.MTyp tA0, cPhi0) in
     let cD'' = LF.Dec (cD', LF.Decl (Id.mk_name (Whnf.newMTypName mT'), mT', LF.No)) in
     let cPsi' = Whnf.cnormDCtx (cPsi, LF.MShift 2) in
     let cPhi'' = Whnf.cnormDCtx (cPhi, LF.MShift 2) in
     [(cD'', CovSub (cPsi', LF.Dot (LF.Obj tM, s), LF.STyp (r0, cPhi'')), LF.MShift 2)]

let genCGoals (cD' : LF.mctx) (cT : LF.ctyp) : (LF.mctx * cov_goal * LF.msub) list * depend =
  let dep_of_typ = function
    | LF.Atom (_, _, LF.Nil) -> Atomic
    | _ -> Dependent
  in
  match cT with
  | LF.ClTyp (LF.MTyp tA, cPsi) ->
     dprintf
       begin fun p ->
       p.fmt "[SPLIT] CovGoal: @[%a |- %a@]"
         (P.fmt_ppr_lf_dctx cD' P.l0) cPsi
         (P.fmt_ppr_lf_typ cD' cPsi P.l0) tA
       end;
     let dep0 = dep_of_typ tA in
     ( genCovGoals (cD', cPsi, Whnf.normTyp (tA, S.LF.id))
     , dep0
     )

  | LF.ClTyp (LF.PTyp tA, cPsi) ->
     begin match cPsi with
     | LF.CtxVar _ -> ([], Atomic)
     (* In the interactive mode, prevent splitting on parameter variables
         whose type is simply a context variable and ask the user to split on
         the context first; should maybe raise error. *)
     | _ ->
        dprintf
          begin fun p ->
          p.fmt "[SPLIT] CovGoal (PVAR): @[%a |- %a@]"
            (P.fmt_ppr_lf_dctx cD' P.l0) cPsi
            (P.fmt_ppr_lf_typ cD' cPsi P.l0) tA
          end;
        let dep0 = dep_of_typ tA in
        (* bp : This may potentially even loop!;
           but this could initiate a potential split of PV including splitting the context
           g |- #A should result in g', x|- x   g', x|- #q
           in this implementation, we assume that the context split has been done separetely,
           and hence we would only loop if we were to split #p (and initiate another context split)
         *)
        ( genBCovGoals (cD', cPsi, Whnf.normTyp (tA, S.LF.id))
        , dep0
        )
     end

  | LF.ClTyp (sTyp, cPsi) ->
     begin match cPsi with
     | LF.CtxVar _ -> ([], Atomic)
     (* In the interactive mode, prevent splitting on substitution variables
         should be postponed until the domain, cPsi, has been refined and is
         either . (empty) or cPsi', _
         if cPsi is simply a context variable and ask the user to split on
         the context first; should maybe raise Split error. *)
     | _ ->
        ( genSVCovGoals (cD', (cPsi, sTyp))
        , Atomic
        )
     end


let rec best_ctx_cand (cD, cv_list) k cD_tail =
  match cv_list, cD with
  | [], _ -> NoCandidate
  | [LF.CtxOffset j], LF.Dec (cD', cd) ->
     if j = k
     then
       let ctx_goals = genCtxGoals cD' cd in
       let f (cD', cPhi, ms) =
         (* cD' |- ms : cD *)
         let ms' = LF.MDot (LF.CObj (cPhi), ms) in
         let k = List.length cD_tail in
         dprintf
           begin fun p ->
           p.fmt "[ctx_goal] @[<v>cD' = @[%a@]@,\
                  ms' = @[%a@]@]"
             (P.fmt_ppr_lf_mctx P.l0) cD'
             (P.fmt_ppr_lf_msub cD' P.l0) ms
           end;
         let cD'', ms0 = addToMCtx cD' (cD_tail, ms') in
         (* cD', cD_tail |- ms0 : cD, cD_tail *)
         dprintf
           begin fun p ->
           p.fmt "[ctx_goal] @[@[%a@] |-@ @[%a@]@ : @[%a@]@]"
             (P.fmt_ppr_lf_mctx P.l0) cD''
             (P.fmt_ppr_lf_msub cD'' P.l0) ms0
             (P.fmt_ppr_lf_mctx P.l0) (append cD cD_tail)
           end;
         CtxCandidate (cD'', Whnf.cnormDCtx (cPhi, LF.MShift k), ms0)
       in
       let ctx_goals' = List.map f ctx_goals in
       SomeCtxCands ctx_goals'
     else
       best_ctx_cand (cD', cv_list) (k+1) (cd::cD_tail)


let rec best_cand (cD, mv_list) k cD_tail =
  match mv_list, cD with
  | [], _ -> NoCandidate
  | LF.Offset j :: mvlist',  LF.(Dec (cD', (Decl (_, cT, _) as md))) ->
     if k = j
     then
       begin
         try
           let cov_goals', dep0 = genCGoals cD' cT in
           let cov_goals0 =
             List.map
               (fun (cD', cg, ms) ->
                 let k = List.length cD_tail in
                 match cg with
                 | CovGoal (cPsi', tR, sA') ->
                    dprintf
                      begin fun p ->
                      p.fmt "[best_cand] generated covgoal @[%a@]"
                        (Prettycov.fmt_ppr_cov_goal cD') cg
                      end;
                    let ms' = LF.MDot (LF.ClObj (Context.dctxToHat cPsi', LF.MObj tR), ms) in
                    let cD'', ms0 = addToMCtx cD' (cD_tail, ms') in
                    let cg' =
                      CovGoal
                        ( Whnf.cnormDCtx (cPsi', LF.MShift k)
                        , Whnf.cnorm (tR, LF.MShift k)
                        , (Whnf.cnormTyp (Whnf.normTyp sA', LF.MShift k), S.LF.id)
                        )
                    in
                    TermCandidate (cD'', cg',  ms0)
                 | CovSub (cPhi,  s, sT) ->
                    let ms' = LF.MDot (LF.ClObj (Context.dctxToHat cPhi, LF.SObj s), ms) in
                    let cD'', ms0 = addToMCtx cD' (cD_tail, ms') in
                    let cg' =
                      CovSub
                        ( Whnf.cnormDCtx (cPhi, LF.MShift k)
                        , Whnf.cnormSub (s, LF.MShift k)
                        , Whnf.cnormClTyp (sT, LF.MShift k)
                        )
                    in
                    TermCandidate (cD'', cg',  ms0))
               cov_goals'
           in

           match best_cand (cD', mvlist') (k+1) (md::cD_tail) with
           | NoCandidate -> SomeTermCands (dep0, cov_goals0)
           | SomeTermCands (dep, cov_goals) ->
              begin match dep, dep0 with
              | Dependent, Atomic -> SomeTermCands (dep, cov_goals)
              | Atomic, Dependent -> SomeTermCands (dep0, cov_goals0)
              | _, _ -> SomeTermCands (dep0, cov_goals0)
              (*
              | _, _ ->
                 if List.length cov_goals < List.length cov_goals0
                 then SomeTermCands (dep, cov_goals)
                 else SomeTermCands (dep0, cov_goals0)
               *)
              end
         with
         | Abstract.Error (_, Abstract.LeftoverConstraints) ->
            print_endline
              "WARNING: Encountered left-over constraints in higher-order unification.\n Try another candidate.";
            best_cand (cD', mvlist') (k+1) (md::cD_tail)
       end
     else
       best_cand (cD', mv_list) (k+1) (md::cD_tail)


(* Implement function which generates coverage goals for general computation-level types *)
(* genPattSpine cD (tau_v, t) = (cD0, cG0, pS, ttau)

   if cD |- [t] tau_v
   then cD0; cG0 |- pS : [t]tau_v > ttau
 *)
let rec genPattSpine =
  function
  | Comp.TypArr (tau1, tau2), t ->
     let pv1 = NameGenerator.new_patvar_name () in
     let pat1 = Comp.PatFVar (Loc.ghost, pv1) in
     let cG, pS, ttau =
       genPattSpine (tau2, t)
     in
     ( (pv1, Whnf.cnormCTyp (tau1,t), false) :: cG
     , Comp.PatApp (Loc.ghost, pat1, pS)
     , ttau
     )
  | Comp.TypPiBox ((LF.Decl (x, LF.CTyp sW, _)), tau), t ->
     let cPsi' =
       let open! LF in
       let mmvar =
         { name = x
         ; instantiation = ref None
         ; cD = Empty
         ; typ = LF.CTyp sW
         ; constraints = ref []
         ; depend = Maybe
         }
       in
       CtxVar (CInst (mmvar, Whnf.m_id))
     in
     let pat1 =
       Comp.PatMetaObj
         ( Loc.ghost
         , (Loc.ghost, LF.CObj cPsi')
         )
     in
     let cG, pS, ttau0 =
       genPattSpine (tau, LF.MDot (LF.CObj (cPsi'), t))
     in
     ( cG
     , Comp.PatApp (Loc.ghost, pat1, pS)
     , ttau0
     )

  | Comp.TypPiBox ((LF.Decl (u, LF.ClTyp (LF.MTyp tP,  cPsi), _)), tau), t ->
     let tP' = Whnf.cnormTyp (tP, t) in
     let cPsi' = Whnf.cnormDCtx (cPsi, t) in
     let tR = etaExpandMVstr LF.Empty cPsi' (tP', S.LF.id) in
     let pat1 =
       Comp.PatMetaObj
         ( Loc.ghost
         , (Loc.ghost, LF.ClObj (Context.dctxToHat cPsi', LF.MObj tR))
         )
     in
     let cG, pS, ttau0 =
       genPattSpine (tau, LF.MDot (LF.ClObj (Context.dctxToHat cPsi', LF.MObj tR), t))
     in
     (cG, Comp.PatApp (Loc.ghost, pat1, pS), ttau0)

  | typ ->
     ([], Comp.PatNil, typ)

(** Suppose tau_v is a well-formed type in meta-context cD_p and c is
    a computation-level constructor with type tau_c.
    This function tries to generate a pattern for the constructor `c`.
    To do this, it first generates a spine consisting of variables for
    the pattern (one for each arrow/pibox type in tau_c) (the pattern
    head is `c`).
    This computes a new type `tau` with a delayed meta-substitution
    `t` such that `tau[t]` makes sense in the empty context.
 *)
let genPatt (cD_p, tau_v) (c, tau_c) =
  let cG, pS, (tau, t) = genPattSpine (tau_c, Whnf.m_id) in
  let pat = Comp.PatConst (Loc.ghost, c, pS) in
  dprintf
    begin fun p ->
    p.fmt "[genPatt] @[<v>%a : %a@,\
           expected type: @[%a@]@]"
      (P.fmt_ppr_cmp_pattern LF.Empty (compgctx_of_gctx cG) P.l0) pat
      (P.fmt_ppr_cmp_typ LF.Empty P.l0) (Whnf.cnormCTyp (tau, t))
      (P.fmt_ppr_cmp_typ cD_p P.l0) tau_v
    end;
  let ms = Ctxsub.mctxToMSub cD_p in
  begin
    try
      U.unifyCompTyp LF.Empty (tau, t) (tau_v, ms);
      let cD', cG', pat', tau', ms' =
        Abstract.covpatt
          (Whnf.cnormCtx (compgctx_of_gctx cG, Whnf.m_id))
          (Whnf.cnormPattern (pat, Whnf.m_id))
          (Whnf.cnormCTyp (tau_v, ms)) (Whnf.cnormMSub ms)
      in
      let ccG' = gctx_of_compgctx cG' in
      dprint
        begin fun _ ->
        "[genPatt] - Return Coverage Pattern"
        end;
      Some (cD', CovPatt (ccG', pat', (tau', Whnf.m_id)), ms')
    with
    (* expected type and generated type for spine do not
       unify; therefore c pS is not inhabit tau_v
     *)
    | U.Failure _ ->
       None
    | Abstract.Error (_, Abstract.LeftoverConstraints) as e ->
       print_string
         "WARNING: Generation of pattern encountered left-over constraints in higher-order unification\n";
       raise e
  end

let rec genAllPatt ((cD_v, tau_v) : LF.mctx * Comp.typ) =
  function
  | [] -> []
  | (c, tau_c) :: ctau_list ->
     begin match genPatt (cD_v, tau_v) (c, tau_c) with
     | Some (cD, cg, ms) ->
        let pat_list = genAllPatt (cD_v, tau_v) ctau_list
        in (cD, cg, ms) :: pat_list
     | None -> genAllPatt (cD_v, tau_v) ctau_list
     end

let genPatCGoals (cD : LF.mctx) (cG1 : gctx) tau (cG2 : gctx) =
  match tau with
  | Comp.TypCross (tau1, tau2) ->
     let pv1 = NameGenerator.new_patvar_name () in
     let pv2 = NameGenerator.new_patvar_name () in
     let cG1' = (pv1, tau1, false) :: (pv2, tau2, false) :: cG1 in
     let cG' = cG1' @ cG2 in
     let pat =
       Comp.PatPair
         ( Loc.ghost
         , Comp.PatFVar (Loc.ghost, pv1)
         , Comp.PatFVar (Loc.ghost, pv2)
         )
     in
     let cg = CovPatt (cG', pat, (tau, Whnf.m_id)) in
     [(cD, cg, Whnf.m_id)]

  | Comp.TypBox (loc, (LF.ClTyp (LF.MTyp tA, cPsi) as mT)) ->
     let cgoals, _ = genCGoals cD mT in
     let f (cD', cg, ms) =
       let CovGoal (cPsi', tR, sA') = cg in
       dprintf
         begin fun p ->
         p.fmt "[genPatCGoals] @[<v>%a@]"
           P.fmt_ppr_lf_msub_typing (cD', ms, cD)
         end;
       let m_obj =
         ( Loc.ghost
         , LF.ClObj (Context.dctxToHat cPsi', LF.MObj tR)
         )
       in
       let pat_r = Comp.PatMetaObj (Loc.ghost, m_obj) in
       let tau_r =
         ( Comp.TypBox (loc, LF.ClTyp (LF.MTyp (LF.TClo sA'), cPsi'))
         , Whnf.m_id
         )
       in
       let cG' = cnormCtx (cG1, ms) @ cnormCtx (cG2,ms) in
       dprintf
         begin fun p ->
         p.fmt "[genPatCGoals] @[<v>old cG = @[%a@]@,\
                new cG' = @[%a@]@]"
           (P.fmt_ppr_cmp_gctx cD P.l0)
           (compgctx_of_gctx (cG1 @ cG2))
           (P.fmt_ppr_cmp_gctx cD' P.l0)
           (compgctx_of_gctx cG')
         end;
       (cD', CovPatt (cG', pat_r, tau_r), ms)
     in
     List.map f cgoals

  | Comp.TypBase (_, c, mS) ->
     dprintf
       begin fun p ->
       p.fmt "[genPatCGoals] for @[%a@]"
         (P.fmt_ppr_cmp_typ cD P.l0) tau
       end;
     let constructors =
       !((Store.Cid.CompTyp.get c).Store.Cid.CompTyp.constructors)
       |> List.rev
     in
     if constructors = []
     then
       dprint
         begin fun _ ->
         "[genPatCGoals] No Constructors defined for that type"
         end;
     let ctau_list =
       let f c =
         let tau_c = (Store.Cid.CompConst.get c).Store.Cid.CompConst.typ in
         dprintf
           begin fun p ->
           p.fmt "[genPatCGoals] constructor: %s : %a"
             (R.render_cid_comp_const c)
             (P.fmt_ppr_cmp_typ LF.Empty P.l0) tau_c
           end;
         (c, tau_c)
       in
       List.map f constructors
     in
     let r =
       List.map
         (fun (cD, cg, ms) ->
           let CovPatt (cG0, pat, ttau) = cg in
           let cG0' = cnormCtx (cG1, ms) @ cG0 @ cnormCtx (cG2, ms) in
           (cD, CovPatt (cG0', pat, ttau), ms)
         )
         (genAllPatt (cD, tau) ctau_list)
     in
     dprintf
       begin fun p ->
       p.fmt "[genPatCGoals] @[<v>generated %d cases for type @[%a@]:@,\
              @[%a@]"
         (List.length r)
         (P.fmt_ppr_cmp_typ cD P.l0) tau
         Prettycov.fmt_ppr_cov_goals r
       end;
     r
  | _ -> []

let rec mvInSplitCand cD vlist =
  function
  | [] -> vlist
  | Cand (_, _, _, sl) :: cands ->
     mvInSplitCand cD (mvInSplit cD vlist sl) cands

and mvInSplit cD vlist =
  function
  | [] -> vlist
  | Split (CovGoal (_, LF.Root (_, LF.MVar (u, _), _), _), _) :: sl ->
     let pvlist, cvlist, mvlist = vlist in
     if List.mem u mvlist
     then mvInSplit cD vlist sl
     else mvInSplit cD (pvlist, cvlist, (u :: mvlist)) sl

  | Split (CovGoal (_, LF.Root (_, LF.PVar (k, _), _), _), _) :: sl ->
     let pvlist, cvlist, mvlist = vlist in
     if List.mem (LF.Offset k) mvlist
     then mvInSplit cD vlist sl
     else
       (* we only split on a parameter variable, if its context is
          a proper context and not just a context variable *)
       begin match Whnf.mctxPDec cD k with
       | (_, _, LF.CtxVar _) ->
          mvInSplit cD (pvlist, cvlist, mvlist) sl
       | _ ->
          mvInSplit cD (pvlist, cvlist, LF.Offset k :: mvlist) sl
       end

  | Split (CovGoal (_, LF.Root (_, LF.Proj _, _), _), _) :: sl ->
     mvInSplit cD vlist sl

  | Split (CovSub (_, LF.SVar (u, _, _), _), _) :: sl ->
     let pvlist, cvlist, mvlist = vlist in
     if List.mem (LF.Offset u) mvlist
     then mvInSplit cD vlist sl
     else mvInSplit cD (pvlist, cvlist, LF.Offset u :: mvlist) sl

  | Split _ :: sl ->
     dprint
       begin fun _ ->
       "SPLIT CAND (other - an equation which was not solvable earlier due to constraints (for example pruning of a bound meta-variable is not possible) :\n"
       end;
     mvInSplit cD vlist sl

  | SplitCtx (LF.CtxVar psi, cPhi) :: sl ->
     let pvlist, cvlist, mvlist = vlist in
     if List.mem psi cvlist
     then mvInSplit cD (pvlist, cvlist, mvlist) sl
     else mvInSplit cD (pvlist, psi :: cvlist, mvlist) sl

  | SplitPat ((Comp.PatFVar (_, x), ttau), (patt_p, ttau_p)) :: sl ->
     let pvlist, cvlist, mvlist = vlist in
     if List.mem x pvlist
     then mvInSplit cD vlist sl
     else mvInSplit cD (x :: pvlist, cvlist, mvlist) sl

let best_split_candidate cD candidates =
  (* assume candidates are non-empty *)
  let _, cvsplit_list, mvsplit_list =
    mvInSplitCand cD ([], [], []) candidates
  in
  (* first _ describes the pattern variables one can split on,
      but we always split on pattern variables before calling best_split_candidate *)
  let mv_list_sorted =
    List.sort
      (fun (LF.Offset k) (LF.Offset k') ->
        if k' < k
        then 1
        else
          if k' = k
          then 0
          else -1
      )
      mvsplit_list
  in
  let cv_list_sorted =
    List.sort
      (fun (LF.CtxOffset k) (LF.CtxOffset k') ->
        if k' < k
        then 1
        else
          if k' = k
          then 0
          else -1
      )
      cvsplit_list
  in
  dprintf
    begin fun p ->
    p.fmt "[best_split_candidate] @[<v>candidates:@,@[%a@]@]"
      Prettycov.fmt_ppr_mvlist mv_list_sorted
    end;
  if cv_list_sorted = []
  then best_cand (cD, mv_list_sorted) 1 []
  else
    begin
      dprint
        begin fun _ ->
        "Context Split possible\n"
        end;
      best_ctx_cand (cD, cv_list_sorted) 1 []
    end


(* ************************************************************************************* *)
(* refine_mv (cD, cG, candidates, patt) =

   if cD; cG |- patt
      and candidates = [(cD_p, cG_p, mE, sE), ... ]
      cG = Empty
   then
        refine the best candidate from cD using
        cD1 |- ms1 : cD, .... cDk |- msk : cD
        and generate k new coverage problems

 *)
let refine_mv ((cD, cG, candidates, patt) as cov_problem) =
  match cD with
  | LF.Empty ->
     (* print_string (candidatesToString cov_problem); *)
     dprint
       begin fun _ ->
       "[refine_mv] NOTHING TO REFINE"
       end;
     open_cov_problems := (cD, cG, patt) :: !open_cov_problems;
     raise (Error (Loc.ghost, NothingToRefine))
  (* [] *)
  (* raise (Error "Nothing to refine") *)
  | _ ->
     let cov_goals' = best_split_candidate cD candidates in
     dprintf
       begin fun p ->
       p.fmt "[Original candidates] @[<v>%a@]"
         Prettycov.fmt_ppr_cov_problem cov_problem
       end;
     begin match cov_goals', candidates with
     | SomeCtxCands ctx_goals, [] -> []
     | SomeCtxCands ctx_goals, _ ->
        (* bp : TODO refine_ctx_cov_problem ctx_goals cov_problem *)
        (*      raise (Error "Context refinment not implemented yet") *)
        dprint
          begin fun _ ->
          "Some CtxCands ... "
          end;
        let cands = refine_pattern ctx_goals cov_problem in
        dprint
          begin fun _ ->
          "[refine_pattern] done"
          end;
        cands

     | SomeTermCands (_, []), [] -> []
     | SomeTermCands (_, []), _ ->
        open_cov_problems := (cD, cG, patt) :: !open_cov_problems;
        raise (Error (Loc.ghost, NothingToRefine))
     | SomeTermCands (_, cgoals), _ ->
        dprintf
          begin fun p ->
          p.fmt "[refine_mv] @[<v>generated coverage goals:@,\
                 @[%a@]@,
                 for pattern: @[%a@]@]"
            Prettycov.fmt_ppr_cov_goals (List.map (fun (TermCandidate cg) -> cg) cgoals)
            (P.fmt_ppr_cmp_pattern cD (compgctx_of_gctx cG) P.l0) patt
          end;
        refine_pattern cgoals cov_problem
     (*              let Comp.PatMetaObj (_, mO) = patt in
                      let cPhi, tM = match mO with
                      | Comp.MetaObjAnn (_, cPhi, tM) -> (cPhi, tM)
                      | Comp.MetaObj (loc, phat, tM) -> (Context.hatToDCtx phat, tM)
                      in

                      let lf_cov_problem = (cD, cG, candidates, (cPhi, tM)) in
                      refine_lf_cov_problem cgoals lf_cov_problem      *)
     | NoCandidate, [] -> []
     | NoCandidate, _ ->
        open_cov_problems := (cD, cG, patt) :: !open_cov_problems;
        []
     end

let rec subst_pattern (pat_r, pv) pattern =
  match pattern with
  | Comp.PatFVar (loc, y) ->
     if y = pv
     then pat_r
     else pattern
  | Comp.PatPair (loc, pat1, pat2) ->
     let pat1' = subst_pattern (pat_r, pv) pat1 in
     let pat2' = subst_pattern (pat_r, pv) pat2 in
     Comp.PatPair (loc, pat1', pat2')
  | Comp.PatAnn (loc, pat, tau) ->
     let pat' = subst_pattern (pat_r, pv) pat in
     Comp.PatAnn (loc, pat', tau)
  | Comp.PatConst (loc, c, pS) ->
     let pS' = subst_pattern_spine (pat_r, pv) pS in
     Comp.PatConst (loc, c, pS')
  | _ -> pattern

and subst_pattern_spine (pat_r, pv) =
  function
  | Comp.PatNil -> Comp.PatNil
  | Comp.PatApp (loc, pat, pS) ->
     let pat' = subst_pattern (pat_r, pv) pat in
     let pS' = subst_pattern_spine (pat_r, pv) pS in
     Comp.PatApp (loc, pat', pS')

let rec subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml) =
  function
  | [] -> (ml, [])
  | (SplitPat ((Comp.PatFVar (_, x), ttau), (patt_p, ttau_p)) as seqn) :: sl ->
     let ml', sl' = subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml) sl in
     if x = pv
     then
       begin
         dprintf
           begin fun p ->
           p.fmt "[subst_spliteqn] @[<v>cD = @[%a@]@,\
                  pat_r = @[%a@]@,\
                  ttau = @[%a@]@,\
                  cD_p = @[%a@]@,\
                  pat_p = @[%a@]@,\
                  ttau_p = @[%a@]@,\
                  ml' = @[%a@]@]"
             (P.fmt_ppr_lf_mctx P.l0) cD
             (P.fmt_ppr_cmp_pattern cD (compgctx_of_gctx cG) P.l0) pat_r
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
             (P.fmt_ppr_lf_mctx P.l0) cD_p
             (P.fmt_ppr_cmp_pattern cD_p cG_p P.l0) patt_p
             (P.fmt_ppr_cmp_typ cD_p P.l0) (Whnf.cnormCTyp ttau_p)
             (Prettycov.fmt_ppr_equations cD cD_p) ml'
           end;
         match_pattern (cD, cG) (cD_p, cG_p) (pat_r, ttau) (patt_p, ttau_p) ml' sl'
       end
     else
       let ml', sl' = subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml) sl in
       (ml', seqn :: sl')
  | seqn :: sl ->
     let ml', sl' = subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml) sl in
     (ml', seqn :: sl')

let rec subst_candidates (cD, cG) (pat_r, pv) =
  function
  | [] -> []
  | Cand (cD_p, cG_p, ml, sl) :: cands ->
     let cands' = subst_candidates (cD, cG) (pat_r, pv) cands in
     begin
       try
         let ml', sl' = subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml) sl in
         Cand (cD_p, cG_p, ml', sl') :: cands'
       with
         Error (_, MatchError _) -> cands'
     end

let rec best_pv_cand' (cD, cG) pvlist (l, bestC) =
  match pvlist with
  | [] -> bestC
  | x :: pvlist ->
     let cov_goals' = genPatCGoals cD cG (lookup cG x) [] in
     let l' = List.length cov_goals' in
     if l > l'
     then best_pv_cand' (cD, cG) pvlist (l', (cov_goals', x))
     else best_pv_cand' (cD, cG) pvlist (l, bestC)

let best_pv_cand (cD, cG) (x :: pvlist) =
  let cov_goals' = genPatCGoals cD cG (lookup cG x) [] in
  dprintf
    begin fun p ->
    p.fmt "[genPatCGoals] @[<v>for %a@,@[%a@]@]"
      Id.print x
      Prettycov.fmt_ppr_cov_goals cov_goals'
    end;
  let l = List.length cov_goals' in
  best_pv_cand' (cD, cG) pvlist (l, (cov_goals', x))

(* find_splitCand sl = list of pattern variables which occur in a
   splitting equation on the left and hence are potential splitting candidates
 *)

let rec pvInSplitCand sl pvlist =
  match sl with
  | [] -> pvlist
  | Split (CovGoal _, _) :: sl -> pvInSplitCand sl pvlist
  | Split (CovSub _, _) :: sl -> pvInSplitCand sl pvlist
  | SplitCtx _ :: sl -> pvInSplitCand sl pvlist
  | SplitPat ((Comp.PatFVar (_, x), ttau), (patt_p, ttau_p)) :: sl ->
     dprint
       begin fun _ ->
       "[pvInSplitCand] Patttern variable " ^ Id.render_name x
       end;
     if List.mem x pvlist
     then pvInSplitCand sl pvlist
     else pvInSplitCand sl (x :: pvlist)

let rec pvInSplitCands candidates pvlist =
  match candidates with
  | [] -> pvlist
  | Cand (_, _, _, sl) :: cands ->
     let pvlist' = pvInSplitCand sl pvlist in
     pvInSplitCands cands pvlist'

let rec refine_patt_cands ((cD, cG, candidates, patt) as cov_problem) (pvsplits, pv) =
  match pvsplits with
  | [] -> []
  | (cD', cg, ms) :: pvsplits ->
     let CovPatt (cG', pat_r, ttau) = cg in
     dprintf
       begin fun p ->
       p.fmt "[refine_patt_cands] @[<v>cD = @[%a@]@,cG = @[%a@]@,old_pat = @[%a@]@,\
              cD' = @[%a@]@,cG' = @[%a@] [ms]pat = @[%a@]@]"
         (P.fmt_ppr_lf_mctx P.l0) cD
         (P.fmt_ppr_cmp_gctx cD P.l0) (compgctx_of_gctx cG)
         (P.fmt_ppr_cmp_pattern cD (compgctx_of_gctx cG) P.l0) patt
         (P.fmt_ppr_lf_mctx P.l0) cD'
         (P.fmt_ppr_cmp_gctx cD' P.l0) (compgctx_of_gctx cG')
         (P.fmt_ppr_cmp_pattern cD' (compgctx_of_gctx cG') P.l0) (Whnf.cnormPattern (patt, ms))
       end;
     let patt' = subst_pattern (pat_r, pv) (Whnf.cnormPattern (patt, ms)) in
     dprintf
       begin fun p ->
       p.fmt "[refine_patt_cands] @[<v>new patt = @[%a@]@,ms = @[%a@]@]"
         (P.fmt_ppr_cmp_pattern cD' (compgctx_of_gctx cG') P.l0) patt'
         (P.fmt_ppr_lf_msub cD' P.l0) ms
       end;
     let candidates' = refine_candidates (cD', cG', ms) (cD, cG, candidates) in
     dprint
       begin fun _ ->
       "[refine_candidates] DONE: The remaining #refined candidates = "
       ^ string_of_int (List.length candidates')
       end;
     let candidates'' = subst_candidates (cD', cG') (pat_r, pv) candidates' in
     dprint
       begin fun _ ->
       "[subst_candidates] DONE"
       end;
     let r_cands = refine_patt_cands cov_problem (pvsplits, pv) in
     begin match candidates'' with
     | [] ->
        open_cov_problems := (cD', cG', patt') :: !open_cov_problems;
        r_cands
     | _ ->
        (cD', cG', candidates'', patt') :: r_cands
     end

let refine ((cD, cG, candidates, patt) as cov_problem) =
  match pvInSplitCands candidates [] with
  | [] ->
     dprintf
       begin fun p ->
       p.fmt "[refine] @[<v>no pattern variables to refine - refine meta-variables@,\
              cov_problem:@,@[%a@]@]"
         Prettycov.fmt_ppr_cov_problem cov_problem
       end;
     refine_mv cov_problem (* there are no pattern variables *)
  | pvlist ->  (* there are pattern variables to be split *)
     dprintf
       begin fun p ->
       p.fmt "[refine] @[<v>pattern = @[%a@]@,found %d candidates@]"
         (P.fmt_ppr_cmp_pattern cD (compgctx_of_gctx cG) P.l0) patt
         (List.length pvlist)
       end;
     let pv_splits, pv = best_pv_cand (cD, cG) pvlist in
     dprintf
       begin fun p ->
       p.fmt "[refine] @[<v>Candidates generated %d cases for:@,@[%a@]@]"
         (List.length pv_splits)
         Prettycov.fmt_ppr_cov_problem cov_problem
       end;
     let r_cands = refine_patt_cands cov_problem (pv_splits, pv) in
     dprintf
       begin fun p ->
       let open Format in
       p.fmt "[refine] @[<v>refined cov_problem:@,@[%a@]@]"
         (pp_print_list ~pp_sep: pp_print_cut Prettycov.fmt_ppr_cov_problem)
         r_cands
       end;
     r_cands

let rec check_all f =
  function
  (* iterate through l and collect all open coverage goals;
     f destructively updates open_cov_problems. *)
  | [] ->
     dprintf
       begin fun p ->
       p.fmt "*** @[<v>[COVERAGE FAILURE] THERE ARE CASE(S) NOT COVERED:@,\
              @[%a@]@]"
         Prettycov.fmt_ppr_open_cov_problems !open_cov_problems
       end
  | h :: t ->
     f h;
     check_all f t

(* At least one of the candidates in cand_list must be solvable,
   i.e. splitCand = []  and matchCand are solvable
 *)


(* check_cov_problem cov_problem = ()

   (cD, cG, candidates, cg) = cov_problem

   succeeds if there exists a candidate (Cand (cD_p, cG_p, matchCand, splitCand))
   s.t. there are no splitCand and all matchCand can we solved using unification.

   otherwise

   will try to refine the given candidates and check coverage again.


   if there are candidates where there are no splitCandidate but matchCand
   cannot be solved, then add them to open_cov_problems, i.e. objects which are
   not covered.

 *)
let rec check_cov_problem cov_problem =
  let cD, cG, candidates, cg = cov_problem in
  (* existsCandidate candidates nCands open_cg
      Tries to see whether a given candidate is true, i.e.
      the pattern covers cg.

      If the pattern covers cg, coverage succeeds
      If the pattern does not cover cg, we add it to the open goals
      If the pattern does not YET cover cg, but it possibly can
      in the future, we extend nCands, the list of new candidates to consider.

   *)
  let rec existsCandidate candidates nCands open_cg =
    match candidates with
    | [] ->
       let cov_prob' = (cD, cG, nCands, cg) in
       open_cov_problems := open_cg @ !open_cov_problems;
       dprint
         begin fun _ ->
         "[existsCandidate] refining variables since candidates have been processed"
         end;
       let cp = refine cov_prob' in
       (* Refine must make progress, i.e. cp =/= cov_problem,
          i.e. nCands must be different from the candidates of the original
          coverage problem *)
       dprintf
         begin fun p ->
         p.fmt "[existsCandidate] @[<v>check coverage (again) for:@,@[%a@]@]"
           Prettycov.fmt_ppr_cov_problems cp
         end;
       check_coverage cp

    | ((Cand (cD_p, cG_p, matchCand, splitCand)) as c) :: cands ->
       begin match splitCand with
       | [] ->
          dprintf
            begin fun p ->
            p.fmt "[check_cov_problem] @[<v>CHECK WHETHER@,  @[%a@]@,IS COVERED?@]"
              (P.fmt_ppr_cmp_pattern cD (compgctx_of_gctx cG) P.l0) cg
            end;
          let s_result = solve cD cD_p matchCand in
          begin match s_result, U.unresolvedGlobalCnstrs () with
          (* No new splitting candidates and all match
             candidates are satisfied *)
          | Solved, false ->
             dprintf
               begin fun p ->
               p.fmt "[check_cov_problem] @[<v>COVERED@,@[%a@]@]"
                 (P.fmt_ppr_cmp_pattern cD (compgctx_of_gctx cG) P.l0) cg
               end;
             (* Coverage succeeds *)
             ()

          (* No new splitting candidates, but leftover constraints *)
          | Solved, true ->
             (* Coverage Fails *)
             let open_goal = (cD, cG, cg) in
             existsCandidate cands nCands (open_goal::open_cg)

          | PossSolvable cand, _ ->
             dprintf
               begin fun p ->
               p.fmt "#### (A) @[<v>NOT COVERED YET BUT THERE IS HOPE AND WE CAN SPLIT ON@,@[%a@]@]"
                 (Prettycov.fmt_ppr_candidate (cD, compgctx_of_gctx cG)) c
               end;
             (* Some equations in matchCand cannot be solved by hounif;
                 they will be resurrected as new splitting candidates *)
             existsCandidate cands (cand :: nCands) open_cg

          (* match candidates were not solvable;
             this candidate gives rise to coverage failure *)
          | NotSolvable, _ ->
             (* Coverage Fails *)
             dprintf
               begin fun p ->
               p.fmt "**** (B) @[<v>THE FOLLOWING CANDIDATE IS NOT COVERED@,@[%a@]@]"
                 (Prettycov.fmt_ppr_candidate (cD, compgctx_of_gctx cG)) c
               end;
             let open_goal = (cD, cG, cg) in
             (* open_cov_problems := ((cO, cD), cPhi,  tM)::!open_cov_problems; *)
             existsCandidate cands nCands (open_goal :: open_cg)
          end
       | _ -> existsCandidate cands (c :: nCands) open_cg
       end
  in
  existsCandidate candidates [] []

and check_coverage (cov_problems : cov_problems) =
  check_all (function cov_prob -> check_cov_problem cov_prob) cov_problems


(* ****************************************************************************** *)

(* Flags *)
let enableCoverage = ref false (* true iff coverage should be checked *)
let warningOnly = ref false (* true iff failed coverage should generate a warning *)
let no_covers = ref 0 (* number of times coverage checking has yielded a negative result *)

(* ****************************************************************************** *)

let rec extract_patterns tau =
  function
  | Comp.Branch (loc, cD, cG, Comp.PatAnn (loc', pat, _), ms, e) ->
     extract_patterns tau (Comp.Branch (loc, cD, cG, pat, ms, e))

  | Comp.Branch (loc, cD, cG, pat, ms, _) ->
     (cD, GenPatt (cG, pat, (tau, ms)))

let rec gen_candidates loc cD covGoal =
  function
  | [] -> []
  | (cD_p, GenPatt (cG_p, pat, ttau)) :: plist ->
     let CovPatt (cG', pat', ttau') = covGoal in
     dprintf
       begin fun p ->
       p.fmt "[gen_candidates] @[<v>pat = @[%a@]@,pat' = @[%a@]@]"
         (P.fmt_ppr_cmp_pattern cD_p cG_p P.l0) pat
         (P.fmt_ppr_cmp_pattern cD_p (compgctx_of_gctx cG') P.l0) pat'
       end;
     let ml, sl = match_pattern (cD, cG') (cD_p, cG_p) (pat', ttau') (pat, ttau) [] [] in
     Cand (cD_p, cG_p, ml, sl) :: gen_candidates loc cD covGoal plist

let initialize_coverage problem projOpt : cov_problems =
  match problem.ctype with
  | Comp.TypBox (loc, LF.CTyp w) ->
     let cD' = LF.Dec (problem.cD, LF.Decl (Id.mk_name (Whnf.newMTypName (LF.CTyp w)), LF.CTyp w, LF.Maybe)) in
     let cG' = cnormCtx (problem.cG, LF.MShift 1) in
     let cPsi = LF.CtxVar (LF.CtxOffset 1) in
     (* let covGoal = CovPatt (LF.Empty, Comp.PatMetaObj (loc, LF.CObj cPsi)) in *)
     let mC = Comp.PatMetaObj (Loc.ghost, (Loc.ghost, LF.CObj cPsi)) in
     let mT = Comp.TypBox (loc, LF.CTyp w) in
     let covGoal = CovPatt ([], mC, (mT, LF.MShift 0)) in
     let pat_list = List.map (fun b -> extract_patterns problem.ctype b) problem.branches in
     let cand_list = gen_candidates problem.loc cD' covGoal pat_list in
     [(cD', cG', cand_list, mC)]

  | Comp.TypBox (loc, LF.ClTyp (LF.MTyp tA, cPsi)) ->
     (* If the coverage is for a box-type, we need to see whether
        the case analysis was on a normal LF object. If it isn't then
        we create a new variable as the initial term we
        refine. Otherwise we start from the case's scrutinee, which we
        received through problem.m_obj.
      *)
     begin match problem.m_obj with
     | None ->
        let s, (cPsi', tA') = gen_str problem.cD cPsi tA in
        (* cPsi |- s  : cPsi' *)
        dprintf
          begin fun p ->
          p.fmt "[initialize_coverage] @[<v>not using case scrutinee@,\
                 @[%a@]@]"
            P.fmt_ppr_lf_sub_typing (problem.cD, cPsi, s, cPsi')
          end;
        let mT = LF.ClTyp (LF.MTyp tA', cPsi') in
        let name = Id.mk_name (Whnf.newMTypName mT) in
        let cD' = LF.Dec (problem.cD, LF.Decl (name, mT, LF.Maybe)) in
        let cG' = cnormCtx (problem.cG, LF.MShift 1) in
        let mv = LF.MVar (LF.Offset 1, s) in
        let tM = LF.Root (Loc.ghost, mv, LF.Nil) in
        let cPsi = Whnf.cnormDCtx (cPsi, LF.MShift 1) in
        let tA = Whnf.cnormTyp (tA, LF.MShift 1) in
        let mC = Comp.PatMetaObj (Loc.ghost, (loc, LF.ClObj (Context.dctxToHat cPsi, LF.MObj tM))) in
        let mT = Comp.TypBox (loc, LF.ClTyp (LF.MTyp tA, cPsi)) in
        let covGoal = CovPatt ([], mC, (mT, LF.MShift 0)) in

        dprintf
          begin fun p ->
          p.fmt "[initialize_coverage] @[<v>cD' = @[%a@]@,mC = @[%a@]@]"
            (P.fmt_ppr_lf_mctx P.l0) cD'
            (P.fmt_ppr_cmp_pattern cD' (compgctx_of_gctx cG') P.l0) mC
          end;
        let pat_list = List.map (extract_patterns problem.ctype) problem.branches in
        let cand_list = gen_candidates problem.loc cD' covGoal pat_list in
        [(cD', cG', cand_list, mC)]

     | Some m_obj ->
        dprint
          begin fun _ ->
          "[initialize_coverage] using case scrutinee"
          end;
        let mC = Comp.PatMetaObj (Loc.ghost, m_obj) in
        let covGoal = CovPatt ([], mC, (problem.ctype, LF.MShift 0)) in
        let pat_list = List.map (extract_patterns problem.ctype) problem.branches in
        let cand_list = gen_candidates problem.loc problem.cD covGoal pat_list in
        [(problem.cD, problem.cG, cand_list, mC)]
     end

  | Comp.TypBox (loc, LF.ClTyp (LF.PTyp tA, cPsi)) ->
     let s, (cPsi', tA') = gen_str problem.cD cPsi tA in
     let mT = LF.ClTyp (LF.PTyp tA', cPsi') in
     let cD' = LF.Dec (problem.cD, LF.Decl (Id.mk_name (Whnf.newMTypName mT),  mT, LF.Maybe)) in
     let cG' = cnormCtx (problem.cG, LF.MShift 1) in
     let mv =
       match projOpt with
       | None -> LF.PVar (1, s)
       | Some k -> LF.Proj (LF.PVar (1, s), k)
     in
     let tM = LF.Root (Loc.ghost, mv, LF.Nil) in
     let cPsi = Whnf.cnormDCtx (cPsi, LF.MShift 1) in
     let tA = Whnf.cnormTyp (tA, LF.MShift 1) in
     let mC = Comp.PatMetaObj (Loc.ghost, (Loc.ghost, LF.ClObj (Context.dctxToHat cPsi, LF.MObj tM))) in
     let mT = Comp.TypBox (loc, LF.ClTyp (LF.PTyp tA, cPsi)) in
     let covGoal = CovPatt ([], mC, (mT, LF.MShift 0)) in
     let pat_list = List.map (fun b -> extract_patterns problem.ctype b) problem.branches in
     let cand_list = gen_candidates problem.loc cD' covGoal pat_list in
     [(cD', cG', cand_list, mC)]

  | Comp.TypBox (loc, ((LF.ClTyp (LF.STyp (r, cPhi), cPsi)) as mT)) ->
     let cD' = LF.Dec (problem.cD, LF.Decl (Id.mk_name (Whnf.newMTypName mT),  mT, LF.Maybe)) in
     let cG' = cnormCtx (problem.cG, LF.MShift 1) in
     let s = LF.SVar (1, 0, S.LF.id) in
     let cPhi = Whnf.cnormDCtx (cPhi, LF.MShift 1) in
     let cPsi = Whnf.cnormDCtx (cPsi, LF.MShift 1) in
     let mC = Comp.PatMetaObj (Loc.ghost, (Loc.ghost, LF.ClObj (Context.dctxToHat cPhi, LF.SObj s))) in
     let mT = Comp.TypBox (loc, ((LF.ClTyp (LF.STyp (r, cPhi), cPsi)))) in
     let covGoal = CovPatt ([], mC, (mT, LF.MShift 0)) in

     let pat_list = List.map (fun b -> extract_patterns problem.ctype b) problem.branches in

     let cand_list = gen_candidates problem.loc cD' covGoal pat_list in

     [(cD', cG', cand_list, mC)]


  (* tau := Bool | Cross (tau1, tau2) | U *)
  | tau ->
     let pv = NameGenerator.new_patvar_name () in
     let cG' = (pv, tau, false) :: problem.cG in
     let pat = Comp.PatFVar (Loc.ghost, pv) in
     let pat_list = List.map (fun b -> extract_patterns problem.ctype b) problem.branches in
     let covGoal = CovPatt (cG', pat, (problem.ctype, Whnf.m_id)) in
     let cand_list = gen_candidates problem.loc problem.cD covGoal pat_list in
     [ (problem.cD, cG', cand_list, pat) ]

(* check_emptiness cD = bool
   if for all declarations X:U in cD such that
   splitting on X yields no candidates
 *)
let rec check_emptiness =
  function
  | LF.Empty -> false
  | LF.Dec (cD', (LF.Decl (_, LF.ClTyp (LF.MTyp tA, cPsi), _) as cdecl)) ->
     begin
       try
         match genCovGoals (cD', cPsi, Whnf.normTyp (tA, S.LF.id)) with
         | [] ->
            dprintf
              begin fun p ->
              p.fmt "[check_emptiness] @[%a@] is empty"
                (P.fmt_ppr_lf_ctyp_decl cD' P.l0) cdecl
              end;
            true
         | _ -> check_emptiness cD'
       with
       | Abstract.Error (_, msg) ->
          let open Format in
          fprintf std_formatter
            "@[<v>Unable to prove %a to be empty@,Trying next metavariable.@]@."
            (P.fmt_ppr_lf_typ cD' cPsi P.l0) tA;
          check_emptiness cD'
     end
  | LF.Dec (cD', LF.Decl (_,  LF.ClTyp (LF.PTyp LF.Sigma _, _), _)) ->
     check_emptiness cD'
  | LF.Dec (cD', LF.Decl (_,  LF.ClTyp (LF.PTyp tA, cPsi), _)) ->
     begin
       try
         match genBCovGoals (cD', cPsi, Whnf.normTyp (tA, S.LF.id)) with
         | [] -> true
         | _ -> check_emptiness cD'
       with
       | Abstract.Error (_, msg) ->
          print_string "Unable to prove given type is empty\n"; check_emptiness cD'
     end

  | LF.Dec (cD', LF.Decl _) -> check_emptiness cD'

let rec check_empty_comp cD =
  function
  | [] -> false
  | (_, tau, _)::cG ->
     begin
       try
         let cov_goals' = genPatCGoals cD cG tau [] in
         match cov_goals' with
         | [] -> true
         | _ -> check_empty_comp cD cG
       with
       | _ -> check_empty_comp cD cG
     end

let rec revisit_opengoals : open_cov_problems -> open_cov_problems * open_cov_problems =
  function
  | [] -> ([], [])
  | ((cD, cG, _) as og) :: ogoals ->
     dprintf
       begin fun p ->
       p.fmt "REVISIT OPEN GOAL: %a"
         Prettycov.fmt_ppr_open_cov_problem og
       end;
     U.resetGlobalCnstrs ();
     match () with
     | _ when check_emptiness cD ->
        dprintf
          begin fun p ->
          p.fmt "[revisit_opengoals] cD = @[%a@]"
            (P.fmt_ppr_lf_mctx P.l0) cD
          end;
        let oglist, trivial_list = revisit_opengoals ogoals in
        (oglist, og::trivial_list)
     | _ when check_empty_comp cD cG ->
        dprintf
          begin fun p ->
          p.fmt "[revisit_opengoals] cG = @[%a@]"
            (P.fmt_ppr_cmp_gctx cD P.l0) (compgctx_of_gctx cG)
          end;
        let oglist, trivial_list = revisit_opengoals ogoals in
        (oglist, og::trivial_list)
     | _ ->
        let oglist, trivial_list = revisit_opengoals ogoals in
        (og :: oglist, trivial_list)

let check_coverage_success problem =
  match problem.prag with
  | Comp.PragmaCase ->
     if !open_cov_problems = []
     then
       begin
         dprint
           begin fun _ ->
           "\n ###### COVERS ####### \n"
           end;
         Success
       end
     else
       let s =
         let open Format in
         fprintf str_formatter "@[<v>CASE(S) NOT COVERED:@,@[%a@]@]"
           Prettycov.fmt_ppr_open_cov_problems !open_cov_problems;
         flush_str_formatter ()
       in
       (* Check if the open coverage goals can be proven to be impossible *)
       Failure s

  | Comp.PragmaNotCase ->
     let open Format in
     if !open_cov_problems = []
     then
       Failure
         (fprintf str_formatter
            "\n##   Case expression covers : ##\n##   %a\n##\n\n"
            Loc.print problem.loc;
          flush_str_formatter ())
     else
       begin
         fprintf std_formatter
           "\n##   Case expression doesn't cover, consistent with \"case ... of %%not\" ##\n##   %a\n##   CASE(S) NOT COVERED :\n%a\n\n"
           Loc.print problem.loc
           Prettycov.fmt_ppr_open_cov_problems !open_cov_problems;
         Success
       end

let covers' problem projObj =
  dprintf
    begin fun p ->
    p.fmt "@[<hv>#################################@,### BEGIN COVERAGE FOR TYPE tau = %a@,at %a@]"
      (P.fmt_ppr_cmp_typ problem.cD P.l0) problem.ctype
      Loc.print problem.loc
    end;
  U.resetGlobalCnstrs ();
  let cov_problems = initialize_coverage problem projObj in
  dprintf
    begin fun p ->
    p.fmt "@[<v>Coverage checking a case with %d branch(es)@,at: %a@]"
      (List.length problem.branches)
      Loc.print problem.loc
    end;
  dprintf
    begin fun p ->
    p.fmt "### @[<v>Initial coverage problem:@,@[%a@]@]"
      Prettycov.fmt_ppr_cov_problems cov_problems
    end;
  try
    check_coverage cov_problems;
    dprint
      begin fun _ ->
      "*** !!! COVERAGE CHECKING COMPLETED – Check whether some open coverage goals are trivial. !!!***"
      end;
    dprintf
      begin fun p ->
      p.fmt "*** @[<v>!!! REVISIT :@,@[%a@]"
        Prettycov.fmt_ppr_open_cov_problems !open_cov_problems
      end;
    let o_cg = !open_cov_problems in
    let revisited_og, trivial_og = revisit_opengoals o_cg in
    open_cov_problems := revisited_og;
    check_coverage_success problem
  with
  | Error (_, NothingToRefine) ->
     check_coverage_success problem

(* covers problem = ()

   problem = { loc: loc
             ; prag : pragma
             ; cD : LF.mctx
             ; cG
             ; branches
             ; ctype : tau
             }

   where cD; cPsi |- tA

   Succeeds, if there is at least one pattern which covers elements of type tau
   Fails, otherwise
 *)
let covers problem projObj =
  (* this entry point does some basic checks, i.e. that coverage is
     actually enabled, and that the problem isn't completely trivial.
     Nontrivial coverage problems are discharged to the main function
     covers'.
   *)
  if !Total.enabled || !enableCoverage
  then
    if TrivialCoverageChecker.check problem.cD problem.cG problem.ctype problem.branches
    then
      begin
        (* print_string "Trival Coverage\n"; *)
        Success
      end
    else
      covers' problem projObj
  else
    Success

let is_impossible cD tau =
  [] = genPatCGoals cD [] tau []

let process problem projObj =
  reset_open_cov_problems ();
  match covers problem projObj with
  | Success -> NameGenerator.reset_generator ()
  | Failure message ->
     NameGenerator.reset_generator ();
     if !warningOnly
     then
       begin
         print_string "WARNING: CASES DID NOT COVER\n";
         Error.addInformation ("WARNING: Cases didn't cover: " ^ message)
       end
     else
       raise (Error (problem.loc, NoCover message))

let problems = ref ([] : problem list)
(*
let clear () =
  problems := []

let stage problem =
  problems := problem::!problems
 *)
let map f =
  List.map (fun problem -> f (covers problem None)) (List.rev !problems)

let iter (f : coverage_result -> unit) : unit =
  List.iter (fun problem -> f (covers problem None)) (List.rev !problems)
