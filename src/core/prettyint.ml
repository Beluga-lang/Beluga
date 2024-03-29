open Support
open Format
open Beluga_syntax
open Synint

let (_, _, dprnt) = Debug.(makeFunctions' (toFlags [17]))

module PC = Printer.Control

(* FIXME(Marc-Antoine): Pretty-printing of the internal syntax is not
   implemented correctly for various reasons.

   Name generation: The generation of fresh variable names is required to go
   from a nameless representation to a named representation. At a given binder,
   for instance [\_. tM], one needs to determine what are the identifiers
   used in [tM] to avoid capture. For instance, the variable name [x] and the
   constant name [s] cannot be used as the parameter in [\x. \_. s x tM']. This
   requires the complete referencing environment (i.e., the bindings in scope
   at that point in the program, like during indexing {!module:Index}) in order
   to resolve the constants and offsets in [tM] to names already decided, and
   a traversal of [tM] to collect those used constants and offsets.
   Additionally, in order to respect the order of declaration for name
   generation conventions (using the [--name] pragma), the referencing
   environment has to attach those conventions to the appropriate constant,
   and use the conventions in a type-driven manner.

   Erasure: Reconstructed arguments passed to reconstructed or implicit
   abstractions need to be erased. Reconstructed abstractions are the
   abstractions introduced during signature reconstruction for free variables
   in the user's program. In contrast, implicit abstractions are textually
   specified by the user. If the user can interleave implicit and
   explicit abstractions (like [(g:...) {M:...} (N:...) P]), then we have
   to annotate the argument nodes with a flag indicating that the argument was
   reconstructed. Otherwise, we can just lookup the number of expected explicit
   arguments from the store for a given constant, and remove the first few
   arguments introduced by reconstruction. Properly implementing this will
   require disentangling the plicity flags (implicit/explicit) from the
   reconstructed flags (reconstructed/user-specified) in the internal syntax
   throughout signature reconstruction. There are also known instances of bugs
   where inductivity flags affect plicity flags for some reason.

   Minimal parenthesizing: Parentheses should only be introduced during
   pretty-printing as necessary for the parser to be able to re-parse the
   program. This requires taking into account the precedence, fixity and
   associativity of both user-defined and static operators. This is properly
   implemented for the external syntax {!module:Beluga_syntax.Synext}.


   Overall, pretty-printing of the internal syntax is inherently stateful with
   respect to the Beluga signature, and cannot be implemented before the issues
   with erasure are fixed. This also poses a bigger problem in that stateful
   pretty-printing makes it harder to report types in error messages, and makes
   it impossible to trace the execution of functions with debug statements.
   Arguably, uses of the internal syntax pretty-printer for debugging are
   misleading.

   The approach I'm thinking of to implementing pretty-printing is to first
   translate programs from the internal syntax to the external syntax, then to
   use the already implemented external syntax pretty-printer. This takes care
   of the minimal parenthesizing problem, and guarantees that printed programs
   will parse.

   The translation from the internal syntax to the external syntax may proceed
   as in the following pseudo-code. This translation is type-directed and in
   an inner and an outer phase:

   + The inner phase constructs translator closures that compute the set of
     constant IDs and variable offsets used by the expression to translate.
   + The outer phase traverses the signature to construct the referencing
     environment, and calls the inner phase to perform the translation.

   {[
     type used_constants of {
       used_lf_type_constants : Int.Set.t;
       used_lf_term_constants : Int.Set.t;
       ...
     }

     type used_offsets of {
       used_lf_offsets : Int.Set.t;
       used_meta_offsets : Int.Set.t;
       used_comp_offsets : Int.Set.t;
     }

     type free_variables = Identifier.Set.t

     type used_names_state = used_constants * used_offsets * free_variables

     type referencing_environment = ... (* Like the indexing state, but keeps
        track of name convention pragmas and all visible aliases for each
        constant. *)

     let unshift_offsets (offsets : Int.Set.t) =
       offsets
       |> Int.Set.map (fun offset -> offset - 1)
       |> Int.Set.remove 0 (* Non-positive offsets are out of scope *)

     let unshift_lf_offsets : used_names_state -> used_names_state = ...

     let rec lf_term_translator
         (tM : LF.normal)
         (tA : LF.typ (* For type-driven name generation *))
         : used_names_state * (referencing_environment -> Synext.lf_term) =
       match (tM, tA) with
       | Int.LF.Lam (location, _param, body), Int.LF.PiTyp (_decl, body_typ) ->
           let (body_names, body_translator) =
             lf_term_translator body body_typ
           in
           let lam_translator state =
             let variable = fresh_name state body_names body_typ in
             let body' =
               with_bound_lf_variable state variable body_translator
             in
             Synext.LF.Term.Abstraction
               { location
               ; parameter_identifier = Option.some variable
               ; parameter_type = Option.none
               ; body = body'
               }
           in
           let lam_names = unshift_lf_offsets body_names in
           (lam_names, lam_translator)
       | ...
   ]} *)

let ident_regexp = Str.regexp {|[^"].*|}

(** [is_name_syntactically_valid name] is a heuristic for determining whether
    [name] is syntactically valid. If that is not the case, then the name
    must not have been user-defined, so it was generated during signature
    reconstruction. *)
let is_name_syntactically_valid name =
  Str.string_match ident_regexp (Name.string_of_name name) 0

(* Internal Syntax Pretty Printer Functor *)
module Make (R : Store.Cid.RENDERER) : Printer.Int.T = struct
  type lvl = int
  let l0 = 0

  let print_wf_tag ppf : bool -> unit =
    function
    | true -> fprintf ppf "*"
    | false -> ()

  let l_paren_if cond =
    if cond
    then "("
    else ""

  let r_paren_if cond =
    if cond
    then ")"
    else ""

  let fmt_ppr_lf_svar_class ppf : LF.svar_class -> unit =
    function
    | LF.Ren -> fprintf ppf "#"
    | LF.Subst -> ()

  type depend_print_style =
    [ `depend
    | `inductive
    | `clean
    ]

  let fmt_ppr_plicity ppf =
    function
    | Plicity.Implicit -> pp_print_string ppf "implicit"
    | Plicity.Explicit -> pp_print_string ppf "explicit"

  let fmt_ppr_lf_depend_clean ppf _ = ()

  let fmt_ppr_lf_depend_inductive ppf =
    function
    | Inductivity.Not_inductive -> pp_print_string ppf ""
    | Inductivity.Inductive -> pp_print_string ppf "*"

  let fmt_ppr_lf_depend ppf =
    function
    | Plicity.Implicit, Inductivity.Not_inductive -> pp_print_string ppf "^i"
    | Plicity.Explicit, Inductivity.Not_inductive -> pp_print_string ppf "^e"
    | Plicity.Implicit, Inductivity.Inductive -> pp_print_string ppf "*i"
    | Plicity.Explicit, Inductivity.Inductive -> pp_print_string ppf "*e"

  let fmt_ppr_cmp_split_kind ppf =
    function
    | `split -> fprintf ppf "split"
    | `invert -> fprintf ppf "invert"
    | `impossible -> fprintf ppf "impossible"

  let fmt_ppr_cmp_context_case ppf =
    function
    | Comp.EmptyContext _ -> fprintf ppf "empty context"
    | Comp.ExtendedBy (_, k) ->
      fprintf ppf "@[<hov 2>extended by %d@]" k

  (* Fresh name generation *)

  let rec get_names_dctx : LF.dctx -> Name.t list =
    function
    | LF.Null -> []
    | LF.CtxVar psi -> []
    | LF.DDec (cPsi', LF.TypDecl (n, _))
      | LF.DDec (cPsi', LF.TypDeclOpt n) ->
       n :: get_names_dctx cPsi'

  let fresh_name_dctx (cPsi : LF.dctx) : Name.t -> Name.t =
    Name.gen_fresh_name (get_names_dctx cPsi)
  let fresh_name_mctx (cD : LF.mctx) : Name.t -> Name.t =
    Name.gen_fresh_name (Context.names_of_mctx cD)
  let fresh_name_gctx (cG : Comp.gctx) : Name.t -> Name.t =
    Name.gen_fresh_name (Context.names_of_gctx cG)

  let fresh_name_ctyp_decl (cD: LF.mctx) : LF.ctyp_decl -> LF.ctyp_decl =
    LF.rename_ctyp_decl (fun name -> fresh_name_mctx cD name)

  (** Prints a context.
      Prints each element of the context from left to right with the
      given separator between entries, and using the provided function
      to print an entry.
      The given predicate decides whether an entry should be printed.
      The given printing function receives the subcontext (to the left
      of the entry) plus the entry itself.
   *)
  let fmt_ppr_ctx_filter : 'a. ?sep:(formatter -> unit -> unit) -> ('a LF.ctx * 'a -> bool) -> (formatter -> 'a LF.ctx * 'a -> unit) -> formatter -> 'a LF.ctx -> unit =
    (* the type has to be written in this horrible way to keep OCaml
       from unnecessarily monomorphizing it. *)
    fun ?(sep = pp_print_space) p f ppf ctx ->
    pp_print_list ~pp_sep: sep f ppf (Context.to_sublist ctx |> List.filter p)

  (* Contextual Format Based Pretty Printers
   *
   * We assume types, terms, etc are all in normal form.
   *)

  let rec fmt_ppr_lf_typ cD cPsi lvl ppf =
    function
    | LF.Atom (_, a, LF.Nil) ->
       fprintf ppf "%s"
         (R.render_cid_typ a)

    | LF.Atom (_, a, ms) ->
       let cond = lvl > 1 in
       let Store.Cid.Typ.Entry.({ implicit_arguments = k; _ }) = Store.Cid.Typ.get a in
       let ms =
         (* drop implicits *)
         if !PC.printImplicit
         then ms
         else LF.drop_spine k ms
       in
       fprintf ppf "%s@[<hov 2>%s@ @[<hov>%a@]@]%s"
         (l_paren_if cond)
         (R.render_cid_typ a)
         (fmt_ppr_lf_spine cD cPsi 2) ms
         (r_paren_if cond)

    | LF.PiTyp ((LF.TypDecl (x, a), (Depend.Yes | Depend.Maybe), Plicity.Explicit), b) ->
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "@[<1>%s{%a : %a}@ %a%s@]"
         (l_paren_if cond)
         Name.pp x
         (fmt_ppr_lf_typ cD cPsi 0) a
         (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, a))) 0) b
         (r_paren_if cond)

    | LF.PiTyp ((LF.TypDecl (x, a), (Depend.Yes | Depend.Maybe), Plicity.Implicit), b) ->
       (* FIXME(Marc-Antoine): There is technically no syntax for implicit Pi-types *)
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "@[<1>%s(%a : %a)@ %a%s@]"
         (l_paren_if cond)
         Name.pp x
         (fmt_ppr_lf_typ cD cPsi 0) a
         (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, a))) 0) b
         (r_paren_if cond)

    | LF.PiTyp ((LF.TypDecl (x, a), Depend.No, _), b) ->
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

  and fmt_ppr_lf_tuple cD cPsi lvl ppf =
    function
    | LF.Last tM ->
       fmt_ppr_lf_normal cD cPsi lvl ppf tM

    | LF.Cons(tM, rest) ->
       fprintf ppf "%a; %a"
         (fmt_ppr_lf_normal cD cPsi lvl) tM
         (fmt_ppr_lf_tuple cD cPsi lvl) rest

  and fmt_ppr_lf_operator cD cPsi ppf (fixity, name, spine) =
    match fixity with
    | Fixity.Prefix ->
       fmt_ppr_lf_prefix_operator cD cPsi ppf (name, spine)
    | Fixity.Postfix ->
       fmt_ppr_lf_postfix_operator cD cPsi ppf (name, spine)
    | Fixity.Infix ->
       fmt_ppr_lf_infix_operator cD cPsi ppf (name, spine)

  and fmt_ppr_lf_prefix_operator cD cPsi ppf =
    function
    | name, LF.(App (m, Nil)) ->
       fprintf ppf "%a %a"
         Name.pp name
         (fmt_ppr_lf_normal cD cPsi 2) m
    | _ ->
       Error.raise_violation
         "[fmt_ppr_lf_prefix_operator] spine length <> 1"

  and fmt_ppr_lf_postfix_operator cD cPsi ppf =
    function
    | name, LF.(App (m, Nil)) ->
       fprintf ppf "%a %a"
         (fmt_ppr_lf_normal cD cPsi 2) m
         Name.pp name
    | _ ->
       Error.raise_violation
         "[fmt_ppr_lf_postfix_operator] spine length <> 1"

  and fmt_ppr_lf_infix_operator cD cPsi ppf =
    function
    | name, LF.(App (m1, App (m2, Nil))) ->
       fprintf ppf "%a %a %a"
         (fmt_ppr_lf_normal cD cPsi 2) m1
         Name.pp name
         (fmt_ppr_lf_normal cD cPsi 2) m2
    | _ ->
       Error.raise_violation
         "[fmt_ppr_lf_infix_operator] spine length <> 2"

  and fmt_ppr_lf_normal cD cPsi lvl ppf =
    let deimplicitize_spine h ms =
      match h with
      | _ when !PC.printImplicit -> ms
      | LF.Const c ->
         LF.drop_spine (Store.Cid.Term.get_implicit_arguments c) ms
      | _ -> ms
    in
    function
    | LF.Lam (_, x, m) ->
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "%s@[<hov 2>\\%a.@ @[%a@]@]%s"
         (l_paren_if cond)
         Name.pp x
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
          begin match w with
          | CompInfo -> Error.raise_violation "expected LFHole; got comp hole"
          | LFInfo ->
             let { lfSolution; cPsi; _ } = h.info in
             begin match lfSolution with
             | None ->
                fprintf ppf "?%s" name
             | Some sM ->
                fprintf ppf "%a" (fmt_ppr_lf_normal cD cPsi l0) (Whnf.norm sM)
             end
          end
       end
    | LF.Tuple (_, tuple) ->
       fprintf ppf "<%a>"
         (fmt_ppr_lf_tuple cD cPsi lvl) tuple

    | LF.Clo(tM, s) ->
       fmt_ppr_lf_normal cD cPsi lvl ppf (Whnf.norm (tM, s))

    | LF.Root (_, _, _, Plicity.Implicit) when Bool.not !PC.printImplicit ->
       fprintf ppf "_" (* FIXME: what to do about spines? -je *)

    | LF.Root (_, h, LF.Nil, _) ->
       fprintf ppf "%a" (fmt_ppr_lf_head cD cPsi lvl) h

    | LF.(Root (_, (Const cid as h), ms, _)) ->
       let ms = deimplicitize_spine h ms in
       let Store.Cid.Term.Entry.({ name; _ }) = Store.Cid.Term.get cid in
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
            (fmt_ppr_lf_spine cD cPsi 2) ms
            (r_paren_if cond)
       end
    | LF.Root (_, h, ms, _) ->
       let ms = deimplicitize_spine h ms in
       let cond = lvl > 1 in
       fprintf ppf "%s%a %a%s"
         (l_paren_if cond)
         (fmt_ppr_lf_head cD cPsi lvl) h
         (fmt_ppr_lf_spine cD cPsi 2) ms
         (r_paren_if cond)

  and fmt_ppr_lf_head cD cPsi lvl ppf head =
    let paren s =
      Bool.not (PC.db()) && lvl > 0
      && match s with
         | LF.EmptySub | LF.Undefs -> false
         | LF.Shift _ when Bool.not (Context.hasCtxVar cPsi) -> false
         | _ -> true
    in
    let rec fmt_head_with proj =
      function
      | LF.HClo (h, s, sigma) ->
         fprintf ppf "%s[%a[%a]]"
           (R.render_bvar cPsi h)
           (fmt_ppr_lf_offset cD) s
           (fmt_ppr_lf_sub cD cPsi lvl) sigma
      | LF.HMClo (h, ((s, theta), sigma)) ->
         fprintf ppf "%s[%a[%a ; %a]]"
           (R.render_bvar cPsi h)
           (fmt_ppr_lf_mmvar lvl) s
           (fmt_ppr_lf_msub cD lvl) theta
           (fmt_ppr_lf_sub cD cPsi lvl) sigma
      | LF.BVar x ->
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
           (fmt_ppr_lf_sub cD cPsi lvl) s
           (r_paren_if (paren s))

      | LF.MPVar ((c, ms), s) ->
         fprintf ppf "%s%a%s[%a][%a]%s"
           (l_paren_if (paren s))
           (fmt_ppr_lf_mmvar lvl) c
           proj
           (fmt_ppr_lf_msub cD lvl) ms
           (fmt_ppr_lf_sub cD cPsi lvl) s
           (r_paren_if (paren s))

      | LF.MVar(c, LF.Undefs)
        | LF.MVar(c, LF.EmptySub) ->
         let f =
           if Context.is_null cPsi
           then
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
         if Substitution.LF.isId s
         then
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
         if Substitution.LF.isId s
         then
           fprintf ppf "%a%s"
             (fmt_ppr_lf_offset cD) c
             proj
         else
           fprintf ppf "%s%a%s[%a]%s"
             (l_paren_if (paren s))
             (fmt_ppr_lf_offset cD) c
             proj
             (fmt_ppr_lf_sub cD cPsi lvl) s
             (r_paren_if (paren s))

      | LF.FVar x ->
         fprintf ppf "%a%s"
           Name.pp x
           proj

      | LF.FMVar (u, s) ->
         fprintf ppf "FMV %s%a%s[%a]%s"
           (l_paren_if (paren s))
           Name.pp u
           proj
           (fmt_ppr_lf_sub cD cPsi lvl) s
           (r_paren_if (paren s))

      | LF.FPVar (p, s) ->
         fprintf ppf "%sFPV %a%s[%a]%s"
           (l_paren_if (paren s))
           Name.pp p
           proj
           (fmt_ppr_lf_sub cD cPsi lvl) s
           (r_paren_if (paren s))

      | LF.Proj (head, k) ->
         fmt_head_with ("." ^ string_of_int k) head

    in
    fmt_head_with "" head


  and fmt_ppr_lf_spine cD cPsi lvl ppf =
    function
    | LF.Nil -> ()
    | LF.App(m, LF.Nil) ->
       fprintf ppf "@[%a@]"
         (fmt_ppr_lf_normal cD cPsi (lvl + 1)) m
    | LF.App (m, ms) ->
       fprintf ppf "@[%a@]@ @[%a@]"
         (fmt_ppr_lf_normal cD cPsi (lvl + 1)) m
         (fmt_ppr_lf_spine cD cPsi lvl) ms
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
    (* FIXME: O(n^2) algorithm below.
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
         [fun ppf _ -> Name.pp ppf x]
      | LF.DDec (cPsi', LF.TypDecl (x, _))
        | LF.DDec (cPsi', LF.TypDeclOpt x) ->
         prepare_lf_sub_id cPsi' @ [fun ppf _ -> Name.pp ppf x]
    in
    let rec fmt_ppr_lf_sub_shift ppf (cPsi, n) = match cPsi, n with
      | _, 0 -> prepare_lf_sub_id cPsi
      | LF.DDec (cPsi', _), n -> fmt_ppr_lf_sub_shift ppf (cPsi', n-1)
      | _, _ ->
         [fun ppf () -> fprintf ppf "SUB-SHIFT-INVALID-%d" n]
    in
    let rec self lvl =
      function
      | LF.(EmptySub | Undefs) -> []
      | LF.Shift n -> fmt_ppr_lf_sub_shift ppf (cPsi, n)
      | LF.FSVar (_, (s_name, s)) ->
         [fun ppf _ ->
          fprintf ppf "FSV %a[%a]"
            Name.pp s_name
            (fmt_ppr_lf_sub cD cPsi lvl) s]

      | LF.SVar (c, _, s) ->
         [fun ppf _ ->
          fprintf ppf "%a[@[%a@]]"
            (fmt_ppr_lf_offset cD) c
            (fmt_ppr_lf_sub_natural cD cPsi lvl) s]

      | LF.MSVar (_, ((_sigma, t), s)) ->
         [fun ppf _ ->
          fprintf ppf "$?S[@[%a@];@ @[%a@]]"
           (fmt_ppr_lf_msub cD lvl) t
           (fmt_ppr_lf_sub_natural cD cPsi lvl) s]

      | LF.Dot (f, s) ->
         self lvl s @ [fun ppf _ -> print_front ppf f]
    in
    match s with
    | LF.Shift _ when Bool.not (Context.hasCtxVar cPsi) ->
       (* Print nothing at all, because the user would have written nothing at all *)
       ()
    | _ ->
       fprintf ppf "%a"
         (pp_print_list ~pp_sep: Format.comma
            (fun ppf f -> f ppf ()))
         (self lvl s)

  and fmt_ppr_lf_sub_deBruijn cD cPsi lvl ppf s =
    let rec self lvl ppf =
      function
      | LF.EmptySub -> fprintf ppf "EmptySub"
      | LF.Undefs -> fprintf ppf "Undefs"
      | LF.Shift n ->
         fprintf ppf "^%s"
           (R.render_offset n)

      | LF.FSVar (n, (s_name, s)) ->
         fprintf ppf
           "^%s FSV %a[%a]"
           (R.render_offset n)
           Name.pp s_name
           (self lvl) s

      | LF.SVar (c, n, s) ->
         fprintf ppf
           "^%s %a[%a]"
           (R.render_offset n)
           (fmt_ppr_lf_offset cD) c
           (self lvl) s

      | LF.MSVar (n, ((_sigma, t), s)) ->
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


  and fmt_ppr_lf_front cD cPsi lvl ppf =
    function
    | LF.Head h ->
       fprintf ppf "%a"
         (fmt_ppr_lf_head cD cPsi lvl) h

    | LF.Obj m ->
       fprintf ppf "%a"
         (fmt_ppr_lf_normal cD cPsi lvl) m

    | LF.Undef ->
       fprintf ppf "undef"

  and fmt_ppr_lf_msub cD lvl ppf =
    function
    | LF.MShift k ->
       fprintf ppf "^%s" (string_of_int k)

    | LF.MDot (f, s) ->
       fprintf ppf "@[%a@],@ @[%a@]"
         (fmt_ppr_lf_msub cD lvl) s
         (fmt_ppr_lf_mfront cD 1) f

  and fmt_ppr_lf_mfront' cD ppf =
    function
    | LF.CObj cPsi ->
       fprintf ppf "[@[%a@]]"
         (fmt_ppr_lf_dctx cD 0) cPsi
    | LF.ClObj (phat, LF.MObj m) ->
       let cPsi = Context.hatToDCtx phat in
       fprintf ppf "[@[<hov 2>@[%a@] |-@ @[%a@]@]]"
         (fmt_ppr_lf_dctx_hat cD 0) cPsi
         (fmt_ppr_lf_normal cD cPsi 0) m
    | LF.ClObj (phat, LF.SObj s) ->
       let cPsi = Context.hatToDCtx phat in
       fprintf ppf "$[@[<hov 2>@[%a@] |-@ @[%a@]@]]"
         (fmt_ppr_lf_dctx_hat cD 0) cPsi
         (fmt_ppr_lf_sub cD cPsi 0) s
    | LF.ClObj (phat, LF.PObj h) ->
       let cPsi = Context.hatToDCtx phat in
       fprintf ppf "[@[<hov 2>@[%a@] |-@ @[%a@]@]]"
         (fmt_ppr_lf_dctx_hat cD 0) cPsi
         (fmt_ppr_lf_head cD cPsi 0) h
    | LF.MV k ->
       fprintf ppf "[%s]"
         (R.render_cvar cD k)
    | LF.MUndef ->
       fprintf ppf "[UNDEF]"

  and fmt_ppr_lf_mfront cD lvl ppf mO =
    fmt_ppr_lf_mfront' cD ppf mO

  and fmt_ppr_lf_mfront_typed cD (lvl : lvl) ppf =
    function
    | LF.(ClObj (_, LF.MObj m), ClTyp (_, cPsi)) ->
       fprintf ppf "[@[<hov 2>@[%a@] |-@ @[%a@]@]]"
         (fmt_ppr_lf_dctx cD 0) cPsi
         (fmt_ppr_lf_normal cD cPsi 0) m
    | LF.(ClObj (_, LF.SObj s), ClTyp (_, cPsi)) ->
       fprintf ppf "$[@[<hov 2>@[%a@] |-@ @[%a@]@]]"
         (fmt_ppr_lf_dctx cD 0) cPsi
         (fmt_ppr_lf_sub cD cPsi 0) s
    | LF.(ClObj (_, LF.PObj h), ClTyp (_, cPsi)) ->
       fprintf ppf "[@[<hov 2>@[%a@] |-@ @[%a@]@]]"
         (fmt_ppr_lf_dctx cD 0) cPsi
         (fmt_ppr_lf_head cD cPsi 0) h
    | (cM, _) -> fmt_ppr_lf_mfront' cD ppf cM

  and fmt_ppr_cmp_meta_obj cD lvl ppf (_, mO) =
    fmt_ppr_lf_mfront cD lvl ppf mO

  and fmt_ppr_cmp_meta_obj_typed cD lvl ppf ((_, cM), cU) =
    fmt_ppr_lf_mfront_typed cD lvl ppf (cM, cU)

  and fmt_ppr_lf_mmvar lvl ppf v =
    (* check whether the mmvar is instantiated or not before proceeding to print *)
    let u = LF.(v.instantiation) in
    match !u with
    | None ->
       let open LF in
       fprintf ppf "?%a_%d"
         Name.pp v.name
         v.mmvar_id
    | Some it ->
       match LF.(v.typ) with
       | LF.ClTyp (_, cPsi) ->
          fmt_ppr_lf_iterm LF.(v.cD) cPsi lvl ppf it

  and fmt_ppr_lf_offset cD ppf n =
    fprintf ppf "%s" (R.render_cvar cD n)

  and fmt_ppr_lf_cvar cD ppf =
    function
    | LF.Offset n -> fmt_ppr_lf_offset cD ppf n
    | LF.Inst mmvar -> fmt_ppr_lf_mmvar l0 ppf mmvar

  and fmt_ppr_lf_ctx_var cD ppf =
    function
    | LF.CInst (v, theta) ->
       let g = LF.(v.instantiation) in
       begin match !g with
       | None ->
          fprintf ppf "?%a[%a]"
            Name.pp LF.(v.name)
            (fmt_ppr_lf_msub cD 0) theta

       | Some (LF.ICtx cPsi) ->
          fprintf ppf "%a"
            (fmt_ppr_lf_dctx LF.(v.cD) 0) (Whnf.cnormDCtx (cPsi, theta))
       end

    | LF.CtxOffset psi ->
       begin match Context.lookup' cD psi with
       | (Option.Some LF.Decl { name = u; plicity = Plicity.Implicit; _ }
       | Option.Some LF.DeclOpt { name = u; plicity = Plicity.Implicit; _}) when !PC.printCtxUnderscore ->
          fprintf ppf "_"
       | Option.Some LF.Decl { name = u; _ }
       | Option.Some LF.DeclOpt { name = u ; _} ->
          fprintf ppf "%a" Name.pp u
       | Option.None -> fprintf ppf "FREE CtxVar %d" psi
       end
    | LF.CtxName psi ->
       fprintf ppf "%a"
         Name.pp psi

  and fmt_ppr_lf_typ_rec cD cPsi _lvl ppf typrec =
    let ppr_element cD cPsi ppf (x, tA) =
      fprintf ppf "@[<hv>%a :@ @[%a@]@]"
        Name.pp x
        (fmt_ppr_lf_typ cD cPsi 0) tA
    in
    let rec ppr_elements cD cPsi ppf =
      function
      | LF.SigmaLast (None, tA) -> fmt_ppr_lf_typ cD cPsi 0 ppf tA
      | LF.SigmaLast (Some x, tA) -> ppr_element cD cPsi ppf (x, tA)
      (*          | LF.SigmaElem (x, tA1, LF.SigmaLast tA2) ->
                  begin
                  ppr_element cD cPsi ppf ". " (x, tA1);
                  fprintf ppf "%a" (fmt_ppr_lf_typ cD (LF.DDec(cPsi, LF.TypDecl(x, tA1))) 0) tA2
                  end *)
      | LF.SigmaElem (x, tA, tRec) ->
         let x = fresh_name_dctx cPsi x in
         fprintf ppf "%a,@ %a"
           (ppr_element cD cPsi) (x, tA)
           (ppr_elements cD (LF.DDec(cPsi, LF.TypDecl (x, tA)))) tRec
    in
    fprintf ppf "@[<hv>%a@]" (ppr_elements cD cPsi) typrec

  and projectCtxIntoDctx = function
    | LF.Empty -> LF.Null
    | LF.Dec (rest, last) -> LF.DDec (projectCtxIntoDctx rest, last)

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
        fprintf ppf "%s" (Name.show (Store.Cid.Schema.get_name_from_schema s))
      with
      | Not_found -> print_without_name s

    else *)
    print_without_name s

  and frugal_block cD cPsi lvl ppf =
    function
    | LF.SigmaLast(_, tA) -> fmt_ppr_lf_typ cD cPsi 0 ppf tA
    | other -> fprintf ppf "block (%a)" (fmt_ppr_lf_typ_rec cD cPsi lvl) other

  and fmt_ppr_lf_sch_elem lvl ppf =
    function
    | LF.SchElem (LF.Empty, sgmDecl) ->
       fprintf ppf "%a"
         (frugal_block LF.Empty LF.Null lvl) sgmDecl

    | LF.SchElem (typDecls, sgmDecl) ->
       let cPsi = projectCtxIntoDctx typDecls in
       fprintf ppf "@[some [%a] %a@]"
         (ppr_typ_decl_dctx LF.Empty) cPsi
         (frugal_block LF.Empty cPsi lvl) sgmDecl


  and ppr_typ_decl_dctx cD ppf =
    function
    | LF.Null -> ()

    | LF.DDec (LF.Null, LF.TypDecl (x, tA)) ->
       fprintf ppf "%a : %a"    (* formerly "., %s : %a"    -jd 2010-06-03 *)
         Name.pp x
         (fmt_ppr_lf_typ cD LF.Null 0) tA

    | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
       fprintf ppf "%a, %a : %a"
         (ppr_typ_decl_dctx cD) cPsi
         Name.pp x
         (fmt_ppr_lf_typ cD cPsi 0) tA


  and fmt_ppr_lf_dctx_hat cD _lvl ppf =
    function
    | LF.Null -> fprintf ppf ""

    | LF.CtxVar ctx_var ->
       fmt_ppr_lf_ctx_var cD ppf ctx_var

    | LF.DDec (LF.Null, LF.TypDeclOpt x) ->
       fprintf ppf "%a"
         Name.pp x

    | LF.DDec (cPsi, LF.TypDeclOpt x) ->
       fprintf ppf "%a, %a"
         (fmt_ppr_lf_dctx_hat cD 0) cPsi
         Name.pp x

    | LF.DDec (LF.Null, LF.TypDecl(x, _)) ->
       fprintf ppf "%a"
         Name.pp x

    | LF.DDec (cPsi, LF.TypDecl(x, _)) ->
       fprintf ppf "%a, %a"
         (fmt_ppr_lf_dctx_hat cD 0) cPsi
         Name.pp x

  and fmt_ppr_lf_dctx' cD ppf =
    function
    | LF.Null ->
       fprintf ppf ""

    | LF.CtxVar ctx_var ->
       fmt_ppr_lf_ctx_var cD ppf ctx_var

    | LF.DDec (LF.Null, LF.TypDecl (x, tA)) ->
       let x = fresh_name_dctx LF.Null x in
       fprintf ppf "@[<hv 2>%a :@ @[%a@]@]"
         Name.pp x
         (fmt_ppr_lf_typ cD LF.Null 0) tA

    | LF.DDec (LF.Null, LF.TypDeclOpt x) ->
       let x = fresh_name_dctx LF.Null x in
       fprintf ppf "%a : _"
         Name.pp x

    | LF.DDec (cPsi, LF.TypDecl (x, tA)) ->
       let x = fresh_name_dctx cPsi x in
       fprintf ppf "@[%a@],@ @[<hv 2>%a :@ @[%a@]@]"
         (fmt_ppr_lf_dctx' cD) cPsi
         Name.pp x
         (fmt_ppr_lf_typ cD cPsi 0) tA

    | LF.DDec (cPsi, LF.TypDeclOpt x) ->
       let x = fresh_name_dctx cPsi x in
       fprintf ppf "%a,@ %a : _"
         (fmt_ppr_lf_dctx' cD) cPsi
         Name.pp x

  and fmt_ppr_lf_dctx cD lvl ppf cPsi =
    fprintf ppf "@[<hv>%a@]" (fmt_ppr_lf_dctx' cD) cPsi

  and fmt_ppr_lf_mctx ?(all = false) ?(sep = Format.comma) lvl ppf cD =
    let should_print =
      if all
      then fun _ -> true
      else
        function
        | (_, LF.Decl { plicity = Plicity.Explicit; _ }) ->
           Bool.not !Printer.Control.printNormal
        | (_, LF.Decl { plicity = Plicity.Implicit; _ }) ->
           Bool.not !Printer.Control.printNormal
           && !Printer.Control.printImplicit
        | _ -> true
    in
    fmt_ppr_ctx_filter ~sep: sep should_print
      (fun ppf (cD', d) ->
        fprintf ppf "%a"
          (fmt_ppr_lf_ctyp_decl cD') d)
      ppf
      cD

  and fmt_ppr_lf_kind cPsi lvl ppf =
    function
    | LF.Typ ->
       fprintf ppf "type"

    | LF.PiKind ((LF.TypDecl (x, a), (Depend.Yes | Depend.Maybe), Plicity.Explicit), k) ->
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "@[<2>%s{@[%a :@ @[%a@]@]}@ @[%a@]%s@]"
         (l_paren_if cond)
         Name.pp x
         (fmt_ppr_lf_typ LF.Empty cPsi 0) a
         (fmt_ppr_lf_kind (LF.DDec(cPsi, LF.TypDeclOpt x)) 0) k
         (r_paren_if cond)

    | LF.PiKind ((LF.TypDecl (x, a), (Depend.Yes | Depend.Maybe), Plicity.Implicit), k) ->
      (* FIXME(Marc-Antoine): There is technically no syntax for implicit Pi-types *)
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "@[<2>%s(@[%a :@ @[%a@]@])@ @[%a@]%s@]"
         (l_paren_if cond)
         Name.pp x
         (fmt_ppr_lf_typ LF.Empty cPsi 0) a
         (fmt_ppr_lf_kind (LF.DDec(cPsi, LF.TypDeclOpt x)) 0) k
         (r_paren_if cond)

    | LF.PiKind ((LF.TypDecl (x, a), Depend.No, _), k) ->
       let x = fresh_name_dctx cPsi x in
       let cond = lvl > 0 in
       fprintf ppf "%s@[<2>@[%a@] ->@ @[%a@]%s@]"
         (l_paren_if cond)
         (fmt_ppr_lf_typ LF.Empty cPsi 1) a
         (fmt_ppr_lf_kind (LF.DDec(cPsi, LF.TypDeclOpt x)) 0) k
         (r_paren_if cond)

  and fmt_ppr_lf_mtyp' cD k =
    Printer.fmt_ppr_ctx_underscore false
      begin fun ppf cU ->
      match cU with
      | LF.ClTyp (LF.MTyp tA, cPsi) ->
         fprintf ppf "%s@[<hov 2>@[%a@] |-@ @[%a@]@]%s"
           (match k with `parens -> "(" | `bracks -> "[")
           (fmt_ppr_lf_dctx cD 0) cPsi
           (fmt_ppr_lf_typ cD cPsi 0) tA
           (match k with `parens -> ")" | `bracks -> "]")

      | LF.ClTyp (LF.PTyp tA, cPsi) ->
         fprintf ppf "%s@[<hov 2>@[%a@] |-@ @[%a@]@]%s"
           (match k with `parens -> "#(" | `bracks -> "#[")
           (fmt_ppr_lf_dctx cD 0) cPsi
           (fmt_ppr_lf_typ cD cPsi 0) tA
           (match k with `parens -> ")" | `bracks -> "]")

      | LF.ClTyp (LF.STyp (cl, cPhi), cPsi) ->
         fprintf ppf "%s@[<hov 2>@[%a@] |- %a@ @[%a@]@]%s"
           (match k with `parens -> "$(" | `bracks -> "$[")
           (fmt_ppr_lf_dctx cD 0) cPsi
           fmt_ppr_lf_svar_class cl
           (fmt_ppr_lf_dctx cD 0) cPhi
           (match k with `parens -> ")" | `bracks -> "]")
      | LF.CTyp (Some cid) ->
         let x = Store.Cid.Schema.get_name cid in
         fprintf ppf "%a"
           Name.pp x
      | LF.CTyp None -> fprintf ppf "CTX"
      end

  and fmt_ppr_lf_mtyp cD =
    fmt_ppr_lf_mtyp' cD `bracks

  (* If a declaration is implicit and you don't want to print it, then
     it's *YOUR* responsibility to check the plicity of the
     declaration and skip calling this function. Otherwise, it is
     impossible to get the spacing to work correctly in the printed
     material. *)
  and fmt_ppr_lf_ctyp_decl ?(fmt_ppr_depend = fmt_ppr_lf_depend_clean) cD ppf =
    function
    | LF.Decl { name = u; typ = mtyp; plicity; inductivity } ->
       fprintf ppf "@[<2>%a%a :@ @[%a@]@]"
         Name.pp u
         fmt_ppr_depend (plicity, inductivity)
         (fmt_ppr_lf_mtyp' cD `parens) mtyp

    | LF.DeclOpt { name; _ } ->
       fprintf ppf "%a : _"
         Name.pp name

  and fmt_ppr_lf_ctyp_decl_harpoon cD ppf =
    function
    | LF.Decl { plicity = Plicity.Implicit; _ } as d ->
       fprintf ppf "@[%a (not in scope)@]"
         (fmt_ppr_lf_ctyp_decl cD) d
    | LF.Decl _ as d ->
       fprintf ppf "@[%a@]"
         (fmt_ppr_lf_ctyp_decl cD) d
    | LF.DeclOpt _ ->
       Error.raise_violation "[fmt_ppr_lf_ctyp_decl_harpoon] DeclOpt impossible"

  and isImplicitDecl =
    function
    | LF.Decl { plicity; _ }
    | LF.DeclOpt { plicity; _ } -> Plicity.is_implicit plicity

  and fmt_ppr_lf_iterm cD cPsi lvl ppf =
    function
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
  let rec fmt_ppr_cmp_kind cD lvl ppf =
    function
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

  let rec fmt_ppr_cmp_meta_spine cD lvl ppf =
    function
    | Comp.MetaNil ->
       fprintf ppf ""
    | Comp.MetaApp (mO, _, mS, Plicity.Implicit) ->
       fmt_ppr_cmp_meta_spine cD lvl ppf mS
    | Comp.MetaApp (mO, mT, mS, Plicity.Explicit) ->
       fprintf ppf "@ @[%a@]%a"
         (fmt_ppr_cmp_meta_obj_typed cD (lvl + 1)) (mO, mT)
         (fmt_ppr_cmp_meta_spine cD lvl) mS

  let rec fmt_ppr_cmp_typ cD lvl ppf =
    function
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

    | Comp.TypCross (_, taus) ->
       let cond = lvl > 0 in
       fprintf ppf "%s@[<2>%a@]%s"
         (l_paren_if cond)
         (List2.pp
           ~pp_sep:(fun ppf () -> fprintf ppf "@ * ")
           (fmt_ppr_cmp_typ cD 1)) taus
         (r_paren_if cond)

    (* Special case for printing implicit context variable
       quantifiers; these can never be omitted, and are printed with
       parentheses instead of curly braces. *)
    | Comp.TypPiBox (_, LF.(Decl { name = u; typ = CTyp w; plicity = Plicity.Implicit; _ } as d), tau) ->
       let cond = lvl > 1 in
       let d' =
         LF.Decl
           { name = u
           ; typ = LF.CTyp w
           ; plicity = Plicity.explicit
           ; inductivity = Inductivity.not_inductive
           }
       in
       let cD' = LF.Dec (cD, d') in
       fprintf ppf "%s@[<2>(@[<2>%a@])@ @[%a@]%s@]"
         (l_paren_if cond)
         (fmt_ppr_lf_ctyp_decl cD) d
         (* furthermore, they need to be considered *EXPLICIT* when
            printing the remaining type, so that they don't appear as
            _ *)
         (fmt_ppr_cmp_typ cD' 1) tau
         (r_paren_if cond)

    | Comp.TypPiBox (_, ctyp_decl, tau) ->
       let ctyp_decl = fresh_name_ctyp_decl cD ctyp_decl in
       if Bool.not !PC.printImplicit && isImplicitDecl ctyp_decl
       then
         fprintf ppf "%a" (fmt_ppr_cmp_typ (LF.Dec (cD, ctyp_decl)) 1) tau
       else
         let cond = lvl > 1 in
         fprintf ppf "%s@[<2>{@[<2>%a@]}@ @[%a@]%s@]"
           (l_paren_if cond)
           (fmt_ppr_lf_ctyp_decl cD) ctyp_decl
           (fmt_ppr_cmp_typ (LF.Dec(cD, ctyp_decl)) 1) tau
           (r_paren_if cond)

    | Comp.TypClo (_, _) ->
       fprintf ppf "TypClo!"

    | Comp.TypInd tau ->
       if !PC.printImplicit
       then
         fprintf ppf "@[%a@]*"
           (fmt_ppr_cmp_typ cD 10) tau
       else
         fmt_ppr_cmp_typ cD lvl ppf tau

  let fmt_ppr_cmp_suffices_typ cD ppf =
    function
    | `exact tau -> fmt_ppr_cmp_typ cD l0 ppf tau
    | `infer _ -> fprintf ppf "_"

  let rec fmt_ppr_pat_spine cD cG lvl ppf =
    function
    | Comp.PatNil -> fprintf ppf ""
    | Comp.PatApp (_, pat, pat_spine) ->
       fprintf ppf "@[%a@]@ @[%a@]"
         (fmt_ppr_cmp_pattern cD cG (lvl + 1)) pat
         (fmt_ppr_pat_spine cD cG lvl) pat_spine

  and fmt_ppr_cmp_pattern cD cG lvl ppf =
    let rec dropSpineLeft ms n =
      match (ms, n) with
      | (_, 0) -> ms
      | (Comp.PatNil, _) -> ms
      | (Comp.PatApp (_, _, rest), n) -> dropSpineLeft rest (n-1)
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

    | Comp.PatTuple (_, pats) ->
       fprintf ppf "(@[%a@])"
         (List2.pp
           ~pp_sep:(fun ppf () -> fprintf ppf ",@ ")
           (fmt_ppr_cmp_pattern cD cG 0)) pats

    | Comp.PatAnn (_, pat, _, Plicity.Implicit) ->
       fmt_ppr_cmp_pattern cD cG 0 ppf pat

    | Comp.PatAnn (_, pat, tau, Plicity.Explicit) ->
       fprintf ppf "(%a : %a)"
         (fmt_ppr_cmp_pattern cD cG 0) pat
         (fmt_ppr_cmp_typ cD 0) tau

    | Comp.PatVar (_, offset) ->
       fprintf ppf "%s"
         (R.render_var cG offset)

    | Comp.PatFVar (_, name) ->
       fprintf ppf "%a"
         Name.pp name

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

  let fmt_ppr_cmp_total_dec_kind ppf =
    function
    | `trust -> fprintf ppf "trust"
    | `partial -> fprintf ppf "partial"
    | `not_recursive -> fprintf ppf "notrec"
    | `inductive order ->
       fprintf ppf "total @[%a@]"
         fmt_ppr_cmp_numeric_order order

  (** Prints a totality declaration for *debugging*.
      This does not generate syntactically valid Beluga.
   *)
  let fmt_ppr_cmp_total_dec ppf { Comp.name; tau; order } =
    fprintf ppf "@[<hov 2>@[%a@]:@ @[<hv 2>%a :@ @[%a@]@]@]"
      fmt_ppr_cmp_total_dec_kind order
      Name.pp name
      (fmt_ppr_cmp_typ LF.Empty l0) tau

  let fmt_ppr_cmp_meta_branch_label ppf =
    function
    | `ctor cid -> fprintf ppf "%s" (R.render_cid_term cid)
    | `pvar k ->
       fprintf ppf "#%a"
         (Option.print (fun ppf -> fprintf ppf ".%d"))
         k
    | `bvar -> fprintf ppf "head variable"

  let rec fmt_ppr_cmp_exp cD cG lvl ppf =
    function
    | Comp.Fn (_, x, e) ->
       let x = fresh_name_gctx cG x in
       let cond = lvl > 0 in
       (*            fprintf ppf "@[<2>%sfn %s =>@ %a%s@]" *)
       fprintf ppf "%sfn %a =>@ %a%s"
         (l_paren_if cond)
         Name.pp x
         (fmt_ppr_cmp_exp cD (LF.Dec(cG, Comp.CTypDeclOpt x)) 0) e
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
    (*               (fmt_ppr_cmp_exp cD' cG' 0) e *)
    (*               (r_paren_if cond); *)


    | Comp.MLam (_, x, e, Plicity.Explicit) ->
       let x = fresh_name_mctx cD x in
       let cond = lvl > 0 in
       let cD' = LF.Dec(cD, LF.DeclOpt { name = x; plicity = Plicity.explicit }) in
       let cG' = Whnf.cnormGCtx (cG, LF.MShift 1) in
       fprintf ppf "%smlam %a =>@ %a%s"
         (l_paren_if cond)
         Name.pp x
         (fmt_ppr_cmp_exp cD' cG' 0) e
         (r_paren_if cond);

    | Comp.MLam (_, x, e, Plicity.Implicit) ->
       let x = fresh_name_mctx cD x in
       let cD' = LF.(Dec(cD, DeclOpt { name = x; plicity = Plicity.implicit })) in
       let cG' = Whnf.cnormGCtx (cG, LF.MShift 1) in
       fmt_ppr_cmp_exp cD' cG' 0 ppf e

    | Comp.Tuple (_, es) ->
       fprintf ppf "(@[%a@])"
         (List2.pp
           ~pp_sep:(fun ppf () -> fprintf ppf ",@ ")
           (fmt_ppr_cmp_exp cD cG 0)) es

    | Comp.LetTuple (_, i, (xs, e)) ->
       let xs' = List2.map (fresh_name_gctx cG) xs in
       let cG' =
         xs'
         |> List2.to_list
         |> List.fold_left (fun cG x -> LF.Dec (cG, Comp.CTypDeclOpt x)) cG in
       let cond = lvl > 1 in
       fprintf ppf "@[<2>%slet (@[%a@]) = %a@ in %a%s@]"
         (l_paren_if cond)
         (List2.pp ~pp_sep:(fun ppf () -> fprintf ppf ",@ ") Name.pp) xs'
         (fmt_ppr_cmp_exp cD cG 0) i
         (fmt_ppr_cmp_exp cD cG' 0) e
         (r_paren_if cond)


    | Comp.Let(_, i, (x, e)) ->
       let x = fresh_name_gctx cG x in
       let cond = lvl > 1 in
       fprintf ppf "%s@[@[<hv 2>let %a =@ @[%a@]@]@ in@ @[%a@]@]%s"
         (l_paren_if cond)
         Name.pp x
         (fmt_ppr_cmp_exp cD cG 0) i
         (fmt_ppr_cmp_exp cD (LF.Dec(cG, Comp.CTypDeclOpt x)) 0) e
         (r_paren_if cond)

    | Comp.Box (_, cM, cU) ->
       fmt_ppr_cmp_meta_obj_typed cD 0 ppf (cM, cU)

    | Comp.Impossible (_, i) ->
       let cond = lvl > 0 in
       fprintf ppf "%simpossible @[%a@]%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_exp cD cG 0) i
         (r_paren_if cond)

    | Comp.Case (_, prag, i, bs) ->
       begin match bs with
       | [] ->
          let cond = lvl > 0 in
          fprintf ppf "%simpossible @[%a@]%s"
            (l_paren_if cond)
            (fmt_ppr_cmp_exp cD cG 0) i
            (r_paren_if cond)
       | [Comp.Branch (_, cD_prefix, (cD_b, cG_b), pat, t, e)] ->
          let cond = lvl > 1 in
          fprintf ppf "%s@[<hv>@[<hv>let @[%a@[<h>%a@] =@ @[%a@]@]@ @]in@ @[%a@]@]%s"
            (l_paren_if cond)
            (fmt_ppr_lf_mctx ~sep: pp_print_space l0) cD_prefix
            (fmt_ppr_cmp_pattern cD_b cG_b 0) pat
            (fmt_ppr_cmp_exp cD cG 0) i
            (fmt_ppr_cmp_exp cD_b (Context.append cG cG_b) 0) e
            (r_paren_if cond)
       | bs ->
          let open Comp in
          let cond = lvl > 0 in
          fprintf ppf "%s@[<v>case @[%a@] of%s@,@[%a@]@]%s"
            (l_paren_if cond)
            (fmt_ppr_cmp_exp cD cG 0) i
            begin match prag with
            | PragmaCase -> ""
            | PragmaNotCase -> " --not"
            end
            (fmt_ppr_cmp_branches cG) bs
            (r_paren_if cond)
       end

    | Comp.Hole (loc, id, name) ->
       let name =
         let open HoleId in
         begin match name with
         | Named n -> n
         | Anonymous -> ""
         end
       in
       begin
         try
           fprintf ppf "?%s" name
         with
         | _ -> fprintf ppf "?%s" name
       end

    | Comp.Var (_, x) ->
       fprintf ppf "%s"
         (R.render_var cG x)

    | Comp.Const (_, prog) ->
       fprintf ppf "%s"
         (R.render_cid_prog prog)

    | Comp.DataConst (_, c) ->
       fprintf ppf "%s"
         (R.render_cid_comp_const c)

    | Comp.Obs (_, e, t, obs) ->
       fprintf ppf "%a.%s"
         (fmt_ppr_cmp_exp cD cG 1) e
         (R.render_cid_comp_dest obs)

    | Comp.Apply (_, i, e) ->
       let cond = lvl > 1 in
       fprintf ppf "%s@[<2>@[%a@]@ @[%a@]@]%s"
         (l_paren_if cond)
         (fmt_ppr_cmp_exp cD cG 1) i
         (fmt_ppr_cmp_exp cD cG 2) e
         (r_paren_if cond)

    | Comp.MApp (_, i, cM, cU, plicity) ->
      if Plicity.is_explicit plicity || !PC.printImplicit then
        let cond = lvl > 1 in
        fprintf ppf "%s@[<2>@[%a@]@ @[%a@]@]%s"
          (l_paren_if cond)
          (fmt_ppr_cmp_exp cD cG 1) i
          (fmt_ppr_cmp_meta_obj_typed cD 0) (cM, cU)
          (r_paren_if cond)
      else
        fmt_ppr_cmp_exp cD cG lvl ppf i (* not printing implicits *)


    | Comp.AnnBox (_, cM, cT) ->
      fmt_ppr_cmp_meta_obj_typed cD 1 ppf (cM, cT)

  and fmt_ppr_cmp_value lvl ppf =
    function
    | Comp.FunValue _ -> fprintf ppf " fn "
    | Comp.ThmValue _ -> fprintf ppf " rec "
    | Comp.MLamValue _ -> fprintf ppf " mlam "
    | Comp.CtxValue _ -> fprintf ppf " mlam "
    | Comp.BoxValue mC -> fprintf ppf "%a" (fmt_ppr_cmp_meta_obj LF.Empty 0) mC
    | Comp.ConstValue _ -> fprintf ppf " const "
    | Comp.TupleValue vs ->
       fprintf ppf "(@[%a@])"
         (List2.pp ~pp_sep:(fun ppf () -> fprintf ppf ",@ ") (fmt_ppr_cmp_value 0)) vs
    | Comp.DataValue (c, spine) ->
       (* Note: Arguments in data spines are accumulated in reverse order, to
          allow applications of data values in constant time. *)
       let k =
         if !Printer.Control.printImplicit
         then 0
         else Store.Cid.CompConst.get_implicit_arguments c
       in
       (* the function drop and print_spine can probably be combined
          to avoid traversing the spine twice.
        *)
       let rec drop =
         function
         | Comp.DataNil -> (Comp.DataNil, 0)
         | Comp.DataApp (v, spine) ->
            let (ms', k') = drop spine in
            if k' < k then (ms', k'+1)
            else (Comp.DataApp (v, ms'), k'+1)
       in
       let rec print_spine ppf =
         function
         | Comp.DataNil -> ()
         | Comp.DataApp (v, spine) ->
            print_spine ppf spine;
            fprintf ppf " %a" (fmt_ppr_cmp_value 1) v
       in
       let (pat_spine, k') = drop spine in (* k = length of original spine *)


       let cond = lvl > 0 && (k' - k) > 1 in
       fprintf ppf "%s%s%a%s"
         (l_paren_if cond)
         (R.render_cid_comp_const c) print_spine pat_spine
         (r_paren_if cond)

  and fmt_ppr_cmp_branches cG ppf bs =
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut (fmt_ppr_cmp_branch cG))
      bs

  and fmt_ppr_cmp_branch cG ppf (Comp.Branch (_, cD_prefix, (cD1', cG_p), pat, t, e)) =
    fprintf ppf "@[<v2>| @[%a@]@[%a@] =>@ @[%a@]@]"
      (fmt_ppr_lf_mctx 0) cD_prefix
      (fmt_ppr_cmp_pattern cD1' cG_p 0) pat
      (* NOTE: Technically: cD |- cG ctx and
       *       cD1' |- mcomp (MShift n) t    <= cD where n = |cD1|
       * -bp
       *)
      (fmt_ppr_cmp_exp cD1' (Context.append cG cG_p) 1) e

  and fmt_ppr_cmp_subgoal_path cD cG ppf path =
    let rec format_path =
      let open Comp.SubgoalPath in
      function
      | Here -> []
      | Suffices (i, k, p) ->
         let f ppf () =
           fprintf ppf "premise %d of @[%a@]" k
             (fmt_ppr_cmp_exp cD cG l0) i
         in
         f :: format_path p
      | Intros p ->
         (fun ppf () -> fprintf ppf "intros") :: format_path p
      | MetaSplit (i, lbl, p) ->
         let f ppf () =
           fprintf ppf "split @[%a@] (case @[%a@])"
             (fmt_ppr_cmp_exp cD cG l0) i
             fmt_ppr_cmp_meta_branch_label lbl
         in
         f :: format_path p
      | CompSplit (i, c, p) ->
         let f ppf () =
           fprintf ppf "split @[%a@] (case %s)"
             (fmt_ppr_cmp_exp cD cG l0) i
             (R.render_cid_comp_const c)
         in
         f :: format_path p
      | ContextSplit (i, Comp.EmptyContext _, p) ->
         let f ppf () =
           fprintf ppf "split @[%a@] (case empty context)"
             (fmt_ppr_cmp_exp cD cG l0) i
         in
         f :: format_path p
      | ContextSplit (i, Comp.ExtendedBy (_, k), p) ->
         let f ppf () =
           fprintf ppf "split @[%a@] (case extended by %d)"
             (fmt_ppr_cmp_exp cD cG l0) i
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
    let print_line ppf () =
      for _ = 1 to 80 do
        fprintf ppf "-"
      done
    in
    let open Comp in
    fun { context = {cD; cG; _} as ctx; goal; solution; label } ->
    fprintf ppf
      "@[<v>%a\
       @,%a\
       @,%a\
       @,%a\
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
         match !(g.solution) with
         | None -> fprintf ppf "?"
         | Some proof ->
            dprnt "[fmt_ppr_cmp_proof] chasing pointer!";
            fmt_ppr_cmp_proof cD cG ppf proof
       end
    | Command (stmt, proof) ->
       fprintf ppf "%a"
         (fmt_ppr_cmp_command_and_proof cD cG) (stmt, proof)
    | Directive d ->
       fmt_ppr_cmp_directive cD cG ppf d

  and fmt_ppr_cmp_command cD cG ppf cmd =
    let fmt_ppr_unbox_modifier ppf =
      function
      | Some `Strengthened -> fprintf ppf "strengthened"
      | None -> fprintf ppf "unboxed"
    in
    let open Comp in
    match cmd with
    | Unbox (i, name, _, modifier) ->
       fprintf ppf "@[<hv>by @[%a@]@ as %a %a@]"
         (fmt_ppr_cmp_exp cD cG l0) i
         Name.pp name
         fmt_ppr_unbox_modifier modifier
    | By (i, name, _) ->
       fprintf ppf "@[<hv 2>by @[%a@]@ as %a@]"
         (fmt_ppr_cmp_exp cD cG l0) i
         Name.pp name

  and fmt_ppr_cmp_command_and_proof cD cG ppf (c, p) =
    let cD', cG' =
      let open Comp in
      match c with
      | Unbox (_, u, _, _) ->
         (LF.Dec (cD, LF.DeclOpt { name = u; plicity = Plicity.explicit }), Whnf.cnormGCtx (cG, LF.MShift 1))
      | By (_, x, _) ->
         (cD, LF.Dec (cG, Comp.CTypDeclOpt x))
    in
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
    let open Comp in
    fun cD cG f ppf (SplitBranch (c, _, _, h)) ->
    let Hypothetical (_, hyp, _) = h in
    fprintf ppf "@[<v>case %a:@,%a@]"
      f c
      (fmt_ppr_cmp_hypothetical cD cG) h

  and fmt_ppr_cmp_directive cD cG ppf : Comp.directive -> unit =
    let open Comp in
    let print_split ppf i bs f =
      fprintf ppf "@[split@ @[%a@] as@]@,@[<v>%a@]"
        (fmt_ppr_cmp_exp cD cG l0) i
         (pp_print_list ~pp_sep: pp_print_cut
            (fmt_ppr_cmp_split_branch cD cG f))
         bs
    in
    function
    | Intros h -> fprintf ppf "intros@,%a" (fmt_ppr_cmp_hypothetical cD cG) h
    | Suffices (i, ps) ->
       fprintf ppf "@[<v>@[<2>suffices by@ @[%a@]@] toshow@,@[<v>%a@]@]"
         (Printer.fmt_ppr_implicits false
            (fmt_ppr_cmp_exp cD cG l0))
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
            (fmt_ppr_cmp_exp cD cG l0))
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
            (fmt_ppr_cmp_exp cD cG l0))
         t;

  and fmt_ppr_cmp_hypotheses_listing ppf =
    let open Comp in
    fun { cD; cG; _ } ->
    fprintf ppf
      "@[<v>Meta-context:\
       @,  @[<v>%a@]\
       @,Computational context:\
       @,  @[<v>%a@]\
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
    fun (Hypothetical (_, h, proof)) ->
    fprintf ppf "@[<v>{ %a @[<v>%a@]@,}@]"
      fmt_ppr_cmp_hypotheses h
      (fmt_ppr_cmp_proof h.cD h.cG) proof;

  and fmt_ppr_cmp_hypotheses ppf =
    let open Comp in
    let comma_sep_by fmt l = pp_print_list ~pp_sep: Format.comma fmt l in
    fun { cD; cG; _ } ->
    fprintf ppf "@[<hv>%a@]@,| @[<hv>%a@]@,;"
      (comma_sep_by
         begin fun ppf (cD, x) ->
         fprintf ppf "@[<hov 2>%a@]" (fmt_ppr_lf_ctyp_decl cD) x
         end)
      (Context.to_sublist cD)
      (comma_sep_by (fmt_ppr_cmp_ctyp_decl cD l0))
      (Context.to_list cG)

  and fmt_ppr_cmp_ih_arg cD ppf =
    function
    | Comp.M (m_obj, _cU) -> fmt_ppr_cmp_meta_obj cD l0 ppf m_obj
    | Comp.V k -> fprintf ppf "(offset %d)" k
    | Comp.DC -> fprintf ppf "_"
    | Comp.E -> Misc.not_implemented "IH E printing"

  and fmt_ppr_cmp_ctyp_decl cD lvl =
    Printer.fmt_ppr_ctx_underscore false
      begin fun ppf ->
      function
      | Comp.CTypDecl (x, tau, tag) ->
         fprintf ppf "@[<hov 2>%a@[%a@] :@ @[%a@]@]"
           Name.pp x
           print_wf_tag (tag && !PC.printImplicit)
           (fmt_ppr_cmp_typ cD lvl) tau

      | Comp.CTypDeclOpt x ->
         fprintf ppf "%a : _" Name.pp x
      end

  and fmt_ppr_cmp_gctx ?(sep = Format.comma) cD lvl =
    fmt_ppr_ctx_filter ~sep: sep
      (Fun.const true)
      (fun ppf (_, d) -> fmt_ppr_cmp_ctyp_decl cD l0 ppf d)

  let fmt_ppr_cmp_gctx_typing ppf (cD, cG) =
    fprintf ppf "@[%a@] |-@ @[%a@]"
      (fmt_ppr_lf_mctx l0) cD
      (fmt_ppr_cmp_gctx cD l0) cG

  let fmt_ppr_cmp_typ_typing ppf (cD, tau) =
    fprintf ppf "@[%a@] |-@ @[%a@]"
      (fmt_ppr_lf_mctx l0) cD
      (fmt_ppr_cmp_typ cD l0) tau

  let fmt_ppr_cmp_comp_prog_info ppf e =
    let { Store.Cid.Comp.Entry.name
        ; implicit_arguments
        ; typ
        ; prog
        ; mutual_group
        ; _ } =
      e
    in
    let ds = Store.Cid.Comp.lookup_mutual_group mutual_group in
    fprintf ppf
      "@[<v>name: @[%a@]\
       @,@[<hv 2>type:@ @[%a@]@]\
       @,implicit parameters: %d\
       @,mutual_group: @[%s@]\
       @,@[<hv 2>total_decs:@ @[%a@]@]\
       @,@[<hv 2>definition:@ @[%a@]@]\
       @,@]"
      Name.pp name
      (fmt_ppr_cmp_typ LF.Empty l0) typ
      implicit_arguments
      (R.render_cid_mutual_group mutual_group)
      (pp_print_list ~pp_sep: pp_print_cut fmt_ppr_cmp_total_dec) ds
      (Option.print (fmt_ppr_cmp_value l0)) prog

  let fmt_ppr_cmp_thm ppf =
    function
    (* should cG contain a Dec for the theorem itself? *)
    | Comp.Program e ->
       fmt_ppr_cmp_exp LF.Empty LF.Empty 0 ppf e
    | Comp.Proof p ->
       fmt_ppr_cmp_proof LF.Empty LF.Empty ppf p

  let fmt_ppr_cmp_thm_prefix ppf =
    function
    | Comp.Program _ -> fprintf ppf "rec"
    | Comp.Proof _ -> fprintf ppf "proof"


  let fmt_ppr_cmp_ih_args cD cG ppf : Comp.ih_arg list -> unit =
    pp_print_list ~pp_sep: pp_print_space (fmt_ppr_cmp_ih_arg cD) ppf

  let fmt_ppr_cmp_ih cD cG ppf (Comp.WfRec (f, args, tau)) =
    fprintf ppf "@[<hv 2>@[%a@] @[%a@] :@ @[%a@]@]"
      Name.pp f
      (fmt_ppr_cmp_ih_args cD cG) args
      (fmt_ppr_cmp_typ cD l0) tau

  let fmt_ppr_cmp_ihctx cD cG ppf cIH =
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut (fmt_ppr_cmp_ih cD cG))
      (Context.to_list cIH)

  let rec fmt_ppr_sgn_decl ppf =
    function
    | Sgn.CompTypAbbrev _ -> ()
    | Sgn.Const { identifier; typ; _ } ->
       fprintf ppf "%a : %a.@\n"
         Identifier.pp identifier
         (fmt_ppr_lf_typ LF.Empty LF.Null l0) typ

    | Sgn.Typ { identifier; kind; _ } ->
       fprintf ppf "%a : %a.@\n"
         Identifier.pp identifier
         (fmt_ppr_lf_kind LF.Null l0) kind

    | Sgn.CompTyp { identifier; kind; _ } ->
       fprintf ppf "@\ndatatype %a : @[%a@] = @\n"
         Identifier.pp identifier
         (fmt_ppr_cmp_kind LF.Empty l0) kind

    | Sgn.CompCotyp { identifier; kind; _ } ->
       fprintf ppf "@\ncodatatype %a : @[%a@] = @\n"
         Identifier.pp identifier
         (fmt_ppr_cmp_kind LF.Empty l0) kind

    | Sgn.CompDest
      { identifier
      ; mctx=cD
      ; observation_typ=tau0
      ; return_typ=tau1
      ; _
      } ->
       fprintf ppf "@ | (%a : @[%a@] :: @[%a@]@\n"
         Identifier.pp identifier
         (fmt_ppr_cmp_typ cD l0) tau0
         (fmt_ppr_cmp_typ cD l0) tau1

    | Sgn.CompConst { identifier; typ; _ } ->
       fprintf ppf "@ | %a : @[%a@]@\n"
         Identifier.pp identifier
         (fmt_ppr_cmp_typ LF.Empty l0) typ

    | Sgn.Recursive_declarations { declarations; _ } ->
      declarations
      |> List1.to_list
      |> List.iter (fmt_ppr_sgn_decl ppf)

    | Sgn.Val { identifier; typ; expression; expression_value=None; _ } ->
       fprintf ppf "@\nlet %a : %a = %a@\n"
         Identifier.pp identifier
         (fmt_ppr_cmp_typ LF.Empty l0) typ
         (fmt_ppr_cmp_exp LF.Empty LF.Empty l0) expression

    | Sgn.Val { identifier; typ; expression; expression_value=Some value; _ } ->
       fprintf ppf "@\nlet %a : %a = %a@\n   ===> %a@\n"
         Identifier.pp identifier
         (fmt_ppr_cmp_typ LF.Empty l0) typ
         (fmt_ppr_cmp_exp LF.Empty LF.Empty l0) expression
         (fmt_ppr_cmp_value l0) value

    | Sgn.Schema { identifier; schema; _ } ->
       fprintf ppf "@\nschema %a = @[%a@];@\n"
         Identifier.pp identifier
         (fmt_ppr_lf_schema ~useName:false l0) schema

    | Sgn.Theorem { identifier; cid; typ; body; _ } ->
       fprintf ppf "%a %a : %a =@ @[<v2>%a;@]"
         fmt_ppr_cmp_thm_prefix body
         Identifier.pp identifier
         (fmt_ppr_cmp_typ LF.Empty 0) typ
         fmt_ppr_cmp_thm body

    | Sgn.Module { identifier; entries; _ } ->
       let aux fmt t = List.iter (fun x ->  fmt_ppr_sgn_entry fmt x) t in
       fprintf ppf "@\nmodule %a = struct@\n@[<v2>%a@]@\nend;@\n"
         Identifier.pp identifier
         aux entries

  and fmt_ppr_associativity ppf associativity =
    match associativity with
    | Associativity.Left_associative -> pp_print_string ppf "left"
    | Associativity.Right_associative -> pp_print_string ppf "right"
    | Associativity.Non_associative -> pp_print_string ppf "none"

  and fmt_ppr_global_pragma ppf global_pragma =
    match global_pragma with
    | Sgn.No_strengthening _ ->
        Format.pp_print_string ppf "--nostrengthen"
    | Sgn.Warn_on_coverage_error _ ->
        Format.pp_print_string ppf "--warncoverage"
    | Sgn.Initiate_coverage_checking _ ->
        Format.pp_print_string ppf "--coverage"

  and fmt_ppr_pragma ppf pragma =
    match pragma with
    | Sgn.NamePrag
        { constant
        ; meta_variable_base
        ; computation_variable_base
        ; location = _
        } -> (
        match computation_variable_base with
        | Option.Some computation_variable_base ->
            fprintf ppf "@\n--name %a %a %a.@\n" Qualified_identifier.pp
              constant Identifier.pp meta_variable_base Identifier.pp
              computation_variable_base
        | Option.None ->
            fprintf ppf "@\n--name %a %a.@\n" Qualified_identifier.pp
              constant Identifier.pp meta_variable_base)
    | Sgn.NotPrag { location = _ } -> fprintf ppf "@\n--not@\n"
    | Sgn.OpenPrag { module_identifier; location = _ } ->
        fprintf ppf "@\n--open %a.@\n" Qualified_identifier.pp
          module_identifier
    | Sgn.DefaultAssocPrag { associativity; location = _ } ->
        fprintf ppf "@\n--assoc %a.@\n" fmt_ppr_associativity associativity
    | Sgn.PrefixFixityPrag { constant; precedence; postponed = _; location = _ } -> (
        match precedence with
        | Option.Some precedence ->
            fprintf ppf "@\n--prefix %a %d.@\n" Qualified_identifier.pp
              constant precedence
        | Option.None ->
            fprintf ppf "@\n--prefix %a.@\n" Qualified_identifier.pp constant
        )
    | Sgn.InfixFixityPrag
        { constant; precedence; associativity; postponed = _; location = _ } -> (
        match (precedence, associativity) with
        | Option.Some precedence, Option.Some associativity ->
            fprintf ppf "@\n--infix %a %d %a.@\n" Qualified_identifier.pp
              constant precedence fmt_ppr_associativity associativity
        | Option.None, Option.Some associativity ->
            fprintf ppf "@\n--infix %a %a.@\n" Qualified_identifier.pp
              constant fmt_ppr_associativity associativity
        | Option.Some precedence, Option.None ->
            fprintf ppf "@\n--infix %a %d.@\n" Qualified_identifier.pp
              constant precedence
        | Option.None, Option.None ->
            fprintf ppf "@\n--infix %a.@\n" Qualified_identifier.pp constant)
    | Sgn.PostfixFixityPrag { constant; precedence; postponed = _; location = _ } -> (
        match precedence with
        | Option.Some precedence ->
            fprintf ppf "@\n--postfix %a %d.@\n" Qualified_identifier.pp
              constant precedence
        | Option.None ->
            fprintf ppf "@\n--postfix %a.@\n" Qualified_identifier.pp
              constant)
    | Sgn.AbbrevPrag { module_identifier; abbreviation; location = _ } ->
        fprintf ppf "@\n--abbrev %a %a.@\n" Qualified_identifier.pp
          module_identifier Identifier.pp abbreviation
    | Sgn.Query
        { name
        ; typ = tA, _i
        ; expected_solutions
        ; maximum_tries
        ; location = _
        } -> (
        let fmt_ppr_query_argument ppf argument =
          match argument with
          | Option.Some argument -> pp_print_int ppf argument
          | Option.None -> pp_print_string ppf "*"
        in
        match name with
        | Option.Some name ->
            fprintf ppf "--query@ %a@ %a@ %a :@ %a." fmt_ppr_query_argument
              expected_solutions fmt_ppr_query_argument maximum_tries
              Identifier.pp name
              (fmt_ppr_lf_typ LF.Empty LF.Null l0)
              tA
        | Option.None ->
            fprintf ppf "--query@ %a@ %a@ :@ %a." fmt_ppr_query_argument
              expected_solutions fmt_ppr_query_argument maximum_tries
              (fmt_ppr_lf_typ LF.Empty LF.Null l0)
              tA)

  and fmt_ppr_sgn_entry ppf entry =
    match entry with
    | Sgn.Pragma { pragma; _} -> fmt_ppr_pragma ppf pragma
    | Sgn.Declaration { declaration; _ } -> fmt_ppr_sgn_decl ppf declaration
    | Sgn.Comment { content; _ } ->
      Format.pp_print_string ppf "%{{";
      Format.pp_print_cut ppf ();
      Format.pp_print_string ppf content;
      Format.pp_print_cut ppf ();
      Format.pp_print_string ppf "}}%"

  and fmt_ppr_sgn_file ppf { Sgn.global_pragmas; entries; _ } =
    List.iter (fun global_pragma ->
      fmt_ppr_global_pragma ppf global_pragma;
      Format.pp_print_newline ppf ()) global_pragmas;
    List.iter (fun entry ->
      fmt_ppr_sgn_entry ppf entry;
      Format.pp_print_newline ppf ()) entries

  let fmt_ppr_sgn ppf sgn = List1.iter (fmt_ppr_sgn_file ppf) sgn

  let fmt_ppr_theorem ppf (identifier, body, typ) =
    fprintf ppf "%a %a : %a =@ @[<v2>%a;@]"
      fmt_ppr_cmp_thm_prefix body
      Identifier.pp identifier
      (fmt_ppr_cmp_typ LF.Empty 0) typ
      fmt_ppr_cmp_thm body
end (* Int.Make *)

(* Default Error Pretty Printer Functor Instantiation *)
module DefaultPrinter = Make (Store.Cid.NamedRenderer)
