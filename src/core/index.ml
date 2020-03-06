(* -------------------------------------------------------------*)
(*  indexing
 *
 * index_term names ext_m = (m, fvars)
 *
 * Translates an object ext_m in external syntax
 * into an object m in approximate internal syntax.
 *
 * ASSUMPTION:
 *
 *    ext_m is in beta normal form
 *
 *)

open Support
open Store
open Store.Cid
open Syntax
module Ext = Syntax.Ext
module Apx = Syntax.Apx

module P = Pretty.Ext.DefaultPrinter

let (dprintf, dprint, _) = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

let print_subst_class ppf cl =
  let open Format in
  match cl with
  | Ext.LF.Subst -> fprintf ppf "substitution"
  | Ext.LF.Ren -> fprintf ppf "renaming"

type illegal_subst_term =
  [ `bvar
  | `const
  | `pure_lf
  ]

let print_illegal_subst_term ppf : illegal_subst_term -> unit =
  let open Format in
  function
  | `bvar -> fprintf ppf "bound variable"
  | `const -> fprintf ppf "LF constant"
  | `pure_lf -> fprintf ppf "pure LF type"

type open_or_closed =
  [ `open_term
  | `closed_term
  ]

type fvars =
  { open_flag : open_or_closed
  ; vars : CVar.cvar list
  }

let append_fvars f1 f2 flag =
  { open_flag = flag
  ; vars = f1.vars @ f2.vars
  }

let empty_fvars open_flag = { open_flag; vars = [] }

(** State monad. *)
type ('s, 'a) state = 's -> 's * 'a

(** State monad with the state instantiated to a list of free (contextual) variables. *)
type 'a fvar_state = (fvars, 'a) state

(** A strategy for disambiguating an LF name.
    In general the disambiguation strategy is the same in all cases,
    except the very end when we generate a free variable.
    In (pure) LF types, we disambiguate by generating `FVar'.
    These are abstracted into LF Pi-types.
    In contextual LF types, we disambiguate by generating `FMVar'.
    These are abstracted into computational Pi-box types.
 *)
type name_disambiguator =
  CVar.t -> BVar.t -> Syntax.Loc.t * Id.name -> Ext.LF.sub option -> Apx.LF.head fvar_state

type lf_indexing_context =
  { disambiguate_name : name_disambiguator
  ; cvars : CVar.t
  ; bvars : BVar.t
  }

let empty_lf_indexing_context disambiguate_name =
  { cvars = CVar.create ()
  ; bvars = BVar.create ()
  ; disambiguate_name
  }

(** Transforms the bound variable list in an indexing context. *)
let modify_bvars (f : BVar.t -> BVar.t) (c : lf_indexing_context) : lf_indexing_context =
  { c with bvars = f c.bvars }

(** Extends the bound variable list in an indexing context with a new entry. *)
let extending_bvars (x : Id.name) (c : lf_indexing_context) : lf_indexing_context =
  modify_bvars (fun bvars -> BVar.extend bvars (BVar.mk_entry x)) c

let extending_by (x : Id.name) (fvars : fvars) : fvars =
  { fvars with vars = x :: fvars.vars }

type 'a index = lf_indexing_context -> 'a fvar_state

(** Transforms the state. *)
let modify (f : 's -> 's) : ('s, unit) state =
  fun s -> (f s, ())

let modify_fvars (f : fvars -> fvars) : unit index =
  fun c -> modify f

(** Runs the indexer with a locally modified context. *)
let locally (f : lf_indexing_context -> lf_indexing_context) (m : 'a index) : 'a index =
  fun c fvars -> m (f c) fvars

let get : ('s, 's) state = fun s -> (s, s)

(** Gets the free variables from the state. *)
let get_fvars : fvars index = fun c -> get

let get_env : lf_indexing_context index =
  fun c fvars -> (fvars, c)

let trying_index (f : unit -> 'a) : 'a option =
  try Some (f ()) with Not_found -> None

type cvar_error_status =
  [ `implicit
  | `unbound
  ]

let cvar_error_to_hint = function
  | `implicit -> Some `implicit_variable
  | _ -> None

let index_cvar' cvars (u : Id.name) : (cvar_error_status, Id.offset) Either.t =
  match
    trying_index (fun _ -> CVar.index_of_name cvars u)
  with
  | None -> Either.Left `unbound
  | Some (`implicit, _) -> Either.Left `implicit
  | Some (_, k) ->
     dprintf begin fun p ->
       p.fmt "[index_cvar'] indexed %a to offset %d at %a"
         Id.print u
         k
         Loc.print_short (Id.loc_of_name u)
       end;
     Either.Right k

let index_cvar (name : Id.name) : (cvar_error_status, Id.offset) Either.t index =
  fun c fvars -> (fvars, index_cvar' c.cvars name)

  (*
let index_bvar (name : Id.name) : Id.offset option index =
  fun c fvars ->
  ( fvars
  , trying_index (fun () -> BVar.index_of_name c.bvars name)
  )
   *)

let get_closed_status : open_or_closed index =
  fun c fvars -> (fvars, fvars.open_flag)

module Bind = struct
  let pure (type a) (x : a) : a index =
    fun _ fvars -> (fvars, x)

  let ($) (type a) (type b) (m : a index) (k : a -> b index) : b index =
    fun c fvars ->
    let (fvars', x) = m c fvars in
    k x c fvars'

  let ($>) (type a) (type b) (m : a index) (f : a -> b) : b index =
    m $ fun x -> pure (f x)

  (** Runs `m' ignoring the unit, then runs `m''. *)
  let ($$) (type a) (m : unit index) (m' : a index) : a index =
    m $ fun _ -> m'

  let (<&) (type a) (m1 : a index) (m2 : unit index) : a index =
    m1 $ fun x -> m2 $$ pure x

  (** Runs two actions, and combines the result into a tuple. *)
  let seq2 (type a1) (type a2) (m1 : a1 index) (m2 : a2 index)
      : (a1 * a2) index =
    m1 $ fun x1 -> m2 $ fun x2 -> pure (x1, x2)
end

(** Hints can be attached to certain errors. *)
type hint =
  [ `needs_box
  | `implicit_variable
  ]

type error =
  | UnboundName          of Id.name
  | UnboundCtxSchemaName of Id.name
  | UnboundCompName      of Id.name
  | UnboundObs           of Id.name
  | UnboundOperator      of Id.name
  | PatVarNotUnique
  | IllFormedCompTyp
  | MisplacedOperator of Id.name
  | MissingArguments  of Id.name * int * int
  | ParseError
  | NameOvershadowing of Id.name
  | SubstitutionNotAllowed of illegal_subst_term
  | NonemptyPatternSpineForVariable of Id.name

exception Error of Syntax.Loc.t * error * hint option

let throw_hint' loc hint e = raise (Error (loc, e, hint))
let throw loc e = throw_hint' loc None e
let throw_hint loc hint e = throw_hint' loc (Some hint) e

let print_error ppf =
  let open Format in
  function
  | NameOvershadowing n ->
     fprintf ppf ("The declaration %a is overshadowing an earlier one.") Id.print n
  | MisplacedOperator n ->
     fprintf ppf ("Illegal use of operator %a.") Id.print n
  | MissingArguments (n, expected, found) ->
     fprintf ppf ("Operator %a expected %d arguments, found %d.") Id.print n expected found

  | UnboundName n ->
     fprintf ppf
       "Unbound data-level variable (ordinary or meta-variable) or constructor: %a."
       Id.print n
  | UnboundCtxSchemaName n ->
     fprintf ppf "Unbound context schema: %a." Id.print n
  | UnboundCompName n ->
     fprintf ppf "Unbound computation-level identifier: %a." Id.print n
  | UnboundObs n ->
     fprintf ppf "Unbound computation-level observation: %a." Id.print n
  | PatVarNotUnique ->
     fprintf ppf "Pattern variable not linear."
  | IllFormedCompTyp ->
     fprintf ppf "Ill-formed computation-level type."
  | ParseError ->
     fprintf ppf "Unable to parse operators into valid structure"
  | SubstitutionNotAllowed s ->
     fprintf ppf "Substitution is not allowed in %a" print_illegal_subst_term s
  | NonemptyPatternSpineForVariable x ->
     fprintf ppf "Variable patterns may not be applied; is %a misspelled?"
       Id.print x

let print_hint ppf : hint -> unit =
  let open Format in
  function
  | `needs_box ->
     pp_print_string ppf
       "This identifier is bound as a contextual variable. Did \
        you mean to write it in a box?"
  | `implicit_variable ->
     pp_print_string ppf
       "This variable is an implicit parameter. It cannot be \
        accessed directly."

let _ =
  let open Format in
  Error.register_printer
    (fun (Error (loc, err, hint)) ->
      Error.print_with_location loc
        (fun ppf ->
          fprintf ppf "@[<v>%a%a@]"
            print_error err
            (Maybe.print
               begin fun ppf h ->
               fprintf ppf "@,- @[<hov>%a@]"
                 print_hint h
               end)
            hint
    ))

(** Require that a substitution be None in the given situation `case'. *)
let require_no_sub loc (case : illegal_subst_term) =
  function
  | None -> ()
  | Some o -> throw loc (SubstitutionNotAllowed case)

(** Invokes the name disambiguation procedure from the indexing
    context.
 *)
let disambiguate_name :
      Syntax.Loc.t * Id.name -> Ext.LF.sub option ->
      Apx.LF.head index =
  fun p s ->
  fun c fvars ->
  c.disambiguate_name c.cvars c.bvars p s fvars

let lookup_fv' (m : Id.name) fvars =
  List.exists (Id.equals m) fvars.vars

let lookup_fv (m : Id.name) : bool index =
  Bind.(get_fvars $> lookup_fv' m)

let print_fvars ppf (vs : Var.t) =
  let open Format in
  pp_print_list
    ~pp_sep: Fmt.comma
    (fun ppf x -> Id.print ppf x.Var.name)
    ppf
    (Var.to_list vs)

let print_fcvars ppf fcvars =
  let open Format in
  pp_print_list
    ~pp_sep: Fmt.comma
    (fun ppf x ->
      fprintf ppf "FMV %s" (Id.render_name x))
    ppf
    fcvars.vars

let rec get_ctxvar psi = match psi with
  | Ext.LF.Null -> None
  | Ext.LF.CtxVar (_loc, psi_name) -> Some psi_name
  | Ext.LF.DDec (psi, _ ) -> get_ctxvar psi
  | Ext.LF.CtxHole -> None


let get_ctxvar_mobj (_loc,mO) = match mO with
  | Ext.LF.CObj cPsi -> get_ctxvar cPsi
  | Ext.LF.ClObj (cPsi, (Ext.LF.EmptySub _, [ _tM ])) -> get_ctxvar cPsi
  | _ -> None

let rec length_typ_rec t_rec = match t_rec with
  | Ext.LF.SigmaLast _ -> 1
  | Ext.LF.SigmaElem (x, _ , rest ) ->
      (print_string (Id.render_name x ^ "  ");
      1 + length_typ_rec rest )

let rec index_kind (k : Ext.LF.kind) : Apx.LF.kind index =
  let open Bind in
  let pi x a k =
    seq2 (index_typ a) (locally (extending_bvars x) (index_kind k))
    $> fun (a', k') -> Apx.LF.PiKind ((Apx.LF.TypDecl (x, a'), Apx.LF.No), k')
  in
  match k with
  | Ext.LF.Typ _ ->
     pure Apx.LF.Typ
  | Ext.LF.ArrKind (_, a, k) ->
     pi (Id.mk_name Id.NoName) a k
  | Ext.LF.PiKind (_, Ext.LF.TypDecl (x, a), k) ->
     pi x a k

and index_typ (a : Ext.LF.typ) : Apx.LF.typ index =
  let open Bind in
  match a with
  | Ext.LF.Atom (loc, a, s) ->
     let a' =
       try
         Typ.index_of_name a
       with
         Not_found ->
         throw loc (UnboundName a)
     in
     index_spine s
     $> fun s' -> Apx.LF.Atom (loc, a', s')

  | Ext.LF.ArrTyp (_loc, a, b) ->
     (* TODO use contextual name generation here *)
      let x = Id.mk_name Id.NoName in
      seq2 (index_typ a) (locally (extending_bvars x) (index_typ b))
      $> fun (a', b') ->
         Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a'), Apx.LF.No), b')

  | Ext.LF.PiTyp (_loc, Ext.LF.TypDecl (x, a), b) ->
     seq2 (index_typ a) (locally (extending_bvars x) (index_typ b))
     $> fun (a', b') ->
        Apx.LF.PiTyp ((Apx.LF.TypDecl (x, a'), Apx.LF.Maybe), b')

  | Ext.LF.Sigma (_, typRec) ->
     index_typ_rec typRec $> fun typRec' -> Apx.LF.Sigma typRec'

  | Ext.LF.AtomTerm (loc, Ext.LF.TList (loc', nl)) ->
     begin match shunting_yard' nl with
     | Ext.LF.Root(_, Ext.LF.Name(_, a, None), tS') ->
        dprintf
          begin fun p ->
          p.fmt "[index_typ] shunting_yard' of @[%a@] gives head @[%a@] and spine @[%a@]"
            (Format.pp_print_list
               ~pp_sep: Format.pp_print_space
               (P.fmt_ppr_lf_normal P.l0))
            nl
            Id.print a
            (P.fmt_ppr_lf_spine P.l0) tS'
          end;
        index_typ (Ext.LF.Atom (loc, a, tS'))
     | _ -> throw loc IllFormedCompTyp
     end

  | Ext.LF.AtomTerm (loc, Ext.LF.Root(loc', Ext.LF.Name(_, name, None), tS)) ->
     index_typ (Ext.LF.Atom (loc', name, tS))

and locOfNormal = function
  | Ext.LF.Lam(l,_,_) -> l
  | Ext.LF.Root(l,_,_) -> l
  | Ext.LF.Tuple(l,_) -> l
  | Ext.LF.Ann(l,_,_) -> l
  | Ext.LF.TList(l,_) -> l
  | Ext.LF.LFHole (l, _) -> l

(* Adaptation of Dijkstra's 'shunting yard' algorithm for
 * parsing infix, postfix, and prefix operators from a list
 *
 * Preconditions:
 *    - All operators (constructors and typs) are contained in the store
 *
 * Post: List of normals is converted to a Root with a head and a spine
 *        - Head contains the name of the atom term that is to be indexed
 *
*)
and shunting_yard (l : Ext.LF.normal list) : Ext.LF.normal =
  shunting_yard' l
  (*
  let rec normalListToSpine : Ext.LF.normal list -> Ext.LF.spine = function
    | [] -> Ext.LF.Nil
    | h::t -> Ext.LF.App(locOfNormal h, h, normalListToSpine t)
  in
  match l with
  | Ext.LF.Root(loc, h, Ext.LF.Nil) :: ms ->
     Ext.LF.Root(loc, h, normalListToSpine ms)
  | _ -> failwith "cannot be empty"
   *)

and shunting_yard' (l : Ext.LF.normal list) : Ext.LF.normal =
  let get_pragma = function
    | Ext.LF.Root(_, Ext.LF.Name(_, name, _), Ext.LF.Nil)
    | Ext.LF.Root(_, Ext.LF.PVar(_, name, _), Ext.LF.Nil) ->
       Maybe.get (Store.OpPragmas.getPragma name)
  in
  let pragmaExists = function
    | Ext.LF.Root(_, Ext.LF.Name(_, name, _), Ext.LF.Nil)
    | Ext.LF.Root(_, Ext.LF.PVar(_, name, _), Ext.LF.Nil) ->
       let args_expected =
         try Typ.args_of_name name with _ ->
           try Term.args_of_name name with _ ->
             -1
       in
       Store.OpPragmas.pragmaExists name && args_expected > 0
    | _ -> false
  in
  let lte (p : Store.OpPragmas.fixPragma) (o : Store.OpPragmas.fixPragma) : bool =
    let p_p = p.Store.OpPragmas.precedence in
    let o_p = o.Store.OpPragmas.precedence in
    let p_a = match p.Store.OpPragmas.assoc with
      | Some a -> a
      | None -> !Store.OpPragmas.default in
    p_p < o_p ||
    (p_p = o_p && p_a = Ext.Sgn.Left)
(*      p.Store.OpPragmas.precedence < o.Store.OpPragmas.precedence ||
    (p.Store.OpPragmas.precedence = o.Store.OpPragmas.precedence &&
      ((o.Store.OpPragmas.assoc = None && !Store.OpPragmas.default = Ext.Sgn.Left) ||
       o.Store.OpPragmas.assoc = Some Ext.Sgn.Left))
 *)  in
  let rec normalListToSpine : Ext.LF.normal list -> Ext.LF.spine = function
    | [] -> Ext.LF.Nil
    | h::t -> Ext.LF.App(locOfNormal h, h, normalListToSpine t)
  in
  let rec parse : int
                  * Ext.LF.normal list
                  * (int * Ext.LF.normal) list
                  * (int * Store.OpPragmas.fixPragma * Syntax.Loc.t) list ->
                  Ext.LF.normal = function
  | i, Ext.LF.TList(_, nl) :: t, y, z ->
      let h = parse (0,nl, [], [])
      in parse(i+1, t,(i,h)::y,z)
  | i, Ext.LF.Lam (loc, name, Ext.LF.TList(_, nl)) :: t, y, z ->
    let h = parse (0, nl, [], []) in
    parse(i+1, t, (i, Ext.LF.Lam(loc, name, h))::y, z)
  | i, h::t, exps, [] when pragmaExists h ->
    let p = get_pragma h
    and loc = locOfNormal h in
    parse(i+1, t, exps, [(i, p, loc)])
  | i, h::t, exps, (x, o, loc_o)::os when pragmaExists h ->
     let p = get_pragma h in
     let loc = locOfNormal h in
     if lte p o then
       begin match o.Store.OpPragmas.fix with
       | Ext.Sgn.Prefix ->
          let args_expected =
            try Typ.args_of_name o.Store.OpPragmas.name with _ ->
              try Term.args_of_name o.Store.OpPragmas.name with _ ->
                throw loc (UnboundOperator o.Store.OpPragmas.name)
          in
          let (ops, es) = take args_expected exps in
          let loc = loc_o in
          let ops = List.map (fun (_,x) ->x) ops in
          let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name, None), normalListToSpine ops) in
          parse(i+1, h::t, (i, e')::es, os)

       | Ext.Sgn.Postfix ->
          let (_, e)::es = exps in
          let loc = locOfNormal e in
          let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name, None), Ext.LF.App(loc, e, Ext.LF.Nil)) in
          parse(i+1, h::t, (i, e')::es, os)

       | Ext.Sgn.Infix ->
          let (_, e2)::(_, e1)::es = exps in
          let loc = locOfNormal e1 in
          let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name, None), normalListToSpine [e1; e2]) in
          parse(i+1, h::t, (i, e')::es, os)
       end
     else
       let loc_p = locOfNormal h in
       parse(i+1, t, exps, (i, p, loc_p)::(x, o, loc_o)::os)
  | i, h ::t, y, z -> parse(i+1, t, (i, h)::y, z)
  | _, [], y, z ->
     reconstruct (y, z)

  and reconstruct : (int * Ext.LF.normal) list * (int * Store.OpPragmas.fixPragma * Syntax.Loc.t) list -> Ext.LF.normal = function
  | [(_, e)], [] -> e
  | exps, (i, o, loc_o)::os when (o.Store.OpPragmas.fix = Ext.Sgn.Prefix) ->
     let args_expected =
       let name = o.Store.OpPragmas.name in
       try Typ.args_of_name name with _ ->
         try Term.args_of_name name with _ ->
           throw loc_o (UnboundOperator name)
     in
    let (ops, es) = take args_expected exps in
    let loc =
      if Syntax.Loc.is_ghost loc_o then
        if args_expected > 0 then
          try let (_,x) = List.hd ops in locOfNormal x
          with _ ->
            throw Syntax.Loc.ghost (MissingArguments (o.Store.OpPragmas.name, args_expected, List.length exps))
        else Syntax.Loc.ghost
      else loc_o
    in
    if List.for_all (fun (x, _) -> x > i) ops then begin
      let ops = List.map (fun (_, x) -> x) ops in
      let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name, None), normalListToSpine ops) in
      reconstruct((i, e')::es, os) end
    else
      throw loc (MisplacedOperator o.Store.OpPragmas.name)

  | (i2, e2)::(i1, e1)::es, (i, o, _loc_o)::os when o.Store.OpPragmas.fix = Ext.Sgn.Infix ->
    let loc = locOfNormal e1 in
    if i2 > i && i > i1 then begin
      let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name, None), normalListToSpine [e1; e2]) in
      reconstruct((i, e')::es, os) end
    else
      throw loc (MisplacedOperator o.Store.OpPragmas.name)

  | (i1, e)::es, (i, o, _loc_o)::os when o.Store.OpPragmas.fix = Ext.Sgn.Postfix ->
    let loc = locOfNormal e in
    if i > i1 then begin
      let e' = Ext.LF.Root(loc, Ext.LF.Name(loc, o.Store.OpPragmas.name, None), Ext.LF.App(loc, e, Ext.LF.Nil)) in
      reconstruct((i, e')::es, os) end
    else
      throw loc (MisplacedOperator o.Store.OpPragmas.name)

  | l, [] ->
    let l' = List.rev l in
    let (_, Ext.LF.Root(loc, h, Ext.LF.Nil)) :: t = l' in
    let t = List.map (fun (_,x) -> x) t in
    Ext.LF.Root(loc, h, normalListToSpine t)

  | a, b ->
    failwith "Error in indexing"

  and take i l =
    let rec aux n l c =
      match l with
      | h::t when n > 0 -> aux (n-1) t (h::c)
      | _  -> (c, l)
    in
    aux i l []
  in
  try
    parse (0, l, [], [])
  with
  | (Error _) as e -> raise e
  | _ -> throw (List.hd l |> Ext.LF.loc_of_normal) ParseError

(* Records are not handled in a general manner
 * We need to change the datatype for typ_rec to be typ_decl ctx
 * XXX
 * Remark: records *must* be nonempty (this is enforced by
   construction) but contexts may be empty.
   If we rewrite records to be contexts, then we now have an
   additional invariant in the code that is not enforced by the types.
   -je
 *)
and index_typ_rec (r : Ext.LF.typ_rec) : Apx.LF.typ_rec index =
  let open Bind in
  match r with
  | Ext.LF.SigmaLast(n, a) ->
     index_typ a $> fun a' -> Apx.LF.SigmaLast (n, a')

  | Ext.LF.SigmaElem (x, a, rest) ->
     seq2
       (index_typ a)
       (locally (extending_bvars x) (index_typ_rec rest))
     $> fun (a', rest') -> Apx.LF.SigmaElem (x, a', rest')

and index_tuple (tuple : Ext.LF.tuple) : Apx.LF.tuple index =
  let open Bind in
  match tuple with
  | Ext.LF.Last m ->
     index_term m $> fun m' -> Apx.LF.Last m'

  | Ext.LF.Cons (m, rest) ->
     seq2 (index_term m) (index_tuple rest)
     $> fun (m', rest') ->
        Apx.LF.Cons (m', rest')

and index_term (m : Ext.LF.normal) : Apx.LF.normal index =
  let open Bind in
  match m with
  | Ext.LF.Lam (loc, x, m) ->
     locally (extending_bvars x) (index_term m)
     $> fun m' -> Apx.LF.Lam (loc, x, m')

  | Ext.LF.Tuple (loc, tuple) ->
     index_tuple tuple $> fun tuple' -> Apx.LF.Tuple (loc, tuple')

  | Ext.LF.Root (loc, h, s) ->
     seq2 (index_head h) (index_spine s)
     $> fun (h', s') -> Apx.LF.Root (loc, h', s')

  | Ext.LF.LFHole (loc, name) -> pure (Apx.LF.LFHole (loc, name))

  | Ext.LF.Ann (loc, m, a) ->
     seq2 (index_typ a) (index_term m)
     $> fun (a', m') ->
        Apx.LF.Ann (loc, m', a')

  | Ext.LF.TList (loc, nl)->
    index_term (shunting_yard nl)

and index_proj = function
  | Ext.LF.ByPos k -> Apx.LF.ByPos k
  | Ext.LF.ByName n -> Apx.LF.ByName n

and index_head (h : Ext.LF.head) : Apx.LF.head index =
  let open Bind in
  match h with
  | Ext.LF.Name (loc, n, o) ->
     dprintf
       (fun p ->
         p.fmt "[index_head] indexing name/variable %a at %a"
           Id.print n
           Loc.print_short loc);
     disambiguate_name (loc, n) o

  | Ext.LF.Proj(loc, h, k) ->
     index_head h $> fun h' -> Apx.LF.Proj (h', index_proj k)

  | Ext.LF.Hole _loc ->
     pure Apx.LF.Hole

  | Ext.LF.PVar (loc, p, s) ->
     lookup_fv p $
       function
       | true ->
          index_sub_opt s $> fun s' -> Apx.LF.FPVar (p, s')
       | false ->
          seq2 get_closed_status (index_cvar p) $
            function
            | `closed_term, Either.Left _ -> throw loc (UnboundName p)
            | `open_term, Either.Left _ ->
               index_sub_opt s
               $ fun s' ->
                 modify_fvars (extending_by p)
                 $$ pure (Apx.LF.FPVar (p, s'))
            | _, Either.Right offset ->
               index_sub_opt s
               $> fun s' ->
                  Apx.LF.PVar (Apx.LF.Offset offset, s')

                      (*
          try
            let offset = CVar.index_of_name cvars p in
            let (s' , fvs') = index_sub_opt cvars bvars fvs s in
            (Apx.LF.PVar (Apx.LF.Offset offset, s') , fvs')
          with Not_found ->
            if closed_flag then
              ((* if lookup_fv fvars (FPV p) then
                  let (s', (fvars', closed_flag))  = index_sub cvars bvars fvs s in
                  (Apx.LF.FPVar (p, s') , (fvars' , closed_flag))
                  else *)
               raise (Error (loc, UnboundName p))
              )
            else
              let (s', (fvars', closed_flag))  = index_sub_opt cvars bvars fvs s in
              (Apx.LF.FPVar (p, s') , (p :: fvars' , closed_flag))
                       *)

and index_spine (s : Ext.LF.spine) : Apx.LF.spine index =
  let open Bind in
  let app m s =
     seq2 (index_term m) (index_spine s)
     $> fun (m', s') -> Apx.LF.App (m', s')
  in
  match s with
  | Ext.LF.Nil -> pure Apx.LF.Nil
  | Ext.LF.App (_, Ext.LF.TList (loc, nl), s) -> app (shunting_yard nl) s
  | Ext.LF.App (_, m, s) -> app m s

(* In the external syntax, `Name` is used for bound variables, constants, and metavariables.
   Since the logic is a bit nasty, it is encapsulated in this helper.

   Here's the logic, in the order in which the checks are performed:
   - Is it a bound variable? -> BVar
   - Is the name already a free variable? -> FMVar
   - Is it a declared metavariable? -> MVar
   - Is it a constant? -> Const
   - Are we in a closed context -> error
   - Otherwise -> FMVar
 *)
and disambiguate_name' f : name_disambiguator =
  fun cvars bvars (loc, name) sub_opt fvars ->
  let disambiguation_message kind k p =
    p.fmt "[disambiguate_name] variable %a -> %s (at %a) %a"
      Id.print name
      kind
      Loc.print_short loc
      (Maybe.print
         (fun ppf x -> Format.fprintf ppf "--> index %d" x))
      k
  in
  (* form an LF indexing context so we can invoke index_sub_opt *)
  let c = {cvars; bvars; disambiguate_name = disambiguate_name' f} in
  try
    ( fvars
    , ( let k = BVar.index_of_name bvars name in
        require_no_sub loc `bvar sub_opt;
        dprintf (disambiguation_message "bound variable" (Some k));
        Apx.LF.BVar k
      (* it's essential to perform `index_of_name` first since it will
         throw the Not_found exception that leads to trying the next case
         in the disambiguation.
         Only once we've ascertained that it is in fact a BVar should
         be demand that no substitution be present.
       *)
      )
    )
  with Not_found ->
    if lookup_fv' name fvars then
      let (fvs', o') =
        dprintf (disambiguation_message "known to be free" None);
        match sub_opt with
        | Some s ->
           let fvs', s' =
             index_sub s c fvars
           in
           fvs', Some s'
        | None -> fvars, None
      in
      (fvs', Apx.LF.FMVar (name, o'))
    else
      match index_cvar' cvars name with
      | Either.Left `implicit ->
         throw_hint
           (Id.loc_of_name name)
           `implicit_variable
           (UnboundName name)
      | Either.Right offset ->
         dprintf (disambiguation_message "contextual variable" (Some offset));
         let (fvs', o') =
           index_sub_opt sub_opt c fvars
         in
         ( fvs'
         , Apx.LF.MVar (Apx.LF.Offset offset, o')
         )
      | Either.Left `unbound ->
         try
           ( fvars
           , ( let k = Term.index_of_name name in
               require_no_sub loc `const sub_opt;
               dprintf (disambiguation_message "LF constant" None);
               Apx.LF.Const k
             (* similar consideration here as for BVar;
                we must ascertain that it is in fact a Const before
                demanding that there be no substitution.
              *)
             )
           )
         with Not_found ->
           dprintf (disambiguation_message "new free variable" None);
           f c (loc, name) sub_opt fvars

and disambiguate_to_fmvars : name_disambiguator =
  fun cvars bvars (loc, name) sub_opt fvars ->
  disambiguate_name'
    (fun c (loc, name) sub_opt fvars ->
      dprintf (fun p -> p.fmt "[disambiguate_name] disambiguating %a to FMVar" Id.print name);
      match fvars.open_flag with
      | `closed_term -> throw loc (UnboundName name)
      | `open_term ->
         let (fvars', s') = index_sub_opt sub_opt c fvars in
         ( extending_by name fvars'
         , Apx.LF.FMVar (name, s')
         )
    )
    cvars bvars (loc, name) sub_opt fvars

and disambiguate_to_fvars : name_disambiguator =
  fun cvars bvars (loc, name) sub_opt fvars ->
  disambiguate_name'
    (fun _ (loc, name) sub_opt fvars ->
      dprintf (fun p -> p.fmt "[disambiguate_name] disambiguating %a to FVar" Id.print name);
      require_no_sub loc `pure_lf sub_opt;
      dprintf (fun p -> p.fmt "FVar %a at %a" Id.print name Loc.print loc);
      (fvars, Apx.LF.FVar name)
    )
    cvars bvars (loc, name) sub_opt fvars


and index_sub_opt (s : Ext.LF.sub option) : Apx.LF.sub option index =
  let open Bind in
  match s with
  | None -> pure None
  | Some s ->
     index_sub s $> Maybe.pure

and index_sub (s : Ext.LF.sub) : Apx.LF.sub index =
  let open Bind in
  let to_head_or_obj tM = match tM with
    | Apx.LF.Root (_,(Apx.LF.BVar _ as h), Apx.LF.Nil)
    | Apx.LF.Root (_,(Apx.LF.PVar _ as h), Apx.LF.Nil)
    | Apx.LF.Root (_,(Apx.LF.Proj _ as h), Apx.LF.Nil) -> Apx.LF.Head h
    | _ -> Apx.LF.Obj tM
  in
  match s with
  | (start, h :: s) ->
     seq2 (index_sub (start, s)) (index_term h)
     $> fun (s', h') -> Apx.LF.Dot (to_head_or_obj h', s')

  | (Ext.LF.Id loc, []) ->
     pure Apx.LF.Id

  | (Ext.LF.EmptySub _, []) ->
     pure Apx.LF.EmptySub

  | (Ext.LF.SVar (loc, u, s), []) ->
     lookup_fv u $
       function
       | true ->
          index_sub_opt s
          $> fun s' -> Apx.LF.FSVar (u, s')
       | false ->
          seq2 get_closed_status (index_cvar u) $
            function
            | `closed_term, Either.Left e ->
               throw_hint' loc (cvar_error_to_hint e) (UnboundName u)
            | `open_term, Either.Left _ ->
               index_sub_opt s
               $ fun s' ->
                 modify_fvars (extending_by u)
                 $$ pure (Apx.LF.FSVar (u, s'))
            | _, Either.Right offset ->
               index_sub_opt s
               $> fun s' -> Apx.LF.SVar (Apx.LF.Offset offset, s')

                      (*
      if lookup_fv fvs (u) then
        let (s', fvs')     = index_sub_opt cvars bvars fvars s in
          (Apx.LF.FSVar (u, s') , fvs')
      else
        begin
          try
            let offset = CVar.index_of_name cvars u in
            let (s', fvs') = index_sub_opt cvars bvars fvars s in
            let _ = dprint (fun () -> "[index_sub] s = " ^ string_of_int offset) in
            (Apx.LF.SVar (Apx.LF.Offset offset, s') , fvs')
          with Not_found ->
            if closed_flag then
              (* if lookup_fv fvars (FMV u) then
                 let (s', (fvars', closed_flag))     = index_sub cvars bvars fvs s in
                 (Apx.LF.FMVar (u, s') , (fvars' , closed_flag))
                 else *)
              raise (Error (loc, UnboundName u))
            else
              let (s', (fvars', closed_flag)) = index_sub_opt cvars bvars fvars s in
              (Apx.LF.FSVar (u, s') , (u :: fvars' , closed_flag))
        end
                       *)

let index_decl disambiguate_name (cvars : CVar.t) (bvars : BVar.t) fvars = function
  | (Ext.LF.TypDecl(x, a)) ->
     let (fvars', a') =
       index_typ a { cvars; bvars; disambiguate_name } fvars
     in
     let bvars = BVar.extend bvars (BVar.mk_entry x) in
     (Apx.LF.TypDecl (x,a'), bvars, fvars')

  | (Ext.LF.TypDeclOpt x) ->
    let bvars' = BVar.extend bvars (BVar.mk_entry x) in
    (Apx.LF.TypDeclOpt x, bvars', fvars)

(** Tries to index the given name as a context variable.
    Computes a cvar_error_status in case free variables are not
    permitted and the name is not bound.
 *)
let index_ctx_var name : (cvar_error_status, Apx.LF.dctx) Either.t index =
  let open Bind in
  lookup_fv name
  $ function
    | true -> Either.Right (Apx.LF.CtxVar (Apx.LF.CtxName name)) |> pure
    | false ->
       seq2 (get_fvars) (index_cvar name)
       $ function
         | _, Either.Right k ->
            Either.Right (Apx.LF.CtxVar (Apx.LF.CtxOffset k)) |> pure
         | fvars, Either.Left e ->
            match fvars.open_flag with
            | `closed_term -> pure (Either.Left e)
            | `open_term ->
               Either.Right (Apx.LF.CtxVar (Apx.LF.CtxName name)) |> pure
               <& modify_fvars (extending_by name)

let rec index_dctx disambiguate_name cvars bvars (fvars : fvars) = function
  | Ext.LF.CtxHole     -> (Apx.LF.CtxHole, bvars, fvars)
  | Ext.LF.Null        -> (Apx.LF.Null , bvars, fvars)

  | Ext.LF.CtxVar (loc, psi_name)  ->
     index_ctx_var psi_name {cvars; bvars; disambiguate_name} fvars
     |> Pair.rmap
          (function
           | Either.Right x -> x
           | Either.Left e ->
              throw_hint' loc (cvar_error_to_hint e) (UnboundName psi_name)
          )
     |> fun (fvars, dctx) -> (dctx, bvars, fvars)

  | Ext.LF.DDec (psi, decl) ->
     let (psi', bvars', fvars') =
       index_dctx disambiguate_name cvars bvars fvars psi
     in
     let (decl', bvars'', fvars'') =
       index_decl disambiguate_name cvars bvars' fvars' decl
     in
     (Apx.LF.DDec (psi', decl'), bvars'', fvars'')

let index_svar_class = function
  | Ext.LF.Ren -> Apx.LF.Ren
  | Ext.LF.Subst -> Apx.LF.Subst

let rec index_ctx d cvars bvars fvars = function
  | Ext.LF.Empty ->
     (Apx.LF.Empty , bvars, fvars)

  | Ext.LF.Dec (psi, dec) ->
     let (psi', bvars', fvars')   = index_ctx d cvars bvars fvars psi in
     let (dec', bvars'', fvars'') = index_decl d cvars bvars' fvars' dec in
     (Apx.LF.Dec (psi', dec'), bvars'', fvars'')

let index_cltyp' (a : Ext.LF.cltyp) : Apx.LF.cltyp index =
  let open Bind in
  match a with
  | Ext.LF.MTyp a ->
     dprintf
       (fun p ->
         p.fmt "[index_cltyp'] indexing meta type %a"
           (P.fmt_ppr_lf_typ P.l0) a);
     index_typ a $> fun a' -> Apx.LF.MTyp a'

  | Ext.LF.PTyp a ->
     dprintf
       (fun p ->
         p.fmt "[index_cltyp'] indexing parameter type %a"
           (P.fmt_ppr_lf_typ P.l0) a);
     index_typ a $> fun a' -> Apx.LF.PTyp a'
                              (*
     in
     begin match a with
     | Ext.LF.AtomTerm (loc, Ext.LF.TList (_, [Ext.LF.Root (_, Ext.LF.Name (_, name, None), Ext.LF.Nil)])) ->
        index_ctx_var name
        $ begin function
          | None -> index_as_ptyp ()
          | Some x -> Apx.LF.STyp (Apx.LF.Subst, x) |> pure
          end
     | _ -> index_as_ptyp ()
     end
                               *)

  | Ext.LF.STyp (cl, phi) ->
     dprintf
       (fun p ->
         p.fmt "[index_cltyp'] indexing %a type %a"
           print_subst_class cl
           (P.fmt_ppr_lf_dctx P.l0) phi);
     seq2 get_env get_fvars
     $ fun (c, fvars) ->
       let (phi', _bvars', fvars) =
         index_dctx c.disambiguate_name c.cvars (BVar.create ()) fvars phi
       in
       modify_fvars (Misc.const fvars)
       $$ pure (Apx.LF.STyp (index_svar_class cl, phi'))

let index_cltyp loc cvars fvars =
  function
  | Ext.LF.ClTyp (cl, psi) ->
     let disambiguate_name = disambiguate_to_fmvars in
     let (psi', bvars, fvars) =
       index_dctx disambiguate_name cvars (BVar.create ()) fvars psi
     in
     let (fvars, cl) =
       index_cltyp' cl {cvars; bvars; disambiguate_name} fvars
     in
     (fvars, Apx.LF.ClTyp (cl, psi'))

  | Ext.LF.CTyp schema_name ->
     try
       let schema_cid = Schema.index_of_name schema_name in
       (fvars, Apx.LF.CTyp schema_cid)
     with Not_found ->
       throw loc (UnboundCtxSchemaName schema_name)

let index_dep =
  function
  | Ext.LF.Maybe -> Apx.LF.Maybe
  | Ext.LF.No -> Apx.LF.No
  | Ext.LF.Inductive ->
     Error.violation
       "[index_dep] Inductive not allowed in external syntax"

let index_cdecl plicity_of_dep cvars fvars = function
  | Ext.LF.DeclOpt _ ->
     Error.violation
       "[index_cdecl] DeclOpt not allowed in external syntax"
  | Ext.LF.Decl(u, (loc,cl), dep) ->
    let (fvars, cl) = index_cltyp loc cvars fvars cl in
    dprintf begin fun p ->
      p.fmt "[index_cdecl] %a at %a"
        Id.print u
        Loc.print_short loc
      end;
    match index_cvar' cvars u with
    | Either.Right _ ->
       throw loc (NameOvershadowing u)
    | Either.Left _ ->
       let cvars =
         CVar.extend cvars
           (CVar.mk_entry u (plicity_of_dep dep))
       in
       (Apx.LF.Decl(u, cl, index_dep dep), cvars, fvars)

let rec index_mctx cvars fvars = function
  | Ext.LF.Empty ->
      (Apx.LF.Empty, cvars, fvars)

  | Ext.LF.Dec (delta, cdec) ->
      let (delta', cvars', fvars') = index_mctx cvars fvars delta in
      let (cdec', cvars'', fvars'') =
        index_cdecl Ext.LF.Depend.to_plicity cvars' fvars' cdec
      in
      (Apx.LF.Dec (delta', cdec'), cvars'', fvars'')


(* Translation of external schemas into approximate schemas *)
let rec index_elements el_list = List.map index_el el_list

and index_el (Ext.LF.SchElem (_, typ_ctx, typ_rec)) =
  let cvars = (CVar.create ()) in
  let bvars = BVar.create () in
  let fvars = empty_fvars `open_term in
  let disambiguate_name = disambiguate_to_fvars in
  let (typ_ctx', bvars, _ ) =
    index_ctx disambiguate_name
      cvars bvars fvars typ_ctx
  in
  dprintf
    (fun p ->
      p.fmt "[index_el] ext block has length %d@." (length_typ_rec typ_rec));
  let (_, typ_rec') =
    index_typ_rec typ_rec {cvars; bvars; disambiguate_name} fvars
  in
  Apx.LF.SchElem (typ_ctx', typ_rec')

let index_schema (Ext.LF.Schema el_list) =
  Apx.LF.Schema (index_elements el_list)

(* Translation of external computations into approximate computations *)

  (*
let index_clobj cvars bvars fcvars m =
  match m with
  | Ext.Comp.MObj m ->
    let (m', fcvars') = index_term cvars bvars fcvars m in
    (Apx.Comp.MObj m', fcvars')
  | Ext.Comp.SObj s ->
    let (s', fcvars') = index_sub cvars  bvars fcvars s in
    (Apx.Comp.SObj s', fcvars')
   *)

let rec index_meta_obj cvars fcvars (l,cM) = match cM with
  | Ext.LF.CObj cpsi ->
     let (cPsi, _bvars, fcvars') =
       index_dctx disambiguate_to_fmvars cvars (BVar.create ()) fcvars cpsi
     in
     ( (l, Apx.Comp.CObj (cPsi))
     , fcvars'
     )

  | Ext.LF.ClObj (cpsi, s) ->
     let (cPsi, bvars, fcvars') =
       index_dctx disambiguate_to_fmvars cvars (BVar.create ()) fcvars cpsi
     in
     let disambiguate_name = disambiguate_to_fmvars in
     let (fcvars'', s') =
       index_sub s {cvars; bvars; disambiguate_name} fcvars'
     in
     ( (l,Apx.Comp.ClObj (cPsi, s'))
     , fcvars''
     )

and index_meta_spine cvars fcvars = function
  | Ext.Comp.MetaNil ->
      (Apx.Comp.MetaNil , fcvars)

  | Ext.Comp.MetaApp (m, s) ->
      let (m', fcvars')  = index_meta_obj  cvars fcvars m in
      let (s', fcvars'') = index_meta_spine cvars fcvars' s in
        (Apx.Comp.MetaApp (m', s') , fcvars'')

let rec index_compkind cvars fcvars = function
  | Ext.Comp.Ctype loc -> Apx.Comp.Ctype loc

  | Ext.Comp.PiKind (loc, cdecl, cK) ->
     let (cdecl', cvars', fcvars') =
       index_cdecl (fun _ -> `explicit) cvars fcvars cdecl
     in
     let cK' = index_compkind cvars' fcvars' cK in
     Apx.Comp.PiKind (loc, cdecl', cK')

let rec index_comptyp (tau : Ext.Comp.typ) cvars : Apx.Comp.typ fvar_state  =
  fun fvars ->
  match tau with
  | Ext.Comp.TypBase (loc, a, ms) ->
     begin
       try
         let a' = CompTyp.index_of_name a in
         let (ms', fvars) = index_meta_spine cvars fvars ms in
         (fvars, Apx.Comp.TypBase (loc, a', ms'))
       with Not_found ->
         try
           let a' = CompCotyp.index_of_name a in
           let (ms', fvars) = index_meta_spine cvars fvars ms in
           (fvars, Apx.Comp.TypCobase (loc, a', ms'))
         with Not_found ->
           begin
             try
               let a' = CompTypDef.index_of_name a in
               let (ms', fvars) = index_meta_spine cvars fvars ms in
               (fvars, Apx.Comp.TypDef (loc, a', ms'))
             with Not_found ->
               throw loc (UnboundName a)
           end
     end
  | Ext.Comp.TypBox (loc, (loc',mU)) ->
      let (fvars, mU') = index_cltyp loc cvars fvars mU in
        (fvars, Apx.Comp.TypBox (loc, (loc',mU')))

  | Ext.Comp.TypArr (loc, tau, tau') ->
      let (fvars, tau1) = index_comptyp tau cvars fvars in
      let (fvars, tau2) = index_comptyp tau' cvars fvars in
      (fvars, Apx.Comp.TypArr (loc, tau1, tau2))

  | Ext.Comp.TypCross (loc, tau, tau') ->
      let (fvars, tau) = index_comptyp tau cvars fvars in
      let (fvars, tau') = index_comptyp tau' cvars fvars in
      (fvars, Apx.Comp.TypCross (loc, tau, tau'))

  | Ext.Comp.TypPiBox (loc, cdecl, tau)    ->
     let (cdecl', cvars, fvars) =
       index_cdecl (fun _ -> `explicit) cvars fvars cdecl
     in
     let (fvars, tau') = index_comptyp tau cvars fvars in
     (fvars, Apx.Comp.TypPiBox (loc, cdecl', tau'))

      (*
  | Ext.Comp.TypInd (tau) ->
      let (tau1, fcvars1) = index_comptyp cvars fcvars tau in
        (Apx.Comp.TypInd tau1, fcvars1)
       *)

(* disambiguation strategies for computational names *)
let d_var, d_const, d_dataconst, d_codataobs =
  let mk ty f con loc x =
    let open Maybe in
    lazy
      (trying_index
         (fun () ->
           dprint (fun _ -> "disambiguting as " ^ ty);
           f x)
       $> fun k -> con loc k)
  in
  let var vars = mk "variable" (Var.index_of_name vars) (fun loc k -> Apx.Comp.Var (loc, k)) in
  let const = mk "constant" Comp.index_of_name (fun loc k -> Apx.Comp.Const (loc, k)) in
  let dataconst = mk "data constructor" CompConst.index_of_name (fun loc k -> Apx.Comp.DataConst (loc, k)) in
  let codataobs = mk "observation" CompDest.index_of_name (fun loc k e' -> Apx.Comp.Obs (loc, e', k)) in
  var, const, dataconst, codataobs

let disambiguate loc x ps =
  Maybe.choice (List.map (fun f -> f loc x) ps) |> Lazy.force

let rec index_exp cvars vars fcvars = function
  | Ext.Comp.Syn (loc , i)   ->
      Apx.Comp.Syn (loc, index_exp' cvars vars fcvars i)

  | Ext.Comp.Impossible (loc, i) ->
     Apx.Comp.Impossible (loc, index_exp' cvars vars fcvars i)

  | Ext.Comp.Fn (loc, x, e) ->
     let vars' = Var.extend vars (Var.mk_entry x) in
       Apx.Comp.Fn (loc, x, index_exp cvars vars' fcvars e)

  | Ext.Comp.Fun (loc, fbr) ->
    Apx.Comp.Fun(loc, index_fbranches cvars vars fcvars fbr)

  | Ext.Comp.MLam (loc, u, e) ->
      let cvars' = CVar.extend cvars (CVar.mk_entry u `explicit) in
        Apx.Comp.MLam (loc, u, index_exp cvars' vars fcvars e)

  | Ext.Comp.Pair (loc, e1, e2) ->
      let e1 = index_exp cvars vars fcvars e1 in
      let e2 = index_exp cvars vars fcvars e2 in
        Apx.Comp.Pair (loc, e1, e2)

  | Ext.Comp.LetPair (loc, i, (x, y, e)) ->
      let i' = index_exp' cvars vars fcvars i in
      let vars1 = Var.extend vars (Var.mk_entry x) in
      let vars2 = Var.extend vars1 (Var.mk_entry y) in
      let e' = index_exp cvars vars2 fcvars e in
        Apx.Comp.LetPair(loc, i', (x,y,e'))

  | Ext.Comp.Let (loc, i, (x, e)) ->
      let i' = index_exp' cvars vars fcvars i in
      let vars1 = Var.extend vars (Var.mk_entry x) in
      let e' = index_exp cvars vars1 fcvars e in
        Apx.Comp.Let (loc, i', (x,e'))

  | Ext.Comp.Box (loc, m)  ->
      let (m', fcvars')  = index_meta_obj  cvars fcvars m in
        Apx.Comp.Box (loc, m')

  | Ext.Comp.Case (loc, prag, i, ([Ext.Comp.Branch (_, Ext.LF.Empty, Ext.Comp.PatName (loc', name, Ext.Comp.PatNil _), e)] as branches)) ->
     (* if we have a single-branch case containing a name, we can
        rewrite it to a `Let' _if_ that name is not a data constructor.
        In principle, this should be unnecessary, because such a
        single-branch case should be identical to a `let` expression.
        However, the case-expression introduces new constraints which
        fail to be solved in some circumstances.
        (I dare you to comment out this case and see how many tests fail.)
        -je
      *)
     disambiguate loc' name [d_dataconst]
     |> Maybe.eliminate
          (fun _ -> (* the name is not a data constructor *)
            let i' = index_exp' cvars vars fcvars i in
            let vars1 = Var.extend vars (Var.mk_entry name) in
            let e' = index_exp cvars vars1 fcvars e in
            Apx.Comp.Let (loc, i', (name, e')))
          (fun x ->
            let i' = index_exp' cvars vars fcvars i in
            let branches' = List.map (index_branch cvars vars fcvars) branches in
            Apx.Comp.Case (loc, prag, i', branches'))

  | Ext.Comp.Case (loc, prag, i, branches) ->
      let i' = index_exp' cvars vars fcvars i in
      let _ = dprint (fun () -> "index case") in
      let branches' = List.map (function b -> index_branch cvars vars fcvars b) branches in
        Apx.Comp.Case (loc, prag, i', branches')

  | Ext.Comp.Hole (loc, name) -> Apx.Comp.Hole (loc, name)

and index_exp' cvars vars fcvars =
  function
  | Ext.Comp.Name (loc, x) ->
     disambiguate loc x [ d_var vars; d_const; d_dataconst ]
     |> Maybe.eliminate
          (fun _ -> throw loc (UnboundCompName x))
          (fun x -> x)

  (* Since observations are syntactically indistinguishable from
     function applications, they get parsed as applications in the
     external syntax.
     This case here performs the necessary disambiguation, since we
     now have scoping information, so we can determine whether the
     application is of a function or of an observation.
   *)
  | Ext.Comp.Apply (loc, Ext.Comp.Name (loc', c), e) ->
     (* we use the same logic as in the case for a bare `Name' but, we
        add one more check at the end to see if it's a declared
        observation.
      *)
     let mk_apply f loc' x =
       lazy
         Maybe.(
         f loc' x
         |> Lazy.force
         $> fun h e' -> Apx.Comp.Apply (loc, h, e'))
     in
     dprint (fun _ -> "[index_exp'] name disambiguation hack for observations");
     disambiguate loc' c
       [ mk_apply (d_var vars)
       ; mk_apply d_const
       ; mk_apply d_dataconst
       ; d_codataobs
       ]
     |> Maybe.eliminate
          (fun _ ->
            let hint =
              Maybe.(trying_index (fun _ -> CVar.index_of_name cvars c) &> pure `needs_box)
            in
            throw_hint' loc' hint (UnboundCompName c))
          (fun f -> index_exp cvars vars fcvars e |> f)

          (*
    begin
      try
        (* first try as an ordinary function *)
        let cid = CompConst.index_of_name c in
        let e' = index_exp  cvars vars fcvars e in
        Apx.Comp.Apply (loc, Apx.Comp.DataConst (loc', cid), e')
      with Not_found ->
        try
          (* then try as an observation *)
          let cid = CompDest.index_of_name c in
          let e' = index_exp  cvars vars fcvars e in
          Apx.Comp.Obs (loc, e', cid)
        with Not_found -> raise (Error (loc', UnboundCompConstName  c))
    end
           *)
  | Ext.Comp.Apply (loc, i, e) ->
      let i' = index_exp' cvars vars fcvars i in
      let e' = index_exp  cvars vars fcvars e in
      Apx.Comp.Apply (loc, i', e')

  | Ext.Comp.BoxVal (loc, m0) ->
      let (mobj', _ )  = index_meta_obj cvars fcvars m0 in
      Apx.Comp.BoxVal (loc, mobj')

  | Ext.Comp.PairVal (loc, i1, i2) ->
      let i1' = index_exp' cvars vars fcvars i1 in
      let i2' = index_exp' cvars vars fcvars i2 in
            Apx.Comp.PairVal (loc, i1', i2')

(* patterns can contain free contextual variables as well as free *computational* variables.
   `fvars` refers to computational variables whereas `fcvars` refers to contextual variables.
 *)
and index_pattern cvars fcvars fvars pat = match pat with
  | Ext.Comp.PatName (loc, c, pat_spine) ->
     (* disambiguation logic:
        First see if it's a defined constructor.
        Otherwise, it's a variable.
      *)
     begin match trying_index (fun _ -> CompConst.index_of_name c) with
     | Some k ->
        dprintf
          (fun p ->
            p.fmt "[index_pattern] %a is matching a constructor"
              Id.print c);
        let (pat_spine', fcvars', fvars')  = index_pat_spine cvars fcvars fvars pat_spine in
        (Apx.Comp.PatConst (loc, k, pat_spine'), fcvars', fvars')
     | None ->
        try
          let _ = Var.index_of_name fvars c in
          throw loc PatVarNotUnique
        with Not_found ->
          match pat_spine with
          | Ext.Comp.PatNil _ ->
             dprintf
               (fun p ->
                 p.fmt "[index_pattern] %a is a variable"
                   Id.print c);
             let fvars' = Var.extend fvars (Var.mk_entry c) in
             (Apx.Comp.PatFVar (loc, c), fcvars, fvars')
          | _ ->
             throw loc (NonemptyPatternSpineForVariable c)
     end

  | Ext.Comp.PatPair (loc, pat1, pat2) ->
     let (pat1, fcvars1, fvars1) = index_pattern cvars fcvars fvars pat1 in
     let (pat2, fcvars2, fvars2) = index_pattern cvars fcvars1 fvars1 pat2 in
     (Apx.Comp.PatPair (loc, pat1, pat2), fcvars2, fvars2)

  | Ext.Comp.PatMetaObj (loc, mO) ->
     let (mO', fcvars1) = index_meta_obj cvars fcvars mO in
     (Apx.Comp.PatMetaObj (loc, mO') , fcvars1, fvars)

  | Ext.Comp.PatAnn (loc, pat, tau) ->
     let (pat', fcvars', fvars') = index_pattern cvars fcvars fvars pat in
     let (fcvars'', tau') = index_comptyp tau cvars fcvars' in
     (Apx.Comp.PatAnn (loc, pat', tau') , fcvars'', fvars')

and index_pat_spine cvars fcvars fvars pat_spine = match pat_spine with
  | Ext.Comp.PatNil loc ->
     ( Apx.Comp.PatNil loc
     , fcvars
     , fvars
     )

  | Ext.Comp.PatApp (loc, pat, pat_spine) ->
      let (pat', fcvars1, fvars1) = index_pattern cvars fcvars fvars pat in
      let (pat_spine', fcvars2, fvars2) = index_pat_spine cvars fcvars1 fvars1 pat_spine in
      ( Apx.Comp.PatApp (loc, pat', pat_spine')
      , fcvars2
      , fvars2
      )

  | Ext.Comp.PatObs (loc, obs, pat_spine) ->
    let (pat_spine', fcvars1, fvars1) = index_pat_spine cvars fcvars fvars pat_spine in
    let cid =
      try
        CompDest.index_of_name obs
      with Not_found ->
        throw loc (UnboundObs obs)
    in
    ( Apx.Comp.PatObs (loc, cid, pat_spine')
    , fcvars1
    , fvars1
    )

and index_fbranches cvars vars fcvars fbranches = match fbranches with
  | Ext.Comp.NilFBranch loc -> Apx.Comp.NilFBranch loc
  | Ext.Comp.ConsFBranch (loc, (patS, e), fbr) ->
     let (patS', fcvars1, vars1) =
       index_pat_spine cvars
         (empty_fvars `open_term)
         (Var.create ())
         patS
     in
     let vars_all  = Var.append vars1 vars in
     let patS'' = reindex_pat_spine vars1 patS' in
     dprintf
       (fun p ->
         p.fmt "[index_fbranches] fcvars in pattern = @[<h>%a@]" print_fcvars fcvars1);
     dprintf
       (fun p ->
         p.fmt "[index_fbranches] fvars in pattern = @[<h>%a@]" print_fvars vars_all);
     let fcv2 = List.append fcvars1.vars fcvars.vars in
     let total_fcvars = { vars = fcv2; open_flag = `closed_term } in
     dprintf
       (fun p ->
         p.fmt "[Fun] fcvars in total = @[<h>%a@]" print_fcvars total_fcvars);
     let e' = index_exp cvars vars_all total_fcvars e in
     let brs = index_fbranches cvars vars fcvars fbr in
     Apx.Comp.ConsFBranch ( loc, (patS'', e'), brs)

(* reindex pattern *)
and reindex_pattern fvars pat = match pat with
  | Apx.Comp.PatFVar (loc, x) ->
      (* all free variable names must be in fvars *)
      let offset = Var.index_of_name fvars x in
        Apx.Comp.PatVar (loc, x, offset)

  | Apx.Comp.PatPair (loc, pat1, pat2) ->
      let pat1 = reindex_pattern fvars pat1 in
      let pat2 = reindex_pattern fvars pat2 in
        Apx.Comp.PatPair (loc, pat1, pat2)
  | Apx.Comp.PatConst (loc, c, pat_spine) ->
      let pat_spine'  = reindex_pat_spine  fvars pat_spine in
        Apx.Comp.PatConst (loc, c, pat_spine')

  | Apx.Comp.PatMetaObj (loc, mO) -> pat

  | Apx.Comp.PatAnn (loc, pat, tau) ->
      let pat' = reindex_pattern fvars pat in
        Apx.Comp.PatAnn (loc, pat', tau)

and reindex_pat_spine fvars pat_spine = match pat_spine with
  | Apx.Comp.PatNil loc -> Apx.Comp.PatNil loc
  | Apx.Comp.PatApp (loc, pat, pat_spine) ->
      let pat' = reindex_pattern fvars pat in
      let pat_spine' = reindex_pat_spine fvars pat_spine in
        Apx.Comp.PatApp (loc, pat', pat_spine')
  | Apx.Comp.PatObs (loc, obs, pat_spine) ->
    Apx.Comp.PatObs (loc, obs, reindex_pat_spine fvars pat_spine)

and index_branch cvars vars fcvars branch =
  match branch with
  | Ext.Comp.Branch (loc, cD, Ext.Comp.PatMetaObj (loc', mO), e) ->
    let _ = dprint (fun () -> "index_branch") in
    (* computing fcvars' is unnecessary? -bp *)
    let fcvars' =
      Maybe.eliminate
        (Misc.const Misc.id)
        (fun psi_name -> extending_by psi_name)
        (get_ctxvar_mobj mO)
        (empty_fvars `open_term)
    in
    let (cD', cvars1, fcvars1)  =
      dprintf (fun p -> p.fmt "[index_branch] indexing cD in branch at %a" Loc.print_short loc);
      index_mctx (CVar.create()) fcvars' cD
    in
    let (mO', fcvars2) = index_meta_obj cvars1 fcvars1 mO in
    dprintf
      (fun p ->
        p.fmt "fcvars in pattern = @[<h>%a@]" print_fcvars fcvars2);
    let cvars_all  = CVar.append cvars1 cvars in
    let fcvars3    =
      { open_flag = `closed_term
      ; vars = List.append fcvars2.vars fcvars.vars
      }
    in
    dprint (fun _ -> "indexing branch body");
    let e'         = index_exp cvars_all vars fcvars3 e in
      Apx.Comp.Branch (loc, cD', Apx.Comp.PatMetaObj (loc', mO'), e')

  | Ext.Comp.Branch (loc, cD, pat, e) ->
     let empty_fcvars = empty_fvars `open_term in
     dprintf (fun p -> p.fmt "[index_branch] general pattern at %a" Loc.print_short loc);
     let (cD', cvars1, fcvars1)  =
       index_mctx (CVar.create()) empty_fcvars cD
     in
     let (pat', fcvars2, fvars2) = index_pattern cvars1 fcvars1 (Var.create ())  pat in
     dprint (fun () -> "[index_branch] index_pattern done");
     let cvars_all = CVar.append cvars1 cvars in
     let vars_all = Var.append fvars2 vars in
     let pat'' = reindex_pattern fvars2 pat' in
     dprint (fun () -> "[index_branch] reindex_pattern done");
     dprintf
       (fun p ->
         p.fmt "fcvars in pattern = @[<h>%a@]" print_fcvars fcvars2);
     let fcvars3 = append_fvars fcvars2 fcvars `closed_term in
     dprint (fun _ -> "indexing branch body");
     let e' = index_exp cvars_all vars_all fcvars3 e in
     Apx.Comp.Branch (loc, cD', pat'', e')

let rec index_gctx cvars vars fvars = function
  | Ext.LF.Empty -> Ext.LF.Empty, vars, fvars
  | Ext.LF.Dec (cG, Ext.Comp.CTypDecl (x, tau)) ->
     let cG', vars, fvars = index_gctx cvars vars fvars cG in
     let fvars, tau' = index_comptyp tau cvars fvars in
     let vars = Var.extend vars (Var.mk_entry x) in
     Apx.LF.Dec (cG', Apx.Comp.CTypDecl (x, tau')), vars, fvars

let rec index_proof cvars vars fvars = function
  | Ext.Comp.Incomplete (loc, name) -> Apx.Comp.Incomplete (loc, name)
  | Ext.Comp.Command (loc, cmd, p) ->
     let cmd', vars, cvars = index_command cvars vars fvars cmd in
     let p' = index_proof cvars vars fvars p in
     Apx.Comp.Command (loc, cmd', p')
  | Ext.Comp.Directive (loc, d) ->
     let d' = index_directive cvars vars fvars d in
     Apx.Comp.Directive (loc, d')

and index_command cvars vars fvars = function
  | Ext.Comp.By (loc, i, x) ->
     let i' = index_exp' cvars vars fvars i in
     let vars = Var.extend vars (Var.mk_entry x) in
     Apx.Comp.By (loc, i', x), vars, cvars
  | Ext.Comp.Unbox (loc, i, x) ->
     let i' = index_exp' cvars vars fvars i in
     let cvars = CVar.extend cvars (CVar.mk_entry x `explicit) in
     Apx.Comp.Unbox (loc, i', x), vars, cvars

and index_directive cvars vars fvars = function
  | Ext.Comp.Intros (loc, h) ->
     let _, _, h' = index_hypothetical h in
     Apx.Comp.Intros (loc, h')
  | Ext.Comp.Solve (loc, e) ->
     let e' = index_exp cvars vars fvars e in
     Apx.Comp.Solve (loc, e')
  | Ext.Comp.Split (loc, i, bs) ->
     let i' = index_exp' cvars vars fvars i in
     let bs' = List.map index_split_branch bs in
     Apx.Comp.Split (loc, i', bs')
  | Ext.Comp.Suffices (loc, i, tau_ps) ->
     let i' = index_exp' cvars vars fvars i in
     let ps' =
       List.map
         begin fun (loc, tau, p) ->
         let (_, tau') = index_comptyp tau cvars (empty_fvars `closed_term) in
         let p' = index_proof cvars vars fvars p in
         (loc, tau', p')
         end
         tau_ps
     in
     Apx.Comp.Suffices (loc, i', ps')

and index_split_branch =
  fun Ext.Comp.({ case_label; branch_body; split_branch_loc }) ->
  let cvars, fvars, branch_body = index_hypothetical branch_body in
  Apx.Comp.(
    { case_label
    ; branch_body
    ; split_branch_loc
    }
  )

and index_hypothetical h =
  let Ext.Comp.({ hypotheses = { cD; cG }; proof; hypothetical_loc }) = h in
  let cvars =
    Context.to_list_map_rev cD
      Ext.LF.(fun _ (Decl (x, _, dep)) -> (x, Depend.to_plicity dep))
    |> CVar.of_list
  in
  let vars =
    Context.to_list_map_rev cG
      (fun _ (Ext.Comp.CTypDecl (x, _)) -> x)
    |> Var.of_list
  in
  let proof =
    index_proof cvars vars (empty_fvars `closed_term) proof in
  let cD, cvars, fvars = index_mctx (CVar.create ()) (empty_fvars `closed_term) cD in
  let cG, vars, fvars = index_gctx cvars (Var.create ()) fvars cG in
  ( cvars
  , fvars
  , Apx.Comp.({ hypotheses = { cD; cG }; proof; hypothetical_loc })
  )

let comptypdef (cT, cK) =
  let cK' = index_compkind (CVar.create ())  (empty_fvars `closed_term) cK in
  let rec unroll cK cvars =
    match cK with
    | Apx.Comp.Ctype _ -> cvars
    | Apx.Comp.PiKind (loc, Apx.LF.Decl(u, ctyp,dep), cK) ->
       let cvars' = CVar.extend cvars (CVar.mk_entry u `explicit) in
       unroll cK cvars'
  in
  let (_, tau) =
    index_comptyp cT (unroll cK' (CVar.create ())) (empty_fvars `closed_term)
  in
  (tau, cK')

let run_empty d f =
  f (empty_lf_indexing_context d) (empty_fvars `closed_term)

let kind d k = run_empty d (index_kind k)
let typ d tA = run_empty d (index_typ tA)
let schema = index_schema
let mctx cD =
  let (cD', _, _) =
    index_mctx (CVar.create ()) (empty_fvars `open_term) cD
  in
  cD'
let compkind = index_compkind (CVar.create ())  (empty_fvars `open_term)

let hcomptyp cvars tau =
  let (_, tau') = index_comptyp tau cvars (empty_fvars `open_term) in
  tau'

let comptyp = hcomptyp (CVar.create ())

let exp vars e =
  index_exp (CVar.create ()) vars (empty_fvars `closed_term) e

let exp' vars i =
  index_exp' (CVar.create ()) vars (empty_fvars `closed_term) i

let proof vars p =
  index_proof (CVar.create ()) vars (empty_fvars `closed_term) p

let thm vars = function
  | Ext.Comp.Program e -> Apx.Comp.Program (exp vars e)
  | Ext.Comp.Proof p -> Apx.Comp.Proof (proof vars p)

let hexp cvars vars e =
  let closed =
    if Store.CVar.length cvars = 0 then
      `closed_term
    else
      `open_term
  in
  index_exp cvars vars (empty_fvars closed) e

let hexp' cvars vars e =
  let closed =
    if Store.CVar.length cvars = 0 then
      `closed_term
    else
      `open_term
  in
  index_exp' cvars vars (empty_fvars closed) e
