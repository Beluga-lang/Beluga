(** Checking termination of a function *)

open Support.Equality
open Support
open Beluga_syntax
open Int
module Unify = Unify.StdTrail
module P = Prettyint.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprintf, dprint, dprnt) = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

type error =
  | NoPositiveCheck of string
  | NoStratifyCheck of string
  | NoStratifyOrPositiveCheck of string
  | WrongArgNum of Id.cid_comp_typ * int
  | RecCallIncompatible of LF.mctx * Comp.ih_arg * Comp.ih_decl
  | NotImplemented of string
  | TooManyArg

exception E of Location.t * error

let throw loc e = raise (E (loc, e))

let error_printer = function
  | TooManyArg ->
      Format.dprintf "Totality declaration for has too many arguments.@\n"
  | RecCallIncompatible (cD, x, Comp.WfRec (f, args, _)) ->
      begin match (x, args) with
      | (_, []) ->
        Format.dprintf "Recursive call is incompatible with valid automatically generated recursive calls. \n Report as a bug."
      | (Comp.M (cM, _ ), (Comp.M (cM', _ ) :: _)) ->
        Format.dprintf "Recursive call is incompatible with valid automatically generated recursive calls. \nBeluga cannot establish that the given recursive call is a size-preserving variant of it.\nArgument found: %a@\nArgument expected: %a@"
          (P.fmt_ppr_cmp_meta_obj cD P.l0) cM
          (P.fmt_ppr_cmp_meta_obj cD P.l0) cM'

      | (Comp.M (cM, _ ), (Comp.V _ :: _)) ->
        Format.dprintf "Recursive call is incompatible with valid automatically generated recursive calls. \n\nArgument found: %a@\nExpected computation-level variable.\n\nCheck specified totality declaration. "
          (P.fmt_ppr_cmp_meta_obj cD P.l0) cM

      | (Comp.V _, _) ->
        Format.dprintf "Recursive call is incompatible with valid automatically generated recursive calls. \n\n Found computation-level variable while generated recursive call expected a meta-object.\n\nCheck specified totality declaration."
      end
  | NoPositiveCheck n ->
      Format.dprintf "Datatype %s has not been checked for positivity or stratification."
        n
        (* (Name.render_name n) *)
  | NoStratifyCheck n ->
      Format.dprintf "Datatype %s has not been checked for stratification."
        n
        (* (Name.render_name n) *)
  | NoStratifyOrPositiveCheck n ->
      Format.dprintf "Datatype %s has not been checked for stratification or positivity."
        n
        (* (Name.render_name n) *)
  | WrongArgNum (n, num) ->
      Format.dprintf "Stratification declaration for %s uses the argument number %d which is out of bounds."
        (R.render_cid_comp_typ n)
        num
  | NotImplemented n ->
      Format.dprintf "The case %s is not implemented yet."
        n

let () =
  Error.register_exception_printer (function
    | E (location, error) ->
        Error.located_exception_printer (error_printer error)
          (List1.singleton location)
    | exn -> Error.raise_unsupported_exception_printing exn)

let print_str f = dprint f
(* let dprint f = print_string ("\n" ^ f ())*)

exception Not_compatible
exception CtxNot_compatible

let enabled = ref false

type rec_arg =
  | M of Comp.meta_obj
  | V of Comp.exp

let shiftArg k =
  function
  | Comp.V x -> Comp.V (x + k)
  | arg -> arg

let rec shiftIH k =
  function
  | LF.Empty -> LF.Empty
  | LF.Dec (cIH', Comp.WfRec (f, args, tau)) ->
     let args' = List.map (shiftArg k) args in
     LF.Dec (shiftIH k cIH', Comp.WfRec (f, args', tau))

let shift = shiftIH 1

let sub_smaller (_, n) =
  function
  | LF.Shift n' ->
     (n - n') < n'
  | _ -> false

let rec smaller_meta_obj =
  function
  | LF.CObj (LF.DDec _) -> true
  | LF.ClObj (phat, LF.MObj (LF.Root (l', h, spine, plicity))) ->
     begin match h with
     | LF.Const _ -> true
     | LF.BVar _ -> true
     | LF.PVar (_, s) ->
        begin match spine with
        | LF.Nil -> sub_smaller phat s
        | _ -> true
        end
     | LF.Proj (h, _) ->
        smaller_meta_obj
          (LF.ClObj
             ( phat
             , LF.MObj (LF.Root (l', h, spine, plicity))
             )
          )
     | LF.MVar (_, s) -> sub_smaller phat s
     | _ -> false
     end
  | LF.ClObj (phat, LF.PObj h) ->
     begin match h with
     | LF.PVar (_, s) ->
        (* print_string "Checking whether proj is smaller (1)\n";*)
        sub_smaller phat s
     | _ -> false
     end

  | _ -> false

let rec mark_gctx =
  function
  | LF.Empty -> LF.Empty
  | LF.Dec (cG, Comp.CTypDecl (x, tau, _)) ->
     LF.Dec (mark_gctx cG, Comp.CTypDecl (x, tau, true))

let rec struct_smaller =
  function
  | Comp.PatMetaObj (loc', (_, mO)) -> smaller_meta_obj mO
  | Comp.PatConst _ -> true
  | Comp.PatVar _ -> false
  | Comp.PatTuple (_, pats) ->
     (* This is quite naive - possibly one of them being smaller is enough *)
     List2.for_all struct_smaller pats
  | Comp.PatAnn (_, pat, _, _) -> struct_smaller pat
  | _ -> false

let order_to_string =
  function
  | None -> " _ "
  | Some (Comp.Arg x) -> string_of_int x

(** Determine whether the arguments given in a totality declaration are valid.
    n: number of args
    tau: type of the recursive function
 *)
let is_valid_args tau n =
  let rec go tau n =
    match (tau, n) with
    | (Comp.TypPiBox (_, _, tau), 1)
      | (Comp.TypArr (_, _, tau), 1) ->
       true
    | (Comp.TypPiBox (_, _, tau), n)
      | (Comp.TypArr (_, _, tau), n) ->
       go tau (n-1)
    | _ -> false
  in
  n = 0 || go tau n

(* Check whether the argument specified by i
   corresponds to a given totality order

   i = Var x then Order.Arg x
   i = Pair (Var x, Var y) then Order.Lex / Order.Sim
   where x and y are in the specified order.


   let satisfies_order cD cG i =
   let total_decs = !mutual_decs in
   (* let m = List.length total_decs in *)
   (* let cg_length = Context.length cG in *)
   let rec relative_order (Comp.Var x) (tau, order, l, k, w) = match tau with
   (* k = implicit arguments encountered so far
   l = non-implicit arguments encountered so far
   w = total number of arguments in totality declaration
   w - k = number of variables introduces via fn in cG
 *)
 | Comp.TypPiBox (_, tau) -> relative_order (Comp.Var x) (tau, order, l, k + 1, w)
 | Comp.TypArr (_, tau) ->
 (match order with
 | Order.Arg y -> let _p = y - k - l in
 if x = (w - y) + 1 (* assumes that all cdecls are before the actual
 rec. arg. *)
 (* comparing de Bruijn position of x in cG with the position
 described by y *)
 then
 ((* print_string ("Considering inductive case for " ^
 P.expSynToString cD cG i ^ " - comparing to position " ^
 string_of_int y ^
 " - comgparing to relative position " ^ string_of_int (y-k-l) ^ " - Yes\n");*)true)
 else
 ((* print_string ("Considering inductive case for " ^
 P.expSynToString cD cG i ^ " - comparing to arg. "
 ^ string_of_int y ^
 " - comparing to relative position " ^ string_of_int (y-k) ^ "? - No\n");*)
 relative_order (Comp.Var x) (tau, order, l + 1, k, w))

 | _ -> false)

 | _ -> false
 in
 match i with
 | Comp.Var x ->
 List.exists (function dec ->
 (* let _ = (print_string ("Considering type " ^
 P.compTypToString LF.Empty dec.typ ^ "\n");
 print_string ("In cG " ^ P.gctxToString cD cG ^ "\n")) in
 let _ = print_string ("Given order " ^ order_to_string
 dec.order ^ "\n") in
 let _ = print_string ("Considering variable " ^
 P.expSynToString cD cG i ^ "\n") in
 *)
 let w = List.length (dec.args) in (* total arguments given in totality declaration *)
 match dec.order with
 | None -> false
 | Some order ->
 relative_order i (dec.typ, order, 0, 0, w)) total_decs
 | _ -> false

 *)

(** Converts the list of totality declarations into an induction ordering list *)
let get_order (mfs : Comp.total_dec list) =
  let f dec =
    let open Comp in
    let tau = dec.tau in
    (* let _ = dprint (fun () -> "[get_order] " ^ (R.render_cid_prog dec.name) ^
        " : " ^ P.compTypToString (LF.Empty) dec.typ) in *)
    match dec.order with
    | `inductive (Arg x) ->
       (dec.name, Some [x], (tau, Whnf.m_id))
    | `inductive (Lex xs) ->
       let xs = List.map (fun (Arg x) -> x) xs in
       dprintf (fun p ->
         p.fmt "[get_order] %a"
         (List.pp ~pp_sep:Format.pp_print_space Format.pp_print_int) xs
       );
       (dec.name, Some xs, (tau, Whnf.m_id))
    | `not_recursive
      | `trust
      | `partial ->
       (dec.name, None, (tau, Whnf.m_id))
  in
  List.map f mfs

(** Looks up a declaration based on a function name *)
let lookup_dec f : Comp.total_dec list -> Comp.total_dec option =
  let open Comp in
  List.find_opt (fun { name; _ } -> Name.(name = f))

(** Gets the induction order for the function with name `f`
    Returns None if the
 *)
let get_order_for mfs f : int list option =
  let open Comp in
  let rec find =
    function
    | [] -> None
    | { name; order; _ } :: decs ->
       if Name.(name = f)
       then
         begin
           let open Option in
           order |> option_of_total_dec_kind >>= Order.list_of_order
         end
       else
         find decs
  in
  find mfs

(* Given C:U, f, order Arg i, and type T of f where
   T = Pi X1:U1, ... X:i:Un. T, generate
   meta-variables for all argument up to i, i.e. theta,
   [theta]Un = U

   and return [theta](f X1 ... X(i-1)) C : [theta]T

   check: recursive call and its corresponding type are closed .

 *)

let gen_var' loc cD (x, cU) =
  match cU with
  | LF.ClTyp (LF.MTyp tA, cPsi) ->
     let psihat = Context.dctxToHat cPsi in
     let tM = Whnf.etaExpandMMV loc cD cPsi (tA, Substitution.LF.id) x Substitution.LF.id Plicity.implicit Inductivity.not_inductive in
     ( (loc, LF.ClObj (psihat, LF.MObj tM))
     , LF.ClObj (psihat, LF.MObj tM)
     )
  | LF.ClTyp (LF.PTyp tA, cPsi) ->
     let psihat = Context.dctxToHat cPsi in
     let p = Whnf.newMPVar (Some x) (cD, cPsi, tA) Plicity.implicit Inductivity.not_inductive in
     let h = LF.MPVar ((p, Whnf.m_id), Substitution.LF.id) in
     ( (loc, LF.ClObj (psihat, LF.PObj h))
     , LF.ClObj (psihat, LF.PObj h)
     )
  | LF.ClTyp (LF.STyp (cl, cPhi), cPsi) ->
     let psihat = Context.dctxToHat cPsi in
     let s = Whnf.newMSVar (Some x) (cD, cl, cPsi, cPhi) Plicity.implicit Inductivity.not_inductive in
     let sigma = LF.MSVar (0, ((s, Whnf.m_id), Substitution.LF.id)) in
     ( (loc, LF.ClObj (psihat, LF.SObj sigma))
     , LF.ClObj (psihat, LF.SObj sigma)
     )

  | LF.CTyp (schema_cid) ->
     let mmvar =
       let open! LF in
       Whnf.newMMVar' (Some x) (cD, CTyp schema_cid) Plicity.implicit Inductivity.not_inductive
     in
     let cPsi = LF.CtxVar (LF.CInst (mmvar, Whnf.m_id)) in
     ( (loc, LF.CObj cPsi)
     , LF.CObj (cPsi)
     )

let gen_var loc cD (LF.Decl { name = x; typ = cU; _ }) =
  (gen_var' loc cD (x, cU) , cU)

(*
gen_meta_obj sW (k, cdecl) = cM


If  cD |- cdecl   where cdecl = clTyp (cU)
    k-th position in cD is cdecl (modulo some shifts),

then

   a) if cU is a schema , then we simply create a CtxVar with the offset k

   b) if cU is a contextual type [cPsi |- _ ]
      then
       cD ; cPsi' |- r : cPsi   where cPsi' is a generalization of th LF context cPsi
       s.t. cPsi' has schema sW and r is a variable mapping

       and

       cD ; cPsi' |- cM : cU

 *)

let gen_meta_obj (k, wk) cdecl =
  match cdecl with
  | LF.CTyp (schema_cid) ->
     (Location.ghost, LF.CObj (LF.CtxVar (LF.CtxOffset k)))
  | LF.ClTyp (LF.MTyp tA, cPsi) ->
     let psihat' = Context.dctxToHat cPsi in
     (* let psihat' = Whnf.cnorm_psihat phat theta in *)
     (* BP: Generate a substitution from cPsi to padded cPsi that
            matches the required schema
            [cPsi |- tA]  (from pattern variables in cD)

      *)
     let mv = LF.MVar (LF.Offset k, wk) in
     let tM = LF.Root (Location.ghost, mv, LF.Nil, Plicity.explicit) in
     (Location.ghost, LF.ClObj (psihat', LF.MObj tM))

  | LF.ClTyp (LF.PTyp tA, cPsi) ->
     let psihat' = Context.dctxToHat cPsi in
     (* let psihat' = Whnf.cnorm_psihat phat theta in *)
     let pv = LF.PVar (k, wk) in
     (Location.ghost, LF.ClObj (psihat', LF.PObj pv))

  | LF.ClTyp (LF.STyp (_, cPsi), cPhi) ->
     let sv = LF.SVar (k, 0, wk) in
     let psihat' = Context.dctxToHat cPsi in
     (* let psihat' = Whnf.cnorm_psihat phat theta in *)
     (Location.ghost, LF.ClObj (psihat', LF.SObj sv))

let uninstantiated_arg cM =
  match Whnf.cnormMetaObj (cM, Whnf.m_id) with
  | (_, LF.CObj (LF.CtxVar (LF.CInst _))) -> true
  | (_, LF.ClObj (_, LF.MObj (LF.Root (_, h, _, _)))) ->
     begin match h with
     | LF.MMVar _ -> true
     | _ -> false
     end
  | (_, LF.ClObj ((Some _, n), LF.PObj h)) ->
     if n > 0
     then
       match h with
       | LF.MPVar _ -> true
       | _ -> false
     else
       false
  | (_, LF.ClObj (_, LF.SObj (LF.MSVar _))) -> true
  | _ -> false

let rec generalize =
  function
  | [] -> []
  | Comp.M (cM, cU) :: args ->
     if uninstantiated_arg cM
     then Comp.DC :: generalize args
     else Comp.M (cM, cU) :: generalize args
  | Comp.V x :: args ->
     Comp.V x :: generalize args
  | Comp.DC :: args ->
     Comp.DC :: generalize args

let valid_args args =
  match List.rev args with
  | Comp.DC :: _ -> false
  | _ -> true


(* genTypeAgainstSchema cD cPsi b tA  schema = H , tA_g

Precondition:
  cD ; cPsi |- tA    and  schema = W1 + ... Wn where Wi = some cPhi' block (x1:A1, ... xk:Ak) as cPhi
  Further, let b be BVar 0

If
   there exists  Wi and a substitution cD ; cPsi |- t : cPhi'
   s.t. [t][b.1/x1, ... b.j-1/x(j-1)]Aj = tA

then

  (b.j ,   block [t](x1:A1, ... xk:Ak))

 *)
let genTypeAgainstSchema cD cPsi b tA (LF.Schema elements as schema) =
  dprintf
    begin fun p ->
    p.fmt "[genTypeAgainstSchema] @[<v>type %a@,against@,schema %a@]"
      (P.fmt_ppr_lf_typ cD cPsi P.l0) tA
      (P.fmt_ppr_lf_schema P.l0) schema
    end;
  (* existsElem b (1,n) elem = x.j iff
     elem = SchElem (some cPhi block (x1:A1, ... xn:An)) and [b.1/x1, ... b.j-1/x(j-1)]Aj = tA  *)
  let existsElem b (1, n) (LF.SchElem (some_part, block_part))  =
    let sArec =
    match Whnf.whnfTyp (tA, Substitution.LF.id) with
    | (LF.Sigma tArec, s') -> (tArec, s')
    | (tA', s') -> (LF.SigmaLast (None, tA'), s') in
   let dctx = Lfcheck.projectCtxIntoDctx some_part in
   let dctxSub = Lfcheck.ctxToSub' cPsi dctx in
    try
      Unify.unifyTypRec cD cPsi (block_part, dctxSub) sArec;
      Some (b, tA)
    with Unify.Failure _  ->  None (* find an element in block_part that unifies with tA – todo *)
  in
  let rec checkElems elements = match elements with
    | [] -> None (* generalization not possible, i.e. there exists no schema element where tA fits *)
    | elem :: elems ->
       begin
         let LF.SchElem (_, trec) = elem in
           match existsElem b (1, LF.blockLength trec) elem with
         | Some (h, tA) -> Some (h , tA)
         | None -> (* no generalization possible – check the reset of elements *)
            checkElems elems
       end
 in
 checkElems elements

(* gen_ctx cD ; cPsi sW = cPsi'

If  cD  |- cPsi ctx
then
   cD |- cPsi' : sW
   cD ; cPsi' |- wk : cPsi

note that we always generate the identity here
but when checking the actual recursive call arg against the generated one
we will check for weakenings, etc.
 *)

let gen_ctx cD cPsi ((schema_id : Id.cid_schema), schema)  =  (cPsi , Substitution.LF.id)


(*
gen_arg cD (k, cU) cU0 = cM

if cD |- cU  and k is a position in cD
    . |- cU0  where cU0 may contain references to contextual variables
              and cU0 is in normal form
then
   cD |- cM : cU0

If cU / cU0 are contextual types and
  cU = [cPsi |- mT] and cU0 = [cPsi0 |- mT0]
there also exists a variable substitution wk s.t.
  cPsi' |- wk : cPsi and a meta-substitution {theta} for all the
  references in cU0 s.t.

  [wk]mT = {theta}mT0 and cPsi' = {theta}cPsi0

 *)
let gen_arg cD  (k, cU) cU0 =
  match cU0 with
  | LF.CTyp _schema ->
      (Unify.unifyMetaTyp cD (cU, Whnf.m_id) (cU0, Whnf.m_id);
       gen_meta_obj (k,Substitution.LF.id) cU)
  | LF.ClTyp (mT1, cPsi1) ->
      let LF.ClTyp (LF.MTyp tA, cPsi) = cU in
      (Unify.unifyMetaTyp cD (cU , Whnf.m_id) (cU0, Whnf.m_id);
       gen_meta_obj (k, Substitution.LF.id) cU)
(* creates a meta-variable Delta ; cPsi' |- u[wk] : [wk]tA where u::[Psi |- tA] *)

 (* Given i and tau, compute an ordered list L of argments
   s.t. for all k < i

   if k-th position in L = 0 then
   type at i-th position in tau does NOT depend on it

   k-th position in L = 1 then
   type at i-th position in tau does depend on it


   We then generate a spine of arguments using L; any position
   marked with 0 in L, will generate DC; positions marked with 1
   will generate a term M.

  Invariant:

  If cD |- cU where cU is the type of the induct. argument
     which is in k-th position in cD
     cD |- ttau (type of the recursive function that is being called)

  then
      args is an ordered list of n objects
      (i.e. contextual objects cM, computation variables,
            and don't care arg. not yet determined)
      cD |- args <| tau => tau_r
     (the list of arguments/spine checks against a prefix of tau and
      returns the remaining part of tau. )
 *)

let rec rec_spine cD (k, cU) =
  function
  | (0, ttau) -> ([], Whnf.cnormCTyp ttau)
  | (1, (Comp.TypPiBox (_, LF.Decl { typ = cU'; _ }, tau), theta)) ->
     let cU0 = Whnf.cnormMTyp (cU', theta) in
         begin
           try
             dprintf (fun p -> p.fmt "Generate rec. argument\n");
             let (_, ft) as cM = gen_arg cD  (k, cU) cU0  in
             dprintf (fun p -> p.fmt  "Generated rec. arg. %a@\n" (P.fmt_ppr_cmp_meta_obj cD P.l0) cM);
             let (spine, tau_r) = rec_spine cD (k, cU) (0, (tau, LF.MDot (ft, theta))) in
             (Comp.M (cM, cU) :: spine, tau_r)
           with
           | e ->
              raise Not_compatible
         end

  | (1, (Comp.TypArr (_, Comp.TypBox (loc, LF.ClTyp (LF.MTyp tA', cPsi')), tau), theta)) ->
     let cPsi0 = Whnf.cnormDCtx (cPsi', theta) in
     let tA0   = Whnf.cnormTyp (tA', theta) in
     let cU' = LF.ClTyp (LF.MTyp tA0, cPsi0) in
     begin
       try
         let cM = gen_arg cD (k, cU) cU' in
         (* if we succeed, then cD |- cU = cU' *)
         let (spine, tau_r) = rec_spine cD (k, cU) (0, (tau, theta)) in
         (Comp.M (cM, cU') :: spine, tau_r)
       with
       | e ->
          raise Not_compatible
     end
  | (1, ttau) ->
     let tau = Whnf.cnormCTyp ttau in
     dprintf
       begin fun p ->
       p.fmt "[rec_spine] @[<v>Incompatible IH: ran out of arguments;@,last type is: %a@]"
         (P.fmt_ppr_cmp_typ cD P.l0) tau
       end;
     raise Not_compatible

  | (n, (Comp.TypPiBox (_, cdecl, tau), theta)) ->
     let ((cN, ft), cU0) = gen_var Location.ghost cD (Whnf.cnormCDecl (cdecl, theta))  in
     (* cN is a meta-variable that will be instantiated when we encounter the
        the rec. argument; note that the rec. argument and it's type may depend on cN *)
     let (spine, tau_r) = rec_spine cD (k, cU) (n - 1, (tau, LF.MDot (ft, theta))) in
     (Comp.M (cN, cU0) :: spine, tau_r)

  | (n, (Comp.TypArr (_, _, tau2), theta)) ->
     let (spine, tau_r) = rec_spine cD (k, cU) (n - 1, (tau2, theta)) in
     (Comp.DC :: spine, tau_r)

let rec rec_spine' cD (x, ttau0) =
  function
  | (0, ttau) -> ([], Whnf.cnormCTyp ttau)

  | (1, (Comp.TypPiBox _, _)) ->
     raise Not_compatible (* Error *)

  | (1, (Comp.TypArr (_, tau1, tau2), theta)) ->
     begin
       try
         Unify.unifyCompTyp cD ttau0 (tau1, theta);
         let (spine, tau_r) = rec_spine' cD (x, ttau0) (0, (tau2, theta)) in
         (Comp.V x :: spine, tau_r)
       with
       | _ -> raise Not_compatible
     end
  | (n, (Comp.TypPiBox (_, cdecl, tau), theta)) ->
     let ((cN, ft) , cU0) = gen_var Location.ghost cD (Whnf.cnormCDecl (cdecl, theta) ) in
     (* cN is a meta-variable that will be instantiated when we encounter the
        the rec. argument; note that the rec. argument and it's type may depend on cN *)
     let (spine, tau_r) = rec_spine' cD (x, ttau0) (n - 1, (tau, LF.MDot (ft, theta))) in
     (Comp.M (cN, cU0) :: spine, tau_r)

  | (n, (Comp.TypArr (_, _, tau2), theta)) ->
     let (spine, tau_r) = rec_spine' cD (x, ttau0) (n - 1, (tau2, theta)) in
     (Comp.DC :: spine, tau_r)

let rec gen_rec_calls cD cIH (cD', j) mfs =
  match cD' with
  | LF.Empty -> cIH

  | LF.Dec (cD', LF.Decl { name = u; typ = cU; inductivity = Inductivity.Not_inductive; _ }) ->
     dprintf
       begin fun p ->
       p.fmt "[gen_rec_calls] @[<v>ignoring cD' entry %d, i.e.\
              @,@[<hv 2>%a :@ @[%a@]@]\
              @,since it isn't inductive\
              @]"
         j
         Name.pp u
         P.(fmt_ppr_cmp_meta_typ cD') cU
       end;
     gen_rec_calls cD cIH (cD', j + 1) mfs

  | LF.Dec (cD', (LF.Decl { name = u; typ = cU; plicity; inductivity } as d)) ->
     let k = j + 1 in
     let cU' = Whnf.cnormMTyp (cU, LF.MShift (j + 1)) in
     let mf_list = get_order mfs in
     dprintf
       begin fun p ->
       p.fmt "[gen_rec_calls] @[<v>Generate rec. calls given variable@,@[%a@]\
              @,considering a total of %d recursive functions@]"
         (P.fmt_ppr_lf_ctyp_decl cD') d
         (List.length mf_list)
       end;

     let mk_wfrec (f, x, ttau) =
       dprintf
         begin fun p ->
         p.fmt "[mk_wf_rec] @[<v>for @[%a@] for position %d\
                @,@[<hv 2>type of recursive call:@ @[%a@]@]@]"
           (P.fmt_ppr_lf_ctyp_decl cD') d
           x
           (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
         end;
       let (args, tau) = rec_spine cD (k, cU') (x, ttau) in
       (* rec_spine may raise Not_compatible *)
       dprintf
         begin fun p ->
         p.fmt "[mk_wfrec] generated Arguments for rec. call %a"
           P.(fmt_ppr_cmp_ih_args cD LF.Empty) args
         end;
       let args = generalize args in
       dprintf
         begin fun p ->
         p.fmt "[mk_wfrec] generated recursive Call : %a"
           P.(fmt_ppr_cmp_ih cD LF.Empty) (Comp.WfRec (f, args, tau))
         end;
       Comp.WfRec (f, args, tau)
     in
     let rec mk_wfrec_all (f, ttau) =
       function
       | [] -> []
       | x :: xs ->
          begin
            try
              dprintf
                begin fun p ->
                p.fmt "[mk_wfrec_all] @[<v>trying recursive call on argument %d\
                       @,of function %a@]"
                  x
                  Name.pp f
                end;
              mk_wfrec (f, x, ttau) :: mk_wfrec_all (f, ttau) xs
            with
            | Not_compatible ->
               dprint
                 begin fun () ->
                 "[wk_wfrec_all] skipped Not_compatible recursive call"
                 end;
               mk_wfrec_all (f, ttau) xs
          end
     in

     let rec mk_all (cIH, j) =
       function
       | [] -> cIH
       | (_, None, _) :: mf_list -> mk_all (cIH, j) mf_list
       | (f, Some xs, ttau) :: mf_list ->
          let ds = mk_wfrec_all (f, ttau) xs in
          let cIH' = List.fold_right (fun d cIH' -> LF.Dec (cIH', d)) ds cIH in
          (* Check that generated call is valid -
             mostly this prevents cases where we have contexts not matching
             a given schema *)
          mk_all (cIH', j) mf_list
     in
     dprintf (fun p -> p.fmt "[gen_rec_calls] for j = %d@\n" j);
     let cIH' = mk_all (cIH, j) mf_list in
     dprintf (fun p -> p.fmt "[gen_rec_calls] for j = %d" (j + 1));
     gen_rec_calls cD cIH' (cD', j + 1) mfs

(* Generating recursive calls on computation-level variables *)
let rec get_return_type cD x =
  function
  | (Comp.TypArr (_, _, tau0), theta) -> get_return_type cD x (tau0, theta)
  | (Comp.TypPiBox (_, cdecl, tau0), theta) ->
     let ((_, ft), _cU) = gen_var (Location.ghost) cD (Whnf.cnormCDecl (cdecl, theta)) in
     get_return_type cD x (tau0, LF.MDot (ft, theta))
  | ttau -> (x, ttau)

let rec gen_rec_calls' cD cG cIH (cG0, j) mfs =
  match cG0 with
  | LF.Empty -> cIH
  | LF.Dec (cG', Comp.CTypDecl (x, tau0, false)) ->
     gen_rec_calls' cD cG cIH (cG', j + 1) mfs

  | LF.Dec (cG', Comp.CTypDecl (x, tau0, true)) ->
     let mf_list = get_order mfs in
     dprintf
       begin fun p ->
       p.fmt "[gen_rec_calls'] @[<v>for variable %a of type \
              @,@[%a@]@]"
         Name.pp x
         (P.fmt_ppr_cmp_typ cD P.l0) tau0
       end;
     let (_, ttau0') =
       get_return_type cD (Comp.Var (Location.ghost, j)) (tau0, Whnf.m_id)
     in
     let mk_wfrec (f, x, ttau) =
       dprintf begin fun p ->
         p.fmt
           "[gen_rec_calls'] @[<v>Return Type @[%a@] for arg %d\
            @,type of function: %a : %a@]"
           (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau0')
           x
           Name.pp f
           (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
         end;
       let (args, tau) = rec_spine' cD (j, ttau0') (x, ttau) in
       let args = generalize args in
       let d = Comp.WfRec (f, args, tau) in
       dprintf
         begin fun p ->
         p.fmt "[gen_rec_calls'] Recursive call: @[%a@]"
           P.(fmt_ppr_cmp_ih cD cG) (Comp.WfRec (f, args, tau))
         end;
       d
     in
     let rec mk_wfrec_all (f, ttau) =
       function
       | [] -> []
       | x :: xs ->
          begin
            try
              (mk_wfrec (f, x, ttau)) :: mk_wfrec_all (f, ttau) xs
            with
            | Not_compatible ->
               mk_wfrec_all (f, ttau) xs
          end
     in
     let rec mk_all cIH =
       function
       | [] -> cIH
       | (_, None, _) :: mf_list -> mk_all cIH mf_list
       | (f, Some xs, ttau) :: mf_list ->
          dprintf
            begin fun p ->
            p.fmt "[mk_all] function %a with order %a"
              Name.pp f
              Format.(pp_print_list ~pp_sep: pp_print_space pp_print_int)
              xs
            end;
          let ds = mk_wfrec_all (f, ttau) xs in
          let cIH' = List.fold_right (fun d cIH' -> LF.Dec (cIH', d)) ds cIH in
          mk_all cIH' mf_list
     in
     let cIH' = mk_all cIH mf_list in
     gen_rec_calls' cD cG cIH' (cG', j + 1) mfs


(** Computes the well-founded recursive calls for the given group of
    mutual functions on the given contexts.
    If the list of functions is empty, then an empty context is
    computed.
 *)
let wf_rec_calls cD cG mfs =
  if List.null mfs
  then LF.Empty
  else
    begin
      dprintf
        begin fun p ->
        p.fmt
          "Generate recursive calls from@\ncD = %a@\ncG = %a"
          (P.fmt_ppr_lf_mctx P.l0) cD
          (P.fmt_ppr_cmp_gctx cD P.l0) cG
        end;
      let cIH = gen_rec_calls cD (LF.Empty) (cD, 0) mfs in
      let cIH' = gen_rec_calls' cD cG cIH (cG, 1) mfs in
      Unify.resetGlobalCnstrs ();
      dprintf
        begin fun p ->
        p.fmt "[wf_rec_calls] generated IH = %a"
          P.(fmt_ppr_cmp_ihctx cD cG) cIH'
        end;
      cIH'
    end

(*  ------------------------------------------------------------------------ *)
(* wkSub cPsi cPsi' = s

   iff cPsi' is a prefix of cPsi and
       cPsi |- s : cPsi'

*)
exception WkViolation

let rec wkSub cPsi cPsi' =
  if Whnf.convDCtx cPsi cPsi'
  then Substitution.LF.id
  else
    match cPsi with
    | LF.DDec (cPsi0, _) ->
       Substitution.LF.comp (wkSub cPsi0 cPsi') (Substitution.LF.shift)
    | _ -> raise (WkViolation)


(* weakSub cPsi cPsi' = s

   iff cPsi' is a subset of cPsi and
       cPsi |- s : cPsi'

*)
(* pos cPsi tA k = k'

   if cPsi0 = cPsi, x1:tB1, .., xk:tBk
    and k' is the position of the declaration (y:tA) in cPsi0


   i.e. (k'-k) is the position of (y:tA) in cPsi

   NOTE: there might be more than one declaration in cPsi with type tA;
   this will return the rightmost position. We do not compute all possible
   positions.
*)
let rec pos cPsi tA k =
  match cPsi with
  (* cPsi |- tA *)
  | LF.Null -> None
  | LF.CtxVar _ -> None
  | LF.DDec (cPsi, LF.TypDecl (_, tB)) ->
     if Whnf.convTyp (tA, Substitution.LF.invShift) (tB, Substitution.LF.id)
     then Some k
     else
       pos cPsi (Whnf.normTyp (tA, Substitution.LF.invShift)) (k + 1)

let rec weakSub cD cPsi cPsi' =
  if Whnf.convDCtx cPsi cPsi'
  then Substitution.LF.id
  else
    match cPsi' with
    | LF.DDec (cPsi', LF.TypDecl (x, tA)) ->
       let s = weakSub cD cPsi cPsi' in (* cPsi |- s : cPsi' *)
       begin match pos cPsi (Whnf.normTyp (tA, s)) 1 with
       | Some k ->
          (* print_string (" Found at " ^ string_of_int k ^ "\n"); *)
          LF.Dot (LF.Head (LF.BVar k), s)
       | None ->
          (* print_string (" Not Found.\n"); *)
          raise WkViolation
       end
    | _ -> LF.Shift (Context.dctxLength cPsi)

(* convDCtxMod cPhi (* found *) cPsi (* expected*) = sigma

   iff

    cD |- cPhi ctx,  cD |- cPsi ctx
   and there exists a projection weakening substitution sigma s.t.

   cPsi |- sigma : cPhi

   Note: this could be generalized to allow for subordination


bp: Generalization to support
    [g, x:term, y:term |- M] ~~~> [g, b:block x:term, u:oft x _ , y:term |- M[..,b.1, y]

    Found : [g, x:term, y:term ]
    Expected: [g, b:block x:term, u:oft x _ , y:term]

 *)

let convDCtxMod cD cPhi (* found *) cPsi (* expected *) =
  let (cPsi', lazy s_proj, _) = ConvSigma.gen_flattening cD cPsi in
  dprintf
    begin fun p ->
    p.fmt "[convDCtxGenMod] - @[<v> (expected) cPsi = %a \n (expected) flat_cPsi = %a \n (found) cPhi = %a@]"
      (P.fmt_ppr_lf_dctx cD P.l0) cPsi
      (P.fmt_ppr_lf_dctx cD P.l0) cPsi'
      (P.fmt_ppr_lf_dctx cD P.l0) cPhi
    end;
  (* cPsi |- s_proj : cPsi' *)
  try
    let wk_sub = wkSub cPsi' cPhi in
    (* cPsi' |- wk_sub cPhi *)
    Some (Substitution.LF.comp wk_sub s_proj)
  with
  | _ ->
     begin
       try
         let wk_sub = weakSub cD cPsi' cPhi in
         Some (Substitution.LF.comp wk_sub s_proj)
       with
       | _ -> None
     end

(*
  convDCtxGen cD cPhi cPsi = wk

  If cD |- cPhi ctx and cD |- cPsi ctx
     cPhi = cPhi', xn:An, ... x0:A0   and cPsi = cPsi', xn:An, ... x0:A0 (i.e. cPhi and cPsi agree on a prefix)
     and there exists a projection substitution wk' s.t.  cD ; cPsi' |- wk' : cPhi'
  then

      wk = wk', xn/xn, ... , x0/x0   and  cD ; cPsi |- wk : cPhi

  Note: We do not account for possible permutation substitutions that would relate
       g,x:tA, y:tA  ~~ g, y:tA, x:tA


 *)
let rec convDCtxGen'  cD cPhi (* found *) cPsi (* expected *) =  match cPsi , cPhi with
  | cPsi1, LF.Null -> Some (LF.Shift (Context.dctxLength cPsi1))
  | cPsi1, LF.CtxVar c2 ->
     let rec check cPsi = match cPsi with
       | LF.CtxVar c1  when Whnf.convCtxVar c1 c2 -> Some (LF.Shift ((Context.dctxLength cPsi1)))
       | LF.DDec (cPsi' , _ ) -> check cPsi'
       | _ -> None
     in
     check cPsi1
(*  | LF.Null, LF.Null -> Some (Substitution.LF.id)
  | LF.CtxVar c1, LF.CtxVar c2 when Whnf.convCtxVar c1 c2 -> Some (Substitution.LF.id)
 *)
  | LF.DDec (cPsi', LF.TypDecl (_, tA)) , LF.DDec (cPhi', LF.TypDecl (_, tB))  ->
     if Whnf.convTyp (tA, Substitution.LF.id) (tB, Substitution.LF.id) then
       begin
         dprintf
           begin fun p ->
           p.fmt "[convDCtxGen] - @[<v> Type Found %a@, Type Expected %a@]"
             (P.fmt_ppr_lf_typ cD cPhi' P.l0) tA
             (P.fmt_ppr_lf_typ cD cPsi' P.l0) tB
           end ;
         match convDCtxGen' cD cPhi' (* found *) cPsi' (* expected *) with
         | Some wk ->Some (Substitution.LF.dot1 wk)
         | None -> None
       end
     else
       begin
         match convDCtxMod cD cPhi cPsi with
         | Some wk ->
            (dprintf
              begin fun p ->
              p.fmt "[convDCtxGenMod] - @[<v> (expected) %a |- %a : %a (found)@]"
                (P.fmt_ppr_lf_dctx cD P.l0) cPsi
                (P.fmt_ppr_lf_sub cD cPhi P.l0) wk
                (P.fmt_ppr_lf_dctx cD P.l0) cPhi
              end ;
            Some wk)
         | None ->
            begin
              dprintf
                begin fun p ->
                p.fmt "[convDCtxGenMod] FAILED - @[<v> %a |- ? : %a@]"
                  (P.fmt_ppr_lf_dctx cD P.l0) cPsi
                  (P.fmt_ppr_lf_dctx cD P.l0) cPhi
                end ; None
            end
       end
  (* Generate projection substitution *)
  | _ , _ -> None
  and convDCtxGen cD cPhi cPsi = convDCtxGen' cD (Whnf.cnormDCtx (cPhi, Whnf.m_id)) (Whnf.cnormDCtx (cPsi, Whnf.m_id))

(*
  prefixDCtx cD cPsi1 cPsi0 = k

If
  cD |- cPsi1 and cD |- cPsi 0
  and cPsi1 = cPsi0, cPsi'
then
   |cPsi'| = k

 *)

let rec prefixDCtx' cD cPsi1 cPsi0 = match cPsi1 , cPsi0 with
  | cPsi1, LF.Null -> Some (Context.dctxLength cPsi1)
  | cPsi1, LF.CtxVar c2 ->
     let rec check cPsi = match cPsi with
       | LF.CtxVar c1  when Whnf.convCtxVar c1 c2 -> Some (Context.dctxLength cPsi)
       | LF.DDec (cPsi' , _ ) -> check cPsi'
       | _ -> None
     in
     check cPsi1
  | LF.DDec (cPsi1', LF.TypDecl (_, tA)) , LF.DDec (cPsi0', LF.TypDecl (_, tB))  ->
     if Whnf.convTyp (tA, Substitution.LF.id) (tB, Substitution.LF.id) then
       prefixDCtx cD cPsi1' cPsi0'
     else
       None
  | _ , _ -> None
and prefixDCtx cD cPsi1 cPsi0 =
  prefixDCtx' cD (Whnf.cnormDCtx (cPsi1, Whnf.m_id)) (Whnf.cnormDCtx (cPsi0, Whnf.m_id))



let prefix_hat phat phat' =
  match (phat, phat') with
  | ((None, k), (None, k')) -> Some (k' - k)
  | ((Some (LF.CtxOffset g), k), (Some (LF.CtxOffset g'), k')) ->
     if g = g'
     then Some (k' - k)
     else None
  | _ -> None


let rec dot_k s k =
  if k = 0
  then s
  else dot_k (Substitution.LF.dot1 s) (k - 1)

(*
shiftMetaObj cD (cM, cU) (cPsi', sproj/wk, cPsi) = cM', cU'

If
  cD |- cM : cU  and cD ; cPsi' |- s_proj/wk : cPsi

   cU = [cPsi0 |- tA ]

  cPsi0 = cPsi, cPsi1   and |cPsi1| = k

then

cPsi0' = cPsi', cPsi1

 cD |- cM' : cU'    where

    cU' = (cPsi0' |- [dotk proj/wk k]tA  )
    cM' = (cPsi0_hat |- [dotk proj/wk k]tM )

 *)

let shiftMetaObj cD (cM, cU) (cPsi', s_proj, cPsi) =
  dprintf
    begin
      fun p ->
      p.fmt "[shiftMetaObj] with substitution \n %a |-  %a : %a"
        P.(fmt_ppr_lf_dctx cD P.l0) cPsi'
        P.(fmt_ppr_lf_sub cD cPsi P.l0) s_proj
        P.(fmt_ppr_lf_dctx cD P.l0) cPsi
    end;
  let phat0 = Context.dctxToHat cPsi' in
  let phat = Context.dctxToHat cPsi in
  begin match cM , cU with
  | (l, LF.CObj cPhi) , _
       when Whnf.convDCtx cPsi cPhi ->
     (l, LF.CObj cPsi') , cU

  | (l, LF.ClObj ((None, 0), LF.MObj tM)) , _ ->
     cM , cU (* cM is closed and hence it can be used in any context *)

  | (l, LF.ClObj (phat', LF.MObj tM)) , LF.ClTyp (tA , cPsi0) ->
     let rec padctx cPsi' k =  (* we actually know how to pad it... *)
       if k = 0 then cPsi' else padctx (LF.DDec (cPsi',  LF.TypDeclOpt (Name.mk_some_string ("bb" ^ string_of_int k)))) (k-1)
     in
     begin
       match prefixDCtx cD cPsi cPsi0 (* cPsi0 = cPsi, cPsi1 *) ,
               prefix_hat
               (Whnf.cnorm_psihat phat Whnf.m_id)
               (Whnf.cnorm_psihat phat' Whnf.m_id)
       with
       | None , None -> cM , cU (* cPsi0 and cPsi1 are distinct *)
       | Some k , Some k' when k = k' ->
          (l, LF.ClObj (Context.extend_hatctx k phat0, LF.MObj (Whnf.norm (tM, dot_k s_proj k)))) ,
          LF.ClTyp (Whnf.normClTyp (tA , dot_k s_proj k), padctx cPsi' k)
       | Some k' , Some k ->
          (print_string ("k = " ^ string_of_int k   ^ " and k' = " ^ string_of_int k') ;
           (l, LF.ClObj (Context.extend_hatctx k phat0, LF.MObj (Whnf.norm (tM, dot_k s_proj k))))  , LF.ClTyp (Whnf.normClTyp (tA , dot_k s_proj k), padctx cPsi' k))
       | None , Some k ->
          begin
            dprintf begin
                fun p ->
                p.fmt "[shiftMetaObj] : ERROR – prefixDCtx None and prefix_hat diff = %s \n cPsi0 = %a \n cPsi = %a"
                  (string_of_int k)
                  P.(fmt_ppr_lf_dctx cD P.l0) cPsi0
                  P.(fmt_ppr_lf_dctx cD P.l0) cPsi
              end ;
            (l, LF.ClObj (Context.extend_hatctx k phat0, LF.MObj (Whnf.norm (tM, dot_k s_proj k))))  , LF.ClTyp (Whnf.normClTyp (tA , dot_k s_proj k), padctx cPsi' k)
            end
     end

  (* phat' >= phat, i.e. phat is a prefix of phat' possibly *)
  (* if Whnf.conv_hat_ctx phat phat' then
          Comp.MetaObj (l, phat0, Whnf.norm (tM, s_proj))
        else
          cM *)

  | (l, LF.ClObj (phat', LF.PObj tH)) , LF.ClTyp (tA , cPsi0)
       when Whnf.convDCtx cPsi0 cPsi ->
     let LF.Root (_, tH', _, _) =
       Whnf.norm (LF.Root (l, tH, LF.Nil, Plicity.explicit), s_proj)
     in
     (l, LF.ClObj (phat0, LF.PObj tH')) , LF.ClTyp (Whnf.normClTyp (tA, s_proj), cPsi')

  | (l, LF.ClObj (phat', LF.SObj s)) , LF.ClTyp (cPhi , cPsi0)
       when Whnf.convDCtx cPsi0 cPsi ->
     (l, LF.ClObj (phat0, LF.SObj (Substitution.LF.comp s s_proj))) ,
       LF.ClTyp (cPhi , cPsi')
  | _ -> cM , cU
  end

let rec shiftArgs cD args (cPsi', s_proj, cPsi) =
  match args with
  | [] -> []
  | Comp.DC :: args -> Comp.DC :: shiftArgs cD args (cPsi', s_proj, cPsi)
  | Comp.V x :: args -> Comp.V x :: shiftArgs cD args (cPsi', s_proj, cPsi)
  | Comp.M (cM, cU )  :: args ->
     let cM' , cU'= shiftMetaObj cD (cM , cU) (cPsi', s_proj, cPsi) in
     Comp.M (cM', cU') :: shiftArgs cD args (cPsi', s_proj, cPsi)

(*  ------------------------------------------------------------------------ *)


(* filter cD cG cIH e2 = cIH'

   if  cD      |- cIH
       cD ; cG |- e2

       and f e2' args in cIH
       and e2' ~ e2  (size-equivalent)
  then
       f args in cIH'

*)

let rec filter cD cG cIH (loc, e2) =
  match (e2, cIH) with
  | (_, LF.Empty) -> LF.Empty
  (* We are treating contexts in the list of arguments supplied to the IH
     special to allow for context transformations which preserve the size
   *)
  | ( Comp.M ((_, LF.CObj cPsi), _cU)
    , LF.Dec (cIH, Comp.WfRec (f, (Comp.M ((_, LF.CObj cPhi), _ )) :: args, tau))
    ) ->
     let cIH' = filter cD cG cIH (loc, e2) in
     let cPsi = Whnf.cnormDCtx (cPsi, Whnf.m_id) in
     let cPhi = Whnf.cnormDCtx (cPhi, Whnf.m_id) in
     dprintf
       begin fun p ->
       p.fmt "[Total – Filtering for applicable IH] \n  @[<v>Found : %a@]\n  @[<v>Expected %a@]"
         (P.fmt_ppr_lf_dctx cD P.l0) cPhi
         (P.fmt_ppr_lf_dctx cD P.l0) cPsi
       end ;
     if Whnf.convDCtx cPsi cPhi
     then
       LF.Dec (cIH', Comp.WfRec (f, args, tau))
     else
       (dprintf
       begin fun p ->
       p.fmt "[Total – Filtering for applicable IH] Find Conversion as LF Ctx are not equivalent\n"
       end ;
        begin match convDCtxGen cD cPhi (* found *) cPsi (*expected*) with
        | Some s_proj -> (* cPsi |- s_proj/wk : cPhi *)
           dprintf
             begin fun p ->
             p.fmt "[Total – ConvDCtxGen generated substitution] : %a"
             P.(fmt_ppr_lf_sub cD cPsi P.l0) s_proj
             end ;
           let args' = shiftArgs cD args (cPsi, s_proj, cPhi) in
           (* bp : we may need to keep the type of the args to appropriately shift them ;
we cannot know from hat_dctx alone whether we need to shift; we should only shift if an argument cM in args has type [cPhi |- _ ]

            *)
          (* let tau' = shiftCompTyp tau (cPsi, s_proj, cPhi) in *)
          dprintf
            begin fun p ->
            p.fmt "[Total – generated rec. call arg. ] \n %a"
              P.(fmt_ppr_cmp_ih_args cD LF.Empty) args
            end;
          dprintf
            begin fun p ->
            p.fmt "[Total – Converted rec. call arg. ] shifted generated arguments for rec. call\n %a"
              P.(fmt_ppr_cmp_ih_args cD LF.Empty) args'
            end;
          LF.Dec (cIH', Comp.WfRec (f, args', tau))
       | None -> cIH'
       end)

  | (Comp.M (cM', _cU'), LF.Dec (cIH, Comp.WfRec (f, Comp.M (cM, _cU) :: args, tau))) ->
     let cIH' = filter cD cG cIH (loc, e2) in
     let print_meta_obj = P.fmt_ppr_cmp_meta_obj cD P.l0 in
     if Whnf.convMetaObj cM' cM
     then
       begin
         dprintf
           begin fun p ->
           p.fmt "[total-filter] @[<v>IH and recursive call agree on:@,%a == %a@]"
             print_meta_obj cM' print_meta_obj cM
           end;
         LF.Dec (cIH', Comp.WfRec (f, args, tau))
       end
       (* Note: tau' is understood as the approximate type *)
     else
       begin
         dprintf
           begin fun p ->
           p.fmt "[total-filter] @[<v>IH and recursive call do NOT agree:@,%a == %a@]"
             print_meta_obj cM' print_meta_obj cM
           end;
         cIH'
       end

  | (Comp.V y, LF.Dec (cIH, Comp.WfRec (f, Comp.V x :: args, tau))) ->
     let cIH' = filter cD cG cIH (loc, e2) in
     if x = y
     then LF.Dec (cIH', Comp.WfRec (f, args, tau))
     (* Note: tau is the overall return type of ih type
        and it is not the type of f args : tau *)
     else cIH'

  | (_, LF.Dec (cIH, Comp.WfRec (f, Comp.DC :: args, tau))) ->
     let cIH' = filter cD cG cIH (loc, e2) in
     LF.Dec (cIH', Comp.WfRec (f, args, tau))

  | (_, LF.Dec (cIH, wf)) ->
     dprintf
       begin fun p ->
       p.fmt "[total] [filter] @[<v>dropped IH\
              @,@[%a@]@]"
         P.(fmt_ppr_cmp_ih cD cG) wf
       end;
     filter cD cG cIH (loc, e2)
(*      raise (Error (loc, RecCallIncompatible (cD, x, wf))) *)
(* other cases are invalid /not valid recursive calls *)


let filter cD cG cIH (loc, e) =
  (* print_string ("[filter] IH = " ^ ih_to_string cD cG cIH ^ "\n");*)
  filter cD cG cIH (loc, e)

(* check a recursive call in the program is wf

  f = recursive call in the initial state
  check for conversion between arguments applied to f in the "programm"
  and arguments in generated wf-call.

*)

(** Adjusts the given type signature with annotations for the
    induction arguments according to the given order.
    Returns [Option.None] if the order does not match the type, i.e. goes out
    of bounds.
 *)
let annotate'
      (tau : Synint.Comp.typ) (order : int list)
    : Synint.Comp.typ option =
  let open Option in
  let rec ann tau pos =
    match (tau, pos) with
    | (Comp.TypPiBox (loc, LF.Decl d, tau), 1) ->
      Option.some (Comp.TypPiBox (loc, LF.Decl { d with inductivity = Inductivity.inductive }, tau))
    | (Comp.TypArr (loc, tau1, tau2), 1) ->
      Option.some (Comp.TypArr (loc, Comp.TypInd tau1, tau2))
    | (Comp.TypArr (loc, tau1, tau2), n) ->
       ann tau2 (n - 1)
       $> fun tau2' ->
          Comp.TypArr (loc, tau1, tau2')
    | (Comp.TypPiBox (loc, cd, tau), n) ->
       ann tau (n - 1)
       $> fun tau2' ->
          Comp.TypPiBox (loc, cd, tau2')
    | _ -> Option.none
  in
  List.fold_left_opt (fun tau' x -> ann tau' x) tau order

(** Removes all TypInd marks in a computational type. *)
let rec strip : Synint.Comp.typ -> Synint.Comp.typ =
  function
  | Comp.TypInd tau' -> strip tau'
  | Comp.TypPiBox (loc, LF.Decl d, tau') ->
    Comp.TypPiBox (loc, LF.Decl d, strip tau')
  | Comp.TypPiBox (loc, d, tau') -> Comp.TypPiBox (loc, d, strip tau')
  | Comp.TypArr (loc, tau1, tau2) -> Comp.TypArr (loc, strip tau1, strip tau2)
  | Comp.TypCross (loc, taus) -> Comp.TypCross (loc, List2.map strip taus)
  | Comp.TypClo (tau', ms) -> Comp.TypClo (strip tau', ms)
  | tau -> tau

(*  ------------------------------------------------------------------------ *)

(* positivity checking *)

exception Unimplemented

let rec no_occurs a =
  function
  | Comp.TypBase (loc, c, _) ->
     Bool.not (Id.cid_comp_typ_equal a c)
     && begin match (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.Entry.positivity with
        | Sgn.Positivity -> true
        | Sgn.Stratify _ -> true
        | Sgn.StratifyAll _ -> true
        | _ ->
           let n = R.render_cid_comp_typ c in
           throw loc (NoPositiveCheck n)
        end
  (* ((Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity *)
  (* || let n = R.render_cid_comp_typ c in *)
  (* raise (Error (loc, (NoPositiveCheck n))) *)
  (* ) *)
  | Comp.TypCobase _ -> raise Unimplemented
  | Comp.TypDef _ -> raise Unimplemented
  | Comp.TypBox _ -> true
  | Comp.TypArr (_, tau1, tau2) -> no_occurs a tau1 && no_occurs a tau2
  | Comp.TypCross (_, taus) -> List2.for_all (no_occurs a) taus
  | Comp.TypPiBox (_, _, tau') -> no_occurs a tau'
  | Comp.TypClo _ -> raise Unimplemented

let rec check_positive a =
  function
  | Comp.TypBase (loc, c, _) ->
     Id.cid_comp_typ_equal a c
     || begin match (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.Entry.positivity with
        | Sgn.Positivity -> true
        | Sgn.Stratify _ -> true
        | Sgn.StratifyAll _ -> true
        | _ ->
           let n = R.render_cid_comp_typ c in
           throw loc (NoPositiveCheck n)
        end
  (* (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity *)
  (* || let n = R.render_cid_comp_typ c in *)
  (* raise (Error (loc, (NoPositiveCheck n))) *)
  | Comp.TypCobase _ -> true (* TODO *)
  | Comp.TypDef _ -> raise Unimplemented
  | Comp.TypBox _ -> true
  | Comp.TypArr (_, tau1, tau2) -> no_occurs a tau1 && check_positive a tau2
  | Comp.TypCross (_, taus) -> List2.for_all (check_positive a) taus
  | Comp.TypPiBox (_, _, tau') -> check_positive a tau'
  | Comp.TypClo _ -> raise Unimplemented


let rec positive a =
  function
  | Comp.TypBase _ -> true
  | Comp.TypCobase _ -> true
  | Comp.TypDef _ -> raise Unimplemented
  | Comp.TypBox _ -> true
  | Comp.TypArr (_, tau1, tau2) -> check_positive a tau1 && positive a tau2
  | Comp.TypCross (_, taus) -> List2.for_all (positive a) taus
  | Comp.TypPiBox (_, _, tau') -> positive a tau'
  | Comp.TypClo _ -> raise Unimplemented


(* stratification  *)

let rec less_dctx cPsi1 cPsi2 =
  match (cPsi1, cPsi2) with
  | (LF.Null, LF.Null) -> false
  | (LF.Null, _) -> true
  | (_, LF.DDec (cPsi', _)) -> Whnf.convDCtx cPsi1 cPsi' || less_dctx cPsi1 cPsi'
  | _ -> false

(* let rec less_phat phat1 phat2 = *)
(*   (\* print_string ("let's start2\n"); *\) *)
(*   let psi = Whnf.cnorm_psihat phat1 Whnf.m_id in *)
(*   let phi = Whnf.cnorm_psihat phat2 Whnf.m_id in *)
(*   match (psi, phi) with *)
(*     | ((Some cv1, offset1), (Some cv2, offset2)) -> cv1 = cv2 && offset1 < offset2 *)
(*     | ((None, offset1), (None, offset2)) -> offset1 < offset2 *)
(*     | _ -> false *)

let equal_meta_obj _ mC1 mC2 =
  Whnf.convMetaObj mC1 mC2

let rec less_meta_obj cD mC1 mC2 =
  match (mC1, mC2) with
  | ((_, LF.CObj cPsi1), (_, LF.CObj cPsi2)) -> less_dctx cPsi1 cPsi2

  | ((_, LF.ClObj (phat1, LF.MObj tM1)), (loc2, LF.ClObj (phat2, LF.MObj tM2))) ->
     (||)
       begin match tM2 with
       | LF.Root (_, h, tS, _) ->
          let rec leq_some =
            function
            | LF.App (tM', tS') ->
               leq_meta_obj cD mC1 (loc2, LF.ClObj (phat2, LF.MObj tM'))
               || leq_some tS'
            | LF.Nil -> false
            | LF.SClo _ ->
               Error.raise_violation "[less_meta_obj] SClo"
          in
          leq_some tS
       | _ -> false
       end
       begin match prefix_hat phat1 phat2 with
       | Some 0 -> false
       | Some k -> Whnf.conv (tM1, LF.Shift k) (tM2, Substitution.LF.id) (* this is suspicious -bp *)
       | _ -> false
       end

  | (_, LF.ClObj (phat1, LF.PObj tH1)), (_, LF.ClObj (phat2, LF.PObj tH2)) ->
     begin match prefix_hat phat1 phat2 with
     | Some k -> Whnf.convHead (tH1, LF.Shift k) (tH2, Substitution.LF.id)
     | _ -> false
     end
  (* is the first rule still applied in this case? *)

  | ((loc1, LF.ClObj (_, LF.SObj _)), (_, LF.ClObj (_, LF.SObj _))) ->
     Error.raise_violation "[less_meta_obj] SObj"

  | _ -> false


and leq_meta_obj cD mC1 mC2 =
  equal_meta_obj cD mC1 mC2
  || less_meta_obj cD mC1 mC2
  || begin match mC2 with
     | (loc, LF.ClObj ((cv, offset), LF.MObj (LF.Lam (_, x, n)))) ->
        leq_meta_obj cD mC1 (loc, LF.ClObj ((cv, offset + 1), LF.MObj n))
     | _ -> false
     end
  || begin match mC1 with
     | (loc, LF.ClObj ((cv, offset), LF.MObj (LF.Lam (_, x, n)))) ->
        leq_meta_obj cD (loc, LF.ClObj ((cv, offset + 1), LF.MObj n)) mC2
     | _ -> false
     end

(*find the meta obj needs to be compared*)
let rec find_meta_obj mS n =
  match (mS, n) with
    | (Comp.MetaApp (mC, _, _, _), 1) -> mC
    | (Comp.MetaApp (_, _, mS', _), _) -> find_meta_obj mS' (n - 1)
    | (Comp.MetaNil, _) -> raise Not_compatible (* raise (Error (loc, (WrongArgNum n))) *)

(*
return the metaSpine of the target, with context
*)
let rec get_target cD =
  function
  | Comp.TypBase (_, _, mS) -> (cD, mS)
  | Comp.TypArr (_, tau1, tau2) -> get_target cD tau2
  | Comp.TypPiBox (_, dec, tau') -> get_target (LF.Dec (cD, dec)) tau'
  | _ -> raise Not_compatible

let rec mS_size =
  function
  | Comp.MetaApp (_, _, mS', _) -> mS_size mS' + 1
  | Comp.MetaNil -> 0


(*
compare a (cD1', tau1) n (cD2, mC2) cD0 = bool

mC2 is the target

 type_family(tau1) = a
   cD1'  |- tau1 : ctype
   cD02  |- mC2

if  all occurrence of the type family a in tau1 are stratified in n (the metaObj is smaller than mC2)
then return true
otherwise return false

When we get (cD1, mC1) at position n of a TypBase, we compare mC1 with mC2.
However, cD1 and cD2 share some parts but may have their own different contexts.
cD0 is used to track the common parts, then we shift the differences.
*)


let rec compare a cD tau1 mC2 n =
  match tau1 with
  | Comp.TypBase (loc, c, mS1) ->
     if Id.cid_comp_typ_equal a c
     then
       begin
         let mC1 = find_meta_obj mS1 n in
         let b = less_meta_obj cD mC1 mC2 in
         dprintf
           begin fun p ->
           let f = P.fmt_ppr_cmp_meta_obj cD P.l0 in
           p.fmt "COMPARE @[<v>mC1: %a@,mC2: %a@,%aLESS@]"
             f mC1
             f mC2
             (fun ppf x ->
               Format.pp_print_string ppf (if x then "" else "NOT ")) b
           end;
         b
       end
     else
       begin match (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.Entry.positivity with
       | Sgn.Positivity
         | Sgn.Stratify _
         | Sgn.StratifyAll _ -> true
       | _ ->
          let n = R.render_cid_comp_typ c in
          throw loc (NoStratifyOrPositiveCheck n)
       end
  | Comp.TypArr (_, tau, tau') ->
     compare a cD tau mC2 n && compare a cD tau' mC2 n

  | Comp.TypCross (_, taus) ->
     List2.for_all (fun tau -> compare a cD tau mC2 n) taus

  | Comp.TypPiBox (_, dec, tau) ->
     compare a (LF.Dec (cD, dec)) tau (Whnf.cnormMetaObj (mC2, LF.MShift 1)) n

  | Comp.TypBox _
    | Comp.TypClo _
    | Comp.TypCobase _
    | Comp.TypDef _ -> true

(* stratify a tau n = bool

Preconditions:
    |- tau : ctype
    type_family (tau) = a, i.e. the target type of tau has type family a
    n is the position of an argument given to the type family s

if  all occurrence of the type family a in tau are stratified in n
then return true
false otherwise

*)
let stratify a tau n =
  let (cD, mS) = get_target LF.Empty tau in
  let mSize = mS_size mS in
  if (mSize < n || n <= 0)
  then
    throw Location.ghost (WrongArgNum (a, n))
  else
    begin
      let mC = find_meta_obj mS n in
      let rec strat cD0 =
        function
        | Comp.TypBase _
          | Comp.TypCobase _
          | Comp.TypBox _ -> true

        | Comp.TypArr (_, tau1, tau2) ->
           (* cD0 |- tau1 *)
           (* cD |- mC *)
           (* cD = cD0, cDa *)
           (*shif tau1 to be cD |- tau1' *)
           let k0 = Context.length cD0 in
           let k = Context.length cD in
           let tau1' = Whnf.cnormCTyp (tau1, LF.MShift (k - k0)) in
           (compare a cD tau1' mC n) && (strat cD0 tau2)

        | Comp.TypCross (_, taus) ->
           let k0 = Context.length cD0 in
           let k = Context.length cD in
           let msub = LF.MShift (k - k0) in
           let taus' = List2.map (fun tau -> Whnf.cnormCTyp (tau, msub)) taus in
           List2.for_all (fun tau' -> compare a cD tau' mC n) taus'

        | Comp.TypPiBox (_, dec, tau') -> strat (LF.Dec (cD0, dec)) tau'

        | Comp.TypDef _
          | Comp.TypClo _ -> raise Unimplemented
      in
      strat LF.Empty tau
    end

(* stratifyAll a tau = int list
Preconditions:
    |- tau : ctype
    type_family (tau) = a, i.e. the target type of tau has type family a

if the target type has not arguments, then check positvity
otherwise check whether there is a position of arguments which makes stratification satisfied
*)

let stratifyAll a tau =
  let (cD, mS) = get_target LF.Empty tau in
  let mSize = mS_size mS in
  if mSize = 0
  then
    if positive a tau
    then -1
    else 0
  else
    let rec stratAll n =
      if n >= 1
      then
        if stratify a tau n
        then stratAll (n - 1) * 2 + 1
        else stratAll (n - 1) * 2
      else 0
    in
    stratAll mSize
    (*= The current implementation is restricted to stratified datatype type
        constants with at most [32] arguments. This can be fixed using lists:

          let rec stratAll n =
            if n <= mSize
            then stratify a tau n :: stratAll (n + 1)
            else []
          in
          stratAll 1
    *)

(** Decides whether a data object is something we're doing induction
    on, i.e. it's a computational variable whose type is TypInd or
    with a WF flag

    This is similar to the logic used in check.ml to determine the
    kind of a branch: [Ind]DataObj or [Ind]IndexObj.
 *)
let is_comp_inductive (cG : Comp.gctx) (m : Comp.exp) : bool =
  let open Id in
  let open Comp in
  let is_inductive_comp_variable (k : offset) : bool =
    match Context.lookup' cG k with
    | Option.None -> Error.raise (Failure "Computational variable out of bounds")
    | Option.Some r ->
      (* Either it's a TypInd or the WF flag is true *)
      match r with
      | CTypDecl (u, tau, true) -> true
      | CTypDecl (u, TypInd _, _) -> true
      | _ -> false
  in
  match variable_of_exp m with
  | Option.None -> false
  | Option.Some var -> is_inductive_comp_variable var

(** Decides whether an index object is something we're doing
    induction on, i.e. it's a metavariable with the Inductive flag set
    when we look it up in the meta-context.
 *)
let is_meta_inductive (cD : LF.mctx) (mf : LF.mfront) : bool =
  let open Id in
  let open LF in
  let is_inductive_meta_variable (k : offset) : bool =
    match Context.lookup_inductivity cD k with
    | Option.None ->
        Error.raise (Failure "Metavariable out of bounds or missing type")
    | Option.Some (_, Inductivity.Inductive) -> true
    | Option.Some _ -> false
  in
  match variable_of_mfront mf with
  | Option.None -> false
  | Option.Some (var, _) ->
      (* this left projection is possibly sketchy because of projected
         parameter variables, but I don't think parameter variables can ever
         be inductive, so I don't *think* it's a problem. -je *)
      is_inductive_meta_variable var

(** Checks if the scrutinee of a case is on an inductive computational
    variable or an inductive meta-variable. *)
let is_inductive_split (cD : LF.mctx) (cG : Comp.gctx) (i : Comp.exp) : bool =
  if is_comp_inductive cG i then true else
  match Comp.is_meta_obj i with
  | Option.None -> false
  | Option.Some (e, cM) -> is_meta_inductive cD cM

(** Decides, in the context of a given list of totality declarations,
    whether the given function (name) requires totality checking.
    A function requires totality checking only if its totality
    declaration in the given list, if any, is an `inductive
    declaraction.
 *)
let requires_checking f ds =
  match lookup_dec f ds with
  | Option.Some d -> Option.is_some (Comp.option_of_total_dec_kind d.Comp.order)
  | Option.None -> false

(** Applies the given induction order to produce an annotated type. *)
let annotate loc order tau =
  let error e = E (loc, e) in
  match Comp.option_of_total_dec_kind order with
  | Option.Some order -> (
      match Order.list_of_order order with
      | Option.None ->
          Error.raise
            (error (NotImplemented "lexicographic order not fully supported"))
      | Option.Some order_list -> (
          match annotate' tau order_list with
          | Option.None -> Error.raise (error TooManyArg)
          | Option.Some tau -> tau))
  | Option.None -> tau

(** Filters an ihctx to contain only those IHs for the given function
    name. *)
let rec select_ihs name = function
  | LF.Empty -> LF.Empty
  | LF.Dec (cIH, Comp.(WfRec (name', args, tau) as d))
       when Name.(name = name') ->
     LF.Dec (select_ihs name cIH, d)
  | LF.Dec (cIH, _) ->
     (* Remove the declaration if the name doesn't match. *)
     select_ihs name cIH

(** Drops n leading arguments from all recursive calls in a given
    ihctx. *)
let drop_args n =
  Context.map begin fun (Comp.WfRec (name, args, tau)) ->
    Comp.WfRec (name, List.drop n args, tau)
    end

(** Drops one argument from all recursive calls in a given ihctx. *)
let drop_arg = drop_args 1
