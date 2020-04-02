open Support.Equality
(* Checking termination of a function *)

open Support
open Syntax.Int
module Unify = Unify.StdTrail
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let (dprintf, dprint, dprnt) = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

type error =
  | NoPositiveCheck of string
  | NoStratifyCheck of string
  | NoStratifyOrPositiveCheck of string
  | WrongArgNum  of Id.cid_comp_typ * int
  | RecCallIncompatible of LF.mctx * Comp.ih_arg * Comp.ih_decl
  | NotImplemented of string
  | TooManyArg of Id.name

exception Error of Syntax.Loc.t * error

let _ =
  Error.register_printer
    (fun (Error (loc, err)) ->
      Error.print_with_location loc (fun ppf ->
          match err with
          | TooManyArg f ->
             Format.fprintf ppf "Totality declaration for %s has too many arguments.\n"
               (Id.render_name f)
          | RecCallIncompatible (cD, x, Comp.WfRec (f, args, _tau)) ->
             (match x , args with
              | _ , [] ->
                 Format.fprintf ppf "Recursive call is incompatible with valid automatically generated recursive calls. \n Report as a bug."
              | Comp.M cM  , (Comp.M cM' :: _ ) ->
                 Format.fprintf ppf "Recursive call is incompatible with valid automatically generated recursive calls. \nBeluga cannot establish that the given recursive call is a size-preserving variant of it.\nArgument found: %a@\nArgument expected: %a@"
                   (P.fmt_ppr_cmp_meta_obj cD P.l0) cM
                   (P.fmt_ppr_cmp_meta_obj cD P.l0) cM'

              | Comp.M cM  , (Comp.V _ :: _ ) ->
                 Format.fprintf ppf "Recursive call is incompatible with valid automatically generated recursive calls. \n\nArgument found: %a@\nExpected computation-level variable.\n\nCheck specified totality declaration. "
                   (P.fmt_ppr_cmp_meta_obj cD P.l0) cM

              | Comp.V _ , _ ->
                 Format.fprintf ppf "Recursive call is incompatible with valid automatically generated recursive calls. \n\n Found computation-level variable while generated recursive call expected a meta-object.\n\nCheck specified totality declaration."
             )
          | NoPositiveCheck n ->
             Format.fprintf ppf "Datatype %s has not been checked for positivity or stratification."  n (* (Id.render_name n) *)
          | NoStratifyCheck n ->
             Format.fprintf ppf "Datatype %s has not been checked for stratification."  n (* (Id.render_name n) *)
          | NoStratifyOrPositiveCheck n ->
             Format.fprintf ppf "Datatype %s has not been checked for stratification or positivity."  n (* (Id.render_name n) *)
          | WrongArgNum (n, num) ->
             Format.fprintf ppf "Stratification declaration for %s uses the argument number %d which is out of bounds." (R.render_cid_comp_typ n) num
          | NotImplemented n      ->
             Format.fprintf ppf "The case %s is not implemented yet."  n

        )
    )

let print_str f = dprint f
(* let dprint f = print_string ("\n" ^ f () )*)

exception Not_compatible
exception CtxNot_compatible

let enabled = ref false

type rec_arg = M of Comp.meta_obj | V of Comp.exp_syn

let shiftArg k arg = match arg with
  | Comp.V x -> Comp.V (x+k)
  | _ -> arg

let rec shiftIH cIH k = match cIH with
  | LF.Empty -> LF.Empty
  | LF.Dec (cIH', Comp.WfRec (f, args, tau)) ->
     let args' = List.map (shiftArg k) args in
     LF.Dec (shiftIH cIH' k, Comp.WfRec (f, args', tau))

let shift cIH = shiftIH cIH 1

let is_inductive cU =  match cU with
  | LF.Inductive -> true
  | _ -> false

let sub_smaller phat s = match phat , s with
  | (_ , n) , LF.Shift n' ->
     (n-n') < n'
  | _ -> false

let rec smaller_meta_obj cM = match  cM with
  | LF.CObj (LF.DDec (_ , _ )) -> true
  | LF.ClObj (phat, LF.MObj (LF.Root (l', h, spine, plicity))) ->
     begin
       match h with
       | LF.Const _ -> true
       | LF.BVar _ -> true
       | LF.PVar (_, s) ->
          begin
            match spine with
            | LF.Nil -> sub_smaller phat s
            | _ -> true
          end
       | LF.Proj (h, _ ) ->
          smaller_meta_obj
            (LF.ClObj
               ( phat
               , LF.MObj
                   ( LF.Root (l', h, spine, plicity))))
       | LF.MVar (_, s) -> sub_smaller phat  s
       | _ -> false
     end
  | LF.ClObj (phat, LF.PObj h) ->
     begin
       match h with
       | LF.PVar (_, s) ->
          ((* print_string "Checking whether proj is smaller(1)\n";*)
           sub_smaller phat s)
       | _ -> false
     end

  | _ -> false

let rec mark_gctx cG = match cG with
  | LF.Empty -> LF.Empty
  | LF.Dec(cG, Comp.CTypDecl (x,tau, _ )) ->
     LF.Dec (mark_gctx cG, Comp.CTypDecl (x,tau, true))

let rec struct_smaller patt = match patt with
  | Comp.PatMetaObj (loc', (_,mO)) ->
     smaller_meta_obj mO
  | Comp.PatConst (_, _, _ ) -> true
  | Comp.PatVar (_, _ ) -> false
  | Comp.PatPair (_, pat1, pat2 ) ->
     (* This is quite naive - possibly one of them being smaller is enough *)
     struct_smaller pat1 && struct_smaller pat2
  | Comp.PatAnn (_, pat, _, _) -> struct_smaller pat
  | _ -> false

let order_to_string order = match order with
  | None -> " _ "
  | Some (Comp.Arg x) -> string_of_int x

(** Determine whether the arguments given in a totality declaration are valid.
    n: number of args
    tau: type of the recursive function
 *)
let is_valid_args tau n =
  let rec go tau n =
    match tau, n with
    | Comp.TypPiBox (_, _ , tau), 1
      | Comp.TypArr (_, _, tau), 1 -> true
    | Comp.TypPiBox (_, _, tau), n
      | Comp.TypArr (_, _, tau), n -> go tau (n-1)
    | _ -> false
  in
  n = 0 || go tau n

(* Check whether the argument specified by i
   corresponds to a given totality order

   i = Var x then  Order.Arg x
   i = Pair(Var x, Var y) then Order.Lex / Order.Sim
   where x and y are in the specified order.


   let satisfies_order cD cG i =
   let total_decs = !mutual_decs in
   (* let m = List.length total_decs in  *)
   (* let cg_length = Context.length cG in  *)
   let rec relative_order (Comp.Var x) (tau, order,l,k,w) = match tau with
   (* k = implicit arguments encountered so far
   l = non-implicit arguments encountered so far
   w = total number of arguments in totality declaration
   w - k = number of variables introduces via fn in cG
 *)
 | Comp.TypPiBox (_, tau) -> relative_order (Comp.Var x) (tau, order,l, k+1,w)
 | Comp.TypArr (_ , tau) ->
 (match order with
 | Order.Arg y -> let _p = y - k - l in
 if x = (w - y)+1 (* assumes that all cdecls are before the actual
 rec. arg. *)
 (* comparing de Bruijn position of x in cG with the position
 described by y *)
 then
 ( (* print_string ("Considering inductive case for " ^
 P.expSynToString cD cG i ^  " - comparing to position " ^
 string_of_int y ^
 " - comgparing to relative position " ^ string_of_int (y-k-l) ^ " - Yes\n");*)true)
 else
 ( (* print_string ("Considering inductive case for " ^
 P.expSynToString cD cG i ^        " - comparing to arg. "
 ^ string_of_int y ^
 " - comparing to relative position " ^ string_of_int (y-k) ^ "? - No\n");*)
 relative_order (Comp.Var x) (tau, order, l+1, k, w) )

 | _ -> false)

 | _ -> false
 in
 match i with
 | Comp.Var x ->
 List.exists  (function dec ->
 (*                  let _ = (print_string ("Considering type " ^
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
 relative_order i (dec.typ, order,0,0,w) ) total_decs
 | _ -> false

 *)

(** Converts the list of totality declarations into an induction ordering list *)
let get_order (mfs : Comp.total_dec list) =
  let f dec =
    let open Comp in
    let tau = dec.tau in
    (*  let _ = dprint (fun () -> "[get_order] " ^ (R.render_cid_prog dec.name) ^
        " : " ^     P.compTypToString (LF.Empty) dec.typ) in *)
    match dec.order with
    | `inductive (Arg x) ->
       (dec.name, Some [x], (tau, Whnf.m_id))
    | `inductive (Lex xs) ->
       let xs = List.map (fun (Arg x) -> x) xs in
       dprint (fun () -> "[get_order] " ^ List.fold_right (fun x s -> (string_of_int x) ^ " " ^ s) xs "");
       (dec.name, Some xs, (tau, Whnf.m_id))
    | `not_recursive | `trust | `partial -> (dec.name, None, (tau, Whnf.m_id))
  in
  List.map f mfs

(** Looks up a declaration based on a function name *)
let lookup_dec f : Comp.total_dec list -> Comp.total_dec option =
  List.find_opt (fun d -> Id.equals Comp.(d.name) f)

(** Gets the induction order for the function with name `f`
    Returns None if the
 *)
let get_order_for mfs f : int list option =
  let rec find decs = match decs with
    | [] -> None
    | dec::decs ->
       if Id.equals Comp.(dec.name) f then
         let open Maybe in
         Comp.(dec.order |> option_of_total_dec_kind $ Order.list_of_order)
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
     let psihat  = Context.dctxToHat cPsi in
     let tM = Whnf.etaExpandMMV loc cD cPsi (tA, Substitution.LF.id) x Substitution.LF.id LF.Maybe in
     ( (loc, LF.ClObj (psihat, LF.MObj tM))
     , LF.ClObj (psihat, LF.MObj tM)
     )
  | LF.ClTyp (LF.PTyp tA, cPsi) ->
     let psihat  = Context.dctxToHat cPsi in
     let p = Whnf.newMPVar (Some x) (cD, cPsi, tA)  LF.Maybe in
     let h = LF.MPVar ((p, Whnf.m_id), Substitution.LF.id) in
     ( (loc, LF.ClObj (psihat, LF.PObj h))
     , LF.ClObj (psihat, LF.PObj h)
     )
  | LF.ClTyp (LF.STyp (cl, cPhi), cPsi) ->
     let psihat  = Context.dctxToHat cPsi in
     let s     =  Whnf.newMSVar (Some x) (cD, cl, cPsi, cPhi) LF.Maybe in
     let sigma = LF.MSVar (0, ((s , Whnf.m_id), Substitution.LF.id)) in
     ( (loc, LF.ClObj (psihat, LF.SObj sigma))
     , LF.ClObj (psihat, LF.SObj sigma)
     )

  | LF.CTyp (schema_cid) ->
     let mmvar =
       let open! LF in
       Whnf.newMMVar' (Some x) (cD, CTyp schema_cid) Maybe
     in
     let cPsi = LF.CtxVar (LF.CInst (mmvar, Whnf.m_id)) in
     ( (loc, LF.CObj cPsi)
     , LF.CObj (cPsi)
     )

let gen_var loc cD cdecl =
  match cdecl with
  | LF.Decl (x, cU, dep) -> gen_var' loc cD (x, cU)

(* Given i and tau, compute vector V
   s.t. for all k < i

   if k-th position in V = 0 then
   type at i-th position in tau does NOT depend on it

   k-th position in V = 1 then
   type at i-th position in tau does depend on it


   We then generate a spine of arguments using V; any position
   marked with 0 in V, will generate DC; positions marked with 1
   will generate a term M.
 *)

let rec rec_spine cD (cM, cU)  (i, ttau) =
  match i, ttau with
  | 0, _ ->  ([], Whnf.cnormCTyp ttau)
  (*  | 0, n, (Comp.TypPiBox ( _ , tau), theta) ->
      let (spine, tau_r) = rec_spine cD (cM,cU) (i, k-1, (tau,theta)) in
      (Comp.DC :: spine, tau_r)
      | 0, n, (Comp.TypArr (_, tau), theta) ->
      let (spine, tau_r) = rec_spine cD (cM,cU) (i, k-1, (tau,theta)) in
      (Comp.DC :: spine, tau_r)
      else
   *)
  | 1 , (Comp.TypPiBox (_, (LF.Decl (_, cU', _) as _cdecl), tau) , theta)  ->
     begin
       try
         (*print_string ("rec_spine: Unify " ^ P.cdeclToString cD cdecl ^
           "  with " ^ P.cdeclToString cD (Whnf.cnormCDecl (cdecl, theta)) ^ "\n");*)
         Unify.unifyMetaTyp cD (cU, Whnf.m_id) (cU', theta);
         let (_,ft) = cM in
         let (spine, tau_r)  = rec_spine cD (cM, cU) (0, (tau, LF.MDot (ft, theta))) in
         (Comp.M cM::spine, tau_r )
       with
         e ->
         raise Not_compatible
     end

  | 1, (Comp.TypArr (_, Comp.TypBox (loc, LF.ClTyp(LF.MTyp tA, cPsi)), tau), theta) ->
     let cU' = LF.ClTyp (LF.MTyp tA, cPsi) in
     begin
       try
         Unify.unifyMetaTyp cD (cU, Whnf.m_id) (cU', theta);
         let (spine, tau_r)  = rec_spine cD (cM, cU) (0, (tau, theta)) in
         (Comp.M cM::spine, tau_r )
       with
         e ->
         raise Not_compatible
     end
  | 1, ttau ->
     let tau = Whnf.cnormCTyp ttau in
     dprintf
       (fun p ->
         p.fmt "[rec_spine] @[<v>Incompatible IH: ran out of arguments;@,last type is: %a@]"
           (P.fmt_ppr_cmp_typ cD P.l0) tau);
     raise Not_compatible

  | n , (Comp.TypPiBox (_, cdecl, tau) , theta)  ->
     let (cN, ft)        = gen_var (Syntax.Loc.ghost) cD (Whnf.cnormCDecl (cdecl, theta)) in
     let (spine, tau_r)  = rec_spine cD (cM, cU) (n-1, (tau, LF.MDot (ft, theta))) in
     (Comp.M cN :: spine, tau_r)

  | n, (Comp.TypArr (_, _, tau2), theta)  ->
     let (spine, tau_r) = rec_spine cD (cM, cU) (n-1, (tau2, theta)) in
     (Comp.DC :: spine, tau_r)

let rec rec_spine' cD (x, ttau0)  (i, ttau) = match i, ttau with
  | 0, _  -> ([], Whnf.cnormCTyp ttau)
  (* i = 0, k =/= 0
     | (n, (Comp.TypPiBox ( _ , tau), theta)) ->
     let (spine, tau_r) = rec_spine' cD (x,tau) (i, k-1, (tau,theta)) in
     (Comp.DC :: spine, tau_r)
     | (n, (Comp.TypArr (_, tau), theta)) ->
     let (spine, tau_r) = rec_spine' cD (x,tau) (i, k-1, (tau,theta)) in
     (Comp.DC :: spine, tau_r)
   *)
  | 1 , (Comp.TypPiBox (_, cdecl, tau) , theta)  ->
     raise Not_compatible (* Error *)

  | 1, (Comp.TypArr (_, tau1, tau2), theta) ->
     begin
       try
         (* print_string ("Can generate IH for arg " ^
            P.compTypToString cD tau0 ^
            "\nExpected: " ^
            P.compTypToString cD (Whnf.cnormCTyp (tau1,theta)) ^ "\n"); *)
         Unify.unifyCompTyp cD ttau0 (tau1, theta);
         let (spine, tau_r)  = rec_spine' cD (x, ttau0) (0, (tau2, theta)) in
         (Comp.V x::spine, tau_r )
       with
         _ -> raise Not_compatible
     end
  | n , (Comp.TypPiBox (_, cdecl, tau) , theta)  ->
     let (cN, ft)        = gen_var (Syntax.Loc.ghost) cD (Whnf.cnormCDecl (cdecl, theta)) in
     let (spine, tau_r)  = rec_spine' cD (x,ttau0) (n-1, (tau, LF.MDot (ft, theta))) in
     (Comp.M cN :: spine, tau_r)

  | n, (Comp.TypArr (_, _, tau2), theta)  ->
     let (spine, tau_r) = rec_spine' cD (x,ttau0) (n-1, (tau2, theta)) in
     (Comp.DC :: spine, tau_r)


let gen_meta_obj (cdecl, theta) k = match cdecl with
  | LF.CTyp (schema_cid) ->
     (Syntax.Loc.ghost, LF.CObj (LF.CtxVar (LF.CtxOffset k)))
  | LF.ClTyp (LF.MTyp tA, cPsi) ->
     let phat  = Context.dctxToHat cPsi in
     let psihat' = Whnf.cnorm_psihat phat theta in
     let mv = LF.MVar (LF.Offset k, Substitution.LF.id) in
     let tM = LF.Root (Syntax.Loc.ghost, mv, LF.Nil, `explicit) in
     (Syntax.Loc.ghost, LF.ClObj (psihat', LF.MObj tM))

  | LF.ClTyp (LF.PTyp tA, cPsi) ->
     let phat  = Context.dctxToHat cPsi in
     let psihat' = Whnf.cnorm_psihat phat theta in
     let pv = LF.PVar (k, Substitution.LF.id) in
     (Syntax.Loc.ghost, LF.ClObj (psihat', LF.PObj pv))

  | LF.ClTyp (LF.STyp (_, cPsi), cPhi) ->
     let sv = LF.SVar (k, 0, Substitution.LF.id) in
     let phat  = Context.dctxToHat cPsi in
     let psihat' = Whnf.cnorm_psihat phat theta in
     (Syntax.Loc.ghost, LF.ClObj (psihat', LF.SObj sv))

let uninstantiated_arg cM = match Whnf.cnormMetaObj (cM, Whnf.m_id) with
  | _ , LF.CObj (LF.CtxVar (LF.CInst _)) -> true
  | _ , LF.ClObj (phat, LF.MObj (LF.Root (_, h, _spine, _))) ->
     (match h with
      | LF.MMVar (_ , _ ) -> true
      | _ -> false)
  | _ , LF.ClObj ((Some _, n), LF.PObj h) ->
     if n > 0 then
       match h with
       | LF.MPVar (_, _) -> true
       | _ -> false
     else
       false
  | _ , LF.ClObj (_phat, LF.SObj (LF.MSVar (_, _))) -> true
  | _ -> false

let rec generalize args = match args with
  | [] -> []
  | Comp.M cM :: args ->
     if uninstantiated_arg cM then
       Comp.DC :: generalize args
     else
       Comp.M cM :: generalize args
  | Comp.V x :: args ->
     Comp.V x:: generalize args
  | Comp.DC :: args ->
     Comp.DC :: generalize args


let valid_args args = match List.rev args with
  | Comp.DC :: _ -> false
  | _ -> true



let rec gen_rec_calls cD cIH (cD', j) mfs = match cD' with
  | LF.Empty -> cIH
  | LF.Dec (cD', LF.Decl (u, cU, dep)) when not (is_inductive dep) ->
     dprintf begin fun p ->
       p.fmt "[gen_rec_calls] @[<v>ignoring cD' entry %d, i.e.\
              @,@[<hv 2>%a :@ @[%a@]@]\
              @,since it isn't inductive\
              @]"
         j
         Id.print u
         P.(fmt_ppr_cmp_meta_typ cD') cU
       end;
     gen_rec_calls cD cIH (cD', j+1) mfs
  | LF.Dec (cD', LF.Decl (u, cU, dep)) ->
     let cM  = gen_meta_obj (cU, LF.MShift (j+1)) (j+1) in
     let cU' = Whnf.cnormMTyp (cU, LF.MShift (j+1)) in
     let mf_list = get_order mfs in
     dprintf begin fun p ->
       p.fmt "[gen_rec_calls] @[<v>Generate rec. calls given variable@,@[%a@]\
              @,considering a total of %d recursive functions@]"
         (P.fmt_ppr_lf_ctyp_decl cD') (LF.Decl (u, cU, dep))
         (List.length mf_list)
       end;

     let mk_wfrec (f,x,ttau) =
       dprintf begin fun p ->
         p.fmt "[mk_wf_rec] @[<v>for @[%a@] for position %d\
                @,@[<hv 2>type of recursive call:@ @[%a@]@]@]"
           (P.fmt_ppr_lf_ctyp_decl cD') (LF.Decl (u,cU, dep))
           x
           (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
         end;

       let (args, tau) = rec_spine cD (cM, cU') (x, ttau) in
       (* rec_spine may raise Not_compatible *)
       dprintf
         (fun p ->
           p.fmt "[mk_wfrec] generated Arguments for rec. call %a"
             P.(fmt_ppr_cmp_ih_args cD LF.Empty) args);
       let args = generalize args in
       dprintf
         (fun p ->
           p.fmt "[mk_wfrec] generated recursive Call : %a"
             P.(fmt_ppr_cmp_ih cD LF.Empty) (Comp.WfRec (f, args, tau)));
       Comp.WfRec (f, args, tau)
     in
     let rec mk_wfrec_all (f,ttau) xs = match xs with
       | [] -> []
       | x::xs' ->
          begin
            try
              dprintf begin fun p ->
                p.fmt "[mk_wfrec_all] @[<v>trying recursive call on argument %d\
                       @,of function %a@]"
                  x
                  Id.print f
                end;
              mk_wfrec (f, x, ttau) :: mk_wfrec_all (f,ttau) xs'
            with
            | Not_compatible ->
               dprint
                 (fun _ ->
                   "[wk_wfrec_all] skipped Not_compatible recursive call");
               mk_wfrec_all (f,ttau) xs'
          end
     in

     let rec mk_all (cIH,j) mf_list = match mf_list with
       | [] -> cIH
       | (f, None, _ttau)::mf_list ->  mk_all (cIH, j) mf_list
       | (f, Some xs, ttau)::mf_list ->
          let ds =  mk_wfrec_all (f,ttau) xs in
          let cIH' = List.fold_right (fun d cIH' -> LF.Dec(cIH', d)) ds cIH in
          (* Check that generated call is valid -
             mostly this prevents cases where we have contexts not matching
             a given schema *)
          mk_all (cIH',j) mf_list
     in
     let _ =  dprint (fun () -> "[gen_rec_calls] for j = " ^ string_of_int j ^ "\n") in
     let cIH' = mk_all (cIH,j)  mf_list in
     dprint (fun () -> "[gen_rec_calls] for j = " ^ string_of_int (j+1) ^ "\n");
     gen_rec_calls cD cIH'  (cD', j+1) mfs

(* Generating recursive calls on computation-level variables *)
let rec get_return_type cD x ttau =
  match ttau with
  | Comp.TypArr (_, _tau1 , tau0)  , theta -> get_return_type cD x (tau0, theta)
  | Comp.TypPiBox (_, cdecl, tau0) , theta ->
     let (_cN, ft) = gen_var (Syntax.Loc.ghost) cD (Whnf.cnormCDecl (cdecl, theta)) in
     get_return_type cD x (tau0,  LF.MDot (ft, theta))
  | tau, _ -> (x, ttau)

let rec gen_rec_calls' cD cG cIH (cG0, j) mfs =
  match cG0 with
  | LF.Empty -> cIH
  | LF.Dec(cG', Comp.CTypDecl (_x, tau0, false)) ->
     gen_rec_calls' cD cG cIH (cG', j+1) mfs
  | LF.Dec(cG', Comp.CTypDecl (_x, tau0, true)) ->
     let y = j+1 in
     let mf_list = get_order mfs in
     dprintf
       (fun p ->
         p.fmt "[gen_rec_calls'] for %a"
           (P.fmt_ppr_cmp_typ cD P.l0) tau0);
     let (_i, ttau0') = get_return_type cD (Comp.Var (Syntax.Loc.ghost, y)) (tau0, Whnf.m_id) in
     let mk_wfrec (f,x, ttau) =
       dprintf
         (fun p ->
           p.fmt "[gen_rec_calls'] @[<v>Return Type @[%a@] for arg %d@,type of function: %a : %a@]"
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau0')
             x
             Id.print f
             (P.fmt_ppr_cmp_typ cD P.l0) (Whnf.cnormCTyp ttau)
         );
       let (args, tau) = rec_spine' cD (y, ttau0') (x, ttau) in
       let args = generalize args in
       let d = Comp.WfRec (f, args, tau) in
       dprintf
         begin fun p ->
         p.fmt "[gen_rec_calls'] Recursive call: @[%a@]"
           P.(fmt_ppr_cmp_ih cD cG) (Comp.WfRec (f, args, tau))
         end;
       d
     in
     let rec mk_wfrec_all (f,ttau) xs = match xs with
       | [] -> []
       | x::xs' ->
          begin
            try
              (mk_wfrec (f,x,ttau))::mk_wfrec_all (f,ttau) xs'
            with
              Not_compatible ->
              mk_wfrec_all (f,ttau) xs'
          end
     in
     let rec mk_all cIH mf_list =
       match mf_list with
       | [] -> cIH
       | (f, None,   _ttau)::mf_list ->  mk_all cIH mf_list
       | (f, Some xs, ttau)::mf_list ->
          dprint
            (fun () ->
              "[mk_all] Function " ^ Id.render_name f ^ " with lex Order: "
              ^ List.fold_right (fun x s -> (string_of_int x) ^ " " ^ s) xs "");
          let ds = mk_wfrec_all (f, ttau) xs in
          (* Check that generated call is valid -
             mostly this prevents cases where we have contexts not matching
             a given schema *)
          let cIH' = List.fold_right (fun d cIH' -> LF.Dec(cIH', d)) ds cIH in
          mk_all cIH' mf_list
     in
     let cIH' = mk_all cIH mf_list in
     dprint
       (fun _ ->
         "[gen_rec_calls'] Generate more possible rec. calls");
     gen_rec_calls' cD cG cIH' (cG', j+1) mfs


(** Computes the well-founded recursive calls for the given group of
    mutual functions on the given contexts.
    If the list of functions is empty, then an empty context is
    computed.
 *)
let wf_rec_calls cD cG mfs =
  match Misc.List.null mfs with
  | true -> LF.Empty
  | false ->
     dprintf
       (fun p ->
         p.fmt
           "Generate recursive calls from@.cD = %a@.cG = %a"
           (P.fmt_ppr_lf_mctx P.l0) cD
           (P.fmt_ppr_cmp_gctx cD P.l0) cG);
     let cIH  = gen_rec_calls cD (LF.Empty) (cD, 0) mfs in
     let cIH' = gen_rec_calls' cD cG cIH (cG, 0) mfs in
     let _ = Unify.resetGlobalCnstrs () in
     dprintf
       begin fun p ->
       p.fmt "[wf_rec_calls] generated IH = %a"
         P.(fmt_ppr_cmp_ihctx cD cG) cIH'
       end;
     cIH'

(*  ------------------------------------------------------------------------ *)
(* wkSub cPsi cPsi' = s

   iff cPsi' is a prefix of cPsi and
       cPsi |- s : cPsi'

*)
exception WkViolation

let rec wkSub cPsi cPsi' =
  if Whnf.convDCtx cPsi cPsi' then
   Substitution.LF.id
  else
    (match cPsi with
       | LF.DDec (cPsi0, _ ) ->
         Substitution.LF.comp  (wkSub cPsi0 cPsi') (Substitution.LF.shift)
       | _ -> raise (WkViolation)
    )


(* weakSub cPsi cPsi' = s

   iff cPsi' is a subset of cPsi and
       cPsi |- s : cPsi'

*)
(* pos cPsi tA k = k'

   if cPsi0 = cPsi, x1:tB1, .., xk:tBk
    and k' is the position of the declaration (y:tA) in cPsi0


   i.e.  (k'-k) is the position of (y:tA) in cPsi

   NOTE: there might be more than one declaration in cPsi with type tA;
   this will return the rightmost position. We do not compute all possible
   positions.
*)
let rec pos cPsi tA k = match cPsi with
  (* cPsi |- tA *)
  | LF.Null     -> None
  | LF.CtxVar _ -> None
  | LF.DDec (cPsi, LF.TypDecl (_x, tB)) ->
      if Whnf.convTyp (tA, Substitution.LF.invShift) (tB, Substitution.LF.id) then
      Some (k)
      else
      pos cPsi (Whnf.normTyp (tA, Substitution.LF.invShift)) (k+1)

let rec weakSub cD cPsi cPsi' =
  if Whnf.convDCtx cPsi cPsi' then
   Substitution.LF.id
  else
    (match cPsi' with
       | LF.DDec (cPsi', LF.TypDecl (x, tA)) ->
         let s = weakSub cD cPsi cPsi' in (*  cPsi |- s : cPsi' *)
         (* let _ = print_string ("Is " ^ P.typToString cD cPsi' (tA, Substitution.LF.id)
           ^ "\n in " ^ P.dctxToString cD cPsi ^ " ? \n") in*)
         (match pos cPsi (Whnf.normTyp (tA,s)) 1 with
            | Some k ->
              ((* print_string (" Found at " ^ string_of_int k ^ "\n"); *)
              LF.Dot( LF.Head (LF.BVar k), s))
            | None -> (* print_string (" Not Found.\n") ; *) raise WkViolation)
       | _ -> LF.Shift (Context.dctxLength cPsi))

(* convDCtxMod cPsi cPsi' = sigma

   iff

    cD |- cPsi ctx,  cD |- cPsi' ctx
   and there exists a  variable substitution sigma s.t.

   cPsi' |- sigma : cPsi

   Note: this could be generalized to allow for subordination

-bp: Generalize this to allow for permutation substitutions:

Example: cPsi = g, x:tm, y:tm  ~~ g, y:tm, x:tm
  - substitutions:  Id    -or-   (x/y, y/x)


*)
let convDCtxMod cD cPsi cPhi =
  let (cPhi', lazy s_proj, _) = ConvSigma.gen_flattening cD cPhi in
    (*  cPhi |- s_proj : cPhi' *)
    begin try
      let wk_sub = wkSub cPhi' cPsi in
      (* cPhi' |- wk_sub cPsi *)
        Some (Substitution.LF.comp wk_sub s_proj)
    with _ ->
      try
(*       let _ = (print_string "[convDCtxMod] compute possible weakening substitution which allows for permutations : \n" ;
             print_string (" cPsi = " ^ P.dctxToString cD cPsi ^ "\n");
             print_string (" cPhi' = " ^ P.dctxToString cD cPhi' ^ "\n") ) in
*)     let wk_sub = weakSub cD cPhi' cPsi in
        Some (Substitution.LF.comp wk_sub s_proj)
      with _ -> None
    end


let prefix_hat phat phat' = match phat, phat' with
  | (None, k) , (None, k') -> Some (k' - k )
  | (Some (LF.CtxOffset g), k) , (Some (LF.CtxOffset g'), k') ->
      if g = g' then Some (k' - k )
      else None
  | _, _ -> None


let rec dot_k s k = if k = 0 then s
else dot_k (Substitution.LF.dot1 s) (k-1)


let shiftMetaObj cM (cPsi', s_proj, cPsi) =
  let phat  = Context.dctxToHat cPsi in
  let phat0 = Context.dctxToHat cPsi' in
    match cM with
      | l , LF.CObj cPhi ->
        if Whnf.convDCtx cPsi cPhi then
         (l, LF.CObj cPsi')
        else
          cM
      | l , LF.ClObj (phat', LF.MObj tM) ->
        (match prefix_hat (Whnf.cnorm_psihat phat Whnf.m_id)
                           (Whnf.cnorm_psihat phat' Whnf.m_id)  with
          | None -> cM
          | Some k ->
            (l, LF.ClObj (phat0, LF.MObj (Whnf.norm (tM, dot_k s_proj k)))))
        (* phat' >= phat, i.e.  phat is a prefix of phat' possibly *)
(*        if Whnf.conv_hat_ctx phat phat' then
          Comp.MetaObj (l, phat0, Whnf.norm (tM, s_proj))
        else
          cM *)
      | l , LF.ClObj (phat', LF.PObj tH) ->
        if Whnf.convDCtxHat phat phat' then
          let LF.Root (_, tH', _, _) =
            Whnf.norm (LF.Root (l, tH, LF.Nil, `explicit), s_proj)
          in
          (l, LF.ClObj (phat0, LF.PObj tH'))
        else
          cM
      | l , LF.ClObj (phat', LF.SObj s) ->
        if Whnf.convDCtxHat phat phat' then
          (l, LF.ClObj (phat0, LF.SObj (Substitution.LF.comp s s_proj)))
        else
          cM

let rec shiftArgs args (cPsi', s_proj, cPsi) = match args with
  | [] -> []
  | Comp.DC :: args -> Comp.DC :: shiftArgs args (cPsi', s_proj, cPsi)
  | Comp.V x :: args ->  Comp.V x :: shiftArgs args (cPsi', s_proj, cPsi)
  | Comp.M cM :: args ->
      let cM' = shiftMetaObj cM (cPsi', s_proj, cPsi) in
      Comp.M cM' :: shiftArgs args (cPsi', s_proj, cPsi)

(*  ------------------------------------------------------------------------ *)


(* filter cD cG cIH e2 = cIH'

   if  cD      |- cIH
       cD ; cG |- e2

       and f e2' args in cIH
       and e2' ~ e2  (size-equivalent)
  then
       f args in cIH'

*)

let rec filter cD cG cIH (loc, e2) = match e2, cIH with
  | _ , LF.Empty -> LF.Empty
  (* We are treating contexts in the list of arguments supplied to the IH
     special to allow for context transformations which preserve the size
    *)
  | Comp.M (_ , LF.CObj cPsi) ,
    LF.Dec (cIH, Comp.WfRec (f , (Comp.M (_, LF.CObj cPhi)) :: args, tau )) ->
     let cIH' = filter cD cG cIH (loc, e2) in
     let cPsi = Whnf.cnormDCtx (cPsi, Whnf.m_id) in
     let cPhi = Whnf.cnormDCtx (cPhi, Whnf.m_id) in
     (* let _ = print_string ("MetaCtx : FOUND " ^ P.dctxToString cD cPhi ^
        "\n           EXPECTED " ^ P.dctxToString cD cPsi ^  "\n\n") in *)
     if Whnf.convDCtx cPsi cPhi then
       LF.Dec (cIH', Comp.WfRec (f, args, tau))
     else
       (match convDCtxMod cD cPhi cPsi with
        | Some s_proj ->  (*  cPsi |- s_proj : cPhi *)
           let args' = shiftArgs args (cPsi, s_proj, cPhi) in
           (* let tau' = shiftCompTyp tau (cPsi, s_proj, cPhi) in  *)
           LF.Dec (cIH', Comp.WfRec (f, args', tau))
        | None -> cIH'
       )

  | Comp.M cM' , LF.Dec (cIH, Comp.WfRec (f , Comp.M cM :: args, tau )) ->
     let cIH' = filter cD cG cIH (loc, e2) in
     let print_meta_obj = P.fmt_ppr_cmp_meta_obj cD P.l0 in
     if Whnf.convMetaObj cM' cM then
       (  dprintf
            (fun p ->
              p.fmt "[total-filter] @[<v>IH and recursive call agree on:@,%a == %a@]"
                print_meta_obj cM' print_meta_obj cM);
          LF.Dec (cIH', Comp.WfRec (f, args, tau)))
         (* Note: tau' is understood as the approximate type *)
     else
       (dprintf
          (fun p ->
            p.fmt "[total-filter] @[<v>IH and recursive call do NOT agree:@,%a == %a@]"
            print_meta_obj cM' print_meta_obj cM);
        cIH')

  | Comp.V y , LF.Dec (cIH,Comp.WfRec (f , Comp.V x :: args, tau )) ->
     let cIH' = filter cD cG cIH (loc, e2) in
     if x = y then
       LF.Dec (cIH', Comp.WfRec (f, args, tau))
     (* Note: tau is the overall return type of ih type
        and it is not the type of f args : tau *)
     else
       cIH'
  | _ , LF.Dec (cIH,Comp.WfRec (f , Comp.DC :: args, tau )) ->
     let cIH' = filter cD cG cIH (loc, e2) in
     LF.Dec (cIH', Comp.WfRec (f, args, tau))

  | _x, LF.Dec (cIH, wf) ->
     dprintf begin fun p ->
       p.fmt "[total] [filter] @[<v>dropped IH\
              @,@[%a@]@]"
         P.(fmt_ppr_cmp_ih cD cG) wf
       end;
     filter cD cG cIH (loc, e2)
(*      raise (Error (loc, RecCallIncompatible (cD, x, wf))) *)
(* other cases are invalid /not valid recursive calls *)


let filter cD cG cIH (loc, e) =
( (* print_string ("[filter] IH = " ^ ih_to_string cD cG cIH ^ "\n");*)
 filter cD cG cIH (loc, e))

(* check a recursive call in the program is wf

  f = recursive call in the initial state
  check for conversion between arguments applied to f in the "programm"
  and arguments in generated wf-call.

*)

(** Adjusts the given type signature with annotations for the
    induction arguments according to the given order.
    Call `get_order_for` to retrieve an induction order before calling
    this.
    Returns None if the order does not match the type, i.e. goes out
    of bounds.
 *)
let annotate
      (tau : Syntax.Int.Comp.typ) (order : int list)
    : Syntax.Int.Comp.typ option =
  let open Maybe in
  let rec ann tau pos = match tau , pos with
  | Comp.TypPiBox (loc, LF.Decl (x, cU, _dep), tau) , 1 ->
     Comp.TypPiBox (loc, LF.Decl (x, cU, LF.Inductive), tau)
     |> pure
  | Comp.TypArr (loc, tau1, tau2) , 1 ->
     Comp.TypArr (loc, Comp.TypInd tau1, tau2)
     |> pure
  | Comp.TypArr (loc, tau1, tau2) , n ->
     ann tau2 (n-1)
     $> fun tau2' ->
        Comp.TypArr (loc, tau1, tau2')
  | Comp.TypPiBox (loc, cd, tau) , n ->
     ann tau (n-1)
     $> fun tau2' ->
        Comp.TypPiBox(loc, cd, tau2')
  |  _ , _ -> None
  in
  fold_left (fun tau' x -> ann tau' x) tau order

(* TODO rethink LF.Inductive annotations for pi-types.
   Inductivity markings are ORTHOGONAL to plicity markings
   (explicit vs implicit) so there ought to be two flags on each
   pi-type: plicity and inductivity. -je
 *)
(** Removes all TypInd marks in a computational type.
    WARNING: this is NOT an inverse for `annotate`.
    This function will only remove TypInd annotations, but not
    LF.Inductive annotations on Pi-types, which are in fact also
    generated by annotate.
    This is by design, as it is IMPOSSIBLE to remove LF.Inductive
    annotations correctly: we can't figure out whether the pi-type was
    explicit or implicit.
 *)
let rec strip (tau : Syntax.Int.Comp.typ) : Syntax.Int.Comp.typ =
  match tau with
  | Comp.TypInd tau' -> strip tau'
  | Comp.TypPiBox (loc, d, tau') -> Comp.TypPiBox (loc, d, strip tau')
  | Comp.TypArr (loc, tau1, tau2) -> Comp.TypArr (loc, strip tau1, strip tau2)
  | Comp.TypCross (loc, tau1, tau2) -> Comp.TypCross (loc, strip tau1, strip tau2)
  | Comp.TypClo (tau', ms) -> Comp.TypClo (strip tau', ms)
  | tau -> tau

(*  ------------------------------------------------------------------------ *)

(* positivity checking *)

exception Unimplemented

let rec no_occurs a tau =
  match tau with
    | Comp.TypBase (loc, c , _) ->
      not (Id.cid_equals a c) &&
      ( match (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.Entry.positivity with
        | Sgn.Positivity -> true
        | Sgn.Stratify _ -> true
        | Sgn.StratifyAll _ -> true
        | _ ->  let n =  R.render_cid_comp_typ c in
              raise (Error (loc, (NoPositiveCheck n)))
      )
      (* ((Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity *)
      (*  || let n =  R.render_cid_comp_typ c in *)
        (*     raise (Error (loc, (NoPositiveCheck n))) *)
      (* ) *)
    | Comp.TypCobase _ ->  raise Unimplemented
    | Comp.TypDef  _  ->  raise Unimplemented
    | Comp.TypBox  _ -> true
    | Comp.TypArr (_, tau1, tau2)   -> (no_occurs a tau1) && (no_occurs a tau2)
    | Comp.TypCross (_, tau1, tau2) -> (no_occurs a tau1) && (no_occurs a tau2)
    | Comp.TypPiBox (_, _, tau')    ->  no_occurs a tau'
    | Comp.TypClo   _            ->  raise Unimplemented

let rec check_positive a tau =
  match tau with
    | Comp.TypBase (loc, c , _) ->
      (Id.cid_equals a c) ||
      ( match (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.Entry.positivity with
       | Sgn.Positivity -> true
       | Sgn.Stratify _ -> true
       | Sgn.StratifyAll _ -> true
       | _ -> let n =  R.render_cid_comp_typ c in
            raise (Error (loc, (NoPositiveCheck n)))
      )
      (* (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.positivity *)
      (* || let n =  R.render_cid_comp_typ c in *)
      (*    raise (Error (loc, (NoPositiveCheck n))) *)
    | Comp.TypCobase _  ->  true (* TODO *)
    | Comp.TypDef  _  -> raise Unimplemented
    | Comp.TypBox  _ -> true
    | Comp.TypArr (_, tau1, tau2)   -> (no_occurs a tau1) && (check_positive a tau2)
    | Comp.TypCross (_, tau1, tau2) -> (check_positive a tau1) && (check_positive a tau2)
    | Comp.TypPiBox (_, _, tau')    -> check_positive a tau'
    | Comp.TypClo   _            ->  raise Unimplemented


let rec positive a tau =
  match tau with
    | Comp.TypBase _  -> true
    | Comp.TypCobase _ -> true
    | Comp.TypDef  _  -> raise Unimplemented
    | Comp.TypBox _   -> true
    | Comp.TypArr (_, tau1, tau2)   -> (check_positive a tau1) && (positive a tau2)
    | Comp.TypCross (_, tau1, tau2) -> (positive a tau1) && (positive a tau2)
    | Comp.TypPiBox (_, _, tau')    -> positive a tau'
    | Comp.TypClo   _            ->  raise Unimplemented



(* stratification  *)

let rec less_dctx cPsi1 cPsi2 =
  match cPsi1, cPsi2 with
    | LF.Null, LF.Null -> false
    | LF.Null, _       -> true
    | _ , LF.DDec (cPsi', _ )  -> Whnf.convDCtx cPsi1 cPsi' || less_dctx cPsi1 cPsi'
    | _ , _    -> false

(* let rec less_phat phat1 phat2 =  *)
(*   (\* print_string ("let's start2\n"); *\) *)
(*   let psi = Whnf.cnorm_psihat phat1 Whnf.m_id in *)
(*   let phi = Whnf.cnorm_psihat phat2 Whnf.m_id in  *)
(*   match psi, phi with *)
(*     | (Some cv1, offset1), (Some cv2, offset2) -> cv1 = cv2 && offset1 < offset2 *)
(*     | (None, offset1)    , (None, offset2)     -> offset1 < offset2 *)
(*     | _ , _  -> false *)

let equal_meta_obj _cD mC1 mC2 =
   Whnf.convMetaObj mC1 mC2


let rec less_meta_obj cD mC1 mC2 =
  match mC1, mC2 with
    | (_, LF.CObj cPsi1), (_, LF.CObj cPsi2) -> less_dctx cPsi1 cPsi2

    | (_, LF.ClObj (phat1, LF.MObj tM1)), (loc2, LF.ClObj (phat2, LF.MObj tM2)) ->
       (||)
         begin match tM2 with
         | LF.Root(_, h , tS, _)  ->
            let rec leq_some spine =
              match spine with
              | LF.App (tM', tS') ->
                 leq_meta_obj cD mC1 (loc2, LF.ClObj (phat2 , LF.MObj tM'))
                 || leq_some tS'
              | LF.Nil -> false
              | LF.SClo (_, _) ->
                 raise (Error (Syntax.Loc.ghost, NotImplemented "LF.SClo in Total.less_meta_obj"))
            in
            leq_some tS
         | _  ->   false
         end
         begin match prefix_hat phat1 phat2 with
         | Some 0 -> false
         | Some k -> Whnf.conv (tM1, LF.Shift(k)) (tM2, Substitution.LF.id) (* this is suspicious -bp *)
         | _ -> false
         end

    | (_, LF.ClObj (phat1, LF.PObj tH1)) , (_, LF.ClObj (phat2, LF.PObj tH2)) ->
      (let p = prefix_hat phat1 phat2 in
       match p with
       | Some k -> Whnf.convHead (tH1, LF.Shift k) (tH2, Substitution.LF.id)
       | _ -> false
      )
      (*  is the first rule still applied in this case?  *)

    | (loc1, LF.ClObj (_, LF.SObj _) ), (_, LF.ClObj (_ , LF.SObj _)) -> raise (Error (loc1, NotImplemented "Comp.MetaSObj in Total.less_meta_obj"))

    | _, _ -> false


and leq_meta_obj cD mC1 mC2 =
  equal_meta_obj cD mC1 mC2 || less_meta_obj cD mC1 mC2
  || (match mC2 with
      | (loc , LF.ClObj ((cv , offset ), LF.MObj (LF.Lam(_, x, n)))) ->
          leq_meta_obj cD mC1 (loc,  LF.ClObj ((cv , offset + 1 ), LF.MObj n))
      | _ ->  false
     )
  || (match mC1 with
      | (loc , LF.ClObj ((cv , offset ), LF.MObj (LF.Lam(_, x, n)))) ->
          leq_meta_obj cD (loc, LF.ClObj ((cv , offset + 1 ), LF.MObj n)) mC2
      | _ ->  false
     )

(*find the meta obj needs to be compared*)
let rec find_meta_obj mS n =
  match mS, n with
    | Comp.MetaApp (mC, _, _, _)  , 1   ->  mC
    | Comp.MetaApp (_, _, mS', _), _   -> find_meta_obj  mS' (n-1)
    | Comp.MetaNil          , _   -> raise Not_compatible (* raise (Error (loc, (WrongArgNum n))) *)



(*
return the metaSpine of the target, with context
*)
let rec get_target cD tau =
  match tau with
    | Comp.TypBase (_, _, mS)      -> (cD,  mS)
    | Comp.TypArr (_, tau1, tau2)     ->   get_target cD tau2
    | Comp.TypPiBox (_, dec, tau')    ->   get_target (LF.Dec (cD, dec)) tau'
    | _   -> raise Not_compatible

let rec mS_size mS =
  match mS with
    | Comp.MetaApp (_, _, mS', _)   -> mS_size mS' + 1
    | Comp.MetaNil             -> 0


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



let rec compare a cD tau1  mC2 n =
  match  tau1 with
    | Comp.TypBase  (loc, c, mS1) ->
      if Id.cid_equals a c then
        begin
          let  mC1 =  find_meta_obj mS1 n in
          let b = less_meta_obj cD mC1 mC2 in
          dprintf
            (fun p ->
              let f = P.fmt_ppr_cmp_meta_obj cD P.l0 in
              p.fmt "COMPARE @[<v>mC1: %a@,mC2: %a@,%aLESS@]"
                f mC1 f mC2
                (fun ppf x ->
                  Format.pp_print_string ppf (if x then "" else "NOT ")) b);
          b
        end
      else
        begin match (Store.Cid.CompTyp.get c).Store.Cid.CompTyp.Entry.positivity with
        | Sgn.Positivity -> true
        | Sgn.Stratify _ -> true
        | Sgn.StratifyAll _ -> true
        | _ ->  let n =  R.render_cid_comp_typ c in
                raise (Error (loc, (NoStratifyOrPositiveCheck n)))
        end
    | Comp.TypArr   (_, tau, tau') | Comp.TypCross (_, tau, tau')  ->
       (compare a cD tau mC2 n) && (compare a cD tau'  mC2 n)
    | Comp.TypPiBox (_, dec, tau)   ->
      compare a (LF.Dec (cD, dec))  tau    (Whnf.cnormMetaObj   (mC2 , LF.MShift  1))  n
    | Comp.TypBox _    -> true
    | Comp.TypClo _    -> true
    | Comp.TypCobase _ -> true
    | Comp.TypDef _    -> true

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
  if (mSize < n || n <=0 )
  then raise (Error ( (Syntax.Loc.ghost) , (WrongArgNum (a, n))))
  else
    let mC = find_meta_obj mS n  in
    let rec strat cD0 tau0 =
      match tau0 with
      | Comp.TypBase _   -> true
      | Comp.TypCobase _ -> true
      | Comp.TypDef  _   -> raise Unimplemented
      | Comp.TypBox  _   -> true
      | Comp.TypArr   (_, tau1, tau2)   ->

        (* cD0 |- tau1  *)
        (* cD |- mC   *)
        (* cD = cD0, cDa *)
        (*shif tau1 to be  cD |- tau1'  *)
        let k0  = Context.length cD0  in
        let k   = Context.length cD  in
        let tau1' = Whnf.cnormCTyp (tau1, LF.MShift(k- k0)) in
        (compare a cD tau1' mC n) && (strat cD0 tau2)

      | Comp.TypCross (_, tau1, tau2)   ->
        let k0  = Context.length cD0  in
        let k  =  Context.length cD  in
        let tau1' = Whnf.cnormCTyp (tau1, LF.MShift(k-k0)) in
        let tau2' = Whnf.cnormCTyp (tau2, LF.MShift(k-k0)) in
        (compare a cD tau1' mC n) && (compare a cD tau2' mC n)

      | Comp.TypPiBox (_, dec, tau')    ->  strat (LF.Dec (cD0, dec)) tau'
      | Comp.TypClo  _            -> raise Unimplemented
    in
    strat LF.Empty tau

(* stratifyAll a tau = int list
Preconditions:
    |- tau : ctype
    type_family (tau) = a, i.e. the target type of tau has type family a

if the target type has not arguments , then check positvity
otherwise check whether there is a position of arguments which makes stratification satisfied
*)

let stratNum = ref 0

(* let rec calc_exp2 n =  *)
(*   if (n <=1) then 1 *)
(*   else 2 * (calc_exp2 (n-1)) *)

let stratifyAll a tau =
  let (cD, mS) = get_target LF.Empty tau in
  let mSize = mS_size mS in
  if mSize = 0 then
    if (positive a tau) then -1
    else 0
  else
  let rec stratAll n =
    if n>=1 then
      if (stratify a tau n) then (stratAll (n-1)) * 2 + 1
      else (stratAll (n-1)) * 2
      (* let t = if (stratify a tau n) then calc_exp2 n else 0 *)
      (* in t lor (stratAll (n-1)) *)
      (* if (stratify a tau n) then  ((calc_exp2 n) lor (stratAll (n-1) num) ) ) *)
      (* else stratAll (n-1) num *)
    else 0
  in stratAll mSize

(** Decides whether a data object is something we're doing induction
    on, i.e. it's a computational variable whose type is TypInd or
    with a WF flag

    This is similar to the logic used in check.ml to determine the
    kind of a branch: [Ind]DataObj or [Ind]IndexObj.
 *)
let is_comp_inductive (cG : Comp.gctx) (m : Comp.exp_syn) : bool =
  let open Id in
  let open Comp in
  let is_inductive_comp_variable (k : offset) : bool =
    Context.lookup' cG k
    |> Maybe.get' (Failure "Computational variable out of bounds")
    |> function
      (* Either it's a TypInd or the WF flag is true *)
      | CTypDecl (u, tau, true) -> true
      | CTypDecl (u, TypInd _, _) -> true
      | _ -> false
  in
  let open Maybe in
  variable_of_exp m
  $> is_inductive_comp_variable
  $ of_bool
  |> is_some

(** Decides whether an index object is something we're doing
    induction on, i.e. it's a metavariable with the Inductive flag set
    when we look it up in the meta-context.
 *)
let is_meta_inductive (cD : LF.mctx) (mf : LF.mfront) : bool =
  let open Id in
  let open LF in
  let is_inductive_meta_variable (k : offset) : bool =
    Context.lookup_dep cD k
    |> Maybe.get' (Failure "Metavariable out of bounds or missing type")
    |> fun (_, dep) ->
       match dep with
       | LF.Inductive -> true
       | _ -> false
  in
  let open Maybe in
  variable_of_mfront mf
  $> fst
  (* this `fst` is possibly sketchy because of projected parameter
     variables, but I don't think parameter variables can ever be
     inductive, so I don't *think* it's a problem.
     -je *)
  $> is_inductive_meta_variable
  $ of_bool
  |> is_some

(** Checks if the scrutinee of a case is on an inductive computational
    variable or an inductive meta-variable. *)
let is_inductive_split (cD : LF.mctx) (cG : Comp.gctx) (i : Comp.exp_syn) : bool =
  is_comp_inductive cG i
  || let open Maybe in
     Comp.is_meta_obj i
     $> snd
     $> is_meta_inductive cD
     |> is_some

(** Decides, in the context of a given list of totality declarations,
    whether the given function (name) requires totality checking.
    A function requires totality checking only if its totality
    declaration in the given list, if any, is an `inductive
    declaraction.
 *)
let requires_checking f ds =
  match lookup_dec f ds with
  | Some d -> None <> Comp.(d.order |> option_of_total_dec_kind)
  | None -> false
