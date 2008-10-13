(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



(* NOTE: Be careful with taureg-mode M-q in this file – it doesn't
   understand the grammar formatting below very well and will easily
   trash the layout. *)

(* Load the camlp4 extensible grammar syntax extension *)
#load "pa_extend.cmo";;

open Core.Syntax.Int
open Token



module DataVar = Core.Store.DataVar
module Grammar = Camlp4.Struct.Grammar.Static.Make(Lexer)
module Id      = Core.Id
module Term    = Core.Store.Cid.Term
module Typ     = Core.Store.Cid.Typ



(* Silly type needed for manual backtracking. We need this because,
   given Πx:A._, we do not know whether _ is a kind or a type until we
   reach the very end of the syntax tree.  Therefore, we just assume
   it could be either with this type and continue parsing until we
   find out one way or the other. *)
type kind_or_typ =
  | Kind of LF.kind
  | Typ  of LF.typ



(*******************************)
(* Global Grammar Entry Points *)
(*******************************)

let p_sig_eoi = Grammar.Entry.mk "sig_eoi" (* Σ *)



(*****************************************)
(* Dynamically Extensible Beluga Grammar *)
(*****************************************)

EXTEND Grammar
GLOBAL: p_sig_eoi;


  (* Σ *)
  p_sig_eoi:
    [
      [
        decls = LIST0 p_sig_decl; `EOI
          -> decls
      ]
    ]
  ;

  (* A : K. ∨ c : A. *)
  p_sig_decl:
    [
      [
        a_or_c = SYMBOL; ":"; k_or_a_fun = p_kind_or_typ; "."
      -> begin match k_or_a_fun (DataVar.create ()) with
           | Kind k -> Decl.Typ   ((Typ.add  (Typ.mk_entry  (Id.mk_name (Some a_or_c)) k)), k)
           | Typ  a -> Decl.Const ((Term.add (Term.mk_entry (Id.mk_name (Some a_or_c)) a)), a)
         end
      ]
    ]
  ;


  (* Πx:A. K ∨ Πx:A. B
   | {x:A} K ∨ {x:A} B
   | A ->  K ∨ A ->  B
   |       K ∨ A      
   *)
  p_kind_or_typ:
    [
      RIGHTA
        [
          "Π"; x = SYMBOL; ":"; a2_fun = p_full_typ; "."; k_or_a_fun = SELF
        -> fun data_ctx ->
             let data_ctx' = DataVar.extend data_ctx (DataVar.mk_entry (Id.mk_name (Some x))) in
               begin match k_or_a_fun data_ctx' with
                 | Kind k -> Kind (LF.PiKind ((Id.mk_name (Some x), a2_fun data_ctx'), k))
                 | Typ  a -> Typ  (LF.PiTyp  ((Id.mk_name (Some x), a2_fun data_ctx'), a))
               end
        |
          "{"; x = SYMBOL; ":"; a2_fun = p_full_typ; "}"; k_or_a_fun = SELF
        -> fun data_ctx ->
             let data_ctx' = DataVar.extend data_ctx (DataVar.mk_entry (Id.mk_name (Some x))) in
               begin match k_or_a_fun data_ctx' with
                 | Kind k -> Kind (LF.PiKind ((Id.mk_name (Some x), a2_fun data_ctx'), k))
                 | Typ  a -> Typ  (LF.PiTyp  ((Id.mk_name (Some x), a2_fun data_ctx'), a))
               end
        |
          a2_fun = p_basic_typ; "->"; k_or_a_fun = SELF
       -> fun data_ctx ->
            begin match k_or_a_fun data_ctx with
              | Kind k -> Kind (LF.PiKind ((Id.mk_name None, a2_fun data_ctx), k))
              | Typ  a -> Typ  (LF.PiTyp  ((Id.mk_name None, a2_fun data_ctx), a))
            end
        |
           k_fun = p_basic_kind
        -> fun data_ctx ->
             Kind (k_fun data_ctx)
        |
           a_fun = p_basic_typ
        -> fun data_ctx ->
             Typ  (a_fun data_ctx)
        ]
    ]
  ;

  (* type *)
  p_basic_kind:
    [
      [
        "type"
      -> fun _ ->
           LF.TypKind
      ]
    ]
  ;

  (*  a M₁ … Mn
   | (A)
   *)
  p_basic_typ:
    [
      [
         a = SYMBOL; ms = LIST0 p_basic_term
      -> fun data_ctx ->
           let sp = List.fold_right (fun t s -> LF.App (t data_ctx, s)) ms LF.Nil in
             LF.Atom ((Typ.index_of_name (Id.mk_name (Some a))), sp)
      |
        "("; a_fun = p_full_typ; ")"
         ->  a_fun
      ]
    ]
  ;

  (* Πx:A. B
   | {x:A} B
   | A ->  B
   *)
  p_full_typ:
    [
      [
         a_fun = p_basic_typ
      -> a_fun
      |
         "Π"; x = SYMBOL; ":"; a2_fun = SELF; "."; a_fun = SELF
      -> fun data_ctx ->
           let data_ctx' = DataVar.extend data_ctx (DataVar.mk_entry (Id.mk_name (Some x))) in
             LF.PiTyp ((Id.mk_name (Some x), a2_fun data_ctx'), a_fun data_ctx')
      |
         "{"; x = SYMBOL; ":"; a2_fun = SELF; "}"; a_fun = SELF
      -> fun data_ctx ->
           let data_ctx' = DataVar.extend data_ctx (DataVar.mk_entry (Id.mk_name (Some x))) in
             LF.PiTyp ((Id.mk_name (Some x), a2_fun data_ctx'), a_fun data_ctx')
      |
          a2_fun = p_basic_typ; "->"; a_fun = SELF
       -> fun data_ctx ->
            LF.PiTyp ((Id.mk_name None, a2_fun data_ctx), a_fun data_ctx)
      ]
    ]
  ;

  (*  h
   | (M) 
   *)
  p_basic_term:
    [
      [
         h = p_head
      -> fun data_ctx ->
           LF.Root ((h data_ctx), LF.Nil)
      |
         "("; m = p_full_term; ")"
      -> m
      ]
    ]
  ;

  (* λx. M
   | [x] M
   | h M₁ Mn
   | M
   *)
  p_full_term:
    [
      [
         "λ"; x = SYMBOL; "."; m = p_full_term
      -> fun data_ctx ->
           let data_ctx' = DataVar.extend data_ctx (DataVar.mk_entry (Id.mk_name (Some x))) in
             LF.Lam ((Id.mk_name (Some x)), (m data_ctx'))
      |
         "["; x = SYMBOL; "]"; m = p_full_term
      -> fun data_ctx ->
           let data_ctx' = DataVar.extend data_ctx (DataVar.mk_entry (Id.mk_name (Some x))) in
             LF.Lam ((Id.mk_name (Some x)), (m data_ctx'))
      |
         h = p_head; ms = LIST0 p_basic_term
      -> fun data_ctx ->
           let sp = List.fold_right (fun t s -> LF.App (t data_ctx, s)) ms LF.Nil in
             LF.Root (h data_ctx, sp)
      |
         m = p_basic_term
      -> m
      ]
    ]
  ;

  (* x
   | c
   *)
  p_head:
    [
      [
         x_or_c = SYMBOL
      -> fun data_ctx ->
           try
             LF.DataVar (DataVar.index_of_name data_ctx (Id.mk_name (Some x_or_c)))
           with
             | Not_found ->
                (* FIXME: catch another Not_found again... *)
                 LF.Const (Term.index_of_name (Id.mk_name (Some x_or_c)))
      ]
    ]
  ;
END



(********************)
(* Parser Interface *)
(********************)

(* Parse a file and return a signature *)
let parse_file file_name =
  let in_channel = Pervasives.open_in file_name in
  let stream     = Stream.of_channel in_channel in
    try
      Grammar.parse p_sig_eoi (Grammar.Loc.mk file_name) stream
    with
      | Grammar.Loc.Exc_located (loc, exc) ->
          Format.printf "%s\n" (Printexc.to_string exc)
          ; Grammar.Loc.print Format.std_formatter loc
          ; assert false
