(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)

(* NOTE: Be careful with taureg-mode M-q in this file – it doesn't
   understand the grammar formatting below very well and will easily
   trash the layout. *)

(* Load the camlp4 extensible grammar syntax extension *)
#load "pa_extend.cmo";;


open Core
open Core.Common
open Core.Syntax
open Token



module Grammar = Camlp4.Struct.Grammar.Static.Make (Lexer)

(* Silly type needed for manual backtracking. We need this because,
   given Πx:A._, we do not know whether _ is a kind or a type until we
   reach the very end of the syntax tree.  Therefore, we just assume
   it could be either with this type and continue parsing until we
   find out one way or the other. *)
type kind_or_typ =
  | Kind of Ext.LF.kind
  | Typ  of Ext.LF.typ



(*******************************)
(* Global Grammar Entry Points *)
(*******************************)

let p_sgn_eoi = Grammar.Entry.mk "sig_eoi" (* Σ *)



(*****************************************)
(* Dynamically Extensible Beluga Grammar *)
(*****************************************)

EXTEND Grammar
GLOBAL: p_sgn_eoi;


  (* Σ *)
  p_sgn_eoi:
    [
      [
         decls = LIST0 p_sgn_decl; `EOI
      -> decls
      ]
    ]
  ;

  (* A : K. + c : A. *)
  p_sgn_decl:
    [
      [
        a_or_c = SYMBOL; ":"; k_or_a = p_kind_or_typ; "."
      -> begin match k_or_a with
           | Kind k -> Ext.LF.SgnTyp   (_loc, Id.mk_name (Some a_or_c), k)
           | Typ  a -> Ext.LF.SgnConst (_loc, Id.mk_name (Some a_or_c), a)
         end
      |
        "{-#"; "UNIFY_TERM"; "["; decls = LIST0 p_unify_decl SEP "," ;"]"; tm1 = p_full_term; "=?="; tm2 = p_full_term; "#-}"
      -> Ext.LF.SgnPragma (_loc, Ext.LF.PragUnifyTerm (decls, tm1, tm2))
      |
        "{-#"; "UNIFY_TYPE"; "["; decls = LIST0 p_unify_decl SEP "," ;"]"; tp1 = p_full_typ; "=?="; tp2 = p_full_typ; "#-}"
      -> Ext.LF.SgnPragma (_loc, Ext.LF.PragUnifyTyp (decls, tp1, tp2))
      ]
    ]
  ;

  p_unify_decl:
    [
      [
         "term"; "|"; x = SYMBOL; ":"; a = p_full_typ
      -> Ext.LF.UnifyTermDecl (Id.mk_name (Some x), a)
      |
         "term"; "|"; x = SYMBOL; "="; tm = p_full_term; ":"; a = p_full_typ
      -> Ext.LF.UnifyTermDefn (Id.mk_name (Some x), tm, a)
      |
         "type"; "|"; x = SYMBOL; ":"; k = p_kind_or_typ
      -> begin match k with
           | Kind k ->
               Ext.LF.UnifyTypeDecl (Id.mk_name (Some x), k)
         end
      |
         "type"; "|"; x = SYMBOL; "="; tp = p_full_typ; ":"; k = p_kind_or_typ
      -> begin match k with
           | Kind k ->
               Ext.LF.UnifyTypeDefn (Id.mk_name (Some x), tp, k)
         end
      ]
    ]
  ;

  (* Πx:A. K + Πx:A. B
   | {x:A} K + {x:A} B
   | A ->  K + A ->  B
   |       K + A      
   *)
  p_kind_or_typ:
    [
      RIGHTA
        [
          "Π"; x = SYMBOL; ":"; a2 = p_full_typ; "."; k_or_a = SELF
        -> begin match k_or_a with
             | Kind k -> Kind (Ext.LF.PiKind (_loc, Ext.LF.TypDecl (Id.mk_name (Some x), a2), k))
             | Typ  a -> Typ  (Ext.LF.PiTyp  (_loc, Ext.LF.TypDecl (Id.mk_name (Some x), a2), a))
           end
        |
           "{"; x = SYMBOL; ":"; a2 = p_full_typ; "}"; k_or_a = SELF
        -> begin match k_or_a with
             | Kind k -> Kind (Ext.LF.PiKind (_loc, Ext.LF.TypDecl (Id.mk_name (Some x), a2), k))
             | Typ  a -> Typ  (Ext.LF.PiTyp  (_loc, Ext.LF.TypDecl (Id.mk_name (Some x), a2), a))
           end
        |
          a2 = p_basic_typ; "->"; k_or_a = SELF
       -> begin match k_or_a with
            | Kind k -> Kind (Ext.LF.ArrKind (_loc, a2, k))
            | Typ  a -> Typ  (Ext.LF.ArrTyp  (_loc, a2, a))
          end
        |
           k = p_basic_kind
        -> Kind k
        |
           a = p_basic_typ
        -> Typ  a
        ]
    ]
  ;

  (* type *)
  p_basic_kind:
    [
      [
        "type"
      -> Ext.LF.Typ _loc
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
      -> let sp = List.fold_right (fun t s -> Ext.LF.App (_loc, t, s)) ms Ext.LF.Nil in
           Ext.LF.Atom (_loc, Id.mk_name (Some a), sp)
      |
         "("; a = p_full_typ; ")"
      ->  a
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
         a = p_basic_typ
      -> a
      |
         "Π"; x = SYMBOL; ":"; a2 = SELF; "."; a = SELF
      -> Ext.LF.PiTyp (_loc, Ext.LF.TypDecl (Id.mk_name (Some x), a2), a)
      |
         "{"; x = SYMBOL; ":"; a2 = SELF; "}"; a = SELF
      -> Ext.LF.PiTyp (_loc, Ext.LF.TypDecl (Id.mk_name (Some x), a2), a)
      |
         a2 = p_basic_typ; "->"; a = SELF
      -> Ext.LF.ArrTyp (_loc, a2, a)
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
      -> Ext.LF.Root (_loc, h, Ext.LF.Nil)
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
      -> Ext.LF.Lam (_loc, (Id.mk_name (Some x)), m)
      |
         "["; x = SYMBOL; "]"; m = p_full_term
      -> Ext.LF.Lam (_loc, (Id.mk_name (Some x)), m)
      |
         h = p_head; ms = LIST0 p_basic_term
      -> let sp = List.fold_right (fun t s -> Ext.LF.App (_loc, t, s)) ms Ext.LF.Nil in
           Ext.LF.Root (_loc, h, sp)
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
      -> Ext.LF.Name (_loc, Id.mk_name (Some x_or_c))
      ]
    ]
  ;
END



(********************)
(* Parser Interface *)
(********************)

(* NOTE: Subject to change! *)

let parse_stream ?(name = "<stream>") ~input entry =
  try
    InR (Grammar.parse entry (Grammar.Loc.mk name) input)
  with
    | exc -> InL exc

let parse_string ?(name = "<string>") ~input entry =
  let stream = Stream.of_string input in
    parse_stream ~name:name ~input:stream entry

let parse_channel ?(name = "<channel>") ~input entry =
  let stream = Stream.of_channel input in
    parse_stream ~name:name ~input:stream entry

let parse_file ~name entry =
  let in_channel = Pervasives.open_in name in
  let stream     = Stream.of_channel in_channel in
    parse_stream ~name:name ~input:stream entry
