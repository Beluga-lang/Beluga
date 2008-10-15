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
open Core.Store
open Core.Store.Cid
open Core.Syntax
open Token



module Grammar = Camlp4.Struct.Grammar.Static.Make(Lexer)



(* Silly type needed for manual backtracking. We need this because,
   given Πx:A._, we do not know whether _ is a kind or a type until we
   reach the very end of the syntax tree.  Therefore, we just assume
   it could be either with this type and continue parsing until we
   find out one way or the other. *)
type kind_or_typ =
  | Kind of Ext.kind
  | Typ  of Ext.typ



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
           | Kind k -> Ext.SgnTyp   (_loc, Id.mk_name (Some a_or_c), k)
           | Typ  a -> Ext.SgnConst (_loc, Id.mk_name (Some a_or_c), a)
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
             | Kind k -> Kind (Ext.PiKind (_loc, (Id.mk_name (Some x), a2), k))
             | Typ  a -> Typ  (Ext.PiTyp  (_loc, (Id.mk_name (Some x), a2), a))
           end
        |
           "{"; x = SYMBOL; ":"; a2 = p_full_typ; "}"; k_or_a = SELF
        -> begin match k_or_a with
             | Kind k -> Kind (Ext.PiKind (_loc, (Id.mk_name (Some x), a2), k))
             | Typ  a -> Typ  (Ext.PiTyp  (_loc, (Id.mk_name (Some x), a2), a))
           end
        |
          a2 = p_basic_typ; "->"; k_or_a = SELF
       -> begin match k_or_a with
            | Kind k -> Kind (Ext.PiKind (_loc, (Id.mk_name None, a2), k))
            | Typ  a -> Typ  (Ext.PiTyp  (_loc, (Id.mk_name None, a2), a))
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
      -> Ext.Typ _loc
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
      -> let sp = List.fold_right (fun t s -> Ext.App (t, s)) ms Ext.Nil in
           Ext.Atom (_loc, Id.mk_name (Some a), sp)
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
      -> Ext.PiTyp (_loc, (Id.mk_name (Some x), a2), a)
      |
         "{"; x = SYMBOL; ":"; a2 = SELF; "}"; a = SELF
      -> Ext.PiTyp (_loc, (Id.mk_name (Some x), a2), a)
      |
         a2 = p_basic_typ; "->"; a = SELF
      -> Ext.PiTyp (_loc, (Id.mk_name None, a2), a)
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
      -> Ext.Root (_loc, h, Ext.Nil)
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
      -> Ext.Lam (_loc, (Id.mk_name (Some x)), m)
      |
         "["; x = SYMBOL; "]"; m = p_full_term
      -> Ext.Lam (_loc, (Id.mk_name (Some x)), m)
      |
         h = p_head; ms = LIST0 p_basic_term
      -> let sp = List.fold_right (fun t s -> Ext.App (t, s)) ms Ext.Nil in
           Ext.Root (_loc, h, sp)
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
      -> Ext.Name (_loc, Id.mk_name (Some x_or_c))
      ]
    ]
  ;
END



(********************)
(* Parser Interface *)
(********************)

(* NOTE: Subject to change! *)

(* Parse a stream and return a signature *)
let parse_stream ?(name = "<stream>") ~input =
  try
    Grammar.parse p_sgn_eoi (Grammar.Loc.mk name) input
  with
    | Grammar.Loc.Exc_located (loc, exc) ->
        Format.printf "%s\n" (Printexc.to_string exc)
      ; Grammar.Loc.print Format.std_formatter loc
      ; assert false

(* Parse a string and return a signature *)
let parse_string ?(name = "<string>") ~input =
  let stream = Stream.of_string input in
    parse_stream ~name:name ~input:stream

(* Parse a file and return a signature *)
let parse_file ~name =
  let in_channel = Pervasives.open_in name in
  let stream     = Stream.of_channel in_channel in
    parse_stream ~name:name ~input:stream
