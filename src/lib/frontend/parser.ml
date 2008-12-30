(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(* NOTE: Be careful with taureg-mode M-q in this file – it doesn't
   understand the grammar formatting below very well and will easily
   trash the layout. *)

(* Load the camlp4 extensible grammar syntax extension *)
#load "pa_extend.cmo";;

open Core
open Core.Common
open Core.Syntax.Ext
open Token

module Grammar = Camlp4.Struct.Grammar.Static.Make (Lexer)

type kind_or_typ =
  | Kind of LF.kind
  | Typ  of LF.typ

(*******************************)
(* Global Grammar Entry Points *)
(*******************************)

let sgn_eoi = Grammar.Entry.mk "sig_eoi"

(*****************************************)
(* Dynamically Extensible Beluga Grammar *)
(*****************************************)

EXTEND Grammar
GLOBAL: sgn_eoi;

  sgn_eoi:
    [
      [
         decls = LIST0 sgn_decl; `EOI ->
           decls
      ]
    ]
  ;

  sgn_decl:
    [
      [
         a_or_c = SYMBOL; ":"; k_or_a = lf_kind_or_typ; "." ->
           begin match k_or_a with
             | Kind k -> Sgn.Typ   (_loc, Id.mk_name (Some a_or_c), k)
             | Typ  a -> Sgn.Const (_loc, Id.mk_name (Some a_or_c), a)
           end
      |
        "schema"; w = SYMBOL; "="; bs = LIST1 lf_schema_elem SEP "+"; ";" ->
          Sgn.Schema (_loc, Id.mk_name (Some w), LF.Schema bs)
(*       | *)
(*          "{-#"; "UNIFY_TERM"; "["; decls = LIST0 unify_decl SEP "," ;"]"; tm1 = lf_term; "=?="; tm2 = lf_term; "#-}" -> *)
(*            LF.SgnPragma (_loc, LF.PragUnifyTerm (decls, tm1, tm2)) *)
(*       | *)
(*          "{-#"; "UNIFY_TYPE"; "["; decls = LIST0 unify_decl SEP "," ;"]"; tp1 = lf_typ; "=?="; tp2 = lf_typ; "#-}" -> *)
(*            LF.SgnPragma (_loc, LF.PragUnifyTyp (decls, tp1, tp2)) *)
      |
        "rec"; f = SYMBOL; ":"; tau = cmp_typ; "="; e = cmp_exp_chk; ";" ->
          Sgn.Rec (_loc, Id.mk_name (Some f), tau, e)
      ]
    ]
  ;

(*   unify_decl: *)
(*     [ *)
(*       [ *)
(*          "@term"; "|"; x = SYMBOL; ":"; a = lf_typ -> *)
(*            LF.UnifyTermDecl (Id.mk_name (Some x), a) *)
(*       | *)
(*          "@term"; "|"; x = SYMBOL; "="; tm = lf_term; ":"; a = lf_typ -> *)
(*            LF.UnifyTermDefn (Id.mk_name (Some x), tm, a) *)
(*       | *)
(*          "@type"; "|"; x = SYMBOL; ":"; k = lf_kind_or_typ -> *)
(*            begin match k with *)
(*              | Kind k -> *)
(*                  LF.UnifyTypeDecl (Id.mk_name (Some x), k) *)
(*            end *)
(*       | *)
(*          "@type"; "|"; x = SYMBOL; "="; tp = lf_typ; ":"; k = lf_kind_or_typ -> *)
(*            begin match k with *)
(*              | Kind k -> *)
(*                  LF.UnifyTypeDefn (Id.mk_name (Some x), tp, k) *)
(*            end *)
(*       ] *)
(*     ] *)
(*   ; *)

  lf_kind_or_typ:
    [
      RIGHTA
        [
           "{"; x = SYMBOL; ":"; a2 = lf_typ; "}"; k_or_a = SELF ->
             begin match k_or_a with
               | Kind k -> Kind (LF.PiKind (_loc, LF.TypDecl (Id.mk_name (Some x), a2), k))
               | Typ  a -> Typ  (LF.PiTyp  (_loc, LF.TypDecl (Id.mk_name (Some x), a2), a))
             end
        |
           a2 = lf_typ LEVEL "atomic"; "->"; k_or_a = SELF ->
             begin match k_or_a with
               | Kind k -> Kind (LF.ArrKind (_loc, a2, k))
               | Typ  a -> Typ  (LF.ArrTyp  (_loc, a2, a))
             end
        |
           k = lf_kind LEVEL "atomic" ->
             Kind k
        |
           a = lf_typ LEVEL "atomic" ->
             Typ  a
        ]
    ]
  ;

  lf_kind:
    [ RIGHTA
      [
         "{"; x = SYMBOL; ":"; a = lf_typ; "}"; k = SELF ->
           LF.PiKind (_loc, LF.TypDecl (Id.mk_name (Some x), a), k)
      |
         a = lf_typ LEVEL "atomic"; "->"; k = SELF ->
           LF.ArrKind (_loc, a, k)
      ]

    | "atomic"
      [
         "type" ->
           LF.Typ _loc
      ]
    ]
  ;

  lf_ctyp_decl:
    [
      [
        "{"; hash = OPT "#"; u_or_p = SYMBOL; "::"; tA = lf_typ LEVEL "atomic"; "["; cPsi = lf_dctx; "]"; "}" ->
          match hash with
            | None   ->
                LF.MDecl (_loc, Id.mk_name (Some u_or_p), tA, cPsi)

            | Some _ ->
                LF.PDecl (_loc, Id.mk_name (Some u_or_p), tA, cPsi)
      ]
    ]
  ;

  lf_typ:
    [ RIGHTA
        [
           "{"; x = SYMBOL; ":"; a2 = SELF; "}"; a = SELF ->
             LF.PiTyp (_loc, LF.TypDecl (Id.mk_name (Some x), a2), a)
        |
           a2 = SELF; "->"; a = SELF ->
             LF.ArrTyp (_loc, a2, a)
        ]

    | "atomic"
        [
          a = SYMBOL; ms = LIST0 (lf_term LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Some a), sp)
        |
          "("; a = SELF; ")" ->
            a
        ]
    ]
  ;

  lf_term:
    [ RIGHTA
        [
          "\\"; x = SYMBOL; "."; m = SELF ->
            LF.Lam (_loc, (Id.mk_name (Some x)), m)
        ]

    | LEFTA
        [
          h = lf_head; ms = LIST0 (lf_term LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Root (_loc, h, sp)
        ]

    | "atomic"
        [
           h = lf_head ->
             LF.Root (_loc, h, LF.Nil)
        |
           "("; m = SELF; ")" ->
             m
        ]
    ]
  ;

  lf_head:
    [
      [
        u_or_x = SYMBOL ->
          LF.Name (_loc, Id.mk_name (Some u_or_x))
      ]
    ]
  ;

  lf_term_w_meta:
    [ RIGHTA
        [
          "\\"; x = SYMBOL; "."; m = SELF ->
            LF.Lam (_loc, (Id.mk_name (Some x)), m)
        ]

    | LEFTA
        [
          h = lf_head_w_meta; ms = LIST0 (lf_term_w_meta LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Root (_loc, h, sp)
        ]

    | "atomic"
        [
           h = lf_head_w_meta ->
             LF.Root (_loc, h, LF.Nil)
        |
           "("; m = SELF; ")" ->
             m
        ]
    ]
  ;

  lf_head_w_meta:
    [
      [
        "#"; p = SYMBOL; "["; sigma = lf_sub; "]" ->
          LF.PVar (_loc, Id.mk_name (Some p), sigma)
      |
        u_or_x = SYMBOL; sigma = OPT [ "["; sigma = lf_sub; "]" -> sigma ] ->
          match sigma with
            | None ->
                LF.Name (_loc, Id.mk_name (Some u_or_x))
            | Some sigma' ->
                LF.MVar (_loc, Id.mk_name (Some u_or_x), sigma')
      ]
    ]
  ;

  lf_sub:
    [
      [
        "." ->
          LF.Dot _loc
      |
        sigma = SELF; ","; tM = lf_term_w_meta ->
          LF.Normal (_loc, sigma, tM)
      |
        "id"; "("; x = SYMBOL; ")" ->
          LF.Id (_loc, Id.mk_name (Some x))
      ]
    ]
  ;

  (* We don't currently deal with sigma types, so no need for ~ *)
  lf_schema_elem:
    [
      [
        "some"; "["; ahat_decls = LIST0 lf_ahat_decl; "]"; "block"; a = lf_ahat ->
          LF.SchElem (_loc, List.fold_left (fun d ds -> LF.Dec (d, ds)) LF.Empty ahat_decls, LF.SigmaDecl (Id.mk_name None, [a]))
      ]
    ]
  ;

  lf_ahat_decl:
    [
      [
        x = SYMBOL; ":"; a = lf_ahat ->
          LF.TypDecl (Id.mk_name (Some x), a)
      ]
    ]
  ;

  lf_ahat:
    [
      [
        a = lf_typ
          -> a
      ]
    ]
  ;

  lf_dctx:
    [
      [
        "." ->
          LF.Null
      |
        psi = SYMBOL ->
          LF.CtxVar (Id.mk_name (Some psi))
      |
        cPsi = lf_dctx; ","; x = SYMBOL; ":"; tA = lf_typ ->
          LF.DDec (cPsi, LF.TypDecl (Id.mk_name (Some x), tA))
      ]
    ]
  ;

  cmp_typ:
    [ "full" RIGHTA
      [
        "{"; psi = SYMBOL; ":"; "("; w = SYMBOL; ")"; "*"; "}"; tau = SELF ->
          Comp.TypCtxPi (_loc, (Id.mk_name (Some psi), Id.mk_name (Some w)), tau)
      |
        ctyp_decl = lf_ctyp_decl; tau = SELF ->
          Comp.TypPiBox (_loc, ctyp_decl, tau)
      |
        tau1 = SELF; "->"; tau2 = SELF ->
          Comp.TypArr (_loc, tau1, tau2)
      ]
    | "atomic"
      [
        tA = lf_typ (*LEVEL "atomic"*); "["; cPsi = lf_dctx; "]" ->
          Comp.TypBox (_loc, tA, cPsi)
      |
        "("; tau = SELF; ")" ->
          tau
      ]
    ] 
  ;

  cmp_exp_chk:
    [ "full"
      [
         "fn"; f = SYMBOL; "=>"; e = SELF ->
           Comp.Fun (_loc, Id.mk_name (Some f), e)
      |
        "FN"; f = SYMBOL; "=>"; e = SELF ->
          Comp.CtxFun (_loc, Id.mk_name (Some f), e)
      |
        "mlam"; f = SYMBOL; "=>"; e = SELF ->
          Comp.MLam (_loc, Id.mk_name (Some f), e)
      |
        "case"; i = cmp_exp_syn; "of"; bs = LIST1 cmp_branch SEP "|" ->
          Comp.Case (_loc, i, bs)
       |
        "let"; "val"; bs = LIST1 cmp_let_val_binding SEP "val"; "in"; e' = cmp_exp_chk; "end" ->
          List.fold_right
            (fun
               (Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, (tA, cPsi)), Comp.Syn (_, i)))
               e''
               ->
                 Comp.Case (_loc, i, [Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, (tA, cPsi)), e'')]))
            bs
            e'
(* FIXME: locations are wrong here *)
      ]
    | "atomic"
      [
        "box"; "("; vars = LIST0 [ x = SYMBOL -> x ] SEP ","; "."; tM = lf_term_w_meta; ")" ->
          let pHat = List.map (fun x' -> Id.mk_name (Some x')) vars in
            Comp.Box (_loc, pHat, tM)
      |
        i = cmp_exp_syn ->
          Comp.Syn (_loc, i)
      |
        "("; e = SELF; ")" ->
          e
      ]
    ]
  ;

  cmp_exp_syn:
    [ "full"
      [
        i = SELF; e = cmp_exp_chk ->
          Comp.Apply (_loc, i, e)
      |
        i = SELF; "["; cPsi = lf_dctx; "]" ->
          Comp.CtxApp (_loc, i, cPsi)
(*       | *)
(*         i = SELF; "["; vars = LIST0 [ x = SYMBOL -> x ]; "."; tM = lf_term; "]" -> *)
(*           let pHat = List.map (fun x' -> Id.mk_name (Some x')) vars in *)
(*             Comp.MApp (_loc, i, (pHat, tM)) *)
      ]
    | "atomic"
      [
        x = SYMBOL ->
          Comp.Var (_loc, Id.mk_name (Some x))
      |
(*         e = cmp_exp_chk; ":"; tau = cmp_typ -> *)
(*           Comp.Ann (_loc, e, tau) *)
(*       | *)
        "("; i = SELF; ")" ->
          i
      ]
    ]
  ;

  cmp_branch:
    [
      [
        ctyp_decls = LIST0 lf_ctyp_decl; "box"; "("; vars = LIST0 [ x = SYMBOL -> x ] SEP ","; "."; tM = lf_term_w_meta; ")"; ":"; tA = lf_typ LEVEL "atomic"; "["; cPsi = lf_dctx; "]"; "=>"; e = cmp_exp_chk ->
          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls
          and pHat        = List.map (fun x' -> Id.mk_name (Some x')) vars in
            Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, (tA, cPsi)), e)
      ]
    ]
  ;

  cmp_let_val_binding:
    [
      [
        ctyp_decls = LIST0 lf_ctyp_decl; "box"; "("; vars = LIST0 [ x = SYMBOL -> x ] SEP ","; "."; tM = lf_term_w_meta; ")"; ":"; tA = lf_typ LEVEL "atomic"; "["; cPsi = lf_dctx; "]"; "="; i = cmp_exp_syn ->
          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls
          and pHat        = List.map (fun x' -> Id.mk_name (Some x')) vars in
            Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, (tA, cPsi)), Comp.Syn (_loc, i))
(* FIXME: need ghost loc for Syn *)
      ]
    ]
  ;

END

(********************)
(* Parser Interface *)
(********************)

let parse_stream ?(name = "<stream>") ~input entry =
  Grammar.parse entry (Grammar.Loc.mk name) input

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
