(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(* NOTE: Be careful with tuareg-mode M-q in this file – it doesn't
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

  symbol:
    [
      [
        sym = SYMBOL -> sym
      |
        sym = UPSYMBOL -> sym
      ]
    ]
  ;


  sgn_decl:
    [
      [
         a_or_c = symbol; ":"; k_or_a = lf_kind_or_typ; "." ->
           begin match k_or_a with
             | Kind k -> Sgn.Typ   (_loc, Id.mk_name (Some a_or_c), k)
             | Typ  a -> Sgn.Const (_loc, Id.mk_name (Some a_or_c), a)
           end
      |
        "schema"; w = symbol; "="; bs = LIST1 lf_schema_elem SEP "+"; ";" ->
          Sgn.Schema (_loc, Id.mk_name (Some w), LF.Schema bs)
      |
        "rec"; f = symbol; ":"; tau = cmp_typ; "="; e = cmp_exp_chk; ";" ->
          Sgn.Rec (_loc, Id.mk_name (Some f), tau, e)
      ]
    ]
  ;

  lf_kind_or_typ:
    [
      RIGHTA
        [
           "{"; x = symbol; ":"; a2 = lf_typ; "}"; k_or_a = SELF ->
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
         "{"; x = symbol; ":"; a = lf_typ; "}"; k = SELF ->
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
        "{"; hash = OPT "#"; u_or_p = symbol; "::"; tA = lf_typ LEVEL "atomic"; "["; cPsi = lf_dctx; "]"; "}" ->
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
           "{"; x = symbol; ":"; a2 = SELF; "}"; a = SELF ->
             LF.PiTyp (_loc, LF.TypDecl (Id.mk_name (Some x), a2), a)
        |
           a2 = SELF; "->"; a = SELF ->
             LF.ArrTyp (_loc, a2, a)
        ]

    | "atomic"
        [
          "("; a = SELF; ")" ->
            a    
        | 
          a = symbol; ms = LIST0 (lf_term LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Some a), sp)
        ]
    ]
  ;

  lf_term:
    [ RIGHTA
        [
          "\\"; x = symbol; "."; m = SELF ->
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
            "_" -> 
            LF.Root (_loc, LF.Hole _loc , LF.Nil)

        |
           "("; m = SELF; ")" ->
             m
        ]
    ]
  ;

  lf_head:
    [
      [      
        (* "#"; p = SYMBOL; "!";"["; sigma = lf_sub_new; "]"; "!" *) 
        "#"; p = SYMBOL; "["; sigma = lf_sub_new; "]" ->
                LF.PVar (_loc, Id.mk_name (Some p), sigma)

      |
        (* u = UPSYMBOL; sigma' = OPT [ "!"; "["; sigma = lf_sub; "]";"!" -> sigma]  ->  *)
        u = UPSYMBOL; sigma' = OPT [ "["; sigma = lf_sub_new; "]"  -> sigma]  ->  
        (* u = UPSYMBOL; sigma' = OPT [  sigma = lf_sub_new -> sigma]  ->   *)
          begin match sigma' with
            | None       -> LF.Name (_loc, Id.mk_name (Some u))
            | Some sigma -> LF.MVar (_loc, Id.mk_name (Some u), sigma)
          end 
      |
        x = SYMBOL ->
                LF.Name (_loc, Id.mk_name (Some x))

      ]
    ]
  ;

(*  lf_sub:
    [
      [
        "." ->
          LF.EmptySub _loc
      | 
        sigma = SELF; ";"; tM = lf_term -> 
          LF.Dot (_loc, sigma, LF.Normal tM)

      | 
        sigma = SELF; ","; h = lf_head -> 
          LF.Dot (_loc, sigma, LF.Head h)

      |
          "id" ->
          LF.Id (_loc) 
      ]
    ]

  ;
*)

  lf_sub_new:
    [
      [
        "."; "."  ->
          LF.Id (_loc) 

      | 
        sigma = SELF; ","; h = lf_head -> 
          LF.Dot (_loc, sigma, LF.Head h)

      | 
        sigma = SELF; ","; tM = lf_term -> 
          LF.Dot (_loc, sigma, LF.Normal tM)

      |
        "." ->
          LF.EmptySub _loc

      ]
    ]

  ;


  (* We don't currently deal with sigma types, so no need for ~ *)
  lf_schema_elem:
    [
      [
        some = lf_schema_some; "block"; arec = lf_typ_rec_toplevel ->
          LF.SchElem (_loc, List.fold_left (fun d ds -> LF.Dec (d, ds)) LF.Empty some,
                 LF.SigmaDecl (Id.mk_name None, arec))
      ]
    ]
  ;

  lf_schema_some:
    [
      [
       "some"; "["; ahat_decls = LIST0 lf_ahat_decl SEP ","; "]" -> ahat_decls
     | 
       -> []
     ] 
   ] 
;

  lf_typ_rec_toplevel:
    [
      [
        a_list = LIST1 lf_typ_rec_elem SEP ","; "."; a_last = lf_ahat
         -> List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest)) a_list (LF.SigmaLast a_last)
      | 
        a = lf_ahat
         -> LF.SigmaLast a
      ]
    ]
  ;


  lf_typ_rec_elem:
    [
      [
        x = symbol; ":"; a = lf_ahat
         -> (Id.mk_name (Some x), a)
      ]
    ]
  ;

  lf_ahat_decl:
    [
      [
        x = symbol; ":"; a = lf_ahat ->
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
        psi = symbol ->
          LF.CtxVar (Id.mk_name (Some psi))
      |
        cPsi = lf_dctx; ","; x = symbol; ":"; tA = lf_typ ->
          LF.DDec (cPsi, LF.TypDecl (Id.mk_name (Some x), tA))
      ]
    ]
  ;

  cmp_typ:
    [ "full" RIGHTA
      [
        "{"; psi = symbol; ":"; "("; w = symbol; ")"; "*"; "}"; tau = SELF ->
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
        "("; tA = lf_typ (*LEVEL "atomic"*); ")" ; "["; cPsi = lf_dctx; "]" ->
          Comp.TypBox (_loc, tA, cPsi)

      | 
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
         "fn"; f = symbol; "=>"; e = SELF ->
           Comp.Fun (_loc, Id.mk_name (Some f), e)
      |
        "FN"; f = symbol; "=>"; e = SELF ->
          Comp.CtxFun (_loc, Id.mk_name (Some f), e)
      |
        "mlam"; f = symbol; "=>"; e = SELF ->
          Comp.MLam (_loc, Id.mk_name (Some f), e)
      |
        "case"; i = cmp_exp_syn; "of"; bs = LIST1 cmp_branch SEP "|" ->
          Comp.Case (_loc, i, bs)
      |

       (* "let"; ctyp_decls = LIST0 lf_ctyp_decl; "box"; "("; pHat = lf_dctx ;"."; tM = lf_term; ")"; tau = OPT [ ":"; tA = lf_typ LEVEL "atomic"; "["; cPsi = lf_dctx; "]" -> (tA, cPsi)];  "="; i = cmp_exp_syn; "in"; e' = cmp_exp_chk; "end" ->            let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
          Comp.Case (_loc, i, [Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, tau), e')]) *)

        "let"; ctyp_decls = LIST0 lf_ctyp_decl;  "("; pHat = lf_dctx ;"."; tM = lf_term; ")"; tau = OPT [ ":"; tA = lf_typ LEVEL "atomic"; "["; cPsi = lf_dctx; "]" -> (tA, cPsi)];  "="; i = cmp_exp_syn; "in"; e' = cmp_exp_chk ->            let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
          Comp.Case (_loc, i, [Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, tau), e')]) 
      ]

    | "atomic"
      [
        (* "box"; "("; vars = LIST0 [ x = symbol -> x ] SEP ","; "."; tM = lf_term; ")" ->   *)
        "("; vars = LIST0 [ x = symbol -> x ] SEP ","; "."; tM = lf_term; ")" ->  
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
        i = SELF; "["; cPsi = lf_dctx; "]" ->
          Comp.CtxApp (_loc, i, cPsi)

(*       | *)
(*         i = SELF; "["; vars = LIST0 [ x = symbol -> x ]; "."; tM = lf_term; "]" -> *)
(*           let pHat = List.map (fun x' -> Id.mk_name (Some x')) vars in *)
(*             Comp.MApp (_loc, i, (pHat, tM)) *)

      |
        i = SELF; "<"; vars = LIST0 [ x = symbol -> x ] SEP ","; "."; tM = lf_term; ">" ->
          let pHat = List.map (fun x' -> Id.mk_name (Some x')) vars in
            Comp.MApp (_loc, i, (pHat, tM))
      |
        i = SELF; e = cmp_exp_chk ->
          Comp.Apply (_loc, i, e)
      ]
    | "atomic"
      [
        x = symbol ->
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
        (* ctyp_decls = LIST0 lf_ctyp_decl; "box"; "("; pHat = lf_dctx ;"."; tM = lf_term; ")"; tau = OPT [ ":"; tA = lf_typ LEVEL "atomic"; "["; cPsi = lf_dctx; "]" -> (tA, cPsi)]; "=>"; e = cmp_exp_chk ->  *)
        ctyp_decls = LIST0 lf_ctyp_decl; "("; pHat = lf_dctx ;"."; tM = lf_term; ")"; tau = OPT [ ":"; tA = lf_typ LEVEL "atomic"; "["; cPsi = lf_dctx; "]" -> (tA, cPsi)]; "=>"; e = cmp_exp_chk -> 

          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
            Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, tau), e)
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
