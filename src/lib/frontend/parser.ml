(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(* NOTE: Be careful with tuareg-mode M-q in this file -- it doesn't
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


type pair_or_atom =
  | Pair of Comp.exp_chk
  | Atom


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
         a_or_c = SYMBOL; ":"; k_or_a = lf_kind_or_typ ; "." ->
           begin match k_or_a with
             | Kind k -> Sgn.Typ   (_loc, Id.mk_name (Id.SomeString a_or_c), k)
             | Typ  a -> Sgn.Const (_loc, Id.mk_name (Id.SomeString a_or_c), a)
           end
      |
        "schema"; w = SYMBOL; "="; bs = LIST1 lf_schema_elem SEP "+"; ";" ->
          Sgn.Schema (_loc, Id.mk_name (Id.SomeString w), LF.Schema bs)
      |
        "rec"; f = SYMBOL; ":"; tau = cmp_typ; "="; e = cmp_exp_chk; ";" ->
          Sgn.Rec (_loc, Id.mk_name (Id.SomeString f), tau, e)


      | "%name"; w = SYMBOL ; mv = UPSYMBOL ; x = OPT [ y = SYMBOL -> y ]; "." -> 
            Sgn.Pragma (_loc, LF.NamePrag (Id.mk_name (Id.SomeString w), mv, x))

      | "%name"; w = SYMBOL ; mv = UPSYMBOL ; x = OPT [ y = SYMBOL -> y ]; "." -> 
            Sgn.Pragma (_loc, LF.NamePrag (Id.mk_name (Id.SomeString w), mv, x))

      | "%not" ->
            Sgn.Pragma (_loc, LF.NotPrag)
      ]
    ]
  ;

  lf_kind_or_typ:
    [
      RIGHTA
        [
           "{"; x = symbol; ":"; a2 = lf_typ; "}"; k_or_a = SELF ->
             begin match k_or_a with
               | Kind k -> Kind (LF.PiKind (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), k))
               | Typ  a -> Typ  (LF.PiTyp  (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), a))
             end

        |
           a2 = lf_typ LEVEL "atomic"; "->"; k_or_a = SELF ->
             begin match k_or_a with
               | Kind k -> Kind (LF.ArrKind (_loc, a2, k))
               | Typ  a -> Typ  (LF.ArrTyp  (_loc, a2, a))
             end

        | 
          "type" ->
             Kind (LF.Typ _loc)

        |
          a = lf_typ LEVEL "atomic" ->
              Typ a

        ]

    | LEFTA
        [

          k_or_a = SELF; "<-"; a2 = lf_typ LEVEL "atomic" ->
             begin match k_or_a with
               | Kind k -> Kind (LF.ArrKind (_loc, a2, k))
               | Typ  a -> Typ  (LF.ArrTyp  (_loc, a2, a))
             end


        ]
    ]
  ;

  lf_typ:
    [ RIGHTA
        [
           "{"; x = SYMBOL; ":"; a2 = SELF; "}"; a = SELF ->
             LF.PiTyp (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), a)
        |
           a2 = SELF; "->"; a = SELF ->
             LF.ArrTyp (_loc, a2, a)

        ]
    | LEFTA
        [
           a2 = SELF; "<-"; a = SELF ->
             LF.ArrTyp (_loc, a, a2)

        ]

    | "atomic"
        [
          "("; a = SELF; ")" ->
            a    
        | 
          a = SYMBOL; ms = LIST0 (lf_term LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp)
        ]
    ]
  ;

  lf_term:
    [ RIGHTA
        [ 
          "\\"; x = SYMBOL; "."; m = SELF -> 
            LF.Lam (_loc, (Id.mk_name (Id.SomeString x)), m)
        ]

    | 
     LEFTA
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
         u = UPSYMBOL  ->   
            LF.Name (_loc, Id.mk_name (Id.SomeString u))

      |
        x = SYMBOL ->
                LF.Name (_loc, Id.mk_name (Id.SomeString x))

      ]
    ]
  ;

  lf_schema_elem:
    [
      [
        some = lf_schema_some; arec = lf_typ_rec ->
          LF.SchElem (_loc,
                      List.fold_left (fun d ds -> LF.Dec (d, ds)) LF.Empty some,
                      arec)
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

lf_typ_rec_block:
[[
      "block"; a_list = LIST1 lf_typ_rec_elem SEP ","; "."; a_last = lf_typ LEVEL "atomic"
        -> (List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest)) a_list (LF.SigmaLast a_last))
]];

lf_typ_rec:
  [
    [
        b = lf_typ_rec_block
        -> b
    | 
        a = lf_typ
        -> LF.SigmaLast a
    ]
  ]
;


  lf_typ_rec_elem:
    [
      [
        x = SYMBOL; ":"; a = lf_typ
         -> (Id.mk_name (Id.SomeString x), a)

      | 
        x = UPSYMBOL; ":"; a = lf_typ
         -> (Id.mk_name (Id.SomeString x), a)

      ]
    ]
  ;

  lf_ahat_decl:
    [
      [
        x = SYMBOL; ":"; a = lf_typ ->
          LF.TypDecl (Id.mk_name (Id.SomeString x), a)
      ]
    ]
  ;



(* ************************************************************************************** *)
(* Parsing of computations and LF terms occurring in computations                         *)

  clf_ctyp_decl:
    [
      [
        "{"; hash = "#"; p = SYMBOL; "::"; 
         tA = (clf_typ LEVEL "sigma"); "["; cPsi = clf_dctx; "]"; "}" ->
                LF.PDecl (_loc, Id.mk_name (Id.SomeString p), tA, cPsi)


      | 
          "{";  u = UPSYMBOL; "::"; 
         tA = clf_typ LEVEL "atomic"; "["; cPsi = clf_dctx; "]"; "}" ->
           LF.MDecl (_loc, Id.mk_name (Id.SomeString u), tA, cPsi)
      ]
    ]
  ;

  clf_typ:
    [ RIGHTA
        [
           "{"; x = SYMBOL; ":"; a2 = SELF; "}"; a = SELF ->
             LF.PiTyp (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), a)
        |
           a2 = SELF; "->"; a = SELF ->
             LF.ArrTyp (_loc, a2, a)
        ]

    | "atomic"
        [
          "("; a = SELF; ")" ->
            a    
        | 
          a = SYMBOL; ms = LIST0 (clf_term LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp)
        ]
    | "sigma"
        [
          "("; a = SELF; ")" ->
            a    
        | 
          a = SYMBOL; ms = LIST0 (clf_term LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp)
        |
          typRec = lf_typ_rec_block
          ->  LF.Sigma (_loc, typRec)
        ]
    ]
  ;

  clf_term:
    [ RIGHTA
        [
          "\\"; x = SYMBOL; "."; m = SELF ->
            LF.Lam (_loc, (Id.mk_name (Id.SomeString x)), m)
        ]

    | LEFTA
        [
          h = clf_head; ms = LIST0 (clf_term LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Root (_loc, h, sp)
        ]

    | "atomic" 
        [
            (* u = UPSYMBOL; "["; sigma' = clf_sub_new; "]"   ->   
                    LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), sigma'), LF.Nil) *)

          u = UPSYMBOL ->   
            LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), LF.EmptySub _loc), LF.Nil) 

        |  "("; u = UPSYMBOL; sigma' = clf_sub_new; ")"   ->   
                    LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), sigma'), LF.Nil) 

        |   h = clf_head ->
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

  clf_head:
    [
      [
        "#"; p = SYMBOL; "."; k = INTLIT; sigma = clf_sub_new ->
                LF.ProjPVar (_loc, int_of_string k, (Id.mk_name (Id.SomeString p), sigma))
      |
        "#"; p = SYMBOL;  sigma = clf_sub_new ->
                LF.PVar (_loc, Id.mk_name (Id.SomeString p), sigma)
      |
        x = SYMBOL; "."; k = INTLIT ->
                LF.ProjName (_loc, int_of_string k, Id.mk_name (Id.SomeString x))
      |
        x = SYMBOL ->
                LF.Name (_loc, Id.mk_name (Id.SomeString x))
      ]
    ]
  ;


  clf_sub_new:
    [
      [
        "."; "."  ->
          LF.Id (_loc) 

      | 
        sigma = SELF;   h = clf_head -> 
          LF.Dot (_loc, sigma, LF.Head h)

      | 
        sigma = SELF;  tM = clf_term -> 
          LF.Dot (_loc, sigma, LF.Normal tM)


      | 
          h = clf_head -> 
          LF.Dot (_loc, LF.EmptySub _loc, LF.Head h)

      | 
          tM = clf_term -> 
          LF.Dot (_loc, LF.EmptySub _loc, LF.Normal tM)


    (*  |

        ->
          LF.EmptySub _loc *)

      ]
    ]

  ;
 

  clf_dctx:
    [
      [        
       (* "."  *)
        ->
          LF.Null

      |
        psi = SYMBOL ->
          LF.CtxVar (Id.mk_name (Id.SomeString psi))

      |  x = SYMBOL; ":"; tA = clf_typ ->
          LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA))
(*      |
         x = SYMBOL; ":"; typRec = lf_typ_rec ->
          LF.SigmaDec (LF.Null, LF.SigmaDecl (Id.mk_name (Id.SomeString x), typRec))
*)

      |
        cPsi = clf_dctx; ","; x = SYMBOL; ":"; tA = clf_typ ->
          LF.DDec (cPsi, LF.TypDecl (Id.mk_name (Id.SomeString x), tA))
(*      |
        cPsi = clf_dctx; ","; x = SYMBOL; ":"; typRec = lf_typ_rec ->
          LF.SigmaDec (cPsi, LF.SigmaDecl (Id.mk_name (Id.SomeString x), typRec))
*)
      ]
    ]
  ;


(* ************************************************************************************** *)

  cmp_typ:
    [ "full" RIGHTA
      [
        "{"; psi = SYMBOL; ":"; "("; w = SYMBOL; ")"; "*"; "}"; tau = SELF ->
          Comp.TypCtxPi (_loc, (Id.mk_name (Id.SomeString psi), Id.mk_name (Id.SomeString w)), tau)
      |
        ctyp_decl = clf_ctyp_decl; tau = SELF ->
          Comp.TypPiBox (_loc, ctyp_decl, tau)

      |
        tau1 = SELF; "->"; tau2 = SELF ->
          Comp.TypArr (_loc, tau1, tau2)

      ]

    | 
        LEFTA 
      [

        tau1 = SELF; "*"; tau2 = SELF ->
          Comp.TypCross (_loc, tau1, tau2)

      ]


    | 
        "atomic"
      [
        "("; tA = clf_typ (*LEVEL "atomic"*); ")" ; "["; cPsi = clf_dctx; "]" ->
          Comp.TypBox (_loc, tA, cPsi)

      | 
         tA = clf_typ (*LEVEL "atomic"*); "["; cPsi = clf_dctx; "]" ->
           Comp.TypBox (_loc, tA, cPsi)

      |
        "("; tau = SELF; ")" ->
          tau
      ]


    ] 
  ;


  cmp_pair_atom : 
    [
      [
        ","; e2 = cmp_exp_chk ; ")" -> Pair e2

      | ")"                 -> Atom

      ]
    ]
  ;


  cmp_exp_chk:
    [ "full"
      [
         "fn"; f = SYMBOL; "=>"; e = SELF ->
           Comp.Fun (_loc, Id.mk_name (Id.SomeString f), e)
      |
        "FN"; f = SYMBOL; "=>"; e = SELF ->
          Comp.CtxFun (_loc, Id.mk_name (Id.SomeString f), e)
      |
        "mlam"; f = UPSYMBOL; "=>"; e = SELF ->
          Comp.MLam (_loc, Id.mk_name (Id.SomeString f), e)
      |
        "case"; i = cmp_exp_syn; "of"; bs = LIST1 cmp_branch SEP "|" ->
          Comp.Case (_loc, i, bs)

      | 
        "let"; "("; x = SYMBOL; ","; y = SYMBOL; ")"; "="; i = cmp_exp_syn;  "in"; e = SELF ->
          Comp.LetPair (_loc, i, (Id.mk_name (Id.SomeString x), Id.mk_name (Id.SomeString y), e))

      |

       "let"; ctyp_decls = LIST0 clf_ctyp_decl; 
       (* "box"; "("; pHat = clf_dctx ;"."; tM = clf_term; ")";  *)
       "["; pHat = clf_dctx ;"]"; tM = clf_term; 
       tau = OPT [ ":"; tA = clf_typ LEVEL "atomic"; "["; cPsi = clf_dctx; "]" -> (tA, cPsi)];  
       "="; i = cmp_exp_syn; "in"; e' = SELF ->         
         let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
          Comp.Case (_loc, i, [Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, tau), e')]) 

      ]

    | "atomic"
      [
        (* "box"; "("; vars = LIST0 [ x = SYMBOL -> x ] SEP ","; "."; tM = clf_term; ")" ->   *)
      "["; vars = LIST0 [ x = SYMBOL -> x ] SEP ","; "]"; tM = clf_term ->   
          let pHat = List.map (fun x' -> Id.mk_name (Id.SomeString x')) vars in
            Comp.Box (_loc, pHat, tM)

      | 
        "(" ; e1 = SELF; p_or_a = cmp_pair_atom -> 
          begin match p_or_a with 
            | Pair e2 ->   Comp.Pair (_loc, e1, e2)
            | Atom    ->   e1
          end 
      |
        i = cmp_exp_syn ->
          Comp.Syn (_loc, i)
(*      |
        "("; e = SELF; ")" ->
          e
*)
      ]
    ]
  ;


  cmp_exp_syn:
    [ "full"
      [
        i = SELF; "["; cPsi = clf_dctx; "]" ->
          Comp.CtxApp (_loc, i, cPsi)

      |
        i = SELF; "<"; vars = LIST0 [ x = SYMBOL -> x ] SEP ","; "."; tM = clf_term; ">" ->
          let pHat = List.map (fun x' -> Id.mk_name (Id.SomeString x')) vars in
            Comp.MApp (_loc, i, (pHat, tM))
      |
        i = SELF; e = cmp_exp_chk ->
          Comp.Apply (_loc, i, e)
      ]
    | "atomic"
      [
        x = SYMBOL ->
          Comp.Var (_loc, Id.mk_name (Id.SomeString x))
      | 
      "["; cPsi = clf_dctx; "]"; tR = clf_term ->   
            Comp.BoxVal (_loc, cPsi, tR)

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
        ctyp_decls = LIST0 clf_ctyp_decl; 
      (* "box"; "("; pHat = clf_dctx ;"."; tM = clf_term; ")"; *)
        "["; pHat = clf_dctx ;"]"; tM = clf_term; 
         tau = OPT [ ":"; tA = clf_typ LEVEL "atomic"; "["; cPsi = clf_dctx; "]" -> (tA, cPsi)]; 
         "=>"; e = cmp_exp_chk ->  
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
