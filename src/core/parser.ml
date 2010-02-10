(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(* NOTE: Be careful with tuareg-mode M-q in this file -- it doesn't
   understand the grammar formatting below very well and will easily
   trash the layout. *)

(* Load the camlp4 extensible grammar syntax extension *)
#load "pa_extend.cmo";;

(* open Core 
open Core.Common
open Core.Syntax.Ext
*)
open Common
open Syntax.Ext
open Token

module Grammar = Camlp4.Struct.Grammar.Static.Make (Lexer)

type kind_or_typ =
  | Kind of LF.kind
  | Typ  of LF.typ


type pair_or_atom =
  | Pair of Comp.exp_chk
  | Atom


type mixtyp =
  |  MTArr of Loc.t * mixtyp * mixtyp
  |  MTCross of Loc.t * mixtyp * mixtyp
  |  MTCtxPi of  Loc.t * (Id.name * Id.name) * mixtyp
  |  MTBool of Loc.t
  |  MTBox of Loc.t * mixtyp * LF.dctx
  |  MTPiBox of Loc.t * LF.ctyp_decl * mixtyp
  |  MTPiTyp of Loc.t * LF.typ_decl * mixtyp
  |  MTAtom of Loc.t * Id.name * LF.spine

type whichmix = LFMix of LF.typ | CompMix of Comp.typ

exception MixErr of Loc.t

let mixloc = function
  |  MTArr(l, _, _) -> l
  |  MTCross(l, _, _) -> l
  |  MTCtxPi(l, _, _) -> l
  |  MTBool l -> l
  |  MTBox(l, _, _) -> l
  |  MTPiBox(l, _, _) -> l
  |  MTPiTyp(l, _, _) -> l
  |  MTAtom(l, _, _) -> l

(* unmix : mixtyp -> whichmix *  *)
let rec unmix = function
  |  MTArr(l, mt1, mt2) -> begin match (unmix mt1, unmix mt2) with
                                  | (LFMix lf1, LFMix lf2) -> LFMix(LF.ArrTyp(l, lf1, lf2))
                                  | (CompMix c1, CompMix c2) -> CompMix(Comp.TypArr(l, c1, c2))
                                  | (_, _) -> raise (MixErr (mixloc mt2))
                           end
  |  MTCross(l, mt1, mt2) -> CompMix(Comp.TypCross(l, toComp mt1, toComp mt2))
  |  MTCtxPi(l, (sym1, sym2), mt0) -> CompMix(Comp.TypCtxPi(l, (sym1, sym2), toComp mt0))
  |  MTBool l -> CompMix(Comp.TypBool)
  |  MTBox(l, mt0, dctx) -> CompMix(Comp.TypBox(l, toLF mt0, dctx))
  |  MTPiBox(l, cdecl, mt0) -> CompMix(Comp.TypPiBox(l, cdecl, toComp mt0))
  |  MTPiTyp(l, tdecl, mt0) -> LFMix(LF.PiTyp(l, tdecl, toLF mt0))
  |  MTAtom(l, name, spine) -> LFMix(LF.Atom(l, name, spine))

and toLF mt = match unmix mt with
  |  LFMix lf -> lf
  |  _ -> raise (MixErr (mixloc mt))

and toComp mt = match unmix mt with
  |  CompMix c -> c
  |  _ -> raise (MixErr (mixloc mt))



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

  rarr: [[ "->" -> ()
         | "→" -> () ]];  (* Unicode right arrow (HTML &rarr;) *)

  rArr:  [[ "=>" -> ()
         | "⇒" -> () ]];  (* Unicode double right arrow (HTML &rArr;) *)

  dots: [[ "."; "." -> ()
         | "…" -> () ]];  (* Unicode ellipsis (HTML &hellip;) *)

  gLambda: [[ "FN" -> ()
         | "Λ" -> () ]];  (* Unicode capital Lambda (HTML &Lambda;) *)
  
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
        "coercion"; w = SYMBOL; ":"; a_ctx = SYMBOL; rarr; b_ctx = SYMBOL; 
        "="; OPT [ "|"]; bs = LIST1 co_branch SEP "|" ; ";" -> 
          Sgn.Coercion (_loc, Id.mk_name (Id.SomeString w), 
                        LF.CoTyp(Id.mk_name (Id.SomeString a_ctx), Id.mk_name (Id.SomeString b_ctx)), bs)

      |
        "let"; x = SYMBOL; tau = OPT [ ":"; tau = cmp_typ -> tau] ; 
        "="; i = cmp_exp_syn;  ";" ->
          Sgn.Val (_loc, Id.mk_name (Id.SomeString x), tau, i)

      |
(*        "rec"; f = SYMBOL; ":"; tau = cmp_typ; "="; e = cmp_exp_chk; ";" ->
          Sgn.Rec (_loc, [Comp.RecFun (Id.mk_name (Id.SomeString f), tau, e)])
*)

        "rec"; f = LIST1 cmp_rec SEP "and";  ";" ->
          Sgn.Rec (_loc, f)

      | "%name"; w = SYMBOL ; mv = UPSYMBOL ; x = OPT [ y = SYMBOL -> y ]; "." -> 
            Sgn.Pragma (_loc, LF.NamePrag (Id.mk_name (Id.SomeString w), mv, x))

(*      | "%name"; w = SYMBOL ; mv = UPSYMBOL ; x = OPT [ y = SYMBOL -> y ]; "." -> 
            Sgn.Pragma (_loc, LF.NamePrag (Id.mk_name (Id.SomeString w), mv, x)) *)

      | "%not" ->
            Sgn.Pragma (_loc, LF.NotPrag)
      ]
    ]
  ;


  co_branch: 
   [ 
      [

        some_arg = lf_schema_some; arec = lf_typ_rec ; rArr; brec_opt = lf_typ_rec_opt ->
          LF.CoBranch (List.fold_left (fun d ds -> LF.Dec (d, ds)) LF.Empty some_arg, arec, brec_opt)
      ]
   ];




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
           a2 = lf_typ LEVEL "atomic"; rarr; k_or_a = SELF ->
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
           a2 = SELF; rarr; a = SELF ->
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
        some_arg = lf_schema_some; arec = lf_typ_rec ->
          LF.SchElem (_loc,
                      List.fold_left (fun d ds -> LF.Dec (d, ds)) LF.Empty some_arg,
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


  lf_typ_rec_opt:
   [
     [
       b = lf_typ_rec      -> Some b

     | 
       b = "_"             -> None
     ]
   ]
  ;

  lf_typ_rec_block:
    [
      [
      "block"; a_list = LIST1 lf_typ_rec_elem SEP ","; "."; a_last = lf_typ LEVEL "atomic"
        -> (List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest)) a_list (LF.SigmaLast a_last))
      ]
    ]
  ;

 
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


  lf_hat_elem :
    [
      [
        x = SYMBOL ->
        LF.VarName (Id.mk_name (Id.SomeString  x))

      |
        co = SYMBOL; "("; ctx_name = SYMBOL; ")" ->
          LF.CoName (Id.mk_name (Id.SomeString co), Id.mk_name (Id.SomeString ctx_name) )
          
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
           a2 = SELF; rarr; a = SELF ->
             LF.ArrTyp (_loc, a2, a)
        ]

    | "atomic"
        [
          "("; a = SELF; ")" ->
            a    
        | 
          a = SYMBOL; ms = LIST0 clf_normal ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp)
        ]
    | "sigma"
        [
          "("; a = SELF; ")" ->
            a    
        | 
          a = SYMBOL; ms = LIST0 clf_normal ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp)
        |
          typRec = clf_typ_rec_block
          ->  LF.Sigma (_loc, typRec)
        ]
    ]
  ;

  clf_normal:
     [ RIGHTA
       [
          "\\"; x = SYMBOL; "."; m = clf_term_app ->
            LF.Lam (_loc, (Id.mk_name (Id.SomeString x)), m)
       ]

    | "atomic"
        [
         (* u = UPSYMBOL; "["; sigma' = clf_sub_new; "]"   ->   
                     LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), sigma'), LF.Nil)
          |  *)
          u = UPSYMBOL ->
            LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), LF.EmptySub _loc), LF.Nil) 

        |
           "("; u = UPSYMBOL; sigma' = clf_sub_new; ")"   ->   
            LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), sigma'), LF.Nil) 
        |
            h = clf_head ->
             LF.Root (_loc, h, LF.Nil)               
        | 
            "_" -> 
            LF.Root (_loc, LF.Hole _loc , LF.Nil)

        | 
           "("; m = clf_term_app; ")" ->
             m
        |
           "<"; ms = LIST1 clf_term_app SEP ","; ">"  ->
             let rec fold = function [m] -> LF.Last m
                                    | m :: rest -> LF.Cons(m, fold rest)
             in
               LF.Tuple (_loc, fold ms)
        ]
     ]
   ;



  clf_typ_rec_block:
    [[
       "block"; a_list = LIST1 clf_typ_rec_elem SEP ","; "."; a_last = clf_typ LEVEL "atomic"
         -> (List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest)) a_list (LF.SigmaLast a_last))
     ]];
  

  clf_typ_rec_elem:
    [
      [
        x = SYMBOL; ":"; a = clf_typ
         -> (Id.mk_name (Id.SomeString x), a)

      | 
        x = UPSYMBOL; ":"; a = lf_typ
         -> (Id.mk_name (Id.SomeString x), a)

      ]
    ]
  ;


  clf_term_x:
    [  "atomic" 
        [
           a = clf_normal ->
              a
        |
          u = UPSYMBOL ->
            LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), LF.EmptySub _loc), LF.Nil) 
        |
           u = UPSYMBOL ; sigma' = clf_sub_new ->
              LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), sigma'), LF.Nil) 
        ]
    ]
  ;

  clf_term_app:
    [ LEFTA
        [
          h = clf_head; ms = LIST0 clf_normal ->
            let spine = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Root (_loc, h, spine)
        ]

    | RIGHTA
        [
          t = clf_term_x  ->
            t
        ]

    | "atomic" 
        [
          t = clf_term_x  ->
            t
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

      |  "("; "#"; p = SYMBOL; "."; k = INTLIT; sigma = clf_sub_new ; ")" ->
          LF.ProjPVar (_loc, int_of_string k, (Id.mk_name (Id.SomeString p), sigma))
      |
         "("; "#"; p = SYMBOL;  sigma = clf_sub_new ; ")" ->
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
          dots  ->
          LF.Id (_loc) 


       | co = SYMBOL; "("; dots ; ")"  -> 
           LF.CoId (_loc, Id.mk_name (Id.SomeString co)  )

      | 
        sigma = SELF;   h = clf_head -> 
          LF.Dot (_loc, sigma, LF.Head h)

      | 
        sigma = SELF;  tM = clf_normal -> 
          LF.Dot (_loc, sigma, LF.Normal tM)


      | 
          h = clf_head -> 
          LF.Dot (_loc, LF.EmptySub _loc, LF.Head h)

      | 
          tM = clf_normal -> 
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
          LF.CtxVar (_loc, Id.mk_name (Id.SomeString psi))

      |
        co = SYMBOL; "("; psi = SYMBOL; ")" ->
          LF.CoCtx (_loc, Id.mk_name (Id.SomeString co), Id.mk_name (Id.SomeString psi) )


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
     [[
         m = mixtyp  ->  try  toComp m
                         with MixErr l ->
                           (print_string ("Syntax error: Computation-level type used where LF type is expected (" ^ 
                                            Loc.to_string l ^ ")\n");
                            raise (MixErr l))
     ]];

  cmp_pair_atom : 
    [
      [
        ","; e2 = cmp_exp_chk ; ")" -> Pair e2

      | ")"                 -> Atom

      ]
    ]
  ;


 cmp_rec:
   [[
     f = SYMBOL; ":"; tau = cmp_typ; "="; e = cmp_exp_chk -> Comp.RecFun (Id.mk_name (Id.SomeString f), tau, e)
    ]]
;

cmp_exp_chk:
 [ LEFTA [
    e = cmp_exp_chkX   ->   e
  | i = cmp_exp_syn    ->   Comp.Syn (_loc, i)
 ]];

(* cmp_exp_chkX:  checkable expressions, except for synthesizing expressions *)
cmp_exp_chkX:
    [ LEFTA
      [  "fn"; f = SYMBOL; rArr; e = cmp_exp_chk ->
           Comp.Fun (_loc, Id.mk_name (Id.SomeString f), e)

      | gLambda; f = SYMBOL; rArr; e = cmp_exp_chk ->
          Comp.CtxFun (_loc, Id.mk_name (Id.SomeString f), e)

      | "mlam"; f = UPSYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, Id.mk_name (Id.SomeString f), e)

      | "mlam"; hash = "#"; p = SYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, Id.mk_name (Id.SomeString p), e)

      | "case"; i = cmp_exp_syn; "of"; OPT [ "|"]; bs = LIST1 cmp_branch SEP "|" ->
          Comp.Case (_loc, i, bs)

      | "if"; i = cmp_exp_syn; "then"; e1 = cmp_exp_chk ; "else"; e2 = cmp_exp_chk -> 
          Comp.If (_loc, i, e1, e2)

      | "let"; "("; x = SYMBOL; ","; y = SYMBOL; ")"; "="; i = cmp_exp_syn;  "in"; e = cmp_exp_chk ->
          Comp.LetPair (_loc, i, (Id.mk_name (Id.SomeString x), Id.mk_name (Id.SomeString y), e))

      | "let"; ctyp_decls = LIST0 clf_ctyp_decl;
       (* "box"; "("; pHat = clf_dctx ;"."; tM = clf_term; ")";  *)
       "["; pHat = clf_dctx ;"]"; tM = clf_term_app;
       tau = OPT [ ":"; tA = clf_typ LEVEL "atomic"; "["; cPsi = clf_dctx; "]" -> (tA, cPsi) ];
       "="; i = cmp_exp_syn; "in"; e' = cmp_exp_chk
       ->
         let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
          Comp.Case (_loc, i, [Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, tau), e')]) 
      | "(" ; e1 = cmp_exp_chk; p_or_a = cmp_pair_atom -> 
          begin match p_or_a with 
            | Pair e2 ->   Comp.Pair (_loc, e1, e2)
            | Atom    ->   e1
          end 
      ]

    | "atomic"
      [
        (* "box"; "("; vars = LIST0 [ x = SYMBOL -> x ] SEP ","; "."; tM = clf_term; ")" ->   *)
 (*     "["; var = LIST0 [ x = SYMBOL -> x ] SEP ","; "]"; tM = clf_term_app ->   
          let pHat = List.map (fun x' -> Id.mk_name (Id.SomeString x')) vars in
            Comp.Box (_loc, pHat, tM)
 *)
       
        "["; pHat = LIST0 [ x = lf_hat_elem -> x ] SEP ","; "]"; tM = clf_term_app ->            
            Comp.Box (_loc, pHat, tM)
      | 
        "(" ; e1 = cmp_exp_chk; p_or_a = cmp_pair_atom -> 
          begin match p_or_a with 
            | Pair e2 ->   Comp.Pair (_loc, e1, e2)
            | Atom    ->   e1
          end 
(*      |
        "("; e = SELF; ")" ->
          e
*)
      ]
 ];


(* isuffix: something that can follow an i; returns a function that takes the i it follows,
  and returns the appropriate synthesizing expression *)
isuffix:
 [ LEFTA [
     "["; cPsi = clf_dctx; "]"   ->   (fun i -> Comp.CtxApp(_loc, i, cPsi))
   | "<"; vars = LIST0 [ x = lf_hat_elem -> x ] SEP ","; "."; tM = clf_term_app; ">"   ->  (fun i -> Comp.MApp (_loc, i, (vars, tM)))
   | "=="; i2 = cmp_exp_syn   ->  (fun i -> Comp.Equal(_loc, i, i2))
   | x = SYMBOL   ->  (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Var (_loc, Id.mk_name (Id.SomeString x)))))
   | "ttrue"      ->   (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Boolean (_loc, true))))
   | "ffalse"     ->   (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Boolean (_loc, false))))
   | e = cmp_exp_chkX   ->   (fun i -> Comp.Apply(_loc, i, e))
 ]];

cmp_exp_syn:
 [ LEFTA [
    "["; cPsi = clf_dctx; "]"; tR = clf_term_app   ->  ((*print_string ("BOXVAL: " ^ Comp.synToString(Comp.BoxVal (_loc, cPsi, tR)) ^ "\n"); *)  Comp.BoxVal (_loc, cPsi, tR))
   | h = SELF; s = isuffix  ->  s(h)
   | h = SELF; "("; e = cmp_exp_chk; p_or_a = cmp_pair_atom   ->
       Comp.Apply (_loc, h, begin match p_or_a with 
                                    | Pair e2 ->   Comp.Pair (_loc, e, e2)
                                    | Atom    ->   e
                            end)
   | x = SYMBOL ->  Comp.Var (_loc, Id.mk_name (Id.SomeString x))
   | "ttrue"    ->   Comp.Boolean (_loc, true)
   | "ffalse"   ->   Comp.Boolean (_loc, false)
   | "("; i = SELF; ")"   ->   i
 ]];

(******
                      cmp_exp_syn:
                        [ LEFTA
                          [
                            i = SELF; e = cmp_exp_chk ->
                           (print_string("APPLY: " ^ Comp.synToString (Comp.Apply(_loc, i, e)) ^ "\n");
                              Comp.Apply (_loc, i, e))
                          |
                            i = SELF; "["; cPsi = clf_dctx; "]" ->
                              (print_string("CTXAPP: " ^ Comp.synToString (Comp.CtxApp(_loc, i, cPsi)) ^ "\n");
                              Comp.CtxApp (_loc, i, cPsi))
                    (*      |
                              "("; i = SELF; "["; cPsi = clf_dctx; "]"; ")" ->
                              (print_string("(CTXAPP): " ^ Comp.synToString (Comp.CtxApp(_loc, i, cPsi)) ^ "\n");
                              Comp.CtxApp (_loc, i, cPsi))
                    *)

                          |
                            i = SELF; "<"; vars = LIST0 [ x = lf_hat_elem -> x ] SEP ","; "."; tM = clf_term_app; ">" ->
                              (* let pHat = List.map (fun x' -> Id.mk_name (Id.SomeString x')) vars in *)
                                Comp.MApp (_loc, i, (vars, tM))

                          | i1 = SELF; "=="; i2 = SELF -> 
                               Comp.Equal(_loc, i1, i2)

                          ]

                        | "atomic"
                          [
                            x = SYMBOL ->
                              Comp.Var (_loc, Id.mk_name (Id.SomeString x))

                          | "ttrue" -> Comp.Boolean (_loc, true)
                          | "ffalse" -> Comp.Boolean (_loc, false)
                          | 

                          "["; cPsi = clf_dctx; "]"; tR = clf_term_app ->
                                Comp.BoxVal (_loc, cPsi, tR)
                          |
                    (*                    e = cmp_exp_chk; ":"; tau = cmp_typ ->
                                              Comp.Ann (_loc, e, tau)
                                          |
                    *)
                            "("; i = SELF; ")" ->
                              i
                          ]
                        ]
                      ;
*****)


  cmp_branch:
    [
      [
        ctyp_decls = LIST0 clf_ctyp_decl; 
      (* "box"; "("; pHat = clf_dctx ;"."; tM = clf_term; ")"; *)
        "["; pHat = clf_dctx ;"]"; tM = clf_term_app; 
         tau = OPT [ ":"; tA = clf_typ LEVEL "atomic"; "["; cPsi = clf_dctx; "]" -> (tA, cPsi)]; 
         rArr; e = cmp_exp_chk ->  
          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
            Comp.BranchBox (_loc, ctyp_decls', (pHat, tM, tau), e)
      ]
    ]
  ;





  mixtyp:
    [ RIGHTA
      [
        "{"; psi = SYMBOL; ":"; "("; w = SYMBOL; ")"; "*"; "}"; mixtau = SELF ->
          MTCtxPi (_loc, (Id.mk_name (Id.SomeString psi), Id.mk_name (Id.SomeString w)), mixtau)
      |
        ctyp_decl = clf_ctyp_decl; mixtau = SELF ->
          MTPiBox (_loc, ctyp_decl, mixtau)
      |
        mixtau1 = SELF; rarr; mixtau2 = SELF ->
          MTArr (_loc, mixtau1, mixtau2) 
      |
        "{"; x = SYMBOL; ":"; a2 = clf_typ; "}"; mixa = SELF ->
            MTPiTyp (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), mixa)
      ] 
     | 
        LEFTA 
      [

        tau1 = SELF; "*"; tau2 = SELF ->
          MTCross (_loc, tau1, tau2)

      ]
     | 
      "atomic"
      [
         mixtA = mixtyp (*LEVEL "atomic"*); "["; cPsi = clf_dctx; "]" ->
           MTBox (_loc, mixtA, cPsi)

      | tA = "Bool" -> MTBool _loc

      |
        "("; mixtau = mixtyp; ")" ->
          mixtau

      | 
          a = SYMBOL; ms = LIST0 clf_normal ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              MTAtom (_loc, Id.mk_name (Id.SomeString a), sp)
    ] 
  ] ;


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
  let result     = parse_stream ~name:name ~input:stream entry in
     close_in in_channel
   ; result
