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

let rec last l = begin match List.rev l with
  | [] -> None
  | h::t -> Some (h, t)
end 


type kind_or_typ =
  | Kind of LF.kind
  | Typ  of LF.typ


type dctx_or_hat = 
  | Dctx of LF.dctx
  | Hat of LF.psi_hat

type pair_or_atom =
  | Pair of Comp.exp_chk
  | Atom

type clf_pattern = 
  | PatEmpty of Loc.t
  | PatCLFTerm of Loc.t * LF.normal


type mixtyp =
  | MTCompKind of Loc.t
  | MTBase of Loc.t * Id.name * Comp.meta_spine 
  | MTArr of Loc.t * mixtyp * mixtyp
  | MTCross of Loc.t * mixtyp * mixtyp
  | MTCtxPi of  Loc.t * (Id.name * Id.name * Comp.depend) * mixtyp
  | MTBool of Loc.t
  | MTBox of Loc.t * mixtyp * LF.dctx
  | MTPBox of Loc.t * mixtyp * LF.dctx
  | MTCtx of Loc.t * Id.name 
  | MTSub of Loc.t * LF.dctx * LF.dctx
  | MTPiBox of Loc.t * LF.ctyp_decl * mixtyp
(* -bp Pi-types should not occur in computation-level types 
  |  MTPiTyp of Loc.t * LF.typ_decl * mixtyp *)
  | MTAtom of Loc.t * Id.name * LF.spine

type whichmix = LFMix of LF.typ | CompMix of Comp.typ | CompKindMix of Comp.kind

exception MixErr of Loc.t
exception PatternError of Loc.t

let mixloc = function
  |  MTCompKind l -> l 
  |  MTArr(l, _, _) -> l
  |  MTCross(l, _, _) -> l
  |  MTCtxPi(l, _, _) -> l
  |  MTBool l -> l
  |  MTBox(l, _, _) -> l
  |  MTPBox(l, _, _) -> l
  |  MTCtx(l, _) -> l
  |  MTSub(l, _, _) -> l
  |  MTPiBox(l, _, _) -> l
(*  |  MTPiTyp(l, _, _) -> l *)
  |  MTAtom(l, _, _) -> l
  |  MTBase(l, _, _) -> l

(* unmix : mixtyp -> whichmix *  *)
let rec unmix = function
  | MTCompKind l -> CompKindMix (Comp.Ctype l)
  | MTBase (l, a, ms) -> CompMix(Comp.TypBase (Some l, a, ms))
  | MTArr(l, mt1, mt2) -> begin match (unmix mt1, unmix mt2) with
                                  | (LFMix lf1, LFMix lf2) -> LFMix(LF.ArrTyp(l, lf1, lf2))
                                  | (CompMix c1, CompMix c2) -> CompMix(Comp.TypArr(l, c1, c2))

                                  | (CompMix c1, CompKindMix c2) -> 
                                      let x = Id.mk_name (Id.NoName) in 
                                      let (l, cdecl) =   (match c1 with 
                                          | Comp.TypBox (l, tA, cPsi) -> (l, LF.MDecl(l, x, tA, cPsi))
                                          | Comp.TypPBox (l, tA, cPsi) -> (l, LF.PDecl (l, x, tA, cPsi))
                                          | Comp.TypCtx (l, schema)    -> (l, LF.CDecl (l, x, schema))
                                                  )
                                       in 
                                       CompKindMix(Comp.PiKind(l, (cdecl, Comp.Explicit), c2))
(*                                       let mT =   (match c1 with 
                                          | Comp.TypBox (l, tA, cPsi) -> Comp.MetaTyp (l, cPsi, tA)
                                          | Comp.TypPBox (l, tA, cPsi) -> Comp.MetaParamTyp (l, cPsi, tA)
                                          | Comp.TypCtx (l, schema)    -> Comp.MetaSchema (l, schema)
                                                  )
                                       in 
                                       CompKindMix(Comp.ArrKind(l, mT, c2))*)

                                  | (_, _) -> raise (MixErr (mixloc mt2))
                           end
  | MTCross(l, mt1, mt2) -> CompMix(Comp.TypCross(l, toComp mt1, toComp mt2))
  | MTCtxPi(l, (sym1, sym2, dep), mt0) -> 
       begin match unmix mt0 with 
         | CompKindMix mk -> CompKindMix(Comp.PiKind (l, (LF.CDecl (l, sym1, sym2), dep), mk))
         | CompMix mt -> CompMix (Comp.TypCtxPi(l, (sym1, sym2, dep), mt))
         | _ -> raise (MixErr (mixloc mt0))
       end 
  |  MTBool l -> CompMix(Comp.TypBool)
  |  MTCtx  (l, schema) -> CompMix(Comp.TypCtx (l, schema))
  |  MTPBox(l, mt0, dctx) -> CompMix(Comp.TypPBox(l, toLF mt0, dctx))
  |  MTBox(l, mt0, dctx) -> CompMix(Comp.TypBox(l, toLF mt0, dctx))
  |  MTSub(l, dctx1, dctx) -> CompMix(Comp.TypSub(l, dctx1, dctx))
  |  MTPiBox(l, cdecl, mt0) -> 
       begin match unmix mt0 with 
         | CompKindMix mk -> CompKindMix (Comp.PiKind(l, (cdecl, Comp.Explicit), mk))
         | CompMix mt -> CompMix(Comp.TypPiBox(l, cdecl, mt))
         | _ -> raise (MixErr (mixloc mt0))
       end

(*  |  MTPiTyp(l, tdecl, mt0) -> LFMix(LF.PiTyp(l, tdecl, toLF mt0)) *)
  |  MTAtom(l, name, spine) -> LFMix(LF.Atom(l, name, spine))

and toLF mt = match unmix mt with
  |  LFMix lf -> lf
  |  _ -> raise (MixErr (mixloc mt))

and toComp mt = match unmix mt with
  |  CompMix c -> c
  | CompKindMix c -> (let l = mixloc mt in 
                        print_string ("Syntax error: Found Computation-level kind\n              Expected: computation-level type  \n " );
                      raise (MixErr l))
  |  _ -> (let l = mixloc mt in 
             print_string ("Syntax error: Found LF-type\n              Expected: computation-level type     \n");
             raise (MixErr l))


and toCompKind k = match unmix k with
  |  CompKindMix c -> c
  | CompMix c -> (let l = mixloc k in 
                    print_string ("Syntax error: Found Computation-level type\n              Expected: computation-level kind   \n");
                      raise (MixErr l))
  |  _ -> (let l = mixloc k in 
             print_string ("Syntax error: Found LF-type\n              Expected: computation-level kind \n ");

           raise (MixErr l))



(*******************************)
(* Global Grammar Entry Points *)
(*******************************)

let sgn_eoi = Grammar.Entry.mk "sig_eoi"

(*****************************************)
(* Dynamically Extensible Beluga Grammar *)
(*****************************************)

EXTEND Grammar
GLOBAL: sgn_eoi;

(*  sgn_eoi:
    [
      [
(*          decls = LIST0 sgn_decl; `EOI -> *)
           decls = sgn_decls; `EOI  -> decls
      ]
    ]
  ;
*)
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

 sgn_eoi:
   [
     [ decl = sgn_decl; decls = SELF -> decl @ decls
     | `EOI -> []
     ]
   ]
;

  sgn_lf_typ : 
    [
      [ a = SYMBOL; ":"; tA = lf_typ ->
          Sgn.Const   (_loc, Id.mk_name (Id.SomeString a), tA)
      ]
    ]
;
  

  sgn_comp_typ :
    [
      [
        a = UPSYMBOL; ":"; tau = cmp_typ -> 
          Sgn.CompConst (_loc, Id.mk_name (Id.SomeString a), tau)
      ]
    ];


  sgn_decl:
    [
      [
         a_or_c = SYMBOL; ":"; k_or_a = lf_kind_or_typ ; "." ->
           begin match k_or_a with
             | Kind k -> [Sgn.Typ   (_loc, Id.mk_name (Id.SomeString a_or_c), k)]
             | Typ  a -> [Sgn.Const (_loc, Id.mk_name (Id.SomeString a_or_c), a)]
           end

      |
        "datatype"; a = SYMBOL; ":"; k = lf_kind ; "=" ; OPT ["|"] ;
        const_decls = LIST0 sgn_lf_typ SEP "|" ; ";" ->
          Sgn.Typ (_loc, Id.mk_name (Id.SomeString a), k) :: const_decls
            

      | "datatype"; a = UPSYMBOL; ":"; k = cmp_kind ; "="; OPT ["|"] ;  c_decls = LIST0 sgn_comp_typ SEP "|"; ";"  
           -> 
            Sgn.CompTyp (_loc, Id.mk_name (Id.SomeString a), k) :: c_decls

      | "type"; a = UPSYMBOL; ":"; k = cmp_kind ; "=";  tau = cmp_typ ; ";" -> 
          [Sgn.CompTypAbbrev (_loc, Id.mk_name (Id.SomeString a), k, tau)]
      |
        "schema"; w = SYMBOL; "="; bs = LIST1 lf_schema_elem SEP "+"; ";" ->
          [Sgn.Schema (_loc, Id.mk_name (Id.SomeString w), LF.Schema bs)]

      |
        "let"; x = SYMBOL; tau = OPT [ ":"; tau = cmp_typ -> tau] ; 
        "="; i = cmp_exp_syn;  ";" ->
          [Sgn.Val (_loc, Id.mk_name (Id.SomeString x), tau, i)]

      |
(*        "rec"; f = SYMBOL; ":"; tau = cmp_typ; "="; e = cmp_exp_chk; ";" ->
          Sgn.Rec (_loc, [Comp.RecFun (Id.mk_name (Id.SomeString f), tau, e)])
*)

        "rec"; f = LIST1 cmp_rec SEP "and";  ";" ->
          [Sgn.Rec (_loc, f)]

      | "%name"; w = SYMBOL ; mv = UPSYMBOL ; x = OPT [ y = SYMBOL -> y ]; "." -> 
        [Sgn.Pragma (_loc, LF.NamePrag (Id.mk_name (Id.SomeString w), mv, x))]

(*      | "%name"; w = SYMBOL ; mv = UPSYMBOL ; x = OPT [ y = SYMBOL -> y ]; "." -> 
            Sgn.Pragma (_loc, LF.NamePrag (Id.mk_name (Id.SomeString w), mv, x)) *)

      | "%query" ; e = bound ; t = bound ; x = OPT [ y = UPSYMBOL ; ":" -> y ] ; a = lf_typ ; "." ->
        if Option.is_some x then
          let p = Id.mk_name (Id.SomeString (Option.get x)) in
          [Sgn.Query (_loc, Some p, a, e, t)]
        else
          [Sgn.Query (_loc, None, a, e, t)]

      | "%not" ->
        [Sgn.Pragma (_loc, LF.NotPrag)]
      ]
    ]
  ;

  bound:
    [
      [ "*" -> None
      | k = INTLIT -> Some (int_of_string k)
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



  lf_kind:
    [
      RIGHTA
        [
           "{"; x = symbol; ":"; a2 = lf_typ; "}"; k = SELF ->
             LF.PiKind (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), k)

        |
           a2 = lf_typ LEVEL "atomic"; rarr; k = SELF ->
             LF.ArrKind (_loc, a2, k)

        | 
          "type" -> LF.Typ _loc
        ]

    | LEFTA
        [

          k = SELF; "<-"; a2 = lf_typ LEVEL "atomic" ->
            LF.ArrKind (_loc, a2, k)

        ]
    ]
  ;

  lf_typ:
    [ RIGHTA
        [
           "{"; x = symbol; ":"; a2 = SELF; "}"; a = SELF ->
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


(*  lf_typ_rec_opt:
   [
     [
       b = lf_typ_rec      -> Some b

     | 
       b = "_"             -> None
     ]
   ]
  ;
*)
  lf_typ_rec_block:
    [
      [
      "block"; OPT "("; a_list = LIST1 lf_typ_rec_elem SEP "," ; OPT ")"
        (* ","; _u=SYMBOL; ":"; a_last = clf_typ LEVEL "atomic" *)
        -> 
          begin match  last a_list with
          | Some ((_ , a_last) , a_list) -> 
              (List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest)) 
                (List.rev a_list) (LF.SigmaLast a_last))
        end 
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


(*  lf_hat_elem :
    [
      [
        x = SYMBOL ->
          Id.mk_name (Id.SomeString  x)
          
      ]
    ]
  ;

*)



(* ************************************************************************************** *)
(* Parsing of computations and LF terms occurring in computations                         *)



  clf_decl:
  [
    [
      x = SYMBOL; ":"; tA = clf_typ -> LF.TypDecl (Id.mk_name (Id.SomeString x), tA)
    ]

  ]
;


  clf_ctyp_decl:
    [
      [
        "{"; hash = "#"; p = SYMBOL; ":"; 
         "["; cPsi = clf_dctx; "."; tA = clf_typ LEVEL "atomic";  "]"; "}" ->
           LF.PDecl (_loc, Id.mk_name (Id.SomeString p), tA, cPsi)

      | 
        "{"; hash = "#"; s = UPSYMBOL; ":"; 
         cPhi = clf_dctx; "["; cPsi = clf_dctx; "]"; "}" ->
                LF.SDecl (_loc, Id.mk_name (Id.SomeString s), cPhi, cPsi)


      | 
          "{";  u = UPSYMBOL; ":"; 
         "["; cPsi = clf_dctx; "."; tA = clf_typ LEVEL "atomic";  "]"; "}" ->
           LF.MDecl (_loc, Id.mk_name (Id.SomeString u), tA, cPsi)

      |
          "{"; psi = SYMBOL; ":"; w = SYMBOL; "}" -> 
            LF.CDecl (_loc, Id.mk_name (Id.SomeString psi), Id.mk_name (Id.SomeString w))

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
       "block"; OPT "("; a_list = LIST1 clf_typ_rec_elem SEP "," ; OPT ")"
       (* ; "."; a_last = clf_typ LEVEL "atomic" *)
         -> begin match  last a_list with
          | Some ((_ , a_last) , a_list) -> 
              (List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest)) 
                 (List.rev a_list) (LF.SigmaLast a_last))
        end 

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

      | "#"; s = UPSYMBOL;  "["; sigma = clf_sub_new ; "]"-> 
          LF.SVar (_loc, Id.mk_name (Id.SomeString s), sigma)

      ]
    ]
  ;


 
  clf_sub_new:
    [
      [
       
          "^" -> 
          LF.EmptySub (_loc )

      |    dots  ->
          LF.Id (_loc) 

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



  clf_hat_or_dctx:
    [
      [
         -> Hat [ ]
        
      |    x = SYMBOL -> 
            Hat ([Id.mk_name (Id.SomeString x)])

      |   x = SYMBOL; ":"; tA = clf_typ ->
          Dctx (LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
      |
        cPsi = clf_hat_or_dctx; ","; x = SYMBOL; ":"; tA = clf_typ ->
          begin match cPsi with 
            | Hat [ ] -> Dctx (LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
            | Hat [g] -> Dctx (LF.DDec (LF.CtxVar (_loc, g), LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
            | Dctx cPsi' -> Dctx (LF.DDec (cPsi', LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
          end

      | phat = clf_hat_or_dctx; "," ; y = SYMBOL  ->
          begin match phat with 
            | Hat phat -> Hat (phat @ [Id.mk_name (Id.SomeString y)])
          end
       
      ]
    ]
  ;





(* ************************************************************************************** *)
(*
 meta_obj: 
   [
     [
       

     ]
   ];

*)

cmp_kind:
  [
    [ 
      k = mixtyp -> try toCompKind k 
                    with MixErr l -> (print_string ("at  location  " ^ Loc.to_string l) ; raise (MixErr l))
    ]
  ];


  cmp_typ:
     [[
         m = mixtyp  -> try toComp m 
                    with MixErr l -> (print_string ("at  location  " ^ Loc.to_string l) ; raise (MixErr l))
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

case_pragma:
 [[
    "%not" -> Pragma.PragmaNotCase
  | -> Pragma.RegularCase
 ]];

(* cmp_exp_chkX:  checkable expressions, except for synthesizing expressions *)
cmp_exp_chkX:
    [ LEFTA
      [  "fn"; f = SYMBOL; rArr; e = cmp_exp_chk ->
           Comp.Fun (_loc, Id.mk_name (Id.SomeString f), e)

      | gLambda; f = SYMBOL; rArr; e = cmp_exp_chk ->
          Comp.CtxFun (_loc, Id.mk_name (Id.SomeString f), e)

      | "mlam"; f = SYMBOL; rArr; e = cmp_exp_chk ->
          Comp.CtxFun (_loc, Id.mk_name (Id.SomeString f), e)

      | "mlam"; f = UPSYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, Id.mk_name (Id.SomeString f), e)

      | "mlam"; "#"; s = UPSYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, Id.mk_name (Id.SomeString s), e)

      | "mlam"; hash = "#"; p = SYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, Id.mk_name (Id.SomeString p), e)

      | "case"; i = cmp_exp_syn; "of"; prag = case_pragma; OPT [ "|"]; bs = LIST1 cmp_branch SEP "|" ->
          Comp.Case (_loc, prag, i, bs)

      | "impossible"; i = cmp_exp_syn; "in"; 
         ctyp_decls = LIST0 clf_ctyp_decl; "["; pHat = clf_dctx ;"]"  -> 
           let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
             Comp.Case (_loc, Pragma.RegularCase, i, [Comp.BranchBox (_loc, ctyp_decls', (pHat, Comp.EmptyPattern, None))])

      | "if"; i = cmp_exp_syn; "then"; e1 = cmp_exp_chk ; "else"; e2 = cmp_exp_chk -> 
          Comp.If (_loc, i, e1, e2)

      | "let"; "("; x = SYMBOL; ","; y = SYMBOL; ")"; "="; i = cmp_exp_syn;  "in"; e = cmp_exp_chk ->
          Comp.LetPair (_loc, i, (Id.mk_name (Id.SomeString x), Id.mk_name
          (Id.SomeString y), e))

      | "let";  x = SYMBOL; "="; i = cmp_exp_syn;  "in"; e = cmp_exp_chk ->
          Comp.Let (_loc, i, (Id.mk_name (Id.SomeString x), e))

      | "let"; ctyp_decls = LIST0 clf_ctyp_decl;
       (* "box"; "("; pHat = clf_dctx ;"."; tM = clf_term; ")";  *)
       "["; pHat = clf_dctx ;"."; tM = clf_term_app; "]";
       tau = OPT [ ":"; "["; cPsi = clf_dctx; "."; tA = clf_typ LEVEL "atomic";  "]" -> (tA, cPsi) ];
       "="; i = cmp_exp_syn; "in"; e' = cmp_exp_chk
       ->
         let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
          Comp.Case (_loc, Pragma.RegularCase, i, [Comp.BranchBox (_loc,  ctyp_decls', (pHat, Comp.NormalPattern (tM, e'), tau))]) 
      | "(" ; e1 = cmp_exp_chk; p_or_a = cmp_pair_atom -> 
          begin match p_or_a with 
            | Pair e2 ->   Comp.Pair (_loc, e1, e2)
            | Atom    ->   e1
          end 
      ]

    | "atomic"
      [
              
        "["; phat_or_psi = clf_hat_or_dctx ; "." ; tM = clf_term_app;  "]"  ->             
          begin match phat_or_psi with
            | Dctx cPsi ->  Comp.Syn(_loc, Comp.BoxVal (_loc, cPsi, tM)) 
            | Hat phat  ->                 Comp.Box (_loc, phat, tM) 
      end


(*        "["; phat_or_psi = clf_hat_or_dctx ; " . " ; tM = clf_term_app; "]" ->             
          begin match phat_or_psi with
            | Dctx cPsi ->  Comp.Syn(_loc, Comp.BoxVal (_loc, cPsi, tM)) 
            | Hat phat  ->                 Comp.Box (_loc, phat, tM) 
      end
*)
(*      | 
          "["; phat_or_psi = clf_hat_or_dctx ; "]" ; sigma = clf_sub_new ->             
          begin match phat_or_psi with
(*            | Dctx cPsi ->  Comp.Syn(_loc, Comp.SBoxVal (_loc, cPsi, tM))  *)
            | Hat phat  ->                 Comp.SBox (_loc, phat, sigma) 
          end
*)

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

  "["; phat_or_psi = clf_hat_or_dctx ; mobj = OPT ["."; tM = clf_term_app -> tM ]; "]"   ->  
     begin match (phat_or_psi , mobj) with 
       | (Dctx cPsi, Some tM)   -> (fun i -> Comp.MAnnApp (_loc, i, (cPsi,  tM)))
       | (Hat phat, Some tM)    -> (fun i -> Comp.MApp (_loc, i, (phat, tM)))
       | (Dctx cPsi, None)      -> (fun i -> Comp.CtxApp(_loc, i, cPsi)) 
       | ( Hat [psi] , None)    -> (fun i -> Comp.CtxApp(_loc, i, LF.CtxVar (_loc, psi)))
       | ( Hat [ ]   , None)    -> (fun i -> Comp.CtxApp(_loc, i, LF.Null))
         | ( _ , _   )      ->  raise (MixErr _loc)
     end 

(* | "["; cPsi = clf_dctx; "]"   ->   (fun i -> Comp.CtxApp(_loc, i, cPsi))   *)
(*   "["; phat_or_psi = clf_hat_or_dctx; "]" ->   
     begin match phat_or_psi with 
       | Dctx cPsi -> (fun i -> Comp.CtxApp(_loc, i, cPsi))
       | Hat phat -> raise (MixErr _loc)
     end 

 | "["; phat_or_psi = clf_hat_or_dctx ; "."; tM = clf_term_app; "]"   ->  
     begin match phat_or_psi with
       | Dctx cPsi  -> (fun i -> Comp.MAnnApp (_loc, i, (cPsi,  tM)))
       | Hat phat   -> (fun i -> Comp.MApp (_loc, i, (phat, tM)))
     end 
*)
 | "<"; phat_or_psi = clf_hat_or_dctx ; "."; tM = clf_term_app; ">"   ->  
     begin match phat_or_psi with
       | Dctx cPsi ->  (fun i -> Comp.MAnnApp (_loc, i, (cPsi, tM)))
       | Hat phat  ->  (fun i -> Comp.MApp (_loc, i, (phat, tM)))
     end

(* | "["; phat_or_psi = clf_hat_or_dctx ; "."; tM = clf_term_app; "]"   ->  
     begin match phat_or_psi with
       | Dctx cPsi ->  (fun i -> Comp.MAnnApp (_loc, i, (cPsi, tM)))
       | Hat phat  ->  (fun i -> Comp.MApp (_loc, i, (phat, tM)))
     end

*)

   | "=="; i2 = cmp_exp_syn   ->  (fun i -> Comp.Equal(_loc, i, i2))
   | x = SYMBOL   ->  
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Var (_loc, Id.mk_name (Id.SomeString x)))))
   | x = UPSYMBOL   ->  
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Const (_loc, Id.mk_name (Id.SomeString x)))))
   | "ttrue"      ->   
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Boolean (_loc, true))))
   | "ffalse"     ->   
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Boolean (_loc, false))))
   | e = cmp_exp_chkX   ->   
       (fun i -> Comp.Apply(_loc, i, e))
 ]];

cmp_exp_syn:
 [ LEFTA [
(*    "["; cPsi = clf_dctx; "]"; tR = clf_term_app   ->  
      ((*print_string ("BOXVAL: " ^ Comp.synToString(Comp.BoxVal (_loc, cPsi, tR)) ^ "\n"); *)  
        Comp.BoxVal (_loc, cPsi, tR))
*)
   "["; cPsi = clf_dctx; "."; tR = clf_term_app ; "]" ->  
      ((*print_string ("BOXVAL: " ^ Comp.synToString(Comp.BoxVal (_loc, cPsi, tR)) ^ "\n"); *)  
        Comp.BoxVal (_loc, cPsi, tR))
   | h = SELF; s = isuffix  ->  s(h)
   | h = SELF; "("; e = cmp_exp_chk; p_or_a = cmp_pair_atom   ->
       Comp.Apply (_loc, h, begin match p_or_a with 
                                    | Pair e2 ->   Comp.Pair (_loc, e, e2)
                                    | Atom    ->   e
                            end)
   | x = UPSYMBOL ->  Comp.Const (_loc, Id.mk_name (Id.SomeString x))
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


(* pattern spine: something that can follow a constructor; returns a function
  that takes the constructor it follows,
  and returns the appropriate synthesizing expression *)

clf_pattern : 
    [
      [
        tM = clf_term_app -> PatCLFTerm (_loc, tM)
     |
        "{"; "}" -> PatEmpty _loc
      ]
    ]
  ;


  cmp_branch_pattern:
    [
      [
        "["; cPsi = clf_dctx ; mobj = OPT ["."; tM = clf_pattern -> tM ]; "]" ;
         tau = OPT [ ":"; "["; cPsi = clf_dctx; "."; tA = clf_typ LEVEL "atomic"; "]" -> Comp.TypBox(_loc,tA, cPsi)] 
          ->   
              begin match  mobj with 
            | Some (PatEmpty _loc')   -> 
                (match tau with None -> Comp.PatEmpty (_loc', cPsi)
                   | Some tau -> Comp.PatAnn (_loc', Comp.PatEmpty (_loc', cPsi), tau)
                )
            | Some (PatCLFTerm (_loc', tM))   -> 
                (match tau with None -> Comp.PatMetaObj (_loc, Comp.MetaObjAnn (_loc',  cPsi,  tM))
                  | Some tau -> Comp.PatAnn (_loc, Comp.PatMetaObj(_loc, Comp.MetaObjAnn (_loc, cPsi,    tM)), tau))

            | None -> 
                (match tau with None -> Comp.PatMetaObj (_loc, Comp.MetaCtx (_loc,  cPsi))
                  | Some tau -> Comp.PatAnn (_loc, Comp.PatMetaObj(_loc, Comp.MetaCtx (_loc, cPsi)), tau))
              end 

     | "ttrue" -> Comp.PatTrue (_loc) 
     | "ffalse" -> Comp.PatFalse (_loc) 
     | x = SYMBOL ->  Comp.PatVar (_loc, Id.mk_name (Id.SomeString x))
     | x = UPSYMBOL; s = LIST0 (cmp_branch_pattern) -> 
         let sp = List.fold_right (fun t s -> Comp.PatApp (_loc, t, s)) s Comp.PatNil in 
           Comp.PatConst (_loc, Id.mk_name (Id.SomeString x), sp)
     | "("; p = SELF; ")"   ->  p 
      ]
    ]
  ;



  cmp_branch:
    [
      [
        ctyp_decls = LIST0 clf_ctyp_decl; 
        pattern = cmp_branch_pattern;
         rest = OPT [rArr; e = cmp_exp_chk -> e] ->
          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
           (match rest with
              | Some e  -> Comp.Branch (_loc, ctyp_decls', pattern, e)
              | None    ->  Comp.EmptyBranch (_loc, ctyp_decls', pattern)
           )
(*      |
          ctyp_decls = LIST0 clf_ctyp_decl; 
      (* "sbox"; "("; pHat = clf_dctx ;"."; tM = clf_term; ")"; *)
        "["; cPsi = clf_dctx ;"]"; sigma = clf_sub_new;  
         cPhi = OPT [ ":"; cPhi = clf_dctx -> cPhi ] ; 
         rArr; e = cmp_exp_chk ->  
           let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
            Comp.BranchSBox (_loc, ctyp_decls', (cPsi, sigma, cPhi), e)
*)
      ]
    ]
  ;

(*  cmp_branch:
    [
      [
        ctyp_decls = LIST0 clf_ctyp_decl; 
      (* "box"; "("; pHat = clf_dctx ;"."; tM = clf_term; ")"; *)
        "["; pHat = clf_dctx ;"."; pattern = cmp_branch_pattern;  "]";
         tau = OPT [ ":"; "["; cPsi = clf_dctx; "."; tA = clf_typ LEVEL "atomic"; "]" -> (tA, cPsi)]; 
         rest = OPT [rArr; e = cmp_exp_chk -> e] ->
          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
           (match (pattern, rest) with
              | (Some tM, Some e)  -> Comp.BranchBox (_loc, ctyp_decls', (pHat, Comp.NormalPattern (tM, e), tau))
              | (None, None) ->  Comp.BranchBox (_loc, ctyp_decls', (pHat, Comp.EmptyPattern, tau))
              | (Some _tM, None) -> (print_string ("Syntax error: missing body of case branch\n"); raise (MixErr _loc))
              | (None, Some _e) -> (print_string ("Syntax error: can't have a body with an empty pattern \"{}\"\n"); raise (MixErr _loc)))
      |
          ctyp_decls = LIST0 clf_ctyp_decl; 
      (* "sbox"; "("; pHat = clf_dctx ;"."; tM = clf_term; ")"; *)
        "["; cPsi = clf_dctx ;"]"; sigma = clf_sub_new;  
         cPhi = OPT [ ":"; cPhi = clf_dctx -> cPhi ] ; 
         rArr; e = cmp_exp_chk ->  
           let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
            Comp.BranchSBox (_loc, ctyp_decls', (cPsi, sigma, cPhi), e)
      ]
    ]
  ;

*)
(*   boxtyp :
   [
     [

         a = SYMBOL;  "["; cPsi = clf_dctx; "]" ->
              MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), LF.Nil), cPsi )

     | 
          "("; a = SYMBOL;  ms = LIST0 clf_normal; ")"; "["; cPsi = clf_dctx; "]" ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), sp), cPsi )


     ]
   ]
  ;
*)

  meta_obj:
    [
      [  

        "["; phat_or_psi = clf_hat_or_dctx ; mobj = OPT ["."; tM = clf_term_app -> tM ]; "]"   ->  
          begin match (phat_or_psi , mobj) with 
            | (Dctx cPsi, Some tM)   -> Comp.MetaObjAnn (_loc, cPsi,  tM)
            | (Hat phat, Some tM)    -> Comp.MetaObj (_loc, phat, tM)
            | (Dctx cPsi, None)      -> Comp.MetaCtx (_loc, cPsi)
            | ( Hat [psi] , None)    -> Comp.MetaCtx (_loc, LF.CtxVar (_loc, psi))
            | ( Hat [ ]   , None)    -> Comp.MetaCtx (_loc, LF.Null)
            | ( _ , _   )      ->  raise (MixErr _loc)
          end 
            (* Anything else should raise a meaningful parse error that a
               meta_obj is expected *)
      ]
    ];

  mixtyp:
    [ RIGHTA
      [
        "{"; psi = SYMBOL; ":";  w = SYMBOL; "}"; mixtau = SELF ->
          MTCtxPi (_loc, (Id.mk_name (Id.SomeString psi), 
                          Id.mk_name (Id.SomeString w), Comp.Explicit), mixtau)


  | "("; psi = SYMBOL; ":";  w = SYMBOL; ")"; mixtau = SELF ->
          MTCtxPi (_loc, (Id.mk_name (Id.SomeString psi), 
                          Id.mk_name (Id.SomeString w), Comp.Implicit), mixtau)

      |
        ctyp_decl = clf_ctyp_decl; mixtau = SELF ->
          MTPiBox (_loc, ctyp_decl, mixtau)
      |
        mixtau1 = SELF; rarr; mixtau2 = SELF ->
          MTArr (_loc, mixtau1, mixtau2) 
(*    |
        "{"; x = SYMBOL; ":"; a2 = clf_typ; "}"; mixa = SELF ->
            MTPiTyp (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), mixa)
*)
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

        tA = "Bool" -> MTBool _loc

      | tK = "ctype" -> MTCompKind _loc

      | 
          a = UPSYMBOL; ms = LIST0 meta_obj  ->
            let sp = List.fold_right (fun t s -> Comp.MetaApp (t, s)) ms  Comp.MetaNil in
              MTBase (_loc, Id.mk_name (Id.SomeString a), sp)

      | a = SYMBOL -> 
          MTCtx (_loc, Id.mk_name (Id.SomeString a))
      |
        "("; mixtau = mixtyp ; ")" ->
           mixtau 

      |   "(" ; "[";  cPsi = clf_dctx; "."; a = SYMBOL;  "]" ; rarr; mixtau2 = mixtyp ; ")" -> 
              MTArr(_loc, MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), LF.Nil), cPsi ), 
                    mixtau2) 

      |   "(" ; "#"; "[";  cPsi = clf_dctx; "."; a = SYMBOL;  "]" ; rarr; mixtau2 = mixtyp ; ")" -> 
              MTArr(_loc, MTPBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), LF.Nil), cPsi ), 
                    mixtau2) 

      (*   |   "["; cPsi = clf_dctx;  "."; a = SYMBOL;  "]" -> 
              MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), LF.Nil), cPsi )
      *)
      | 
          "#";"["; cPsi = clf_dctx; "."; a = SYMBOL;  ms = LIST0 clf_normal; "]"  ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              MTPBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), sp), cPsi ) 


      | 
          "["; cPsi = clf_dctx; "."; "("; a = SYMBOL;  ms = LIST0 clf_normal; ")"; "]"  ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), sp), cPsi ) 


      | 
          "["; cPsi = clf_dctx; "."; a = SYMBOL;  ms = LIST0 clf_normal; "]"  ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), sp), cPsi ) 

      
      | "("; ".";  ")"; "["; cPsi = clf_dctx; "]" -> 
          let cPhi0 = LF.Null in 
            MTSub (_loc, cPhi0, cPsi)


      | "("; x = SYMBOL; ":"; tA = clf_typ;  ")"; "["; cPsi = clf_dctx; "]" -> 
          let cPhi0 = LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA)) in 
            MTSub (_loc, cPhi0, cPsi)


      | "("; x = SYMBOL; ":"; tA = clf_typ; ","; decls = LIST1 clf_decl SEP ","; 
          ")"; "["; cPsi = clf_dctx; "]" -> 
          let cPhi0 = LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA)) in  
          let cPhi = List.fold_left (fun d ds -> LF.DDec(d, ds)) cPhi0 decls in 
            MTSub (_loc, cPhi, cPsi)


      | "("; psi = SYMBOL; ","; decls = LIST1 clf_decl SEP ","; 
          ")"; "["; cPsi = clf_dctx; "]" -> 
          let cPhi0 = LF.CtxVar (_loc, Id.mk_name (Id.SomeString psi)) in
          let cPhi = List.fold_left (fun d ds -> LF.DDec(d, ds)) cPhi0 decls in 
            MTSub (_loc, cPhi, cPsi)


(*      | 
          a = SYMBOL; ms = LIST0 clf_normal; ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              MTAtom (_loc, Id.mk_name (Id.SomeString a), sp) 
*)
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
