(* this is the original beluga parser with print statements in the file ast.out *)

(* Load the camlp4 extensible grammar syntax extension *)
#load "pa_extend.cmo";;

(* open Core 
open Core.Common
open Core.Syntax.Ext
*)
open Common
open Syntax.Ext
open Token
let out_channel = open_out "ast.out";
module Grammar = Camlp4.Struct.Grammar.Static.Make (Lexer)

type kind_or_typ =
  | Kind of LF.kind
  | Typ  of LF.typ


type dctx_or_hat = 
  | Dctx of LF.dctx
  | Hat of LF.psi_hat

type pair_or_atom =
  | Pair of Comp.exp_chk
  | Atom


type mixtyp =
  |  MTArr of Loc.t * mixtyp * mixtyp
  |  MTCross of Loc.t * mixtyp * mixtyp
  |  MTCtxPi of  Loc.t * (Id.name * Id.name * Comp.depend) * mixtyp
  |  MTBool of Loc.t
  |  MTBox of Loc.t * mixtyp * LF.dctx
  |  MTSub of Loc.t * LF.dctx * LF.dctx
  |  MTPiBox of Loc.t * LF.ctyp_decl * mixtyp
(* -bp Pi-types should not occur in computation-level types 
  |  MTPiTyp of Loc.t * LF.typ_decl * mixtyp *)
  |  MTAtom of Loc.t * Id.name * LF.spine

type whichmix = LFMix of LF.typ | CompMix of Comp.typ

exception MixErr of Loc.t

let mixloc = function
  |  MTArr(l, _, _) -> l
  |  MTCross(l, _, _) -> l
  |  MTCtxPi(l, _, _) -> l
  |  MTBool l -> l
  |  MTBox(l, _, _) -> l
  |  MTSub(l, _, _) -> l
  |  MTPiBox(l, _, _) -> l
(*  |  MTPiTyp(l, _, _) -> l *)
  |  MTAtom(l, _, _) -> l

(* unmix : mixtyp -> whichmix *  *)
let rec unmix = function
  |  MTArr(l, mt1, mt2) -> begin match (unmix mt1, unmix mt2) with
                                  | (LFMix lf1, LFMix lf2) -> LFMix(LF.ArrTyp(l, lf1, lf2))
                                  | (CompMix c1, CompMix c2) -> CompMix(Comp.TypArr(l, c1, c2))
                                  | (_, _) -> raise (MixErr (mixloc mt2))
                           end
  |  MTCross(l, mt1, mt2) -> CompMix(Comp.TypCross(l, toComp mt1, toComp mt2))
  |  MTCtxPi(l, (sym1, sym2, dep), mt0) -> CompMix(Comp.TypCtxPi(l, (sym1, sym2, dep), toComp mt0))
  |  MTBool l -> CompMix(Comp.TypBool)
  |  MTBox(l, mt0, dctx) -> CompMix(Comp.TypBox(l, toLF mt0, dctx))
  |  MTSub(l, dctx1, dctx) -> CompMix(Comp.TypSub(l, dctx1, dctx))
  |  MTPiBox(l, cdecl, mt0) -> CompMix(Comp.TypPiBox(l, cdecl, toComp mt0))
(*  |  MTPiTyp(l, tdecl, mt0) -> LFMix(LF.PiTyp(l, tdecl, toLF mt0)) *)
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
         decls = LIST0 sgn_decl; `EOI -> output_string out_channel "sgn_eoi list0 sgn_dcl \n";  decls
      ]
    ]
  ;

  symbol:
    [
      [
        sym = SYMBOL -> output_string out_channel sym; output_string out_channel " : symbol: SYMBOL \n"; sym
      |
        sym = UPSYMBOL -> output_string out_channel sym; output_string out_channel " : symbol: UPSYMBOL \n"; sym
      ]
    ]
  ;

  rarr: [[ "->" -> ()
         | "→" -> output_string out_channel "rarr "; output_char out_channel '\n' ]];  (* Unicode right arrow (HTML &rarr;) *)

  rArr:  [[ "=>" -> ()
         | "⇒" -> output_string out_channel "rArr "; output_char out_channel '\n' ]];  (* Unicode double right arrow (HTML &rArr;) *)

  dots: [[ "."; "." -> ()
         | "…" -> output_string out_channel "dots "; output_char out_channel '\n' ]];  (* Unicode ellipsis (HTML &hellip;) *)

  gLambda: [[ "FN" -> output_string out_channel "gLambda: FN "; output_char out_channel '\n'
         | "Λ" -> output_string out_channel "glambda: capital labmda "; output_char out_channel '\n' ]];  (* Unicode capital Lambda (HTML &Lambda;) *)
  
  sgn_decl:
    [
      [
         a_or_c = SYMBOL; ":"; k_or_a = lf_kind_or_typ ; "." ->
           begin match k_or_a with
             | Kind k -> output_string out_channel "sgn_decl: SYMBOL : kind "; output_string out_channel a_or_c; output_char out_channel '\n'; Sgn.Typ   (_loc, Id.mk_name (Id.SomeString a_or_c), k)
             | Typ  a -> output_string out_channel "sgn_decl: SYMBOL :  type "; output_string out_channel a_or_c; output_char out_channel '\n'; Sgn.Const (_loc, Id.mk_name (Id.SomeString a_or_c), a)
           end
      |
        "schema"; w = SYMBOL; "="; bs = LIST1 lf_schema_elem SEP "+"; ";" -> output_string out_channel "sgn_decl: schema symbol list1 sep "; output_char out_channel '\n'; 
          Sgn.Schema (_loc, Id.mk_name (Id.SomeString w), LF.Schema bs)

      |
        "let"; x = SYMBOL; tau = OPT [ ":"; tau = cmp_typ -> tau] ; 
        "="; i = cmp_exp_syn;  ";" -> output_string out_channel "sgn_decl: = cmp_exp_syn ; "; output_char out_channel '\n'; 
          Sgn.Val (_loc, Id.mk_name (Id.SomeString x), tau, i)

      |

        "rec"; f = LIST1 cmp_rec SEP "and";  ";" -> output_string out_channel "sgn_decl: rec list1 cmp-rec and ; "; output_char out_channel '\n'; 
          Sgn.Rec (_loc, f)

      | "%name"; w = SYMBOL ; mv = UPSYMBOL ; x = OPT [ y = SYMBOL -> y ]; "." ->  output_string out_channel w; output_string out_channel mv; 
                                                               output_string out_channel " : sgn_decl: %name symbol upsymbol opt \n"; Sgn.Pragma (_loc, LF.NamePrag (Id.mk_name (Id.SomeString w), mv, x))


      | "%not" -> output_string out_channel "sgn_decl: %not"; output_char out_channel '\n'; 
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
               | Kind k -> output_string out_channel "lf_kind_or_typ : { x : lf_typ } self kind k "; output_char out_channel '\n'; Kind (LF.PiKind (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), k))
               | Typ  a -> output_string out_channel "lf_kind_or_typ : { x : lf_typ } self typ a "; output_char out_channel '\n'; Typ  (LF.PiTyp  (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), a))
             end

        |
           a2 = lf_typ LEVEL "atomic"; rarr; k_or_a = SELF ->
             begin match k_or_a with
               | Kind k -> output_string out_channel "lf_kind_or_typ rarr self kind"; output_char out_channel '\n'; Kind (LF.ArrKind (_loc, a2, k))
               | Typ  a -> output_string out_channel "lf_kind_or_typ rarr self type \n";  Typ  (LF.ArrTyp  (_loc, a2, a))
             end

        | 
          "type" ->  output_string out_channel "lf_kind_or_typ : type "; output_char out_channel '\n';
             Kind (LF.Typ _loc)

        |
          a = lf_typ LEVEL "atomic" -> output_string out_channel "lf_kind_or_typ : lf_typ LEVEL atomic "; output_char out_channel '\n';
              Typ a

        ]

    | LEFTA
        [

          k_or_a = SELF; "<-"; a2 = lf_typ LEVEL "atomic" ->
             begin match k_or_a with
               | Kind k -> output_string out_channel "lf_kind_or_typ : SELF <- lf_typ LEVEL atomic kind k "; output_char out_channel '\n'; Kind (LF.ArrKind (_loc, a2, k))
               | Typ  a -> output_string out_channel "lf_kind_or_typ : SELF <- lf_typ LEVEL atomic typ a "; output_char out_channel '\n';Typ  (LF.ArrTyp  (_loc, a2, a))
             end

        ]
    ]
  ;

  lf_typ:
    [ RIGHTA
        [
           "{"; x = SYMBOL; ":"; a2 = SELF; "}"; a = SELF -> output_string out_channel "lf_typ  { x : self }"; output_char out_channel '\n';
             LF.PiTyp (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), a)
        |
           a2 = SELF; rarr; a = SELF ->output_string out_channel "lf_typ: righta self rarr self"; output_char out_channel '\n';
             LF.ArrTyp (_loc, a2, a)

        ]
    | LEFTA
        [
           a2 = SELF; "<-"; a = SELF -> output_string out_channel "lf_typ : self <- self "; output_char out_channel '\n';
             LF.ArrTyp (_loc, a, a2)

        ]

    | "atomic"
        [
          "("; a = SELF; ")" -> output_string out_channel "lf_typ : (self) "; output_char out_channel '\n';
            a    
        | 
          a = SYMBOL; ms = LIST0 (lf_term LEVEL "atomic") -> output_string out_channel "lf_typ : symbol lf_term atomic : "; output_string out_channel a; output_char out_channel '\n';
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp)
        ]
    ]
  ;


  lf_term:
    [ RIGHTA
        [ 
          "\\"; x = SYMBOL; "."; m = SELF -> output_string out_channel "lf_term : symbol . self "; output_char out_channel '\n';
            LF.Lam (_loc, (Id.mk_name (Id.SomeString x)), m)
        ]

    | 
     LEFTA
        [
          h = lf_head; ms = LIST0 (lf_term LEVEL "atomic") -> output_string out_channel "lf_term : lf_head list0 "; output_char out_channel '\n';
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Root (_loc, h, sp)
        ]

    | "atomic"
        [  
           h = lf_head -> output_string out_channel "lf_term : atomic lf head "; output_char out_channel '\n';
             LF.Root (_loc, h, LF.Nil)
               
        | 
            "_" -> output_string out_channel "lf_term : atomic _ "; output_char out_channel '\n';
            LF.Root (_loc, LF.Hole _loc , LF.Nil)

        |
           "("; m = SELF; ")" -> output_string out_channel "(self)"; output_char out_channel '\n';
             m


        ]
    ]
  ;

  lf_head:
    [
      [      
         u = UPSYMBOL  ->  output_string out_channel u; output_string out_channel " : lf_head : upsymbol \n"; LF.Name (_loc, Id.mk_name (Id.SomeString u))

      |
        x = SYMBOL -> output_string out_channel x; output_string out_channel " : lf_head : symbol \n"; LF.Name (_loc, Id.mk_name (Id.SomeString x))

      ]
    ]
  ;

  lf_schema_elem:
    [
      [
        some_arg = lf_schema_some; arec = lf_typ_rec -> output_string out_channel "lf_schema_elem : lf_schema_some lf_typ_rec "; output_char out_channel '\n'; 
          LF.SchElem (_loc,
                      List.fold_left (fun d ds -> LF.Dec (d, ds)) LF.Empty some_arg,
                      arec)
      ]
    ]
  ;

  lf_schema_some:
    [
      [
       "some"; "["; ahat_decls = LIST0 lf_ahat_decl SEP ","; "]" -> output_string out_channel "lf_schema_some : some [ list0 lf_ahat_decl , ] "; output_char out_channel '\n'; ahat_decls
       | 
          -> []  (* no print statement *)
      ] 
    ] 
  ;

  lf_typ_rec_block:
    [
      [
      "block"; a_list = LIST1 lf_typ_rec_elem SEP ","; "."; a_last = lf_typ LEVEL "atomic"
        -> output_string out_channel "lf_type_rec_block : block list1 lf_typ_rec_elem ,  ."; output_char out_channel '\n';
              (List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest)) a_list (LF.SigmaLast a_last))
      ]
    ]
  ;

 
  lf_typ_rec:
    [
      [
        b = lf_typ_rec_block
        -> output_string out_channel "lf_type_rec : lf_type_rec_block"; output_char out_channel '\n'; b
      | 
        a = lf_typ
        -> output_string out_channel "lf_type_rec : lf_type"; output_char out_channel '\n'; LF.SigmaLast a
      ]
    ]
  ;


  lf_typ_rec_elem:
    [
      [
        x = SYMBOL; ":"; a = lf_typ
         -> output_string out_channel "lf_type_rec_elem : SYMBOL : lf_typ"; output_char out_channel '\n'; (Id.mk_name (Id.SomeString x), a)

      | 
        x = UPSYMBOL; ":"; a = lf_typ
         -> output_string out_channel "lf_type_rec_elem : UPSYMBOL : lf_typ"; output_char out_channel '\n'; (Id.mk_name (Id.SomeString x), a)

      ]
    ]
  ;

  lf_ahat_decl:
    [
      [
        x = SYMBOL; ":"; a = lf_typ -> output_string out_channel "lf_ahat_decl : SYMBOL : lf_typ"; output_char out_channel '\n';
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
      x = SYMBOL; ":"; tA = clf_typ -> output_string out_channel "clf_decl : SYMBOL : clf_typ"; output_char out_channel '\n';
            LF.TypDecl (Id.mk_name (Id.SomeString x), tA)
    ]

  ]
;


  clf_ctyp_decl:
    [
      [
        "{"; hash = "#"; p = SYMBOL; "::"; 
         tA = (clf_typ LEVEL "sigma"); "["; cPsi = clf_dctx; "]"; "}" -> output_string out_channel "clf_ctyp_decl : { # SYMBOL :: clf_typ [ clf_dctx ] }"; output_char out_channel '\n';
                LF.PDecl (_loc, Id.mk_name (Id.SomeString p), tA, cPsi)

      | 
        "{"; hash = "#"; s = UPSYMBOL; "::"; 
         cPhi = clf_dctx; "["; cPsi = clf_dctx; "]"; "}" -> output_string out_channel "clf_ctyp_decl : { # UPSYMBOL :: clf_dctx [ clf_dctx ] }"; output_char out_channel '\n';
                LF.SDecl (_loc, Id.mk_name (Id.SomeString s), cPhi, cPsi)


      | 
          "{";  u = UPSYMBOL; "::"; 
         tA = clf_typ LEVEL "atomic"; "["; cPsi = clf_dctx; "]"; "}" -> output_string out_channel "clf_ctyp_decl : { # UPSYMBOL :: clf_typ LEVEL atomic [ clf_dctx ] }"; output_char out_channel '\n';
           LF.MDecl (_loc, Id.mk_name (Id.SomeString u), tA, cPsi)

      |
          "{"; psi = SYMBOL; ":"; "("; w = SYMBOL; ")"; "*"; "}" -> output_string out_channel "clf_ctyp_decl : { # SYMBOL : (  SYMBOL ) }"; output_char out_channel '\n';
            LF.CDecl (_loc, Id.mk_name (Id.SomeString psi), Id.mk_name (Id.SomeString w))

      ]
    ]
  ;

  clf_typ:
    [ RIGHTA
        [
           "{"; x = SYMBOL; ":"; a2 = SELF; "}"; a = SELF -> output_string out_channel "clf_typ : RIGHTA { # SYMBOL : SELF }"; output_char out_channel '\n';
             LF.PiTyp (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), a)
        |
           a2 = SELF; rarr; a = SELF -> output_string out_channel "clf_typ : RIGHTA SELF rarr SELF "; output_char out_channel '\n';
             LF.ArrTyp (_loc, a2, a)
        ]

    | "atomic"
        [
          "("; a = SELF; ")" -> output_string out_channel "clf_typ : atomic ( SELF ) "; output_char out_channel '\n';
            a    

        | 
           a = SYMBOL; ms = LIST0 clf_normal -> output_string out_channel "clf_typ : atomic SYMBOL List0 clf_normal "; output_char out_channel '\n';
             let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in 
               LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp) 


        ]
    | "sigma"
        [
          "("; a = SELF; ")" -> output_string out_channel "clf_typ : sigma (SELF) "; output_char out_channel '\n';
            a    
        | 
          a = SYMBOL; ms = LIST0 clf_normal ->  output_string out_channel "clf_typ : sigma SYMBOL list0 clf_normal "; output_char out_channel '\n';
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp)
        |
          typRec = clf_typ_rec_block
          ->   output_string out_channel "clf_typ : sigma clf_typ_rec_block "; output_char out_channel '\n'; LF.Sigma (_loc, typRec)
        ]
    ]
  ;

  clf_normal:
     [ RIGHTA
       [
          "\\"; x = SYMBOL; "."; m = clf_term_app ->  output_string out_channel "clf_normal : RIGHTA \\ SYMBOL . clf_term_app "; output_char out_channel '\n';
            LF.Lam (_loc, (Id.mk_name (Id.SomeString x)), m)
       ]

    | "atomic"
        [
          u = UPSYMBOL ->  output_string out_channel u; output_string out_channel ": clf_normal : atomic UPSYMBOL "; output_char out_channel '\n';
            LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), LF.EmptySub _loc), LF.Nil) 

        |
           "("; u = UPSYMBOL; sigma' = clf_sub_new; ")"   ->  output_string out_channel u; output_string out_channel " :clf_normal : atomic ( UPSYMBOL clf_sub_new ) "; output_char out_channel '\n'; 
            LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), sigma'), LF.Nil) 
        |
            h = clf_head -> output_string out_channel "clf_normal : atomic clf-head "; output_char out_channel '\n';
             LF.Root (_loc, h, LF.Nil)               
        | 
            "_" -> output_string out_channel "clf_normal : atomic _ "; output_char out_channel '\n';
            LF.Root (_loc, LF.Hole _loc , LF.Nil)

        | 
           "("; m = clf_term_app; ")" -> output_string out_channel "clf_normal : atomic ( clf_term_app ) "; output_char out_channel '\n';
             m
        |
           "<"; ms = LIST1 clf_term_app SEP ","; ">"  -> output_string out_channel "clf_normal : atomic < list1 clf_term_app SEP , > "; output_char out_channel '\n';
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
         -> output_string out_channel "clf_typ_rec_block : block list1 clf_typ_rec_elem SEP , . clf_typ LEVEL atomic "; output_char out_channel '\n';
               (List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest)) a_list (LF.SigmaLast a_last))
     ]];
  

  clf_typ_rec_elem:
    [
      [
        x = SYMBOL; ":"; a = clf_typ
         -> output_string out_channel "clf_typ_rec_elem : x SYMBOL : clf_typ "; output_char out_channel '\n';
        (Id.mk_name (Id.SomeString x), a)

      | 
        x = UPSYMBOL; ":"; a = lf_typ
         -> output_string out_channel "clf_typ_rec_elem : x UPSYMBOL : lf_typ "; output_char out_channel '\n'; (Id.mk_name (Id.SomeString x), a)

      ]
    ]
  ;


  clf_term_x:
    [  "atomic" 
        [
           a = clf_normal -> output_string out_channel "clf_term_x : atomic clf_normal "; output_char out_channel '\n';
              a
        |
          u = UPSYMBOL -> output_string out_channel "clf_term_x : atomic UPSYBOL "; output_char out_channel '\n';
            LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), LF.EmptySub _loc), LF.Nil) 
        |
           u = UPSYMBOL ; sigma' = clf_sub_new ->  output_string out_channel "clf_term_x : atomic UPSYBOL clf_sub_new "; output_char out_channel '\n';
              LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), sigma'), LF.Nil) 
        ]
    ]
  ;

  clf_term_app:
    [ LEFTA
        [
          h = clf_head; ms = LIST0 clf_normal ->  output_string out_channel "clf_term_app : LEFTA clf_head list0 clf_normal "; output_char out_channel '\n';
            let spine = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Root (_loc, h, spine)
        ]

    | RIGHTA
        [
          t = clf_term_x  -> output_string out_channel "clf_term_app : RIGHTA clf_term_x "; output_char out_channel '\n';
            t
        ]

    | "atomic" 
        [
          t = clf_term_x  -> output_string out_channel "clf_term_app : atomic clf_term_x "; output_char out_channel '\n';
            t
         

        ]
    ]
  ;

  clf_head:
    [
      [

        "#"; p = SYMBOL; "."; k = INTLIT; sigma = clf_sub_new -> output_string out_channel p; output_string out_channel " : clf_head : # SYMBOL . INTLIT clf_sub_new \n";
          LF.ProjPVar (_loc, int_of_string k, (Id.mk_name (Id.SomeString p), sigma))
      |
        "#"; p = SYMBOL;  sigma = clf_sub_new -> output_string out_channel p; output_string out_channel " : clf_head : # SYMBOL  clf_sub_new \n";
          LF.PVar (_loc, Id.mk_name (Id.SomeString p), sigma)

      |  "("; "#"; p = SYMBOL; "."; k = INTLIT; sigma = clf_sub_new ; ")" -> output_string out_channel p; output_string out_channel " : clf_head : (# SYMBOL . INTLIT clf_sub_new) \n";
          LF.ProjPVar (_loc, int_of_string k, (Id.mk_name (Id.SomeString p), sigma))
      |
         "("; "#"; p = SYMBOL;  sigma = clf_sub_new ; ")" -> output_string out_channel p; output_string out_channel " : clf_head : (# SYMBOL clf_sub_new) \n";
          LF.PVar (_loc, Id.mk_name (Id.SomeString p), sigma)
      |
        x = SYMBOL; "."; k = INTLIT -> output_string out_channel x; output_string out_channel " : clf_head : SYMBOL . INTLIT \n";
          LF.ProjName (_loc, int_of_string k, Id.mk_name (Id.SomeString x))
      |
        x = SYMBOL -> output_string out_channel x; output_string out_channel " : clf_head : SYMBOL \n";
         LF.Name (_loc, Id.mk_name (Id.SomeString x))

      | "#"; s = UPSYMBOL;  "["; sigma = clf_sub_new ; "]"-> output_string out_channel s; output_string out_channel " : clf_head : # UPSYMBOL [ clf_sub_new] \n";
          LF.SVar (_loc, Id.mk_name (Id.SomeString s), sigma)

      ]
    ]
  ;


 
  clf_sub_new:
    [
      [
       
          "^" -> output_string out_channel "clf_sub_new : ^ "; output_char out_channel '\n';
          LF.EmptySub (_loc )

      |    dots  -> output_string out_channel "clf_sub_new : dots "; output_char out_channel '\n';
          LF.Id (_loc) 

      | 
        sigma = SELF;   h = clf_head -> output_string out_channel "clf_sub_new : SELF clf_head "; output_char out_channel '\n';
          LF.Dot (_loc, sigma, LF.Head h)

      | 
        sigma = SELF;  tM = clf_normal -> output_string out_channel "clf_sub_new : SELF clf_normal "; output_char out_channel '\n';
          LF.Dot (_loc, sigma, LF.Normal tM)


      | 
        h = clf_head -> output_string out_channel "clf_sub_new : clf_head "; output_char out_channel '\n';
          LF.Dot (_loc, LF.EmptySub _loc, LF.Head h)


      | 
         tM = clf_normal -> output_string out_channel "clf_sub_new : clf_normal "; output_char out_channel '\n';
          LF.Dot (_loc, LF.EmptySub _loc, LF.Normal tM)



      ]
    ]

  ;

 

  clf_dctx:
    [
      [        
        -> output_string out_channel "clf_dctx \n";
          LF.Null

      |
        psi = SYMBOL -> output_string out_channel psi; output_string out_channel " : clf_dctx : symbol \n";
          LF.CtxVar (_loc, Id.mk_name (Id.SomeString psi))

      |  x = SYMBOL; ":"; tA = clf_typ -> output_string out_channel x; output_string out_channel " : clf_dctx : SYMBOL : clf_typ \n";
          LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA))

      |
        cPsi = clf_dctx; ","; x = SYMBOL; ":"; tA = clf_typ -> output_string out_channel x; output_string out_channel " : clf_dctx : clf_dctx , SYMBOL : clf_typ \n";
          LF.DDec (cPsi, LF.TypDecl (Id.mk_name (Id.SomeString x), tA))

      ]
    ]
  ;



  clf_hat_or_dctx:
    [
      [
         -> output_string out_channel "clf_hat_or_dctx : "; output_char out_channel '\n';
               Hat [ ]
        
      |    x = SYMBOL -> output_string out_channel "clf_hat_or_dctx : SYMBOL"; output_char out_channel '\n';
            Hat ([Id.mk_name (Id.SomeString x)])

      |   x = SYMBOL; ":"; tA = clf_typ -> output_string out_channel "clf_hat_or_dctx : SYMBOL : clf_typ"; output_char out_channel '\n';
          Dctx (LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
      |
        cPsi = clf_hat_or_dctx; ","; x = SYMBOL; ":"; tA = clf_typ ->
          begin match cPsi with 
            | Hat [ ] -> output_string out_channel "clf_hat_or_dctx : clf_hat_or_dctx , SYMBOL : clf_typ hat []"; output_char out_channel '\n';
                        Dctx (LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
            | Hat [g] -> output_string out_channel "clf_hat_or_dctx : clf_hat_or_dctx , SYMBOL : clf_typ hat [g]"; output_char out_channel '\n';
                        Dctx (LF.DDec (LF.CtxVar (_loc, g), LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
            | Dctx cPsi' -> output_string out_channel "clf_hat_or_dctx : clf_hat_or_dctx , SYMBOL : clf_typ Dctx"; output_char out_channel '\n';
                        Dctx (LF.DDec (cPsi', LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
          end

      | phat = clf_hat_or_dctx; "," ; y = SYMBOL  ->
          begin match phat with 
            | Hat phat -> output_string out_channel "clf_hat_or_dctx : clf_hat_or_dctx , SYMBOL hat "; output_char out_channel '\n'; Hat (phat @ [Id.mk_name (Id.SomeString y)])
          end
       
      ]
    ]
  ;





(* ************************************************************************************** *)

  cmp_typ:
     [[
         m = mixtyp  ->  output_string out_channel "cmp_typ : mixtyp"; output_char out_channel '\n'; try  toComp m
                         with MixErr l ->  (print_string ("Syntax error: Computation-level type used where LF type is expected (" ^ 
                                            Loc.to_string l ^ ")\n");
                            raise (MixErr l))
     ]];

  cmp_pair_atom : 
    [
      [
        ","; e2 = cmp_exp_chk ; ")" -> output_string out_channel "cmp_pair_atom : , cmp_exp_chk )"; output_char out_channel '\n'; Pair e2

      | ")"                 -> output_string out_channel "cmp_pair_atom : )"; output_char out_channel '\n'; Atom

      ]
    ]
  ;


 cmp_rec:
   [[
     f = SYMBOL; ":"; tau = cmp_typ; "="; e = cmp_exp_chk -> output_string out_channel "cmp_rec "; output_char out_channel '\n';
                Comp.RecFun (Id.mk_name (Id.SomeString f), tau, e)
    ]]
;

cmp_exp_chk:
 [ LEFTA [
    e = cmp_exp_chkX   ->  output_string out_channel "cmp_exp_chk : cmp_exp_chkX"; output_char out_channel '\n'; e
  | i = cmp_exp_syn    ->  output_string out_channel "cmp_exp_chk : cmp_exp_csyn"; output_char out_channel '\n'; Comp.Syn (_loc, i)
 ]];

case_pragma:
 [[
    "%not" -> output_string out_channel "case_pragma : %not"; output_char out_channel '\n'; Syntax.PragmaNotCase
  | -> output_string out_channel "case_pragma : "; output_char out_channel '\n'; Syntax.RegularCase
 ]];

(* cmp_exp_chkX:  checkable expressions, except for synthesizing expressions *)
cmp_exp_chkX:
    [ LEFTA
      [  "fn"; f = SYMBOL; rArr; e = cmp_exp_chk -> output_string out_channel "case_exp_chkX : LEFTA fn SYMBOL rArr cmp_exp_chk"; output_char out_channel '\n';
           Comp.Fun (_loc, Id.mk_name (Id.SomeString f), e)

      | gLambda; f = SYMBOL; rArr; e = cmp_exp_chk -> output_string out_channel "case_exp_chkX : LEFTA gLambda SYMBOL rArr cmp_exp_chk"; output_char out_channel '\n';
          Comp.CtxFun (_loc, Id.mk_name (Id.SomeString f), e)

      | "mlam"; f = UPSYMBOL; rArr; e = cmp_exp_chk -> output_string out_channel "case_exp_chkX : LEFTA mlam UPSYMBOL rArr cmp_exp_chk"; output_char out_channel '\n';
          Comp.MLam (_loc, Id.mk_name (Id.SomeString f), e)

      | "mlam"; "#"; s = UPSYMBOL; rArr; e = cmp_exp_chk -> output_string out_channel "case_exp_chkX : LEFTA mlam # UPSYMBOL rArr cmp_exp_chk"; output_char out_channel '\n';
          Comp.MLam (_loc, Id.mk_name (Id.SomeString s), e)

      | "mlam"; hash = "#"; p = SYMBOL; rArr; e = cmp_exp_chk -> output_string out_channel "case_exp_chkX : LEFTA mlam # SYMBOL rArr cmp_exp_chk"; output_char out_channel '\n';
          Comp.MLam (_loc, Id.mk_name (Id.SomeString p), e)

      | "case"; i = cmp_exp_syn; "of"; prag = case_pragma; OPT [ "|"]; bs = LIST1 cmp_branch SEP "|" ->
                output_string out_channel "case_exp_chkX : LEFTA case cmp_exp_syn of case_pragma OPT | list1 cmp_branch SEP |"; output_char out_channel '\n';
          Comp.Case (_loc, prag, i, bs)

      | "impossible"; i = cmp_exp_syn; "in"; 
         ctyp_decls = LIST0 clf_ctyp_decl; "["; pHat = clf_dctx ;"]"  -> 
           output_string out_channel "case_exp_chkX : LEFTA impossible in cmp_exp_syn"; output_char out_channel '\n';
           let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
             Comp.Case (_loc, Syntax.RegularCase, i, [Comp.BranchBox (_loc, ctyp_decls', (pHat, Comp.EmptyPattern, None))])

      | "if"; i = cmp_exp_syn; "then"; e1 = cmp_exp_chk ; "else"; e2 = cmp_exp_chk -> 
          output_string out_channel "case_exp_chkX : LEFTA in cmp_exp_syn then cmp_exp_chk"; output_char out_channel '\n';
          Comp.If (_loc, i, e1, e2)

      | "let"; "("; x = SYMBOL; ","; y = SYMBOL; ")"; "="; i = cmp_exp_syn;  "in"; e = cmp_exp_chk ->
          output_string out_channel "case_exp_chkX : LEFTA let ( SYMBOL , SYMBOL ) cmp_exp_syn in cmp_exp_chk"; output_char out_channel '\n';
          Comp.LetPair (_loc, i, (Id.mk_name (Id.SomeString x), Id.mk_name (Id.SomeString y), e))

      | "let"; ctyp_decls = LIST0 clf_ctyp_decl;

       "["; pHat = clf_dctx ;"]"; tM = clf_term_app;
       tau = OPT [ ":"; tA = clf_typ LEVEL "atomic"; "["; cPsi = clf_dctx; "]" -> (tA, cPsi) ];
       "="; i = cmp_exp_syn; "in"; e' = cmp_exp_chk
       -> output_string out_channel "case_exp_chkX : LEFTA let ..... "; output_char out_channel '\n';
         let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in

          Comp.Case (_loc, Syntax.RegularCase, i, [Comp.BranchBox (_loc,  ctyp_decls', (pHat, Comp.NormalPattern (tM, e'), tau))]) 


      | "(" ; e1 = cmp_exp_chk; p_or_a = cmp_pair_atom -> output_string out_channel "case_exp_chkX : LEFTA ( cmp_exp_chk cmp_pair_atom"; output_char out_channel '\n';
          begin match p_or_a with 
            | Pair e2 ->   Comp.Pair (_loc, e1, e2)
            | Atom    ->   e1
          end 
      ]

    | "atomic"
      [
              
        "["; phat_or_psi = clf_hat_or_dctx ; "]" ; tM = clf_term_app ->             
          begin match phat_or_psi with
            | Dctx cPsi ->  output_string out_channel "case_exp_chkX : atomic [ clf_hat_or_dctx ] Dctx"; output_char out_channel '\n';
                Comp.Syn(_loc, Comp.BoxVal (_loc, cPsi, tM)) 
            | Hat phat  ->  output_string out_channel "case_exp_chkX : atomic [ clf_hat_or_dctx ] Hat"; output_char out_channel '\n'; 
                     Comp.Box (_loc, phat, tM) 
      end

      | 
          "["; phat_or_psi = clf_hat_or_dctx ; "]" ; sigma = clf_sub_new -> output_string out_channel "case_exp_chkX : atomic  [ clf_hat_or_dctx ] clf_sub_new"; output_char out_channel '\n';             
          begin match phat_or_psi with
            | Hat phat  ->                 Comp.SBox (_loc, phat, sigma) 
          end

      | 
        "(" ; e1 = cmp_exp_chk; p_or_a = cmp_pair_atom -> 
          begin match p_or_a with 
            | Pair e2 -> output_string out_channel "case_exp_chkX : atomic  ( clf_exp_chk ) clf_pair_atom Pair"; output_char out_channel '\n';  
                        Comp.Pair (_loc, e1, e2)
            | Atom    -> output_string out_channel "case_exp_chkX : atomic  ( clf_exp_chk ) clf_pair_atom Atom"; output_char out_channel '\n'; e1
          end 

      ]
 ];

isuffix:
 [ LEFTA [
     "["; cPsi = clf_dctx; "]"   -> output_string out_channel "isuffix : LEFTA [ clf_dctx ]"; output_char out_channel '\n'; 
                 (fun i -> Comp.CtxApp(_loc, i, cPsi))


 | "<"; phat_or_psi = clf_hat_or_dctx ; "."; tM = clf_term_app; ">"   ->  
     begin match phat_or_psi with
       | Dctx cPsi -> output_string out_channel "isuffix : LEFTA < clf_hat_dctx . clf_term_app > Dctx"; output_char out_channel '\n';
                 (fun i -> Comp.MAnnApp (_loc, i, (cPsi, tM)))
       | Hat phat  -> output_string out_channel "isuffix : LEFTA < clf_hat_dctx . clf_term_app > Hat"; output_char out_channel '\n';
                 (fun i -> Comp.MApp (_loc, i, (phat, tM)))
     end



   | "=="; i2 = cmp_exp_syn   -> output_string out_channel "isuffix : LEFTA == cmp_exp_syn"; output_char out_channel '\n';
                (fun i -> Comp.Equal(_loc, i, i2))
   | x = SYMBOL   ->  output_string out_channel "isuffix : LEFTA SYMBOL"; output_char out_channel '\n';
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Var (_loc, Id.mk_name (Id.SomeString x)))))
   | "ttrue"      ->  output_string out_channel "isuffix : LEFTA ttrue"; output_char out_channel '\n'; 
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Boolean (_loc, true))))
   | "ffalse"     -> output_string out_channel "isuffix : LEFTA ffalse"; output_char out_channel '\n';  
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Boolean (_loc, false))))
   | e = cmp_exp_chkX   ->  output_string out_channel "isuffix : LEFTA cmp_exp_chkX"; output_char out_channel '\n'; 
       (fun i -> Comp.Apply(_loc, i, e))
 ]];

cmp_exp_syn:
 [ LEFTA [
    "["; cPsi = clf_dctx; "]"; tR = clf_term_app   -> output_string out_channel "cmp_exp_syn : LEFTA [ clf_hat_dctx ] clf_term_app \n";  
      ((*print_string ("BOXVAL: " ^ Comp.synToString(Comp.BoxVal (_loc, cPsi, tR)) ^ "\n"); *)  
        Comp.BoxVal (_loc, cPsi, tR))
   | h = SELF; s = isuffix  -> output_string out_channel "cmp_exp_syn : LEFTA SELF isuffixe \n";  s(h)
   | h = SELF; "("; e = cmp_exp_chk; p_or_a = cmp_pair_atom   ->
       Comp.Apply (_loc, h, begin match p_or_a with 
                                    | Pair e2 -> output_string out_channel "cmp_exp_syn : LEFTA SELF ( cmp_exp_chk cmp_pair_atom Pair \n"; 
                                          Comp.Pair (_loc, e, e2)
                                    | Atom    -> output_string out_channel "cmp_exp_syn : LEFTA SELF ( cmp_exp_chk cmp_pair_atom Atom \n";  
                                                  e
                            end)
   | x = SYMBOL -> output_string out_channel x; output_string out_channel " : cmp_exp_syn : LEFTA SYMBOL \n";
                Comp.Var (_loc, Id.mk_name (Id.SomeString x))
   | "ttrue"    ->  output_string out_channel "cmp_exp_syn : LEFTA ttrue \n";
                 Comp.Boolean (_loc, true)
   | "ffalse"   -> output_string out_channel "cmp_exp_syn : LEFTA ffalse \n";
                Comp.Boolean (_loc, false)
   | "("; i = SELF; ")"   -> output_string out_channel "cmp_exp_syn : LEFTA (SELF) \n";  i
 ]];

  cmp_branch_pattern:
    [
      [
        tM = clf_term_app -> output_string out_channel "cmp_branch_pattern : clf_term_app"; output_char out_channel '\n'; Some tM
     |
        "{"; "}" -> output_string out_channel "cmp_branch_pattern : { }"; output_char out_channel '\n'; None
      ]
    ]
  ;

  cmp_branch:
    [
      [
        ctyp_decls = LIST0 clf_ctyp_decl; 
        "["; pHat = clf_dctx ;"]"; pattern = cmp_branch_pattern;
         tau = OPT [ ":"; tA = clf_typ LEVEL "atomic"; "["; cPsi = clf_dctx; "]" -> (tA, cPsi)]; 
         rest = OPT [rArr; e = cmp_exp_chk -> e] ->
          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
           (match (pattern, rest) with

              | (Some tM, Some e)  -> output_string out_channel "cmp_branch : ctyp_decls...atmomic... Some Some"; output_char out_channel '\n';
                        Comp.BranchBox (_loc, ctyp_decls', (pHat, Comp.NormalPattern (tM, e), tau))

              | (None, None) -> output_string out_channel "cmp_branch : ctyp_decls...atomic... None Nome"; output_char out_channel '\n'; 
                        Comp.BranchBox (_loc, ctyp_decls', (pHat, Comp.EmptyPattern, tau))

              | (Some _tM, None) -> output_string out_channel "cmp_branch : ctyp_decls...atmomic... Some None"; output_char out_channel '\n';
                        (print_string ("Syntax error: missing body of case branch\n"); raise (MixErr _loc))

              | (None, Some _e) -> output_string out_channel "cmp_branch : ctyp_decls...atmomic... None Some"; output_char out_channel '\n';
                        (print_string ("Syntax error: can't have a body with an empty pattern \"{}\"\n"); raise (MixErr _loc)))
      |
          ctyp_decls = LIST0 clf_ctyp_decl; 
        "["; cPsi = clf_dctx ;"]"; sigma = clf_sub_new;  
         cPhi = OPT [ ":"; cPhi = clf_dctx -> cPhi ] ; 
         rArr; e = cmp_exp_chk -> output_string out_channel "cmp_branch : ctyp_decls... "; output_char out_channel '\n'; 
           let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
            Comp.BranchSBox (_loc, ctyp_decls', (cPsi, sigma, cPhi), e)
      ]
    ]
  ;

  mixtyp:
    [ RIGHTA
      [
        "{"; psi = SYMBOL; ":"; "("; w = SYMBOL; ")"; "*"; "}"; mixtau = SELF ->
          output_string out_channel "mixtyp : RIGHA { SYMBOL : ( SYMBOL ) * } SELF"; output_char out_channel '\n';
          MTCtxPi (_loc, (Id.mk_name (Id.SomeString psi), 
                          Id.mk_name (Id.SomeString w), Comp.Explicit), mixtau)


      | "{"; psi = SYMBOL; ":";  w = SYMBOL; "}"; mixtau = SELF ->
          output_string out_channel "mixtyp : RIGHA { SYMBOL : SYMBOL } SELF"; output_char out_channel '\n';
          MTCtxPi (_loc, (Id.mk_name (Id.SomeString psi), 
                          Id.mk_name (Id.SomeString w), Comp.Implicit), mixtau)

      |
        ctyp_decl = clf_ctyp_decl; mixtau = SELF ->
          output_string out_channel "mixtyp : RIGHA ctyp_decl SELF"; output_char out_channel '\n';
          MTPiBox (_loc, ctyp_decl, mixtau)
      |
        mixtau1 = SELF; rarr; mixtau2 = SELF ->
          output_string out_channel "mixtyp : RIGHA SELF rarr SELF"; output_char out_channel '\n';
          MTArr (_loc, mixtau1, mixtau2) 

      ] 
     | 
        LEFTA 
      [

        tau1 = SELF; "*"; tau2 = SELF -> output_string out_channel "mixtyp : LEFTA SELF * SELF"; output_char out_channel '\n';
          MTCross (_loc, tau1, tau2)

      ]

     | 
      "atomic"
      [

         tA = "Bool" -> output_string out_channel "mixtyp : atomic Bool"; output_char out_channel '\n'; 
                MTBool _loc


      |
        "("; mixtau = mixtyp ; ")" -> output_string out_channel "mixtyp : atomic (mixtyp)"; output_char out_channel '\n';
           mixtau 


      |   "(" ; a = SYMBOL;  "["; cPsi = clf_dctx; "]" ; rarr; mixtau2 = mixtyp ; ")" -> 
              output_string out_channel "mixtyp : atomic ( SYMBOL [ clf_dctx ] rarr mixtyp )"; output_char out_channel '\n';
              MTArr(_loc, MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), LF.Nil), cPsi ), 
                    mixtau2)

      |   a = SYMBOL;  "["; cPsi = clf_dctx; "]" -> output_string out_channel "mixtyp : atomic SYMBOL [ clf_dctx ]"; output_char out_channel '\n';
              MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), LF.Nil), cPsi )

      | 
          "("; a = SYMBOL;  ms = LIST0 clf_normal; ")"; "["; cPsi = clf_dctx; "]" -> 
            output_string out_channel a ; output_string out_channel " : mixtyp : atomic ( SYMBOL list0 clf_normal ) \n";
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), sp), cPsi )

      
      | "("; ".";  ")"; "["; cPsi = clf_dctx; "]" -> 
          output_string out_channel "mixtyp : atomic (. ) [ clf_dtcx ]"; output_char out_channel '\n';
          let cPhi0 = LF.Null in 
            MTSub (_loc, cPhi0, cPsi)


      | "("; x = SYMBOL; ":"; tA = clf_typ;  ")"; "["; cPsi = clf_dctx; "]" -> 
          output_string out_channel "mixtyp : atomic ( SYMBOL : clf_typ ) [ clf_dctx ]"; output_char out_channel '\n';
          let cPhi0 = LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA)) in 
            MTSub (_loc, cPhi0, cPsi)


      | "("; x = SYMBOL; ":"; tA = clf_typ; ","; decls = LIST1 clf_decl SEP ","; 
          ")"; "["; cPsi = clf_dctx; "]" -> 
          output_string out_channel "mixtyp : atomic ( SYMBOL : clf_typ , list1 clf_decl SEP,) [ clf_dctx ]"; output_char out_channel '\n';
          let cPhi0 = LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA)) in  
          let cPhi = List.fold_left (fun d ds -> LF.DDec(d, ds)) cPhi0 decls in 
            MTSub (_loc, cPhi, cPsi)


      | "("; psi = SYMBOL; ","; decls = LIST1 clf_decl SEP ","; 
          ")"; "["; cPsi = clf_dctx; "]" -> 
          output_string out_channel "mixtyp : atomic ( SYMBOL , list1 clf_decl SEP , ) clf_dctx"; output_char out_channel '\n';
          let cPhi0 = LF.CtxVar (_loc, Id.mk_name (Id.SomeString psi)) in
          let cPhi = List.fold_left (fun d ds -> LF.DDec(d, ds)) cPhi0 decls in 
            MTSub (_loc, cPhi, cPsi)

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
