(* sasy parser before the alt_or_prod *)
#load "pa_extend.cmo";;

open Common
open Syntax
open Token
let out_channel = open_out "ast.out";
module Grammar = Camlp4.Struct.Grammar.Static.Make (Lexer)
(*
type kind_or_typ =
  | Kind of Ext.LF.kind
  | Typp  of Ext.LF.typ
*)

(*******************************)
(* Global Grammar Entry Points *)
(*******************************)

let section_eoi = Grammar.Entry.mk "section_eoi"

(*****************************************)
(* Dynamically Extensible SASyLF Grammar *)
(*****************************************)

EXTEND Grammar
GLOBAL: section_eoi;

 section_eoi:
    [
      [
         decls = LIST0 section_decl; `EOI ->  output_string out_channel "section_eoi \n"; decls
      ]
    ]
  ; 

 section_decl:
    [
      [
         "terminals"; lt = LIST1 terminal -> output_string out_channel "section_decl 1 terminals \n"; Terminals_decl(_loc, lt)

      | 
         "terminals"; lt = LIST1 terminal; "\n" -> output_string out_channel "section_decl terminals \n"; Terminals_decl(_loc, lt)

      | 
	 "syntax"; p = prod -> output_string out_channel "syntax \n"; Grammar(_loc, p)

      |
 	 "judgment"; a = SYMBOL; ":"; b = j_syntax; ";"; lj = LIST1 rules -> output_string out_channel "section_decl judgement \n";
                                                                         Judgement(_loc, JName(a), b, None, lj)

      |
         "judgment"; a = SYMBOL; ":"; b = cj_syntax; ";"; "assumes"; c = SYMBOL; lj = LIST1 rules -> output_string out_channel "section_decl judgement assumes \n"; 
                                                                                                 Judgement(_loc, JName(a), b, Some(Assptn(CName(c))), lj)

      
      
      | 
         "theorem"; a = SYMBOL; ":"; b = stmnt;  lp = LIST1 proof; "end"; "theorem" -> output_string out_channel "section_decl theorem \n";
                                                                                        Theorems(_loc, TName(a), b, lp)      


      ]
    ]
  ;

  terminal:
    [
      [
         t = SYMBOL -> output_string out_channel t; output_string out_channel " : terminal \n"; Terminal(_loc, t)
      ]
    ]
  ;


 prod:
    [
      [
         a = typ; DECLA; la = LIST1 alternative SEP "|" -> output_string out_channel "prod typ \n"; Production(_loc, a, la)

      ]
    ]
  ;

typ:
    [
      [
         t = SYMBOL -> output_string out_channel t; output_string out_channel " : typ \n"; Typ(_loc, t)

      ]
    ]
  ; 

 alternative:
    [
      [ 

         t = SYMBOL; a = OPT [ alternative ] ->  output_string out_channel t;

                                         output_string out_channel " alternative symbol aternative \n" ; AltAtomic(_loc, t, a)
     
      |
         "."; t1 = SELF -> output_string out_channel "alternative bin \n"; 
                                                                            AltBin(_loc, t1) 

      |
         a = SYMBOL; "\\"; v1 = OPT [ alternative ] -> output_string out_channel "alternative lam \n";  AltLam(_loc, AName(a), v1)	 
     
      |
         t1 = SYMBOL; "->"; t2 = SYMBOL; b = OPT [ alternative ] -> output_string out_channel "alternative fn -> \n"; AltFn(_loc, Typ(_loc, t1), Ty(Typ(_loc, t2)), b) 

      |
         t1 = SYMBOL; "["; la = LIST1 SELF SEP ","; "]"; b = OPT [ alternative ] -> output_string out_channel "alternative fn [] \n";  AltFn(_loc, Typ(_loc, t1), La(la), b) 
       
      |
         "let"; a = SELF; "="; b = SELF; "in"; c = SELF -> output_string out_channel "alternative fn [] \n";  AltLet(_loc, a, b, c) 
      
      |
         a = SELF; ":"; b = SELF -> output_string out_channel "alternative oft \n";
                                                  AltOft(_loc, a, b)
  (*  
      | (** something's wrong here *)
         ","; la = LIST0 SELF SEP "," -> output_string out_channel "alternative ctx \n";
                                                     AltCtx(_loc, Typ(_loc, "Gamma"), la) *)
         
      |
         "("; LIST0 SELF SEP "," -> output_string out_channel "alternative parent \n"; AltPar 

      |
         ")"; LIST0 SELF SEP "," -> output_string out_channel "alternative parent \n"; AltPar 

      ]
    ]
  ;


 j_syntax:
    [
      [
         la = LIST1 judge -> output_string out_channel "j_syntax mult \n"; JSyntax(_loc, None, la)

      ]
    ]
  ;

 cj_syntax:
    [
      [
         c = SYMBOL; la = LIST1 alternative SEP ","; "|-"; lb = LIST1 judge -> output_string out_channel "cj_styntax mult \n";
                                                                                        JSyntax(_loc, Some(Context(CName(c),la)), lb)

      ]
    ]
  ;

 judge:
    [
      [
         a = SYMBOL -> output_string out_channel a; output_string out_channel " : judge \n"; Judge( _loc, a)

      |
         b = UPSYMBOL -> output_string out_channel b; output_string out_channel " : judge \n"; Judge( _loc, b)

      |
        "=" -> output_string out_channel " : judge = \n"; Judge( _loc, "=")
      ]
    ]
  ; 

 rules:
    [
      [
          LINES; a = SYMBOL; p = premise -> output_string out_channel "rule only conclusion \n"; Rule(_loc, [], RName(a), p)

      |
         lp = LIST1 premise; LINES; a = SYMBOL; p = premise -> output_string out_channel "rule \n"; Rule(_loc, lp, RName(a), p)
         
      ]
    ]
  ;
(* no check if the premise is a judgement premise *)
(* might wan to make a specific type for AltOft *)
 premise:
    [
      [
         a = SYMBOL; ":"; b = var_alternative; ";"-> output_string out_channel "premise symbol var_alternative symbol \n"; 
                                                            Premisse(_loc, Some(PName(a)), None, b)

      |
         a = SYMBOL; ":"; "gamma,"; la = LIST0 var_alternative SEP ","; "|-"; b = var_alternative; ";" -> output_string out_channel "premise symbol : gamma var_alternative symbol \n"; 
                                                                                                                 Premisse(_loc, Some(PName(a)), Some(PContext(la)), b)

      |
         a = var_alternative; ";" -> output_string out_channel "premise var_alternative symbol \n"; 
                                            Premisse(_loc, None, None, a)

      |
         "gamma,"; la = LIST0 var_alternative SEP ","; "|-"; b =  var_alternative; ";" -> output_string out_channel "premise gamma list var_alternative ... \n"; 
                                                                                                Premisse(_loc, None, Some(PContext(la)), b)

      ]
    ]
  ;

  var_alternative:
    [
      [ 
	 v = SYMBOL; a = OPT [ var_alternative ] -> output_string out_channel v; output_string out_channel " : var_alternative 1 \n"; VAltAtomic(_loc, v, a) 
 
      |
         v = UPSYMBOL; a = OPT [ var_alternative ] -> output_string out_channel v; output_string out_channel " : var_alternative 1 \n"; VAltAtomic(_loc, v, a) 

      |
         "="; a = OPT [ var_alternative ] -> output_string out_channel " : var_alternative 1 = \n"; VAltAtomic(_loc, "=", a) 
     
      |
         "("; a = SELF; ")"; b = OPT [ var_alternative ] -> output_string out_channel "var_alternative : (self) "; output_char out_channel '\n'; VAltPar(_loc, a, b)    

      |
         t1 = SYMBOL; "->"; t2 = SYMBOL; b = OPT [ var_alternative ] -> output_string out_channel "var_alternative 3 \n"; VAltFn(_loc, VName(t1), VTy(Typ(_loc, t2)), b)

      |
         t1 = UPSYMBOL; "["; la = LIST1 SELF SEP ","; "]"; b = OPT [ var_alternative ] -> output_string out_channel t1; output_string out_channel " : var_alternative fn [] \n";  
                                                                                        VAltFn(_loc, VName(t1), VLa(la), b)
 
      |
         a = SYMBOL; "\\"; v1 = var_alternative -> output_string out_channel a; output_string out_channel " : var_alternative 4 \n"; VAltLam(_loc, AName(a), v1)

      |
         "."; n = var_alternative -> output_string out_channel "var_alternative 5 \n"; VAltBin(_loc, n)

      | (* confusion with the = sign, check in reconstruct that the last alt is = *)
         "let"; a = var_alternative; (*"="; b = SELF;*) "in"; c = SELF -> output_string out_channel "alternative fn [] \n";  VAltLet(_loc, a, c) 

      |
         a = var_alternative; ":"; b = SYMBOL -> output_string out_channel "var_alternative 6 \n"; 
                                                 VAltOft(_loc, a, VName(b))
    
      |
         "Gamma,"; la = LIST1 var_alternative SEP "," -> output_string out_channel "var_alternative 7 \n";
                                                         VAltCtx(_loc, CName("Gamma"), la)         
      ]
    ]
  ; 

 t_premise:
    [
      [
         a = SYMBOL; ":"; b = var_alternative -> output_string out_channel "premise symbol var_alternative symbol \n"; 
                                                            TPremisse(_loc, Some(PName(a)), None, b)

      |
         a = SYMBOL; ":"; "gamma,"; la = LIST0 var_alternative SEP ","; "|-"; b = var_alternative-> output_string out_channel "premise symbol : gamma var_alternative symbol \n"; 
                                                                                                                 TPremisse(_loc, Some(PName(a)), Some(PContext(la)), b)

      |
         a = var_alternative -> output_string out_channel "premise var_alternative symbol \n"; 
                                            TPremisse(_loc, None, None, a)

      |
         "gamma,"; la = LIST0 var_alternative SEP ","; "|-"; b =  var_alternative -> output_string out_channel "premise gamma list var_alternative ... \n"; 
                                                                                                TPremisse(_loc, None, Some(PContext(la)), b)

      ]
    ]
  ;
 
 stmnt:
    [
      [
         "exists"; p1 = t_premise -> output_string out_channel "stmt \n"; Exist(_loc, p1)

      |
         "forall";  lp1 = LIST1 t_premise SEP ";"; "exists"; p2 = t_premise -> output_string out_channel "stmt \n"; ForAllExist(_loc, lp1, p2)

      ]
    ]
  ; 

 proof:
    [
      [
        np = t_premise; "by"; "induction"; "on"; a = var_name; ":"; lb = LIST1 args; "end"; "induction" -> output_string out_channel "proof proof \n"; Proof(_loc, np, a, lb)

      |
        np = t_premise; "by";j = SELF; "on"; lb = LIST1 var_name SEP "," -> output_string out_channel "proof by rule \n"; PRule(_loc, np, j, lb)

      |
        np = t_premise; "by"; "case"; "analysis"; "on"; lb = LIST1 var_name; la = LIST1 args; "end"; "case"; "analysis" -> output_string out_channel "proof casean \n"; CaseAn(_loc, np, lb, la)

      |
        np = t_premise; "by";"rule"; rn = SYMBOL; b = OPT [ "on"; b = LIST1 var_name SEP "," -> b ] -> output_string out_channel "proof rule \n"; URule(_loc, np, RName(rn), b)

      |
         "induction"; "hypothesis" -> output_string out_channel "proof induction hypothesis \n"; InductionHyp(_loc)

      | 
         "theorem"; tn = SYMBOL -> output_string out_channel "proof theorem \n"; PTheorem(_loc, TName(tn))

      |
         "lemma"; tn = SYMBOL -> output_string out_channel "proof theorem \n"; PTheorem(_loc, TName(tn))

      ]
    ]
  ;

var_name:
    [
      [
         vn = SYMBOL -> output_string out_channel vn; output_string out_channel " : var_name \n"; VName(vn)
      ]
    ]
  ;  

 args:
    [
      [
         "case"; "rule"; r1 = rules; "is"; lp = LIST1 proof; "end"; "case" -> output_string out_channel "args \n"; Argument(_loc, r1, lp)

      |
         "case"; n1 = var_alternative; "is"; lp = LIST1 proof; "end"; "case" -> output_string out_channel "args \n"; Arg(_loc, n1, lp)

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
  let result     = parse_stream ~name:name ~input:stream entry in
     close_in in_channel
   ; result
