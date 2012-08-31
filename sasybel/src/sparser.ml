(* sasy parser trying to fix turnstyle problems *)
#load "pa_extend.cmo";;

open Core
open Syntax
open Stoken
open Ast
module Grammar = Camlp4.Struct.Grammar.Static.Make (Slexer)

exception Error of string

let rec append va va1 =
  match va with
    | VAltAtomic(l, s, vao) -> (begin match vao with
                                  | None -> VAltAtomic(l, s, Some(va1))
                                  | Some(va2) -> VAltAtomic(l, s, Some( append va2 va1))
                                end)
    | _ -> raise (Error ("not implemented"))

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
         decls = LIST0 section_decl; `EOI -> decls
      ]
    ]
  ;

 section_decl:
    [
      [
         "terminals"; lt = LIST1 terminal -> Terminals_decl(_loc, lt)

      |
         "terminals"; lt = LIST1 terminal; "\n" -> Terminals_decl(_loc, lt)

      |
	 "syntax"; lp = LIST1 prod -> Grammar(_loc, lp)

      |
 	 "notation"; a = SYMBOL; ":"; b = j_syntax; ";"; lj = LIST1 rules ->
                                                                         Judgement(_loc, JName(a), b, None, lj)

      |
         "theorem"; a = SYMBOL; ":"; b = stmnt;  lp = LIST1 proof; "end"; "theorem" ->
                                                                                        Theorems(_loc, TName(a), b, lp)

      |
         "context"; a = SYMBOL; `DECLA; lva = LIST1 var_alternative SEP "|"; ";" -> ContextDecl(_loc, CName(a), lva);

      ]
    ]
  ;

 terminal:
    [
      [
         t = SYMBOL -> Terminal(_loc, t)
      ]
    ]
  ;


 prod:
    [
      [
         a = typ; `DECLA; la = LIST1 alternative SEP "|"; ";" ->  Production(_loc, a, la)

      ]
    ]
  ;

typ:
    [
      [
         t = SYMBOL -> Typ(_loc, t)

      ]
    ]
  ;

 alternative:
    [
      [

         t = SYMBOL; a = OPT [ alternative ] ->   AltAtomic(_loc, t, a)

      |
         "."; t1 = SELF ->       AltBin(_loc, t1)

      |
         a = SYMBOL; "\\"; v1 = OPT [ alternative ] ->  AltLam(_loc, AName(a), v1)

      |
         t1 = SYMBOL; "->"; t2 = SYMBOL; b = OPT [ alternative ] -> AltFn(_loc, Typ(_loc, t1), Ty(Typ(_loc, t2)), b)

      |
         t1 = SYMBOL; "["; la = LIST1 SELF SEP ","; "]"; b = OPT [ alternative ] ->   AltFn(_loc, Typ(_loc, t1), La(la), b)

      |
         "let"; a = SELF; "="; b = SELF; "in"; c = SELF ->  AltLet(_loc, a, b, c)

     (* |
         a = SELF; ":"; b = SELF ->  AltOft(_loc, a, b)*) (** should be ommited and left as a judgement to be declared *)

   (*   | (** something's wrong here *)
         t1 = SYMBOL; "|-"; la = LIST0 SELF SEP "," ->   AltCtx(_loc, Typ(_loc, t1), la) *)

      |
         "("; LIST0 SELF SEP "," ->  AltPar

      |
         ")"; LIST0 SELF SEP "," ->  AltPar

      ]
    ]
  ;


 j_syntax:
    [
      [
         la = LIST1 judge -> JSyntax(_loc, None, la)

      ]
    ]
  ;

(* cj_syntax:
    [
      [
         c = SYMBOL; la = LIST1 alternative SEP ","; turnstyle; lb = LIST1 judge -> JSyntax(_loc, Some(Context(CName(c),la)), lb)

      ]
    ]
  ;
*)

 judge:
    [
      [
         a = SYMBOL -> Judge( _loc, a)

      |
         b = UPSYMBOL -> Judge( _loc, b)

      |
        "=" -> Judge( _loc, "=")

      ]
    ]
  ;

 rules:
    [
      [
          `LINES; a = SYMBOL; p = premise -> Rule(_loc, [], RName(a), p)

      |
         lp = LIST1 premise; `LINES; a = SYMBOL; p = premise -> Rule(_loc, lp, RName(a), p)

      ]
    ]
  ;
(* no check if the premise is a judgement premise *)
(* might wan to make a specific type for AltOft *)
 premise:
    [
      [

         a = UPSYMBOL; ":"; la = OPT ["|";  la= LIST1 con_dcl SEP ","; turnstyle -> la]; b = var_alternative; ";" ->
                                                                    Premisse(_loc, Some(PName(a)), la, b)
      |
         a = SYMBOL; ":"; la = OPT ["|";  la= LIST1 con_dcl SEP ","; turnstyle -> la]; b = var_alternative; ";" ->
                                                                    Premisse(_loc, Some(PName(a)), la, b)
      |
         la = OPT ["|";  la= LIST1 con_dcl SEP ","; turnstyle -> la ]; b = var_alternative; ";"  ->
                                                                       Premisse(_loc, None, la, b)

      |
          a = SYMBOL; ":"; b = var_alternative; ";"  ->
                                                            Premisse(_loc, Some(PName(a)), None, b)

      |
         a = UPSYMBOL; ":"; b = var_alternative; ";"  ->
                                                            Premisse(_loc, Some(PName(a)), None, b)

      |
         a = var_alternative; ";"  ->   Premisse(_loc, None, None, a)

      ]
    ]
  ;

  proj:
  [[
       a = SYMBOL; "."; b = INTLIT ->  Proj(_loc, a, int_of_string b)

  ]];

  dots:
  [[
       "."; "." ; lp = LIST0 proj ->  lp

      | "…" ; lp = LIST0 proj ->  lp

  ]];


  var_alternative:
    [
      [
	 v = SYMBOL; a = OPT [ var_alternative ] ->  VAltAtomic(_loc, v, a)

      |
         v = UPSYMBOL; a = OPT [ var_alternative ] -> VAltAtomic(_loc, v, a)

      |
         v = SYMBOL; d = dots; a = OPT [ var_alternative ] -> VAltId(_loc, v, d, a)

      |
         v = UPSYMBOL; d = dots; a = OPT [ var_alternative ] -> VAltId(_loc, v, d, a)

      |
         "="; a = OPT [ var_alternative ] -> VAltAtomic(_loc, "=", a)

      |
         "("; a = SYMBOL; ":"; b = var_alternative; OPT [","]; la = LIST0 typ_dcl SEP ","; ")"; c = OPT [ var_alternative ] ->
                                                 VAltOftBlock(_loc, (a,b)::la, c)
      |
         "("; a = UPSYMBOL; ":"; b = var_alternative; OPT [","]; la = LIST0 typ_dcl SEP ","; ")"; c = OPT [ var_alternative ] ->
                                                 VAltOftBlock(_loc, (a,b)::la, c)
      |
         "("; a = SELF; ")"; b = OPT [ var_alternative ] -> VAltPar(_loc, a, b)

      |
         t1 = SYMBOL; "->"; t2 = SYMBOL; b = OPT [ var_alternative ] -> VAltFn(_loc, VName(t1), VTy(Typ(_loc, t2)), b)

      |
         t1 = UPSYMBOL; "->"; t2 = SYMBOL; b = OPT [ var_alternative ] -> VAltFn(_loc, VName(t1), VTy(Typ(_loc, t2)), b)

      |
         t1 = SYMBOL; "->"; t2 = UPSYMBOL; b = OPT [ var_alternative ] ->VAltFn(_loc, VName(t1), VTy(Typ(_loc, t2)), b)

      |
         t1 = UPSYMBOL; "->"; t2 = UPSYMBOL; b = OPT [ var_alternative ] -> VAltFn(_loc, VName(t1), VTy(Typ(_loc, t2)), b)

      |
         t1 = UPSYMBOL; "["; la = LIST1 SELF SEP ","; "]"; b = OPT [ var_alternative ] ->
                                                                                        VAltFn(_loc, VName(t1), VLa(la), b)

      |
         t1 = UPSYMBOL; dots; "["; la = LIST1 SELF SEP ","; "]"; b = OPT [ var_alternative ] ->
                                                                                        VAltFn(_loc, VName(t1), VLa(la), b)

      |
         t1 = SYMBOL; "["; la = LIST1 SELF SEP ","; "]"; b = OPT [ var_alternative ] ->
                                                                                        VAltFn(_loc, VName(t1), VLa(la), b)

      |
         a = SYMBOL; "\\"; v1 = var_alternative -> VAltLam(_loc, AName(a), v1)

      |
         "."; n = var_alternative -> VAltBin(_loc, n)

      | (* confusion with the = sign, check in reconstruct that the last alt is = *)
         "let"; a = var_alternative; (*"="; b = SELF;*) "in"; c = SELF -> let d = VAltBin(_loc, c) in let b = append a d in VAltLet(_loc,b)

      |
         "{"; a = typ_dcl ; b = OPT [ ","; b = var_alternative -> b ]; "}"; c = var_alternative -> VAltOft(_loc, a, b, c)

      |
         `EMPTY ->  VAltEmpty(_loc)
      ]
    ]
  ;

 typ_dcl:
    [
      [
          a = SYMBOL; ":"; b = var_alternative ->  (a,b)

      ]
    ]
  ;

 turnstyle:
    [
      [
         "|-" -> ()

      ]
    ]
  ;


 con_dcl:
    [
      [
          a = SYMBOL; ":"; b = var_alternative -> NewCon(a,b)

      |

         a = SYMBOL  ->  Con(a)

      ]
    ]
  ;

 t_premise:
    [
      [
         a = UPSYMBOL; ":"; la = OPT ["|"; la= LIST1 con_dcl SEP ","; turnstyle -> la]; b = var_alternative ->
                                                                                                                 TPremisse(_loc, Some(PName(a)), la, b)
      |
         a = SYMBOL; ":"; la = OPT ["|"; la= LIST1 con_dcl SEP ","; turnstyle -> la]; b = var_alternative->
                                                                                                                 TPremisse(_loc, Some(PName(a)), la, b)
      |
         la = OPT ["|";  la= LIST1 con_dcl SEP ","; turnstyle -> la]; b = var_alternative -> TPremisse(_loc, None, la, b)

      |
          a = SYMBOL; ":"; b = var_alternative -> TPremisse(_loc, Some(PName(a)), None, b)

      |
         a = UPSYMBOL; ":"; b = var_alternative ->  TPremisse(_loc, Some(PName(a)), None, b)

      |
         a = var_alternative -> TPremisse(_loc, None, None, a)

      ]
    ]
  ;

 stmnt:
    [
      [
         "exists"; p1 = premise -> Exist(_loc, p1)

      |
         "forall";  lp1 = LIST1 t_premise SEP ";"; "exists"; p2 = premise -> ForAllExist(_loc, lp1, p2)

      ]
    ]
  ;

 proof:
    [
      [
        np = t_premise; "by"; "induction"; "on"; a = t_premise; ";"; lb = LIST1 args; "end"; "induction" -> Proof(_loc, np, a, lb)

      |

        np = t_premise; "by"; "uniqueness"; "of"; "variables"; ";" ->  Unique(_loc, np)

      |
        np = t_premise; "by";j = SELF; "on"; lp = LIST1 t_premise SEP "," ; ";"->  PRule(_loc, np, j, lp)

      |
        np = t_premise; "by"; "case"; "analysis"; "on"; lb = LIST1 var_name SEP ","; ":"; la = LIST1 args; "end"; "case"; "analysis" ->  CaseAn(_loc, np, lb, la)

      |
        np = t_premise; "by";"rule"; rn = SYMBOL; ltp = OPT [ "on"; ltp = LIST1 t_premise SEP "," -> ltp]; ";" -> URule(_loc, np, RName(rn), ltp)

      |
         "induction"; "hypothesis" -> InductionHyp(_loc)

      |
         "theorem"; tn = SYMBOL -> PTheorem(_loc, TName(tn))

      |
         "lemma"; tn = SYMBOL -> PTheorem(_loc, TName(tn))

      ]
    ]
  ;

var_name:
    [
      [
         vn = SYMBOL -> VName(vn)

      |

         vn = UPSYMBOL -> VName(vn)
      ]
    ]
  ;

 args:
    [
      [
         "case"; "rule"; r1 = rules; "is"; lp = LIST1 proof; "end"; "case" -> Argument(_loc, r1, lp)

      |
         "case"; n1 = t_premise ; "is"; lp = LIST1 proof; "end"; "case" -> Arg(_loc, n1, lp)

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
