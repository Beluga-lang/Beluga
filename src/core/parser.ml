(* NOTE: Be careful with tuareg-mode M-q in this file -- it doesn't
   understand the grammar formatting below very well and will easily
   trash the layout. *)

open Syntax.Ext
open Id

module Grammar = Camlp4.Struct.Grammar.Static.Make (Lexer)

exception MixError of (Format.formatter -> unit)
exception IllFormedDataDecl
exception WrongConsType of Id.name * Id.name * Id.name
exception InvalidAssociativity of string

(** Remove any trailing newlines. Named after the Perl function that
    does the same thing. *)
let chomp = function
  | "" -> ""
  | s when s.[String.length s - 1] = '\n' -> String.sub s 0 (String.length s - 1)
  | s -> s

let _ = Error.register_printer
  (fun (Grammar.Loc.Exc_located (loc, exn)) ->
    Error.print_with_location loc (fun ppf ->
      Format.fprintf ppf "%s" (chomp (Printexc.to_string exn))))

let _ = Error.register_printer
  (fun (Stream.Error str) ->
    Error.print (fun ppf -> Format.fprintf ppf "%s" str))

let _ = Error.register_printer
  (fun (MixError f) ->
    Error.print (fun ppf -> f ppf))

let _ = Error.register_printer
  (fun IllFormedDataDecl ->
    Error.print (fun ppf ->
      Format.fprintf ppf "Parse Error: Ill-formed datatype declaration."))

let _ = Error.register_printer
  (fun (WrongConsType (c, a, a')) ->
    Error.print (fun ppf ->
      Error.report_mismatch ppf
        ("Parse Error: Wrong datatype for constructor " ^ (string_of_name c) ^ ".")
        "Expected datatype" Format.pp_print_string (string_of_name a)
        "Actual datatype"   Format.pp_print_string (string_of_name a')))

let _ = Error.register_printer
  (fun (InvalidAssociativity s) -> Error.print (fun ppf ->
    Format.fprintf ppf "Invalid Associativity \"%s\"" s))

let last l = match List.rev l with
  | [] -> None
  | h::t -> Some (h, t)

type kind_or_typ =
  | Kind of LF.kind
  | Typ  of LF.typ

type pair_or_atom =
  | Pair of Comp.exp_chk
  | Atom

type pair_or_atom_syn =
  | Pair_syn of Comp.exp_syn
  | Atom_syn

type pair_or_atom_pat =
  | Pair_pat of Comp.pattern
  | Atom_pat

type mixtyp =
  | MTCompKind of Loc.t
  | MTBase of Loc.t * Id.name * Comp.meta_spine
  | MTIndBase of Loc.t * Id.name * Comp.meta_spine
  | MTArr of Loc.t * mixtyp * mixtyp
  | MTCross of Loc.t * mixtyp * mixtyp
  | MTBox of Loc.t * mixtyp * LF.dctx * LF.depend
  | MTPBox of Loc.t * mixtyp * LF.dctx * LF.depend
  | MTCtx of Loc.t * Id.name * LF.depend
  | MTSub of Loc.t * LF.dctx * LF.dctx * LF.depend
  | MTPiBox of Loc.t * LF.ctyp_decl * mixtyp
(* -bp Pi-types should not occur in computation-level types
  |  MTPiTyp of Loc.t * LF.typ_decl * mixtyp *)
  | MTAtom of Loc.t * Id.name * LF.spine
  | MTAtomTerm of Loc.t * LF.normal


type whichmix = LFMix of LF.typ | CompMix of Comp.typ | CompKindMix of Comp.kind

let mixloc = function
  |  MTCompKind l -> l
  |  MTArr(l, _, _) -> l
  |  MTCross(l, _, _) -> l
  |  MTBox(l, _, _, _) -> l
  |  MTPBox(l, _, _, _) -> l
  |  MTCtx(l, _, _) -> l
  |  MTSub(l, _, _, _) -> l
  |  MTPiBox(l, _, _) -> l
(*  |  MTPiTyp(l, _, _) -> l *)
  |  MTAtom(l, _, _) -> l
  |  MTBase(l, _, _) -> l
  |  MTIndBase(l, _, _) -> l
  |  MTAtomTerm(l, _) -> l

let unmixfail loc = raise (Error.Violation ("Can't unmix. At " ^ Syntax.Loc.to_string loc))

(* unmix : mixtyp -> whichmix *  *)
let rec unmix = function
  | MTCompKind l -> CompKindMix (Comp.Ctype l)
  | MTBase (l, a, ms) -> CompMix(Comp.TypBase (l, a, ms))
  | MTIndBase (l, a, ms) -> CompMix(Comp.TypInd (Comp.TypBase (l, a, ms)))
  | MTArr(l, mt1, mt2) ->
     begin
       match (unmix mt1, unmix mt2) with
       | (LFMix lf1, LFMix lf2) -> LFMix(LF.ArrTyp(l, lf1, lf2))
       | (CompMix c1, CompMix c2) -> CompMix(Comp.TypArr(l, c1, c2))
       | (CompMix c1, CompKindMix c2) ->
          let x = Id.mk_name (Id.NoName) in
          let (l, cdecl) =
            match c1 with
            | Comp.TypInd (Comp.TypBox (l, mtyp)) -> (l, LF.Decl(x, mtyp, LF.Inductive))
            | Comp.TypBox (l, mtyp) -> (l, LF.Decl(x, mtyp, LF.No))
            | _ -> unmixfail (mixloc mt1)
          in
          CompKindMix(Comp.PiKind(l, cdecl, c2))
       | (_, _) -> unmixfail (mixloc mt2)
     end
  | MTCross(l, mt1, mt2) -> CompMix(Comp.TypCross(l, toComp mt1, toComp mt2))
  | MTBox(l, mt0, dctx, LF.No) -> CompMix (Comp.TypBox (l, (l, LF.ClTyp (LF.MTyp (toLF mt0), dctx))))
  | MTBox(l, mt0, dctx, LF.Inductive) -> CompMix (Comp.TypInd (Comp.TypBox (l, (l, LF.ClTyp (LF.MTyp (toLF mt0), dctx)))))
  | MTCtx  (l, schema, LF.No) -> CompMix (Comp.TypBox (l, (l, LF.CTyp schema)))
  | MTCtx  (l, schema, LF.Inductive) -> CompMix (Comp.TypInd(Comp.TypBox (l, (l, LF.CTyp schema))))
  | MTPBox(l, mt0, dctx, LF.No) -> CompMix (Comp.TypBox (l, (l, LF.ClTyp (LF.PTyp (toLF mt0), dctx))))
  | MTPBox(l, mt0, dctx, LF.Inductive) -> CompMix (Comp.TypInd (Comp.TypBox (l, (l, LF.ClTyp (LF.PTyp (toLF mt0), dctx)))))
  | MTSub(l, dctx1, dctx, LF.No) -> CompMix (Comp.TypBox (l, (l, LF.ClTyp (LF.STyp (LF.Subst,dctx1), dctx))))
  | MTSub(l, dctx1, dctx, LF.Inductive) -> CompMix (Comp.TypInd (Comp.TypBox (l, (l,LF.ClTyp (LF.STyp (LF.Subst,dctx1), dctx)))))
  | MTPiBox(l, cdecl, mt0) ->
       begin match unmix mt0 with
         | CompKindMix mk -> CompKindMix (Comp.PiKind(l, cdecl, mk))
         | CompMix mt -> CompMix(Comp.TypPiBox(l, cdecl, mt))
         | _ -> unmixfail (mixloc mt0)
       end
(*  |  MTPiTyp(l, tdecl, mt0) -> LFMix(LF.PiTyp(l, tdecl, toLF mt0)) *)
  | MTAtom(l, name, spine) -> LFMix(LF.Atom(l, name, spine))
  | MTAtomTerm(l, n) -> LFMix (LF.AtomTerm(l, n))

and toLF mt = match unmix mt with
  |  LFMix lf -> lf
  |  _ -> unmixfail (mixloc mt)

and toComp mt = match unmix mt with
  | CompMix c -> c
  | CompKindMix c ->
    raise (MixError (fun ppf -> Format.fprintf ppf
      "Syntax error: @[<v>Found Computation-level kind@;\
                          Expected: computation-level type@]"))
  |  _ ->
    raise (MixError (fun ppf -> Format.fprintf ppf
      "Syntax error: @[<v>Found LF-type@;\
       Expected: computation-level type"))

and toCompKind k = match unmix k with
  | CompKindMix c -> c
  | CompMix c ->
    raise (MixError (fun ppf -> Format.fprintf ppf
      "Syntax error: @[<v>Found Computation-level type@;\
       Expected: computation-level kind@]"))
  |  _ ->
    raise (MixError (fun ppf -> Format.fprintf ppf
      "Syntax error: @[<v>Found LF-type@;\
       Expected: computation-level kind"))

(* Check that datatype declarations are well formed. We can't do this
   later because after parsing there is no structural grouping between
   constructors of a same datatype. *)
let check_datatype_decl a cs =
  let rec retname = function
    | Comp.TypBase (_, c', _) -> c'
    | Comp.TypArr (_, _, tau) -> retname tau
    | Comp.TypPiBox (_, _, tau) -> retname tau
    | _ -> raise IllFormedDataDecl in
  List.iter (fun (Sgn.CompConst (_, c, tau)) ->
    let a' = retname tau in
    if not (a = a') then raise (WrongConsType (c, a, a'))) cs

let check_codatatype_decl a cs =
  let retname = function
    | Comp.TypBase (_, c', _) -> c'
    | _ -> raise IllFormedDataDecl in
  List.iter (fun (Sgn.CompDest (_, c, _, tau0, _)) ->
    let a' = retname tau0 in
    if not (a = a') then raise (WrongConsType (c, a, a'))) cs

let rec split (c : char) (m : string) : (string list * string) =
  try
    let i = String.index m c in
    let l = String.length m in
    let (a, rest) = (String.sub m 0 i, String.sub m (i+1) (l- i - 1)) in
    let (l, n) = split c rest in (a::l, n)
  with
  | Not_found -> ([], m)

let mkEmptyPat (loc, pHat) = Comp.PatMetaObj (loc, (loc,Comp.ClObj (pHat,Comp.MObj (LF.PatEmpty loc))))

type patOrObs = IsPat of Comp.pattern | IsObs of name
  
(*******************************)
(* Global Grammar Entry Points *)
(*******************************)

(* Each of these needs to also be listed in the GLOBAL section of the
 * camlp4 grammar below. *)

let sgn : Sgn.sgn Grammar.Entry.t =
  Grammar.Entry.mk "sgn"

let cmp_typ : Comp.typ Grammar.Entry.t =
  Grammar.Entry.mk "cmp_typ"

let harpoon_command : Syntax.Ext.Harpoon.command Grammar.Entry.t =
  Grammar.Entry.mk "harpoon_command"

let cmp_exp_chk : Comp.exp_chk Grammar.Entry.t =
  Grammar.Entry.mk "cmp_exp_chk"

(*****************************************)
(* Dynamically Extensible Beluga Grammar *)
(*****************************************)

(* We are forced to do this because of a bug in camlp4 that prevents
   qualified names in productions. Also we can't open earlier because
   camlp4 mandates the presence of an error module in Token, so when
   opening that module the module defined by error.ml gets
   overshadowed. *)
open Token

EXTEND Grammar
GLOBAL: sgn cmp_typ harpoon_command cmp_exp_chk;

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

  turnstile: [[ "|-" -> ()
	 | "⊢" -> () ]];

  sgn:
    [
      [ prag = sgn_global_prag; decls = sgn -> prag :: decls
      | decls = sgn_eoi -> decls
      ]
    ];

  sgn_eoi:
   [
     [ decl = sgn_decl; decls = sgn_eoi -> decl @ decls
     | `EOI -> []
     ]
   ];

  sgn_global_prag:
  [
    [
        "--nostrengthen" -> Sgn.GlobalPragma(_loc, Sgn.NoStrengthen)
      |
        "--coverage" -> Sgn.GlobalPragma(_loc, Sgn.Coverage(`Error))
      |
        "--warncoverage" -> Sgn.GlobalPragma(_loc, Sgn.Coverage(`Warn))
    ]
  ];

  sgn_lf_typ :
    [
      [ a = SYMBOL; ":"; tA = lf_typ ->
          Sgn.Const   (_loc, Id.mk_name (Id.SomeString a), tA)
      ]
    ];


  sgn_comp_typ :
    [
      [
        a = UPSYMBOL; ":"; tau = cmp_typ ->
          Sgn.CompConst (_loc, Id.mk_name (Id.SomeString a), tau)
      ]
    ];

  sgn_comp_cotyp :
    [
      [
        ctyp_decls = LIST0 clf_ctyp_decl;
        OPT "("; a = UPSYMBOL; ":"; tau0 = cmp_typ; OPT ")"; "::"; tau1 = cmp_typ ->
        let cD = List.fold_left (fun acc decl -> LF.Dec (acc, decl)) LF.Empty ctyp_decls in
          Sgn.CompDest (_loc, Id.mk_name (Id.SomeString a), cD, tau0, tau1)
      ]
    ];


  sgn_decl:
    [
      [
          "--name"; w = SYMBOL ; mv = UPSYMBOL ; x = OPT [ y = SYMBOL -> y ]; "." ->
            [Sgn.Pragma (_loc, Sgn.NamePrag (Id.mk_name (Id.SomeString w), mv, x))]

        | "--query" ; e = bound ; t = bound ; x = OPT [ y = UPSYMBOL ; ":" -> y ] ; a = lf_typ ; "." ->
            if Option.is_some x then
              let p = Id.mk_name (Id.SomeString (Option.get x)) in
              [Sgn.Query (_loc, Some p, a, e, t)]
            else
              [Sgn.Query (_loc, None, a, e, t)]

        | "--not" ->
            [Sgn.Pragma (_loc, Sgn.NotPrag)]

        | "module"; n = UPSYMBOL; "="; "struct"; decls = LIST1 sgn_decl; "end" ; ";"  ->
              let decls = List.map (fun [x] -> x) decls in
              [Sgn.Module(_loc, n, decls)]

        | a_or_c = SYMBOL; ":"; k_or_a = lf_kind_or_typ;  "." ->
             begin match k_or_a with
               | Kind k -> [Sgn.Typ   (_loc, Id.mk_name (Id.SomeString a_or_c), k)]
               | Typ  a -> [Sgn.Const (_loc, Id.mk_name (Id.SomeString a_or_c), a)]
             end

        | f = mutual_cmp_cdat;
          g = OPT [ "and"; f = LIST1 mutual_cmp_cdat SEP "and" -> f]; ";" ->
            begin match g with
              | None -> [Sgn.MRecTyp(_loc, [f])]
              | Some g' -> [Sgn.MRecTyp(_loc, f::g')]
            end

        | "LF"; f = LIST1 cmp_dat SEP "and"; ";" ->
             [Sgn.MRecTyp(_loc, f)]

        | "typedef"; a = UPSYMBOL; ":"; k = cmp_kind ; "=";  tau = cmp_typ ; ";" ->
            [Sgn.CompTypAbbrev (_loc, Id.mk_name (Id.SomeString a), k, tau)]
        |
          "schema"; w = SYMBOL; "="; bs = LIST1 lf_schema_elem SEP "+"; ";" ->
            [Sgn.Schema (_loc, Id.mk_name (Id.SomeString w), LF.Schema bs)]

(*      | "total" ; x = total_order ; "("; r = SYMBOL ; args = LIST0 call_args ; ")" ;  ";" ->
          [Sgn.Pragma (_loc, Sgn.Total (x, Id.mk_name (Id.SomeString r), args))] *)

      | "--name"; w = SYMBOL ; mv = UPSYMBOL ; x = OPT [ y = SYMBOL -> y ]; "." ->
        [Sgn.Pragma (_loc, Sgn.NamePrag (Id.mk_name (Id.SomeString w), mv, x))]

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

      |
        "--infix"; i = SYMBOL; p = INTLIT; assoc = OPT[x = SYMBOL -> x]; "."->
          begin
            match assoc with
            | Some "left" -> [Sgn.Pragma (_loc, Sgn.FixPrag(Id.mk_name (Id.SomeString i), Sgn.Infix, int_of_string p, Some Sgn.Left))]
            | Some "right" -> [Sgn.Pragma (_loc, Sgn.FixPrag(Id.mk_name (Id.SomeString i), Sgn.Infix, int_of_string p, Some Sgn.Right))]
            | Some "none" -> [Sgn.Pragma (_loc, Sgn.FixPrag(Id.mk_name (Id.SomeString i), Sgn.Infix, int_of_string p, Some Sgn.None))]
            | None -> [Sgn.Pragma (_loc, Sgn.FixPrag(Id.mk_name (Id.SomeString i), Sgn.Infix, int_of_string p, None))]
            | Some s -> raise (InvalidAssociativity s)
          end
  (*     |
        "#postfix"; i = SYMBOL; p = INTLIT; "." ->
          [Sgn.Pragma (_loc, Sgn.FixPrag(Id.mk_name (Id.SomeString i), Sgn.Postfix, int_of_string p, Some Sgn.Left))]
   *)    |
        "--prefix"; i = SYMBOL; p = INTLIT; "."->
          [Sgn.Pragma (_loc, Sgn.FixPrag(Id.mk_name (Id.SomeString i), Sgn.Prefix, int_of_string p, Some Sgn.Left))]

      | "--assoc"; assoc = SYMBOL; "." ->
        begin match assoc with
        | "left" -> [Sgn.Pragma(_loc, Sgn.DefaultAssocPrag Sgn.Left)]
        | "right" -> [Sgn.Pragma(_loc, Sgn.DefaultAssocPrag Sgn.Right)]
        | "none" -> [Sgn.Pragma(_loc, Sgn.DefaultAssocPrag Sgn.None)]
        | s -> raise (InvalidAssociativity s)

        end

      (* A naked expression, in REPL. *)
      | i = cmp_exp_syn ->
        [Sgn.Val (_loc, Id.mk_name (Id.SomeString "it"), None, i)]

      |
        "--open"; n = [n = UPSYMBOL_LIST -> n | n = UPSYMBOL -> n] ->
          let (l,last) = split '.' n in
          [Sgn.Pragma(_loc, Sgn.OpenPrag(l@[last]))]
      |

        "--abbrev"; n = [n = UPSYMBOL_LIST -> n | n = UPSYMBOL -> n]; abbrev = UPSYMBOL ->
          let (l,last) = split '.' n in
          [Sgn.Pragma(_loc, Sgn.AbbrevPrag(l@[last], abbrev))]
      |
	    x = COMMENT -> [Sgn.Comment(_loc, x)]

    ]
  ]
  ;

  call_args:
    [
      [
        x = SYMBOL -> Some (Id.mk_name (Id.SomeString x))

      | "_" -> None
      ]
    ]
;

  total_decl:
    [
      [
        "total"; x = OPT total_order ; "("; r = SYMBOL ; args = LIST0 call_args ;  ")"  ->
            Comp.Total (_loc, x, Id.mk_name (Id.SomeString r), args)
      | "trust" -> Comp.Trust _loc
      ]
    ]
;

  total_order:
    [
      [
        x = SYMBOL -> Comp.Arg (Id.mk_name (Id.SomeString x))
      | "{"; xs = LIST1 [ x = SYMBOL -> x ]  ; "}" -> Comp.Lex (List.map (fun x -> Comp.Arg (Id.mk_name (Id.SomeString x))) xs)
(*      | x = SYMBOL -> Id.mk_name (Id.SomeString x)  *)
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
           "{"; x = symbol; ":"; a2 = lf_typ; "}"; OPT rarr; k_or_a = SELF ->
             let name = LF.TypDecl (Id.mk_name (Id.SomeString x), a2) in
             begin match k_or_a with
               | Kind k -> Kind (LF.PiKind (_loc, name, k))
               | Typ  a -> Typ  (LF.PiTyp  (_loc, name, a))
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
           "{"; x = symbol; ":"; a2 = lf_typ; "}"; OPT rarr; k = SELF ->
             LF.PiKind (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), k)

        |
           a2 = lf_typ LEVEL "atomic"; rarr; k = SELF ->
             LF.ArrKind (_loc, a2, k)

        |
          "type"-> LF.Typ _loc
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
           "{"; x = symbol; ":"; a2 = SELF; "}"; OPT rarr; a = SELF ->
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
          term = lf_term -> begin match term with
            | LF.NTyp(_, t) -> t
            | LF.TList(_, [LF.NTyp(_,t)]) -> t
            | LF.TList(_, [n]) -> LF.AtomTerm(_loc, n)
            | _ -> LF.AtomTerm (_loc, term) end
        |
          x = [a = MODULESYM -> a | a = SYMBOL -> a]; ms = LIST0 (lf_term LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
            let (modules, a) = split '.' x in
              LF.Atom (_loc, Id.mk_name ~modules:modules (Id.SomeString a), sp)
(*         |
          a = SYMBOL; ms = LIST0 (lf_term LEVEL "atomic") ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp) *)
        ]
    ]
  ;

  lf_term:
    [
    "list" [
      l = LIST1 (lf_term LEVEL "lam") ->
            (LF.TList(_loc, l))
      ]
    | "lam" RIGHTA
        [
          "\\"; x = SYMBOL; "."; ms = LIST1 (lf_term LEVEL "lam")->
            LF.Lam (_loc, (Id.mk_name (Id.SomeString x)), LF.TList(_loc, ms))
        ]

    | "atomic"
        [
         "("; m = lf_typ; ann = OPT [ ":"; a = lf_typ -> a ]; ")" ->
            begin match ann, m with
              | None, LF.AtomTerm(_, t) -> t
              | None, _ -> LF.NTyp(_loc, m)
              | Some a, LF.AtomTerm(_, t) -> LF.Ann(_loc, t, a)
            end
        |
            h = lf_head ->
             LF.Root (_loc, h, LF.Nil)

        |
            "_" ->
            LF.Root (_loc, LF.Hole _loc , LF.Nil)
        ]
    ]
  ;

  lf_head:
    [
      [
        x = [a = MODULESYM -> a | a = SYMBOL -> a] -> let (l, n) = split '.' x in (LF.Name (_loc, Id.mk_name ~modules:l (Id.SomeString n)))
    |
        u = UPSYMBOL  ->
          LF.Name (_loc, Id.mk_name (Id.SomeString u))

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

  lf_typ_rec_block:
    [
      [
      "block"; OPT "("; a_list = LIST1 lf_typ_rec_elem SEP "," ; OPT ")"
        (* ","; _u=SYMBOL; ":"; a_last = clf_typ LEVEL "atomic" *)
        ->
          begin match last a_list with
          | Some ((x, a) , a_list) ->
              (List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest))
                (List.rev a_list) (LF.SigmaLast(Some x, a)))
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
        -> let aux = function
           | LF.Atom(_, n, _) -> Some n
           | _ -> None
           in LF.SigmaLast(aux a, a)
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

(*  clf_decl:
  [
    [
      x = SYMBOL; ":"; tA = clf_typ -> LF.TypDecl (Id.mk_name (Id.SomeString x), tA)
    ]

  ]
;
*)
  clf_ctyp_decl:
    [ (* TODO: Refactor this *)
      [
        "{"; hash = "#"; p = SYMBOL; ":";

         "["; cPsi = clf_dctx; turnstile; tA = clf_typ LEVEL "atomic";  "]"; "}"; ind = OPT ["*"] ->
	   let dep = match ind with None -> LF.No | Some _  -> LF.Inductive in
           LF.Decl(Id.mk_name (Id.SomeString p), (_loc,LF.ClTyp (LF.PTyp tA, cPsi)), dep)

      |
        "{"; hash = "#"; s = UPSYMBOL; ":";
         "["; cPsi = clf_dctx; turnstile; ren = OPT["#"] ; cPhi = clf_dctx; "]"; "}" ; ind = OPT ["*"] ->
	   let cl = match ren with None -> LF.Subst | Some _ -> LF.Ren in
	   let dep = match ind with None -> LF.No | Some _  -> LF.Inductive in
            LF.Decl(Id.mk_name (Id.SomeString s), (_loc,LF.ClTyp (LF.STyp (cl, cPhi), cPsi)), dep)

      |
          "{";  u = UPSYMBOL; ":";
         "["; cPsi = clf_dctx; turnstile; tA = clf_typ LEVEL "atomic";  "]"; "}" ; ind = OPT ["*"] ->
	   let dep = match ind with None -> LF.No | Some _  -> LF.Inductive in
           LF.Decl(Id.mk_name (Id.SomeString u), (_loc,LF.ClTyp (LF.MTyp tA, cPsi)), dep)

      |
          "{"; psi = SYMBOL; ":"; w = SYMBOL; "}" ; ind = OPT ["*"] ->
	   let dep = match ind with None -> LF.No | Some _  -> LF.Inductive in
            LF.Decl(Id.mk_name (Id.SomeString psi), (_loc,LF.CTyp(Id.mk_name (Id.SomeString w))), dep)

      ]
    ]
  ;



  clf_typ_pure:
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
                LF.AtomTerm(_loc, LF.TList(_loc, (LF.Root(_loc, LF.Name(_loc, Id.mk_name(Id.SomeString a)), LF.Nil))::ms))
          |
             a = UPSYMBOL; ms = LIST0 clf_normal ->
                LF.AtomTerm(_loc, LF.TList(_loc, (LF.Root(_loc, LF.MVar(_loc, Id.mk_name(Id.SomeString a), LF.RealId), LF.Nil))::ms))



        ]
    ]
  ;


  clf_typ:
    [
      "modules"
      [
          l = OPT[LIST1 [x = UPSYMBOL; "." -> x]]; a = SYMBOL; ms = LIST0 clf_normal ->
            let modules = match l with None -> [] | Some l -> l in
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              LF.Atom (_loc, Id.mk_name ~modules:modules (Id.SomeString a), sp)
      ]

    |
      RIGHTA
        [
           "{"; x = SYMBOL; ":"; a2 = SELF; "}"; a = SELF ->
             LF.PiTyp (_loc, LF.TypDecl (Id.mk_name (Id.SomeString x), a2), a)
        |
           a2 = SELF; rarr; a = SELF ->
             LF.ArrTyp (_loc, a2, a)
        ]

    | "atomic" [
           (* a = SYMBOL; *) ms = LIST1 clf_normal ->
            begin match ms with
              | [LF.NTyp(_, a)] -> a
              | _ -> LF.AtomTerm(_loc, LF.TList(_loc,(*  (LF.Root(_loc, LF.Name(_loc, Id.mk_name(Id.SomeString a)), LF.Nil)):: *) ms))
            end

           |
           a = UPSYMBOL; ms = LIST0 clf_normal ->
              LF.AtomTerm(_loc, LF.TList(_loc, (LF.Root(_loc, LF.MVar(_loc, Id.mk_name(Id.SomeString a), LF.RealId), LF.Nil))::ms))
              (* LF.AtomTerm(_loc, LF.TList(_loc, (LF.Root(_loc, LF.Name(_loc, Id.mk_name(Id.SomeString a)), LF.Nil))::ms)) *)

        ]
    | "sigma"
        [
          "("; a = SELF; ")" ->
            a
        |
          typRec = clf_typ_rec_block
          ->  LF.Sigma (_loc, typRec)
        ]
    ]
  ;

  clf_normal:
     [
      RIGHTA
       [
          "\\"; x = SYMBOL; "."; m = clf_term_app ->
            let m = begin match m with
              | LF.TList(l, (LF.Root(_, LF.MVar (l2, u, LF.EmptySub _), LF.Nil)) :: [LF.Root(_, (LF.Name _ as h), LF.Nil)]) ->
                  LF.Root(l, LF.MVar(l2, u, LF.Dot(l2, LF.EmptySub l2, LF.Head h)), LF.Nil)
              | _ -> m
            end in
            LF.Lam (_loc, (Id.mk_name (Id.SomeString x)), m)
       ]

    | "module"
      [
        modules = LIST1 [ x = UPSYMBOL; "." -> x]; n = SYMBOL ->
          let name = Id.mk_name ~modules:modules (Id.SomeString n) in
          LF.Root(_loc, LF.Name(_loc, name), LF.Nil)
      ]
    | "atomic"
        [
          u = UPSYMBOL ->
            LF.Root(_loc, LF.MVar (_loc, Id.mk_name (Id.SomeString u), LF.RealId), LF.Nil)

	| u = UPSYMBOL; "["; s = clf_sub_new; "]" ->
           LF.Root(_loc, LF.MVar(_loc, Id.mk_name (Id.SomeString u), s), LF.Nil)
        |
           "("; m = clf_term_app; ann = OPT [ ":"; a = clf_typ -> a ]; ")" ->
           begin match ann with
           | None -> m
           | Some a -> LF.Ann (_loc, m, a)
           end
        | h = clf_head -> LF.Root (_loc, h, LF.Nil)

        | "_" -> LF.Root (_loc, LF.Hole _loc , LF.Nil)

        | h = HOLE ->
           let sname = String.sub h 1 (String.length h - 1) in
           let name =
             match sname with
             | "" -> None
             | _ -> Some sname in
           LF.LFHole (_loc, name)

        | "<"; ms = LIST1 clf_term_app SEP ";"; ">"  ->
             let rec fold = function [m] -> LF.Last m
                                    | m :: rest -> LF.Cons(m, fold rest)
             in
               LF.Tuple (_loc, fold ms)

        ]
     ]
   ;

  clf_typ_rec_block:
    [[
       "block"; OPT "("; arg_list = LIST1 clf_typ_rec_elem SEP "," ; OPT ")"
       (* ; "."; a_last = clf_typ LEVEL "atomic" *)
         -> begin match  last arg_list with
          | Some ((n , a_last) , a_list) ->
              let b0 = (List.fold_right (fun (x, a) -> fun rest -> LF.SigmaElem (x, a, rest))
                          (List.rev a_list) (LF.SigmaLast (Some n, a_last)))
              in
                b0
        end

     ]];

  clf_typ_rec_elem:
    [
      [
        x = SYMBOL; ":"; a = clf_typ_pure
         -> (Id.mk_name (Id.SomeString x), a)
      ]
    ]
  ;


  clf_term_app:
    [
      [
        ms = LIST1 clf_normal -> LF.TList(_loc, ms)
      | a = clf_typ -> LF.NTyp(_loc, a)
      | "{"; "}" -> LF.PatEmpty _loc
      ]
  ];

  clf_head:
    [
      [
        "#"; p = SYMBOL; "."; k = clf_proj; "["; sigma = clf_sub_new; "]" ->
          LF.Proj(_loc, LF.PVar (_loc, Id.mk_name (Id.SomeString p), sigma), k)

      | "#"; p = SYMBOL; "."; k = clf_proj ->
          LF.Proj(_loc, LF.PVar (_loc, Id.mk_name (Id.SomeString p), LF.RealId), k)

      |
        "#"; p = SYMBOL; "["; sigma = clf_sub_new; "]" ->
           LF.PVar (_loc, Id.mk_name (Id.SomeString p), sigma)

      | "#"; p = SYMBOL -> LF.PVar (_loc, Id.mk_name (Id.SomeString p), LF.RealId)

      |
        x = SYMBOL; "."; k = clf_proj ->
          LF.Proj(_loc, LF.Name (_loc, Id.mk_name (Id.SomeString x)), k)

      | (* Namespaces supported for non-projection case only? *)
        m = [a = MODULESYM -> a | a = SYMBOL -> a] ->
          let (l, x) = split '.' m in
          LF.Name (_loc, Id.mk_name ~modules:l (Id.SomeString x))

      ]
    ]
  ;

  clf_proj:
    [
      [
	k = INTLIT -> LF.ByPos (int_of_string k)
      | n = SYMBOL -> LF.ByName (Id.mk_name (Id.SomeString n))
      ]
    ];

  clf_sub_term:
    [
     [
          "^" ->
          LF.EmptySub (_loc )

      |    DOTS  ->
          LF.Id (_loc)

      |
         "#"; s = UPSYMBOL; "["; sigma = clf_sub_new ; "]"->
          LF.SVar (_loc, Id.mk_name (Id.SomeString s), sigma)
      | "#"; s = UPSYMBOL -> LF.SVar(_loc, Id.mk_name (Id.SomeString s), LF.RealId)
     ]
    ]
;

  clf_sub_new:
    [
      [   -> LF.EmptySub _loc
      | s = clf_sub_term -> s
      | sigma = SELF; ","; tM = clf_term_app ->
          LF.Dot (_loc, sigma, LF.Normal tM)
      | tM = clf_term_app ->
          LF.Dot (_loc, LF.EmptySub _loc, LF.Normal tM)
      ]
    ]
  ;

  clf_dctx:
    [
      [
       (* turnstile  *)
        ->
          LF.Null
      | "_" -> LF.CtxHole

      |
        psi = SYMBOL ->
          LF.CtxVar (_loc, Id.mk_name (Id.SomeString psi))

      |  x = SYMBOL; ":"; tA = clf_typ ->
          LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA))

      |
        cPsi = clf_dctx; ","; x = SYMBOL; ":"; tA = clf_typ ->
          LF.DDec (cPsi, LF.TypDecl (Id.mk_name (Id.SomeString x), tA))
      ]
    ]
  ;



  clf_hat_or_dctx:
    [
      [
         -> (* Hat [ ] *)
           LF.Null
      | "_" -> LF.CtxHole

      |    x = SYMBOL ->
             LF.CtxVar (_loc, Id.mk_name (Id.SomeString x))
            (* Hat ([Id.mk_name (Id.SomeString x)]) *)

      |   x = SYMBOL; ":"; tA = clf_typ ->
          LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA))
      |
        cPsi = clf_hat_or_dctx; ","; x = SYMBOL; ":"; tA = clf_typ ->
          LF.DDec (cPsi, LF.TypDecl (Id.mk_name (Id.SomeString x), tA))

      | cPsi = clf_hat_or_dctx; "," ; x = SYMBOL  ->
          LF.DDec (cPsi, LF.TypDeclOpt  (Id.mk_name (Id.SomeString x)))

      ]
    ]
  ;

(* ************************************************************************************** *)

  cmp_kind:
    [
      [
      k = mixtyp -> toCompKind k
      ]
    ]
  ;

  cmp_typ:
   [
     [
       m = mixtyp -> toComp m
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

  cmp_pair_atom_syn :
    [
      [
        ","; e2 = cmp_exp_syn ; ")" -> Pair_syn e2

      | ")"                 -> Atom_syn

      ]
    ]
  ;

  cmp_pair_atom_pat :
    [
      [
        ","; e2 = cmp_pattern ; ")" -> Pair_pat e2

      | ")"  -> Atom_pat

      ]
    ]
  ;



  cmp_dat:
    [[
     a = SYMBOL; ":"; k = lf_kind ; "=" ; OPT ["|"] ; const_decls = LIST0 sgn_lf_typ SEP "|" ->
      (Sgn.Typ (_loc, Id.mk_name (Id.SomeString a), k) , const_decls)
    ]]
  ;

  cmp_cdat:
    [[
     p = datatype_flavour; a = UPSYMBOL; ":"; k = cmp_kind ; "="; OPT ["|"] ; c_decls = LIST0 sgn_comp_typ SEP "|" ->
      check_datatype_decl (Id.mk_name (Id.SomeString a)) c_decls;
      (Sgn.CompTyp (_loc, Id.mk_name (Id.SomeString a), k, p) , c_decls)
    ]]
;
 cocmp_cdat:
    [[
    "coinductive"; a = UPSYMBOL; ":"; k = cmp_kind ; "="; OPT ["|"] ; c_decls = LIST0 sgn_comp_cotyp SEP "|" ->
      check_codatatype_decl (Id.mk_name (Id.SomeString a)) c_decls;
      (Sgn.CompCotyp (_loc, Id.mk_name (Id.SomeString a), k) , c_decls)
    ]]
;

 mutual_cmp_cdat:
    [[
        f = cmp_cdat -> f
      | f = cocmp_cdat -> f
   ]]
;

 datatype_flavour:
   [[
     "inductive" -> Sgn.InductiveDatatype
   | "stratified" -> Sgn.StratifiedDatatype
   ]]
;

  cmp_rec:
    [[
      f = SYMBOL; ":"; tau = cmp_typ; "="; t = OPT [ "/"; td = total_decl; "/" -> td] ; e = cmp_exp_chk ->
       Comp.RecFun (_loc, Id.mk_name (Id.SomeString f), t, tau, e)
    ]]
  ;

  cmp_exp_chk:
    [ LEFTA [
      e = cmp_exp_chkX   ->   e
    | i = cmp_exp_syn    ->   Comp.Syn (_loc, i)
    ]];

  case_pragma:
    [[
      "--not" -> Pragma.PragmaNotCase
    | -> Pragma.RegularCase
    ]];


  (* cmp_exp_chkX:  checkable expressions, except for synthesizing expressions *)

  mlam_exp:
  [
    [
      f = SYMBOL -> f
    |
      f = UPSYMBOL -> f
    |
      "#"; f = SYMBOL -> f
    |
      "#"; f = UPSYMBOL -> f
    ]
  ]
  ;

  fn_exp:
  [
    [
      f = SYMBOL -> f
    ]
  ]
  ;

  cmp_copat:
    [
      [ pat = cmp_pattern -> IsPat pat
      | "."; obs = UPSYMBOL -> IsObs (Id.mk_name (Id.SomeString obs))
      ]
    ]
  ;

  cmp_copatSpine:
    [
      [
        patS = LIST1 cmp_copat; rArr; e = cmp_exp_chk ->
        let f acc = function
          | IsPat pat -> Comp.PatApp (_loc, pat, acc)
          | IsObs obs -> Comp.PatObs (_loc, obs, acc)
        in
        let patS' = List.fold_left f (Comp.PatNil _loc) (List.rev patS) in
        (patS', e)
      ]
    ]
  ;
  
  cmp_exp_chkX:
    [ LEFTA
        [ "fn"; fs = LIST1 fn_exp SEP ","; rArr; e = cmp_exp_chk ->
        List.fold_left (fun acc f -> Comp.Fn (_loc, (Id.mk_name (Id.SomeString f)), acc)) e (List.rev fs)

        | "fun"; br = LIST1 cmp_copatSpine SEP "|" ->
        let br' = List.fold_left (fun acc pat -> Comp.ConsFBranch (_loc, pat, acc))
          (Comp.NilFBranch _loc) (List.rev br) in
        Comp.Fun (_loc, br')
        
      | "mlam"; args = LIST1 mlam_exp SEP ","; rArr; e = cmp_exp_chk ->
        List.fold_left (fun acc s -> Comp.MLam(_loc, (Id.mk_name (Id.SomeString s)), acc)) e (List.rev args)

      | "case"; i = cmp_exp_syn; "of"; prag = case_pragma; OPT [ "|"]; bs = LIST1 cmp_branch SEP "|" ->
          Comp.Case (_loc, prag, i, bs)

     | "impossible"; i = cmp_exp_syn; cd = OPT ["in";
         ctyp_decls = LIST0 clf_ctyp_decl; "["; pHat = clf_dctx ;"]" -> (ctyp_decls, pHat)]  ->
           (match cd with
	      | Some (ctyp_decls, pHat) ->
		  let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
		    Comp.Case (_loc, Pragma.RegularCase, i,
                               [Comp.EmptyBranch (_loc, ctyp_decls', mkEmptyPat (_loc, pHat))])
	      | None ->
		    Comp.Case (_loc, Pragma.RegularCase, i,
                               [Comp.EmptyBranch (_loc, LF.Empty, mkEmptyPat (_loc, LF.Null ))]))

      | "let";  x = SYMBOL; "="; i = cmp_exp_syn;  "in"; e = cmp_exp_chk ->
          Comp.Let (_loc, i, (Id.mk_name (Id.SomeString x), e))

      | "let"; ctyp_decls = LIST0 clf_ctyp_decl;
           pat = cmp_pattern; "="; i = cmp_exp_syn; "in"; e = cmp_exp_chk ->
          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds))
                           LF.Empty ctyp_decls in

          let branch = Comp.Branch(_loc, ctyp_decls', pat, e)  in
          Comp.Case (_loc, Pragma.RegularCase, i, [branch])

      | "(" ; e1 = cmp_exp_chk; p_or_a = cmp_pair_atom ->
          begin match p_or_a with
            | Pair e2 ->   Comp.Pair (_loc, e1, e2)
            | Atom    ->   e1
          end

      | h = HOLE ->
         (* h is a string of the form "?hole", so we drop the first
          * character and check whether the name of the hole is empty
          * to construct the true hole name. *)
         let sname = String.sub h 1 (String.length h - 1) in
         let name =
           match sname with
           | "" -> None
           | _ -> Some sname in
         Comp.Hole (_loc, name)

      ]

    | "atomic"
      [

        tR = meta_obj  -> Comp.Box (_loc, tR)

       |
        "(" ; e1 = cmp_exp_chk; p_or_a = cmp_pair_atom ->
          begin match p_or_a with
            | Pair e2 ->   Comp.Pair (_loc, e1, e2)
            | Atom    ->   e1
          end
      ]
 ];

clobj:
  [[
       cPsi = clf_hat_or_dctx ; turnstile ; tR = term_or_sub -> (_loc,Comp.ClObj(cPsi, tR))
     | psi = clf_hat_or_dctx   ->  (_loc,Comp.CObj psi)
  ]];

(* isuffix: something that can follow an i; returns a function that takes the i it follows,
  and returns the appropriate synthesizing expression *)
isuffix:
  [ LEFTA

   [ m = [a = MODULESYM -> a | a = SYMBOL -> a] ->
     let (modules, n) = split '.' m in
     (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Var (_loc, Id.mk_name ~modules:modules (Id.SomeString n)))))
   | x = UPSYMBOL   ->
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.DataConst (_loc, Id.mk_name (Id.SomeString x)))))
   | e = cmp_exp_chkX   ->
       (fun i -> Comp.Apply(_loc, i, e))
 ]];

cmp_exp_syn:
 [
  "modules"[
     m = [a = MODULESYM -> a | a = SYMBOL -> a] ->
     let (modules, n) = split '.' m in
      Comp.Var (_loc, Id.mk_name ~modules:modules (Id.SomeString n))
  ]

  |

 LEFTA [
     tR = meta_obj -> Comp.BoxVal (_loc, tR)

   | h = SELF; s = isuffix  ->  s(h)
   | h = SELF; "("; e = cmp_exp_chk; p_or_a = cmp_pair_atom   ->
       Comp.Apply (_loc, h, begin match p_or_a with
                                    | Pair e2 ->   Comp.Pair (_loc, e, e2)
                                    | Atom    ->   e
                            end)
   | x = UPSYMBOL ->  Comp.DataConst (_loc, Id.mk_name (Id.SomeString x))

   | "("; i = SELF; p_or_a = cmp_pair_atom_syn -> match p_or_a with
       | Pair_syn i2 -> Comp.PairVal (_loc, i, i2)
       | Atom_syn -> i

 ]];

(* pattern spine: something that can follow a constructor; returns a function
   that takes the constructor it follows, and returns the appropriate
   synthesizing expression. *)

  term_or_sub:
  [
    [ (* TODO: Refactor this once head and sub are merged *)
     h = SYMBOL; ","; t = SYMBOL ->
            let su = LF.Dot (_loc, (LF.Dot (_loc, LF.EmptySub _loc, LF.Head (LF.Name (_loc, Id.mk_name (Id.SomeString h))))), LF.Head (LF.Name (_loc, Id.mk_name (Id.SomeString t)))) in
            Comp.SObj su
    | tM = clf_term_app -> Comp.MObj tM
    | s  = clf_sub_new -> Comp.SObj s
    ]
  ];

  cmp_pattern:
    [
      [
      mobj = meta_obj -> Comp.PatMetaObj (_loc, mobj)
     | x = SYMBOL -> Comp.PatVar (_loc, Id.mk_name (Id.SomeString x))
     | x = UPSYMBOL; s = LIST0 (cmp_pattern) ->
         let sp = List.fold_right (fun t s -> Comp.PatApp (_loc, t, s)) s (Comp.PatNil _loc)in
           Comp.PatConst (_loc, Id.mk_name (Id.SomeString x), sp)
     | "("; p = cmp_pattern; p_or_a = cmp_pair_atom_pat   ->
         (match p_or_a with
            | Pair_pat p2 -> Comp.PatPair (_loc, p, p2)
            | Atom_pat -> p)
     | pat = cmp_pattern; ":"; tau = cmp_typ -> Comp.PatAnn (_loc, pat, tau)
      ]
    ]
  ;

  cmp_branch:
    [
      [
        ctyp_decls = LIST0 clf_ctyp_decl;
        pattern = cmp_pattern;
         rest = OPT [rArr; e = cmp_exp_chk -> e] ->
          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
           (match rest with
              | Some e  -> Comp.Branch (_loc, ctyp_decls', pattern, e)
              | None    ->  Comp.EmptyBranch (_loc, ctyp_decls', pattern)
           )
      ]
    ]
  ;



  meta_obj:
    [
      [
        "["; tR = clobj; "]"   -> tR
      ]
    ];

  mixtyp:
    [ RIGHTA
      [
        "{"; psi = SYMBOL; ":"; l = OPT[LIST1 [x = UPSYMBOL; "." -> x]]; w = SYMBOL; "}"; ind = OPT ["*"]; mixtau = SELF ->
          let modules = match l with None -> [] | Some l -> l in
	  let dep = match ind with None -> LF.No | Some _ -> LF.Inductive in
          let ctyp_decl = (LF.Decl(Id.mk_name (Id.SomeString psi),
            (_loc,LF.CTyp(Id.mk_name ~modules:modules (Id.SomeString w))), dep)) in
          MTPiBox (_loc, ctyp_decl, mixtau)

      | "("; psi = SYMBOL; ":"; l = OPT[LIST1 [x = UPSYMBOL; "." -> x]]; w = SYMBOL; ")"; mixtau = SELF ->
          let modules = match l with None -> [] | Some l -> l in
          let ctyp_decl = (LF.Decl(Id.mk_name (Id.SomeString psi),
            (_loc,LF.CTyp(Id.mk_name ~modules:modules (Id.SomeString w))), LF.Maybe)) in
          MTPiBox (_loc, ctyp_decl, mixtau)
      |
        ctyp_decl = clf_ctyp_decl; mixtau = SELF ->
          MTPiBox (_loc, ctyp_decl, mixtau)
      |
        mixtau1 = SELF; rarr; mixtau2 = SELF ->
          MTArr (_loc, mixtau1, mixtau2)
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

        tK = "ctype" -> MTCompKind _loc
      (* allowing prop instead of ctype for ORBI files *)
      | tK = "prop" -> MTCompKind _loc

      | a = UPSYMBOL; ms = LIST0 meta_obj  ->
          let sp = List.fold_right (fun t s -> Comp.MetaApp (t, s)) ms Comp.MetaNil in
              MTBase (_loc, Id.mk_name (Id.SomeString a), sp)

(*      | "("; a = UPSYMBOL; ms = LIST0 meta_obj; ")"; "*"  ->
          let sp = List.fold_right (fun t s -> Comp.MetaApp (t, s)) ms Comp.MetaNil in
              MTIndBase (_loc, Id.mk_name (Id.SomeString a), sp)
*)
      | x = [a = MODULESYM -> a | a = SYMBOL -> a] ->
          let (modules, a) = split '.' x in
          MTCtx (_loc, Id.mk_name ~modules:modules (Id.SomeString a), LF.No)
      |
        "("; mixtau = mixtyp ; ")" ->
           mixtau

      | "#";"["; cPsi = clf_dctx; turnstile; ms = LIST1 clf_normal; "]"  ->
              MTPBox (_loc, MTAtomTerm(_loc, LF.TList(_loc, ms)), cPsi, LF.No)

      | "$"; "["; cPsi = clf_dctx; turnstile; cPhi = clf_dctx; "]"  ->
              MTSub(_loc, cPhi,  cPsi, LF.No)

      | "["; cPsi = clf_dctx; turnstile; ms = LIST1 clf_normal; "]" ->
              MTBox (_loc, MTAtomTerm(_loc, LF.TList(_loc, ms)), cPsi, LF.No )
     ]
  ] ;

  harpoon_command :
    [
      [ (* Recall: due to the open Syntax.Ext at the top, this module
      Harpoon does not refer to harpoon.ml but rather to the Harpoon
      submodule within Syntax.Ext. *)
        "%:intros" -> Syntax.Ext.Harpoon.Intros
      | "%:split"; t = cmp_exp_syn -> Syntax.Ext.Harpoon.Split t
      | "%:show-proof" -> Syntax.Ext.Harpoon.ShowProof
      | "%:defer" -> Syntax.Ext.Harpoon.Defer
      | "%:show-subgoals" -> Syntax.Ext.Harpoon.ShowSubgoals
      | "%:solve"; t = cmp_exp_chk -> Syntax.Ext.Harpoon.Solve t
      ]
    ];

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
