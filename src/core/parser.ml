(* NOTE: Be careful with tuareg-mode M-q in this file -- it doesn't
   understand the grammar formatting below very well and will easily
   trash the layout. *)

(* Load the camlp4 extensible grammar syntax extension *)
#load "pa_extend.cmo";;

open Syntax.Ext
open Id


module Grammar = Camlp4.Struct.Grammar.Static.Make (Lexer)

exception MixError of (Format.formatter -> unit)
exception IllFormedDataDecl
exception WrongConsType of Id.name * Id.name * Id.name

(** Remove any trailing newlines. Named after the Perl function that
    does the same thing. *)
let chomp = function
  | "" -> ""
  | s when s.[String.length s - 1] = '\n' -> String.sub s 0 (String.length s - 1)
  | s -> s

let _ = Error.register_printer
  (fun (Grammar.Loc.Exc_located (loc, exn)) ->
    Error.print_with_location loc (fun ppf ->
      Format.fprintf ppf "Parse Error: %s" (chomp (Printexc.to_string exn))))

let _ = Error.register_printer
  (fun (Stream.Error str) ->
    Error.print (fun ppf -> Format.fprintf ppf "%s" str))

let _ = Error.register_printer
  (fun (MixError f) ->
    Error.print (fun ppf -> f ppf))

let _ = Error.register_printer
  (fun IllFormedDataDecl ->
    Error.print (fun ppf ->
      Format.fprintf ppf "Ill-formed datatype declaration."))

let _ = Error.register_printer
  (fun (WrongConsType (c, a, a')) ->
    Error.print (fun ppf ->
      Error.report_mismatch ppf
        ("Wrong datatype for constructor " ^ c.string_of_name ^ ".")
        "Expected datatype" Format.pp_print_string a.string_of_name
        "Actual datatype"   Format.pp_print_string a'.string_of_name))

let last l = match List.rev l with
  | [] -> None
  | h::t -> Some (h, t)

type kind_or_typ =
  | Kind of LF.kind
  | Typ  of LF.typ

type dctx_or_hat =
  | Dctx of LF.dctx
  | Hat of LF.psi_hat

type pair_or_atom =
  | Pair of Comp.exp_chk
  | Atom


type pair_or_atom_syn =
  | Pair_syn of Comp.exp_syn
  | Atom_syn

type pair_or_atom_pat =
  | Pair_pat of Comp.pattern
  | Atom_pat of Comp.typ option


type term_or_sub =
  | Sub of LF.sub
  | Term of LF.normal

type clf_pattern =
  | PatEmpty of Loc.t
  | PatCLFTerm of Loc.t * LF.normal

type mixtyp =
  | MTCompKind of Loc.t
  | MTBase of Loc.t * Id.name * Comp.meta_spine
  | MTArr of Loc.t * mixtyp * mixtyp
  | MTCross of Loc.t * mixtyp * mixtyp
  | MTBool of Loc.t
  | MTBox of Loc.t * mixtyp * LF.dctx
  | MTPBox of Loc.t * mixtyp * LF.dctx
  | MTCtx of Loc.t * Id.name
  | MTSub of Loc.t * LF.dctx * LF.dctx
  | MTPiBox of Loc.t * (LF.ctyp_decl * Comp.depend) * mixtyp
(* -bp Pi-types should not occur in computation-level types
  |  MTPiTyp of Loc.t * LF.typ_decl * mixtyp *)
  | MTAtom of Loc.t * Id.name * LF.spine

type whichmix = LFMix of LF.typ | CompMix of Comp.typ | CompKindMix of Comp.kind

let mixloc = function
  |  MTCompKind l -> l
  |  MTArr(l, _, _) -> l
  |  MTCross(l, _, _) -> l
  |  MTBool l -> l
  |  MTBox(l, _, _) -> l
  |  MTPBox(l, _, _) -> l
  |  MTCtx(l, _) -> l
  |  MTSub(l, _, _) -> l
  |  MTPiBox(l, _, _) -> l
(*  |  MTPiTyp(l, _, _) -> l *)
  |  MTAtom(l, _, _) -> l
  |  MTBase(l, _, _) -> l

let unmixfail loc = raise (Error.Violation ("Can't unmix. At " ^ Syntax.Loc.to_string loc))

(* unmix : mixtyp -> whichmix *  *)
let rec unmix = function
  | MTCompKind l -> CompKindMix (Comp.Ctype l)
  | MTBase (l, a, ms) -> CompMix(Comp.TypBase (l, a, ms))
  | MTArr(l, mt1, mt2) -> begin match (unmix mt1, unmix mt2) with
                                  | (LFMix lf1, LFMix lf2) -> LFMix(LF.ArrTyp(l, lf1, lf2))
                                  | (CompMix c1, CompMix c2) -> CompMix(Comp.TypArr(l, c1, c2))
                                  | (CompMix c1, CompKindMix c2) ->
                                      let x = Id.mk_name (Id.NoName) in
                                      let (l, cdecl) = match c1 with
                                          | Comp.TypBox (l, tA, cPsi) -> (l, LF.MDecl(l, x, tA, cPsi))
                                          | Comp.TypPBox (l, tA, cPsi) -> (l, LF.PDecl (l, x, tA, cPsi))
                                          | Comp.TypCtx (l, schema)    -> (l, LF.CDecl (l, x, schema)) in
                                      CompKindMix(Comp.PiKind(l, (cdecl, Comp.Explicit), c2))
                                  | (_, _) -> unmixfail (mixloc mt2)
                           end
  | MTCross(l, mt1, mt2) -> CompMix(Comp.TypCross(l, toComp mt1, toComp mt2))
  | MTBool l -> CompMix(Comp.TypBool)
  | MTCtx  (l, schema) -> CompMix(Comp.TypCtx (l, schema))
  | MTPBox(l, mt0, dctx) -> CompMix(Comp.TypPBox(l, toLF mt0, dctx))
  | MTBox(l, mt0, dctx) -> CompMix(Comp.TypBox(l, toLF mt0, dctx))
  | MTSub(l, dctx1, dctx) -> CompMix(Comp.TypSub(l, dctx1, dctx))
  | MTPiBox(l, (cdecl,dep), mt0) ->
       begin match unmix mt0 with
         | CompKindMix mk -> CompKindMix (Comp.PiKind(l, (cdecl, dep), mk))
         | CompMix mt -> CompMix(Comp.TypPiBox(l, (cdecl, dep), mt))
         | _ -> unmixfail (mixloc mt0)
       end

(*  |  MTPiTyp(l, tdecl, mt0) -> LFMix(LF.PiTyp(l, tdecl, toLF mt0)) *)
  |  MTAtom(l, name, spine) -> LFMix(LF.Atom(l, name, spine))

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
  let rec retname = function
    | Comp.TypArr (_, Comp.TypBase (_, c', _), _) -> c'
    | Comp.TypPiBox (_, _, tau) -> retname tau
    | _ -> raise IllFormedDataDecl in
  List.iter (fun (Sgn.CompDest (_, c, tau)) ->
    let a' = retname tau in
    if not (a = a') then raise (WrongConsType (c, a, a'))) cs


(*******************************)
(* Global Grammar Entry Points *)
(*******************************)

let sgn = Grammar.Entry.mk "sgn"

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
GLOBAL: sgn;

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

(*   dots: [[ "."; "." -> ()
         | "…" -> () ]];  (* Unicode ellipsis (HTML &hellip;) *) *)

  gLambda: [[ "FN" -> ()
         | "Λ" -> () ]];  (* Unicode capital Lambda (HTML &Lambda;) *)

  turnstile: [[ "|-" -> ()
	 | "⊢" -> () ]];

  sgn:
    [
      [ prag = sgn_pragma_opts; decls = sgn_eoi -> Sgn.Pragma (_loc, prag) :: decls
      | decls = sgn_eoi -> decls
      ]
    ];

  sgn_eoi:
   [
     [ decl = sgn_decl; decls = SELF -> decl @ decls
     | `EOI -> []
     ]
   ];

  sgn_pragma_opts:
    [
      [ "%opts"; opts = LIST1 [ opt = SYMBOL -> opt]; ";" -> Sgn.OptsPrag opts ]
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
        a = UPSYMBOL; ":"; tau = cmp_typ ->
          Sgn.CompDest (_loc, Id.mk_name (Id.SomeString a), tau)
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

(*      |
        "datatype"; a = SYMBOL; ":"; k = lf_kind ; "=" ; OPT ["|"] ;
        const_decls = LIST0 sgn_lf_typ SEP "|" ; ";" ->
          Sgn.Typ (_loc, Id.mk_name (Id.SomeString a), k) :: const_decls
*)
      | "datatype"; f = LIST1 cmp_dat SEP "and"; ";" ->
           [Sgn.MRecTyp(_loc, f)]
(*
      | "datatype"; a = UPSYMBOL; ":"; k = cmp_kind ; "="; OPT ["|"] ; c_decls = LIST0 sgn_comp_typ SEP "|"; ";" ->
          check_datatype_decl (Id.mk_name (Id.SomeString a)) c_decls;
          Sgn.CompTyp (_loc, Id.mk_name (Id.SomeString a), k) :: c_decls
*)

      | "datatype"; f = cmp_cdat;
        g = OPT [ "and"; f = LIST1 cmp_cdat SEP "and" -> f
                | "and"; f = LIST1 mutual_cmp_cdat SEP "and" -> f]; ";" ->
          begin match g with
            | None -> [Sgn.MRecTyp(_loc, [f])]
            | Some g' -> [Sgn.MRecTyp(_loc, f::g')]
          end

      | "codatatype"; f = cocmp_cdat;
        g = OPT [ "and"; f = LIST1 cocmp_cdat SEP "and" -> f
                | "and"; f = LIST1 mutual_cmp_cdat SEP "and" -> f]; ";" ->
          begin match g with
            | None -> [Sgn.MRecTyp(_loc, [f])]
            | Some g' -> [Sgn.MRecTyp(_loc, f::g')]
          end

      | "typedef"; a = UPSYMBOL; ":"; k = cmp_kind ; "=";  tau = cmp_typ ; ";" ->
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
        [Sgn.Pragma (_loc, Sgn.NamePrag (Id.mk_name (Id.SomeString w), mv, x))]

      | "%query" ; e = bound ; t = bound ; x = OPT [ y = UPSYMBOL ; ":" -> y ] ; a = lf_typ ; "." ->
        if Option.is_some x then
          let p = Id.mk_name (Id.SomeString (Option.get x)) in
          [Sgn.Query (_loc, Some p, a, e, t)]
        else
          [Sgn.Query (_loc, None, a, e, t)]

      | "%not" ->
        [Sgn.Pragma (_loc, Sgn.NotPrag)]

      (* A naked expression, in REPL. *)
      | i = cmp_exp_syn ->
        [Sgn.Val (_loc, Id.mk_name (Id.SomeString "it"), None, i)]

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
            "("; m = SELF; ann = OPT [ ":"; a = lf_typ -> a ]; ")" ->
            begin match ann with
            | None -> m
            | Some a -> LF.Ann (_loc, m, a)
            end

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
         "["; cPsi = clf_dctx; turnstile; tA = clf_typ LEVEL "atomic";  "]"; "}" ->
           LF.PDecl (_loc, Id.mk_name (Id.SomeString p), tA, cPsi)

      |
        "{"; hash = "#"; s = UPSYMBOL; ":";
         cPsi = clf_dctx; turnstile; cPhi = clf_dctx; "}" ->
                LF.SDecl (_loc, Id.mk_name (Id.SomeString s), cPhi, cPsi)


      |
          "{";  u = UPSYMBOL; ":";
         "["; cPsi = clf_dctx; turnstile; tA = clf_typ LEVEL "atomic";  "]"; "}" ->
           LF.MDecl (_loc, Id.mk_name (Id.SomeString u), tA, cPsi)

      |
          "{"; psi = SYMBOL; ":"; w = SYMBOL; "}" ->
            LF.CDecl (_loc, Id.mk_name (Id.SomeString psi), Id.mk_name (Id.SomeString w))

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
             let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
               LF.Atom (_loc, Id.mk_name (Id.SomeString a), sp)


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
           "("; m = clf_term_app; ann = OPT [ ":"; a = clf_typ -> a ]; ")" ->
           begin match ann with
           | None -> m
           | Some a -> LF.Ann (_loc, m, a)
           end
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
        "#"; p = SYMBOL; "."; k = SYMBOL; sigma = clf_sub_new ->
          LF.NamedProjPVar(_loc, Id.mk_name (Id.SomeString k), (Id.mk_name (Id.SomeString p), sigma))
      |
        "#"; p = SYMBOL;  sigma = clf_sub_new ->
           LF.PVar (_loc, Id.mk_name (Id.SomeString p), sigma)

      |  "("; "#"; p = SYMBOL; "."; k = INTLIT; sigma = clf_sub_new ; ")" ->
          LF.ProjPVar (_loc, int_of_string k, (Id.mk_name (Id.SomeString p), sigma))

      |  
          "("; "#"; p = SYMBOL; "."; k = SYMBOL; sigma = clf_sub_new ; ")" ->
          LF.NamedProjPVar (_loc, Id.mk_name (Id.SomeString k), (Id.mk_name (Id.SomeString p), sigma))
      |
         "("; "#"; p = SYMBOL;  sigma = clf_sub_new ; ")" ->
          LF.PVar (_loc, Id.mk_name (Id.SomeString p), sigma)
      |
        x = SYMBOL; "."; k = INTLIT ->
          LF.ProjName (_loc, int_of_string k, Id.mk_name (Id.SomeString x))
      |
        x = SYMBOL; "."; k = SYMBOL ->
          LF.NamedProjName (_loc, Id.mk_name (Id.SomeString k), Id.mk_name (Id.SomeString x))
      
      |
        "#"; p = SYMBOL; "."; k = SYMBOL ->
          LF.NamedProjPVar (_loc, Id.mk_name (Id.SomeString k), (Id.mk_name (Id.SomeString p), LF.EmptySub _loc ))
      |
        "#"; p = SYMBOL ->
            LF.PVar (_loc, Id.mk_name (Id.SomeString p), LF.EmptySub  _loc)
      |
        x = SYMBOL ->
         LF.Name (_loc, Id.mk_name (Id.SomeString x))

 (*     | "#"; s = UPSYMBOL;  "["; sigma = clf_sub_new ; "]"->
          LF.SVar (_loc, Id.mk_name (Id.SomeString s), sigma) *)


      ]
    ]
  ;

  clf_sub_new:
    [
      [
        h = SELF; ","; subs = LIST1 (clf_sub_new LEVEL "atomic") SEP "," -> 
         List.fold_left (fun acc s -> match s with 
           | LF.Dot(l, LF.EmptySub _, front) -> LF.Dot(_loc, acc, front)) (LF.EmptySub(_loc)) (List.rev subs)

      ]
    |
      "atomic"
      [ 
          "^" ->
          LF.EmptySub (_loc )

      |    DOTS  ->
          LF.Id (_loc)

      |
         "#"; s = UPSYMBOL; "["; sigma = clf_sub_new ; "]"->
          LF.SVar (_loc, Id.mk_name (Id.SomeString s), sigma)

      |
        sigma = SELF;  h = clf_head ->
          LF.Dot (_loc, sigma, LF.Head h)

      |
        sigma = SELF; tM = clf_normal ->
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
       (* turnstile  *)
        ->
          LF.Null

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
           Dctx (LF.Null)

      |    x = SYMBOL ->
             Dctx (LF.CtxVar (_loc, Id.mk_name (Id.SomeString x)))
            (* Hat ([Id.mk_name (Id.SomeString x)]) *)

      |   x = SYMBOL; ":"; tA = clf_typ ->
          Dctx (LF.DDec (LF.Null, LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
      |
        cPsi = clf_hat_or_dctx; ","; x = SYMBOL; ":"; tA = clf_typ ->
          begin match cPsi with
            | Dctx cPsi' -> Dctx (LF.DDec (cPsi', LF.TypDecl (Id.mk_name (Id.SomeString x), tA)))
          end

      | phat = clf_hat_or_dctx; "," ; y = SYMBOL  ->
          begin match phat with
            | Dctx (LF.Null) -> Hat [Id.mk_name (Id.SomeString y)]
            | Dctx (LF.CtxVar (_, g)) -> Hat ([g] @ [Id.mk_name (Id.SomeString y)])
            | Hat phat -> Hat (phat @ [Id.mk_name (Id.SomeString y)])
          end

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
        ","; e2 = cmp_branch_pattern ; ")" -> Pair_pat e2

      | ")"; tauOpt = OPT [":" ; tau = cmp_typ -> tau]  -> Atom_pat tauOpt

      ]
    ]
  ;



  cmp_dat:
    [[
     a = SYMBOL; ":"; k = lf_kind ; "=" ; OPT ["|"] ; const_decls = LIST0 sgn_lf_typ SEP "|" ->
       Sgn.Typ (_loc, Id.mk_name (Id.SomeString a), k) :: const_decls
    ]]
  ;

  cmp_cdat:
    [[
    a = UPSYMBOL; ":"; k = cmp_kind ; "="; OPT ["|"] ; c_decls = LIST0 sgn_comp_typ SEP "|" ->
      check_datatype_decl (Id.mk_name (Id.SomeString a)) c_decls;
      Sgn.CompTyp (_loc, Id.mk_name (Id.SomeString a), k) :: c_decls
    ]]
;
 cocmp_cdat:
    [[
    a = UPSYMBOL; ":"; k = cmp_kind ; "="; OPT ["|"] ; c_decls = LIST0 sgn_comp_cotyp SEP "|" ->
      check_codatatype_decl (Id.mk_name (Id.SomeString a)) c_decls;
      Sgn.CompCotyp (_loc, Id.mk_name (Id.SomeString a), k) :: c_decls
    ]]
;

 mutual_cmp_cdat:
    [[
        "datatype"; f = cmp_cdat -> f

      | "codatatype"; f = cocmp_cdat -> f
   ]]
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

  copat_lst:
    [[
       f = UPSYMBOL -> Comp.CopatApp (_loc, Id.mk_name (Id.SomeString f), Comp.CopatNil _loc)
     | g = meta_obj -> Comp.CopatMeta (_loc, g, Comp.CopatNil _loc)
    ]];

  cofun_lst:
    [[
      f = UPSYMBOL; csp = LIST0 copat_lst; rArr; e = cmp_exp_chk ->
        ((Comp.CopatApp (_loc, Id.mk_name (Id.SomeString f), Comp.CopatNil _loc)) :: csp, e)
    ]];

  (* cmp_exp_chkX:  checkable expressions, except for synthesizing expressions *)
  cmp_exp_chkX:
    [ LEFTA
      [  "fn"; f = SYMBOL; rArr; e = cmp_exp_chk ->
           Comp.Fun (_loc, Id.mk_name (Id.SomeString f), e)

      | gLambda; f = SYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, (Id.mk_name (Id.SomeString f), Comp.CObj), e)

      | "mlam"; f = SYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, (Id.mk_name (Id.SomeString f), Comp.CObj), e)

      | "mlam"; f = UPSYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, (Id.mk_name (Id.SomeString f), Comp.MObj), e)

      | "mlam"; "#"; s = UPSYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, (Id.mk_name (Id.SomeString s), Comp.SObj), e)

      | "mlam"; hash = "#"; p = SYMBOL; rArr; e = cmp_exp_chk ->
          Comp.MLam (_loc, (Id.mk_name (Id.SomeString p), Comp.PObj), e)

      | "case"; i = cmp_exp_syn; "of"; prag = case_pragma; OPT [ "|"]; bs = LIST1 cmp_branch SEP "|" ->
          Comp.Case (_loc, prag, i, bs)

      | "cofun"; csp = LIST1 cofun_lst SEP "|" ->
          let f head left = match (head, left) with
            | (Comp.CopatApp (loc, a, csp'), csp'') -> Comp.CopatApp (loc, a, csp'')
            | (Comp.CopatMeta (loc, a, csp'), csp'') -> Comp.CopatMeta (loc, a, csp'') in
          let g = fun (csp1, e) -> (List.fold_right f csp1 (Comp.CopatNil _loc), e) in
          Comp.Cofun (_loc, List.map g csp)

(*      | "impossible"; i = cmp_exp_syn; "in";
         ctyp_decls = LIST0 clf_ctyp_decl; "["; pHat = clf_dctx ;"]"  ->
           let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
             Comp.Case (_loc, Pragma.RegularCase, i, [Comp.BranchBox (_loc, ctyp_decls', (pHat, Comp.EmptyPattern, None))])
*)

     | "impossible"; i = cmp_exp_syn; "in";
         ctyp_decls = LIST0 clf_ctyp_decl; "["; pHat = clf_dctx ;"]"  ->
           let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds)) LF.Empty ctyp_decls in
             Comp.Case (_loc, Pragma.RegularCase, i,
                        [Comp.EmptyBranch (_loc, ctyp_decls', Comp.PatEmpty (_loc, pHat))])
      | "if"; i = cmp_exp_syn; "then"; e1 = cmp_exp_chk ; "else"; e2 = cmp_exp_chk ->
          Comp.If (_loc, i, e1, e2)

      | "let";  x = SYMBOL; "="; i = cmp_exp_syn;  "in"; e = cmp_exp_chk ->
          Comp.Let (_loc, i, (Id.mk_name (Id.SomeString x), e))

      | "let"; ctyp_decls = LIST0 clf_ctyp_decl;
       (* "box"; "("; pHat = clf_dctx ;"."; tM = clf_term; ")";  *)
       "["; pHat = clf_dctx ;turnstile; mobj = clf_pattern; "]";
       tau = OPT [ ":"; "["; cPsi = clf_dctx; turnstile; tA = clf_typ LEVEL "atomic";  "]" -> Comp.TypBox(_loc,tA, cPsi) ];
       "="; i = cmp_exp_syn; "in"; e' = cmp_exp_chk
       ->
         let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds))
                                          LF.Empty ctyp_decls in
         let branch =
           begin match mobj with
            | PatEmpty loc'   ->
                (let pat = (match tau with
                                None -> Comp.PatEmpty (loc', pHat)
                              | Some tau -> Comp.PatAnn (loc', Comp.PatEmpty (loc', pHat), tau))
                 in
                  Comp.EmptyBranch (loc', ctyp_decls', pat)
                )
           | PatCLFTerm (loc', tM) ->
               (let pat = (match tau with
                               None -> Comp.PatMetaObj (_loc, Comp.MetaObjAnn (loc',  pHat,  tM))
                             | Some tau -> Comp.PatAnn (_loc, Comp.PatMetaObj(loc',
                                                    Comp.MetaObjAnn (loc', pHat, tM)), tau))
                in
                  Comp.Branch (loc', ctyp_decls', pat, e')
               )
           end in

         Comp.Case (_loc, Pragma.RegularCase, i, [branch])
      | "let"; ctyp_decls = LIST0 clf_ctyp_decl;
           pat = cmp_branch_pattern; "="; i = cmp_exp_syn; "in"; e = cmp_exp_chk ->
          let ctyp_decls' = List.fold_left (fun cd cds -> LF.Dec (cd, cds))
                           LF.Empty ctyp_decls in

          let branch = Comp.Branch(_loc, ctyp_decls', pat, e)  in
          Comp.Case (_loc, Pragma.RegularCase, i, [branch])
      | "(" ; e1 = cmp_exp_chk; p_or_a = cmp_pair_atom ->
          begin match p_or_a with
            | Pair e2 ->   Comp.Pair (_loc, e1, e2)
            | Atom    ->   e1
          end

      | "?" -> Comp.Hole (_loc)

      ]

    | "atomic"
      [

        "["; phat_or_psi = clf_hat_or_dctx ; turnstile ; tM = clf_term_app;  "]"  ->
          begin match phat_or_psi with
            | Dctx cPsi ->  Comp.Syn(_loc, Comp.BoxVal (_loc, cPsi, tM))
            | Hat phat  ->                 Comp.Box (_loc, Comp.MetaObj (_loc, phat, tM))
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

  "["; phat_or_psi = clf_hat_or_dctx ; turnstile; tM = term_or_sub; "]"   ->
     begin match (phat_or_psi, tM) with
       | (Dctx cPsi, Term tM)   -> (fun i -> Comp.MApp (_loc, i,
                                                        Comp.MetaObjAnn(_loc, cPsi,  tM)))
       | (Hat phat, Term tM)    -> (fun i -> Comp.MApp (_loc, i,
                                                        Comp.MetaObj (_loc, phat, tM)))
       | (Dctx cPsi, Sub s) ->  (fun i -> Comp.MApp (_loc, i, Comp.MetaSObjAnn (_loc,cPsi, s)))
       | (Hat phat, Sub s)  ->  (fun i -> Comp.MApp (_loc, i, Comp.MetaSObj (_loc,phat, s)))
     end

  (*|    "["; phat_or_psi = clf_hat_or_dctx ; turnstile; h = clf_head; ","; t = clf_head; "]" ->
    let s = LF.Dot (_loc, (LF.Dot (_loc, LF.EmptySub _loc, LF.Head h)), LF.Head t) in
     begin match phat_or_psi with
       | Dctx cPsi ->  (fun i -> Comp.MApp (_loc, i, Comp.MetaSObjAnn (_loc,cPsi, s)))
       | Hat phat  ->  (fun i -> Comp.MApp (_loc, i, Comp.MetaSObj (_loc,phat, s)))
     end*)

  | "["; phat_or_psi = clf_hat_or_dctx; "]"   ->
     begin match phat_or_psi with
       | Dctx cPsi     -> (fun i -> Comp.MApp(_loc, i, Comp.MetaCtx (_loc,cPsi)))
       | Hat [psi]      -> (fun i -> Comp.MApp(_loc, i,
                                                       Comp.MetaCtx (_loc, LF.CtxVar (_loc, psi))))
       | Hat []       -> (fun i -> Comp.MApp(_loc, i, Comp.MetaCtx(_loc, LF.Null)))
       | _                      ->
         raise (MixError (fun ppf -> Format.fprintf ppf "Syntax error: meta object expected."))
     end

   (*| "["; phat_or_psi = clf_hat_or_dctx ; turnstile; s = clf_sub_new; "]"   ->
     begin match phat_or_psi with
       | Dctx cPsi ->  (fun i -> Comp.MApp (_loc, i, Comp.MetaSObjAnn (_loc,cPsi, s)))
       | Hat phat  ->  (fun i -> Comp.MApp (_loc, i, Comp.MetaSObj (_loc,phat, s)))
     end*)

 | "<"; phat_or_psi = clf_hat_or_dctx ; "."; tM = clf_term_app; ">"   ->
     begin match phat_or_psi with
       | Dctx cPsi ->  (fun i -> Comp.MApp (_loc, i, Comp.MetaObjAnn (_loc,cPsi, tM)))
       | Hat phat  ->  (fun i -> Comp.MApp (_loc, i, Comp.MetaObj (_loc,phat, tM)))
     end

   | "=="; i2 = cmp_exp_syn   ->  (fun i -> Comp.Equal(_loc, i, i2))
   | x = SYMBOL   ->
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Var (_loc, Id.mk_name (Id.SomeString x)))))
   | x = UPSYMBOL   ->
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.DataConst (_loc, Id.mk_name (Id.SomeString x)))))
   | "ttrue"      ->
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Boolean (_loc, true))))
   | "ffalse"     ->
       (fun i -> Comp.Apply(_loc, i, Comp.Syn (_loc, Comp.Boolean (_loc, false))))
   | e = cmp_exp_chkX   ->
       (fun i -> Comp.Apply(_loc, i, e))
 ]];

cmp_exp_syn:
 [ LEFTA [
   "["; cPsi = clf_dctx; turnstile; tR = clf_term_app ; "]" ->
        Comp.BoxVal (_loc, cPsi, tR)

   | h = SELF; s = isuffix  ->  s(h)
   | h = SELF; "("; e = cmp_exp_chk; p_or_a = cmp_pair_atom   ->
       Comp.Apply (_loc, h, begin match p_or_a with
                                    | Pair e2 ->   Comp.Pair (_loc, e, e2)
                                    | Atom    ->   e
                            end)
   | x = UPSYMBOL ->  Comp.DataConst (_loc, Id.mk_name (Id.SomeString x))
   | x = SYMBOL ->  Comp.Var (_loc, Id.mk_name (Id.SomeString x))

   | "ttrue"    ->   Comp.Boolean (_loc, true)
   | "ffalse"   ->   Comp.Boolean (_loc, false)

   | "("; i = SELF; p_or_a = cmp_pair_atom_syn -> match p_or_a with
       | Pair_syn i2 -> Comp.PairVal (_loc, i, i2)
       | Atom_syn -> i
 ]];

(* pattern spine: something that can follow a constructor; returns a function
   that takes the constructor it follows, and returns the appropriate
   synthesizing expression. *)

clf_pattern :
    [
      [
        tM = clf_term_app -> PatCLFTerm (_loc, tM)
     |
        "{"; "}" -> PatEmpty _loc
      ]
    ]
  ;

  term_or_sub:
  [
    [
     h = SYMBOL; ","; t = SYMBOL ->
            let su = LF.Dot (_loc, (LF.Dot (_loc, LF.EmptySub _loc, LF.Head (LF.Name (_loc, Id.mk_name (Id.SomeString h))))), LF.Head (LF.Name (_loc, Id.mk_name (Id.SomeString t)))) in
            Sub su
    | tM = clf_term_app -> Term tM
    | s  = clf_sub_new -> Sub s
    ]
  ];
(*
    app_or_sub:
  [
    [
     h = SYMBOL; ","; t = SYMBOL ->
            let su = LF.Dot (_loc, (LF.Dot (_loc, LF.EmptySub _loc, LF.Head (LF.Name (_loc, Id.mk_name (Id.SomeString h))))), LF.Head (LF.Name (_loc, Id.mk_name (Id.SomeString t)))) in
            Sub su
(*        (* h = SELF; ",";  *)subs = LIST1 (clf_sub_new LEVEL "atomic") SEP "," -> 
         let su = List.fold_left (fun acc s -> match s with 
           |LF.Dot(l, LF.EmptySub _, front) -> LF.Dot(_loc, acc, front)) (LF.EmptySub(_loc)) (List.rev subs)
       in Sub su *)
    | tM = clf_term_app -> Term tM
    | s  = clf_sub_new -> Sub s
    ]
  ];*)

  cmp_branch_pattern:
    [
      [
        "["; cPsi = clf_dctx ; turnstile; tM = clf_pattern; "]" ;
         tau = OPT [ ":"; "["; cPsi = clf_dctx; turnstile; tA = clf_typ LEVEL "atomic"; "]" -> Comp.TypBox(_loc,tA, cPsi)]
          ->
              begin match tM with
            | PatEmpty _loc'   ->
                (match tau with None -> Comp.PatEmpty (_loc', cPsi)
                   | Some tau -> Comp.PatAnn (_loc', Comp.PatEmpty (_loc', cPsi), tau)
                )
            | PatCLFTerm (_loc', tM)  ->
                (match tau with None -> Comp.PatMetaObj (_loc, Comp.MetaObjAnn (_loc',  cPsi,  tM))
                  | Some tau -> Comp.PatAnn (_loc, Comp.PatMetaObj(_loc, Comp.MetaObjAnn (_loc, cPsi,    tM)), tau))

              end

      |"["; cPsi = clf_dctx ; "]" ;
         tau = OPT [ ":"; "["; cPsi = clf_dctx; turnstile; tA = clf_typ LEVEL "atomic"; "]" -> Comp.TypBox(_loc,tA, cPsi)]
	->
            begin match tau with 
	    |None -> Comp.PatMetaObj (_loc, Comp.MetaCtx (_loc,  cPsi))
            | Some tau -> Comp.PatAnn (_loc, Comp.PatMetaObj(_loc, Comp.MetaCtx (_loc, cPsi)), tau)
              end

      | "["; cPsi = clf_dctx ; turnstile; s = clf_sub_new; "]"   ->
          Comp.PatMetaObj (_loc, Comp.MetaSObjAnn (_loc, cPsi, s))


     | "<"; cPsi = clf_dctx ; turnstile; s = clf_sub_new; ">"   ->
          Comp.PatMetaObj (_loc, Comp.MetaSObjAnn (_loc, cPsi, s))

     | "ttrue" -> Comp.PatTrue (_loc)
     | "ffalse" -> Comp.PatFalse (_loc)
     | x = SYMBOL; tauOpt = OPT [":" ; tau = cmp_typ -> tau] ->
         (match tauOpt with
           | None -> Comp.PatVar (_loc, Id.mk_name (Id.SomeString x))
           | Some tau -> Comp.PatAnn (_loc, Comp.PatVar (_loc, Id.mk_name (Id.SomeString x)), tau)
         )
     | x = UPSYMBOL; s = LIST0 (cmp_branch_pattern) ->
         let sp = List.fold_right (fun t s -> Comp.PatApp (_loc, t, s)) s (Comp.PatNil _loc)in
           Comp.PatConst (_loc, Id.mk_name (Id.SomeString x), sp)
     | "("; p = SELF; p_or_a = cmp_pair_atom_pat   ->
         (match p_or_a with
            | Pair_pat p2 -> Comp.PatPair (_loc, p, p2)
            | Atom_pat None -> p
            | Atom_pat (Some tau) -> Comp.PatAnn (_loc, p, tau))
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
      ]
    ]
  ;



  meta_obj:
    [
      [

        "["; phat_or_psi = clf_hat_or_dctx ; mobj = OPT [turnstile; tM = term_or_sub -> tM ]; "]"   ->
          begin match (phat_or_psi , mobj) with
            | (Dctx cPsi, Some(Term tM))   -> Comp.MetaObjAnn (_loc, cPsi,  tM)
            | (Hat phat, Some(Term tM))    -> Comp.MetaObj (_loc, phat, tM)
            | (Dctx cPsi, Some(Sub s))   -> Comp.MetaSObjAnn (_loc, cPsi,  s)
            | (Hat phat, Some(Sub s))    -> Comp.MetaSObj (_loc, phat, s)
            | (Dctx cPsi, None)      -> Comp.MetaCtx (_loc, cPsi)
            | (Hat [psi], None)      -> Comp.MetaCtx (_loc, LF.CtxVar (_loc, psi))
            | (Hat [], None)         -> Comp.MetaCtx (_loc, LF.Null)
            | (_, _)                 ->
              raise (MixError (fun ppf -> Format.fprintf ppf "Syntax error: meta object expected."))
          end


      ]
    ];

  mixtyp:
    [ RIGHTA
      [
        "{"; psi = SYMBOL; ":";  w = SYMBOL; "}"; mixtau = SELF ->
          let ctyp_decl = (LF.CDecl(_loc, Id.mk_name (Id.SomeString psi),
                                   Id.mk_name (Id.SomeString w)) ,
                           Comp.Explicit) in
          MTPiBox (_loc, ctyp_decl, mixtau)

  | "("; psi = SYMBOL; ":";  w = SYMBOL; ")"; mixtau = SELF ->
          let ctyp_decl = (LF.CDecl(_loc, Id.mk_name (Id.SomeString psi),
                                   Id.mk_name (Id.SomeString w)) ,
                           Comp.Implicit) in
          MTPiBox (_loc, ctyp_decl, mixtau)
      |
        ctyp_decl = clf_ctyp_decl; mixtau = SELF ->
          MTPiBox (_loc, (ctyp_decl, Comp.Explicit), mixtau)
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

        tA = "Bool" -> MTBool _loc

      | tK = "ctype" -> MTCompKind _loc

      |
          a = UPSYMBOL; ms = LIST0 meta_obj  ->
            let sp = List.fold_right (fun t s -> Comp.MetaApp (t, s)) ms Comp.MetaNil in
              MTBase (_loc, Id.mk_name (Id.SomeString a), sp)

      | a = SYMBOL ->
          MTCtx (_loc, Id.mk_name (Id.SomeString a))
      |
        "("; mixtau = mixtyp ; ")" ->
           mixtau

      |   "(" ; "[";  cPsi = clf_dctx; turnstile; a = SYMBOL;  "]" ; rarr; mixtau2 = mixtyp ; ")" ->
              MTArr(_loc, MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), LF.Nil), cPsi ),
                    mixtau2)

      |   "(" ; "#"; "[";  cPsi = clf_dctx; turnstile; a = SYMBOL;  "]" ; rarr; mixtau2 = mixtyp ; ")" ->
              MTArr(_loc, MTPBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), LF.Nil), cPsi ),
                    mixtau2)

      |
          "#";"["; cPsi = clf_dctx; turnstile; a = SYMBOL;  ms = LIST0 clf_normal; "]"  ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              MTPBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), sp), cPsi )


      |
          "["; cPsi = clf_dctx; turnstile; "("; a = SYMBOL;  ms = LIST0 clf_normal; ")"; "]"  ->
            let sp = List.fold_right (fun t s -> LF.App (_loc, t, s)) ms LF.Nil in
              MTBox (_loc, MTAtom(_loc, Id.mk_name (Id.SomeString a), sp), cPsi )


      |
          "["; cPsi = clf_dctx; turnstile; a = SYMBOL;  ms = LIST0 clf_normal; "]"  ->
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
