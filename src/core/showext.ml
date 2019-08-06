
(* a not-so-pretty printer for external syntax, for use in debugging *)

open Format
open Support

module LF = struct
  open Syntax.Ext.LF

  let show_dep ppf = function
    | Maybe -> fprintf ppf "Maybe"
    | No -> fprintf ppf "No"
    | Inductive -> fprintf ppf "Inductive"
     
  let rec show_kind ppf = function
    | Typ _ -> fprintf ppf "type"
    | ArrKind (_, t, k) ->
       fprintf ppf "ArrKind(@[<hv>%a,@ %a@])"
         show_type t
         show_kind k
    | PiKind (_, d, k) ->
       fprintf ppf "PiKind(@[<hv>%a,@ %a@])"
         show_typ_decl d
         show_kind k

  and show_typ_decl ppf = function
    | TypDecl (x, t) ->
       fprintf ppf "TypDecl(@[<hv>%a,@ %a@])"
         Id.print x
         show_type t

  and show_cltyp ppf = function
    | MTyp t -> fprintf ppf "MTyp(%a)" show_type t
    | PTyp t -> fprintf ppf "PTyp(%a)" show_type t
    | STyp (cl, cPsi) ->
       fprintf ppf "STyp(@[<hv>%a,@ %a@])"
         show_svar_class cl
         show_dctx cPsi

  and show_svar_class ppf = function
    | Ren -> fprintf ppf "Ren"
    | Subst -> fprintf ppf "Subst"

  and show_ctyp ppf = function
    | ClTyp (cltyp, cPsi) ->
       fprintf ppf "ClTyp(@[<hv>%a,@ %a@])"
         show_cltyp cltyp
         show_dctx cPsi

  and show_loc_ctyp ppf (_, ctyp) = show_ctyp ppf ctyp

  and show_ctyp_decl ppf = function
    | Decl (x, d, dep) ->
        fprintf ppf "Decl(@[<hv>%a,@ %a,@ %a@])"
          Id.print x
          show_loc_ctyp d
          show_dep dep
    | DeclOpt x ->
       fprintf ppf "DeclOpt(%a)"
         Id.print x

  and show_type ppf = function
    | Atom (_, x, sp) ->
       fprintf ppf "Atom(@[<hv>%a,@ %a@])"
         Id.print x
         show_spine sp
    | ArrTyp (_, t1, t2) ->
       fprintf ppf "ArrTyp(@[<hv>%a,@ %a@])"
         show_type t1
         show_type t2
    | PiTyp (_, d, t) ->
       fprintf ppf "PiTyp(@[<hv>%a,@ %a@])"
         show_typ_decl d
         show_type t
    | Sigma (_, r) ->
       fprintf ppf "Sigma(%a)"
         show_typ_rec r
    | Ctx (_, cPsi) ->
       fprintf ppf "Ctx(%a)"
         show_dctx cPsi
    | AtomTerm (_, m) ->
       fprintf ppf "AtomTerm(%a)"
         show_normal m
         
  and show_normal ppf = function
    | Lam (_, x, m) ->
       fprintf ppf "Lam(@[<hv>%a,@ %a@])"
         Id.print x
         show_normal m
    | Root (_, h, s) ->
       fprintf ppf "Root(@[<hv>%a,@ %a@])"
         show_head h
         show_spine s
    | Tuple (_, t) ->
       fprintf ppf "Tuple(%a)"
         show_tuple t
    | LFHole (_, s) ->
       fprintf ppf "LFHole(%a)"
         (Maybe.print pp_print_string) s
    | Ann (_, m, t) ->
       fprintf ppf "Ann(@[<hv>%a,@ %a@])"
         show_normal m
         show_type t
    | TList (_, ms) ->
       fprintf ppf "TList [@[<hv>%a@]]"
         (pp_print_list
            ~pp_sep: (fun ppf () -> fprintf ppf ";@ ")
            show_normal)
         ms
    | NTyp (_, t) ->
       fprintf ppf "NTyp %a"
         show_type t
    | PatEmpty _ -> fprintf ppf "PatEmpty"

  and show_head ppf = function
    | Name (_, name, s) ->
       fprintf ppf "Name(@[<hv>%a,@ %a@])"
         Id.print name
         show_sub_opt s
    | Hole _ -> fprintf ppf "Hole"
    | PVar (_, name, s) ->
       fprintf ppf "PVar(@[<hv>#%a,@ %a@])"
         Id.print name
         show_sub_opt s
    | Proj (_, h, p) ->
       fprintf ppf "Proj(@[<hv>%a,@ %a@])"
         show_head h
         show_proj p

  and show_proj ppf = function
    | ByPos k -> fprintf ppf ".%d" k
    | ByName name -> fprintf ppf ".%a" Id.print name

  and show_spine ppf sp =
    let ms = list_of_spine sp |> List.rev in
    fprintf ppf "Spine(@[<hv>%a@])"
      (pp_print_list
         ~pp_sep: pp_print_space
         (fun ppf (_, m) -> show_normal ppf m))
      ms

  and show_sub_start ppf = function
    | EmptySub _ -> fprintf ppf "^"
    | Id _ -> fprintf ppf ".."
    | SVar (_, name, s) ->
       fprintf ppf "SVar(@[<hv>#%a,@ %a@])"
         Id.print name
         show_sub_opt s

  and show_sub_opt ppf = function
    | None -> ()
    | Some s -> show_sub ppf s

  and show_sub ppf (start, ms) =
    fprintf ppf "Sub(@[<hv>%a,@ [@[<hv>%a@]]@])"
      show_sub_start start
      (pp_print_list
         ~pp_sep: (fun ppf () -> fprintf ppf ";@ ")
         show_normal)
      ms

  and show_dctx = assert false
  and show_typ_rec = assert false
  and show_tuple = assert false
end

module Comp = struct
  open Format
  open Syntax.Ext.Comp

  let rec show_kind ppf = function
    | Ctype _ -> fprintf ppf "ctype"
    | PiKind (_, d, k) ->
       fprintf ppf "PiKind(@[<hv>%a,@ %a@])"
         LF.show_ctyp_decl d
         show_kind k
end
