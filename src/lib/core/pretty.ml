(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Pretty printing for external and internal syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html

    @author Darin Morrison
*)

open Format



(* Explanation of formatting markup:

   "@[" opens a box (open_box 0).  You may specify more information
   with an argument, e.g., "@[<hov n>" is equivalent to open_hovbox n

   "@]" closes a box (close_box ())

   "@ " outputs a breakable space (print_space ())

   "@," output a break hint (print_cut ())

   "@." end the pretty-printing, closing all boxes still opened
   (print_newline ())

   "@;<n m>" emit a "full" break hint (print_break n m)

   "@?" output pending material in the pretty-printer queue
   (print_flush ())
*)



type lvl    = int

let std_lvl = 0


let l_paren_if cond =
  if cond
  then "("
  else ""

let r_paren_if cond =
  if cond
  then ")"
  else ""



module type CID_RENDERER = sig

  open Id



  val render_name     : name     -> string

  val render_cid_typ  : cid_typ  -> string

  val render_cid_term : cid_term -> string

  val render_offset   : offset   -> string

  val render_var      : var      -> string

end



module Ext = struct

  open Id
  open Syntax.Ext.LF



  (*************************************)
  (* External Syntax Printer Signature *)
  (*************************************)

  module type PRINTER = sig

    (*******************************************)
    (* Contextual Format Based Pretty Printers *)
    (*******************************************)

    val fmt_ppr_sgn_decl : lvl -> formatter -> sgn_decl -> unit

    val fmt_ppr_kind     : lvl -> formatter -> kind     -> unit

    val fmt_ppr_typ      : lvl -> formatter -> typ      -> unit

    val fmt_ppr_normal   : lvl -> formatter -> normal   -> unit

    val fmt_ppr_head     :        formatter -> head     -> unit

    val fmt_ppr_spine    : lvl -> formatter -> spine    -> unit



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    val ppr_sgn_decl : sgn_decl -> unit

    val ppr_kind     : kind     -> unit

    val ppr_type     : typ      -> unit

    val ppr_normal   : normal   -> unit

    val ppr_head     : head     -> unit

    val ppr_spine    : spine    -> unit

  end



  (******************************************)
  (* External Syntax Pretty Printer Functor *)
  (******************************************)

  module Make = functor (R : CID_RENDERER) -> struct

    (*******************************************)
    (* Contextual Format Based Pretty Printers *)
    (*******************************************)

    let rec fmt_ppr_sgn_decl lvl ppf = function
      | SgnConst (_, c, a) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_name    c)
            (fmt_ppr_typ lvl) a

      | SgnTyp (_, a, k)   ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_name     a)
            (fmt_ppr_kind lvl) k

      | _ -> fprintf ppf ""



    and fmt_ppr_kind lvl ppf = function
      | Typ _                         ->
          fprintf ppf "type"

      | ArrKind (_, a, k)             ->
          let cond = lvl > 0 in
            fprintf ppf "@[%s%a -> %a%s@]"
              (l_paren_if cond)
              (fmt_ppr_typ  1) a
              (fmt_ppr_kind 0) k
              (r_paren_if cond)

      | PiKind (_, TypDecl (x, a), k) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name   x)
              (fmt_ppr_typ  0) a
              (fmt_ppr_kind 0) k
              (r_paren_if cond)



    and fmt_ppr_typ lvl ppf = function
      | Atom (_, a, Nil)             ->
          fprintf ppf "%s"
            (R.render_name a)

      | Atom (_, a, ms)              ->
          let cond = lvl > 1 in
            fprintf ppf "%s%s%a%s"
              (l_paren_if cond)
              (R.render_name    a)
              (fmt_ppr_spine 2) ms
              (r_paren_if cond)

      | ArrTyp (_, a, b)             ->
          let cond = lvl > 0 in
            fprintf ppf "@[%s%a -> %a%s@]"
              (l_paren_if cond)
              (fmt_ppr_typ 1) a
              (fmt_ppr_typ 0) b
              (r_paren_if cond)

      | PiTyp (_, TypDecl (x, a), b) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name  x)
              (fmt_ppr_typ 0) a
              (fmt_ppr_typ 0) b
              (r_paren_if cond)



    and fmt_ppr_normal lvl ppf = function
      | Lam (_, x, m)    ->
          let cond = lvl > 0 in
            fprintf ppf "%s[%s] %a%s"
              (l_paren_if cond)
              (R.render_name   x)
              (fmt_ppr_normal 0) m
              (r_paren_if cond)

      | Root (_, h, Nil) ->
          fprintf ppf "%a"
            fmt_ppr_head h

      | Root (_, h, ms)  ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a%a%s"
              (l_paren_if cond)
              fmt_ppr_head     h
              (fmt_ppr_spine 2) ms
              (r_paren_if cond)



    and fmt_ppr_head ppf = function
      | Name (_, n) ->
          fprintf ppf "%s"
            (R.render_name n)



    and fmt_ppr_spine lvl ppf = function
      | Nil            ->
          fprintf ppf ""

      | App (_, m, ms) ->
          fprintf ppf " %a%a"
            (fmt_ppr_normal  lvl) m
            (fmt_ppr_spine lvl) ms



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    let ppr_sgn_decl = fmt_ppr_sgn_decl std_lvl std_formatter

    let ppr_kind     = fmt_ppr_kind     std_lvl std_formatter

    let ppr_type     = fmt_ppr_typ      std_lvl std_formatter

    let ppr_normal   = fmt_ppr_normal     std_lvl std_formatter

    let ppr_head     = fmt_ppr_head             std_formatter

    let ppr_spine    = fmt_ppr_spine    std_lvl std_formatter

  end



  (********************************************)
  (* Default CID_RENDERER for External Syntax *)
  (********************************************)

  module DefaultCidRenderer = struct

    let render_name n   = n.string_of_name

    let render_cid_typ  = string_of_int

    let render_cid_term = string_of_int

    let render_offset   = string_of_int

    let render_var      = string_of_int

  end



  (****************************************************************)
  (* Default External Syntax Pretty Printer Functor Instantiation *)
  (****************************************************************)

  module DefaultPrinter = Make (DefaultCidRenderer)

end


module Int = struct

  open Id
  open Syntax.Int.LF



  (*************************************)
  (* Internal Syntax Printer Signature *)
  (*************************************)

  module type PRINTER = sig

    (*******************************************)
    (* Contextual Format Based Pretty Printers *)
    (*******************************************)

    val fmt_ppr_sgn_decl : lvl -> formatter -> sgn_decl -> unit

    val fmt_ppr_kind     : lvl -> formatter -> kind     -> unit

    val fmt_ppr_typ      : lvl -> formatter -> typ      -> unit

    val fmt_ppr_normal   : lvl -> formatter -> normal   -> unit

    val fmt_ppr_head     : lvl -> formatter -> head     -> unit

    val fmt_ppr_spine    : lvl -> formatter -> spine    -> unit

    val fmt_ppr_sub      : lvl -> formatter -> sub      -> unit

    val fmt_ppr_front    : lvl -> formatter -> front    -> unit

    val fmt_ppr_cvar     : lvl -> formatter -> cvar     -> unit



    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    val ppr_sgn_decl : sgn_decl -> unit

    val ppr_kind     : kind     -> unit

    val ppr_type     : typ      -> unit

    val ppr_normal   : normal   -> unit

    val ppr_head     : head     -> unit

    val ppr_spine    : spine    -> unit

    val ppr_sub      : sub      -> unit

    val ppr_front    : front    -> unit

    val ppr_cvar     : cvar     -> unit

  end



  (******************************************)
  (* Internal Syntax Pretty Printer Functor *)
  (******************************************)

  module Make = functor (R : CID_RENDERER) -> struct

    module InstHashedType = struct
      type t    = normal option ref
      let equal = (==)
      let hash  = Hashtbl.hash
    end

    module InstHashtbl = Hashtbl.Make (InstHashedType)

    let inst_hashtbl : string InstHashtbl.t = InstHashtbl.create 0

    (*******************************************)
    (* Contextual Format Based Pretty Printers *)
    (*******************************************)

    let rec fmt_ppr_sgn_decl lvl ppf = function
      | SgnTyp (a, k)   ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_cid_typ  a)
            (fmt_ppr_kind lvl) k

      | SgnConst (c, a) ->
          fprintf ppf "%s : %a.@.@?"
            (R.render_cid_term c)
            (fmt_ppr_typ lvl)  a



    and fmt_ppr_kind lvl ppf = function
      | Typ                        ->
          fprintf ppf "type"

      | PiKind (TypDecl (x, a), k) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name   x)
              (fmt_ppr_typ  0) a
              (fmt_ppr_kind 0) k
              (r_paren_if cond)



    and fmt_ppr_typ lvl ppf = function
      | Atom (a, Nil)             ->
          fprintf ppf "%s"
            (R.render_cid_typ a)

      | Atom (a, ms)              ->
          let cond = lvl > 1 in
            fprintf ppf "%s%s%a%s"
              (l_paren_if cond)
              (R.render_cid_typ a)
              (fmt_ppr_spine 2) ms
              (r_paren_if cond)

      | PiTyp (TypDecl (x, a), b) ->
          let cond = lvl > 0 in
            fprintf ppf "@[<1>%s{%s : %a}@ %a%s@]"
              (l_paren_if cond)
              (R.render_name  x)
              (fmt_ppr_typ 0) a
              (fmt_ppr_typ 0) b
              (r_paren_if cond)



    and fmt_ppr_normal lvl ppf = function
      | Lam (x, m)    ->
          let cond = lvl > 0 in
            fprintf ppf "%s[%s] %a%s"
              (l_paren_if cond)
              (R.render_name   x)
              (fmt_ppr_normal 0) m
              (r_paren_if cond)

      | Root (h, Nil) ->
          fprintf ppf "%a"
            (fmt_ppr_head lvl) h

      | Root (h, ms)  ->
          let cond = lvl > 1 in
            fprintf ppf "%s%a%a%s"
              (l_paren_if cond)
              (fmt_ppr_head lvl) h
              (fmt_ppr_spine 2)  ms
              (r_paren_if cond)



    and fmt_ppr_head lvl ppf = function
      | BVar x  ->
          fprintf ppf "%s"
            (R.render_offset x)

      | Const c ->
          fprintf ppf "%s"
            (R.render_cid_term c)

      | MVar (c, s) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_cvar lvl) c
            (fmt_ppr_sub  lvl) s



    and fmt_ppr_spine lvl ppf = function
      | Nil          ->
          fprintf ppf ""

      | App (m, ms)  ->
          fprintf ppf " %a%a"
            (fmt_ppr_normal lvl) m
            (fmt_ppr_spine  lvl) ms

      | SClo (ms, s) ->
          let cond = lvl > 1 in
          fprintf ppf "%sSClo (%a, %a)%s"
            (l_paren_if cond)
            (fmt_ppr_spine 0) ms
            (fmt_ppr_sub lvl) s
            (r_paren_if cond)



    (* FIXME *)
    and fmt_ppr_sub lvl ppf = function
      | Shift n     ->
          fprintf ppf "^%s"
            (R.render_offset n)

      (* Not sure how to print a cvar.  -dwm *)
      | SVar (c, s) ->
          fprintf ppf "%a[%a]"
            (fmt_ppr_cvar lvl) c
            (fmt_ppr_sub  lvl) s

      | Dot (f, s)  ->
          fprintf ppf "%a@ .@ %a"
            (fmt_ppr_front 1) f
            (fmt_ppr_sub lvl) s


    and fmt_ppr_front lvl ppf = function
      | Head h ->
          fprintf ppf "%a"
            (fmt_ppr_head lvl) h

      | Obj m  ->
          fprintf ppf "%a"
            (fmt_ppr_normal lvl) m

      | Undef  ->
          fprintf ppf "_"

    and fmt_ppr_cvar lvl ppf = function
      | Offset n ->
          fprintf ppf "%s"
            (R.render_offset n)

      | Inst ({ contents = None } as u, _, _, _) ->
          begin
            try
              fprintf ppf "%s"
                (InstHashtbl.find inst_hashtbl u)
            with
              | Not_found ->
                  (* Should probably create a sep. generator for this -dwm *)
                  let sym = String.uppercase (Gensym.VarData.gensym ()) in
                      InstHashtbl.replace inst_hashtbl u sym
                    ; fprintf ppf "%s" sym
          end

      | Inst ({ contents = Some tM }, _, _, _) ->
          fprintf ppf "%a"
            (fmt_ppr_normal lvl) tM

    (***************************)
    (* Regular Pretty Printers *)
    (***************************)

    let ppr_sgn_decl = fmt_ppr_sgn_decl std_lvl std_formatter

    let ppr_kind     = fmt_ppr_kind     std_lvl std_formatter

    let ppr_type     = fmt_ppr_typ      std_lvl std_formatter

    let ppr_normal   = fmt_ppr_normal   std_lvl std_formatter

    let ppr_head     = fmt_ppr_head     std_lvl std_formatter

    let ppr_spine    = fmt_ppr_spine    std_lvl std_formatter

    let ppr_sub      = fmt_ppr_sub      std_lvl std_formatter

    let ppr_front    = fmt_ppr_front    std_lvl std_formatter

    let ppr_cvar     = fmt_ppr_cvar     std_lvl std_formatter

  end



  (********************************************)
  (* Default CID_RENDERER for External Syntax *)
  (********************************************)

  module DefaultCidRenderer = struct

    open Store.Cid

    let render_name     n = n.string_of_name

    let render_cid_typ  a = render_name (Typ .get a).Typ .name

    let render_cid_term c = render_name (Term.get c).Term.name

    let render_offset   i = string_of_int i

    let render_var      x = string_of_int x

  end



  (****************************************************************)
  (* Default External Syntax Pretty Printer Functor Instantiation *)
  (****************************************************************)

  module DefaultPrinter = Make (DefaultCidRenderer)

end



module Error = struct

  open Syntax.Int

  (***************************)
  (* Error Printer Signature *)
  (***************************)

  module type PRINTER = sig

    module Check : sig

      (********************************)
      (* Format Based Pretty Printers *)
      (********************************)

      val fmt_ppr : formatter -> Check.LF.error -> unit



      (***************************)
      (* Regular Pretty Printers *)
      (***************************)

      val ppr : Check.LF.error -> unit

    end



    module Whnf : sig

      (********************************)
      (* Format Based Pretty Printers *)
      (********************************)

      val fmt_ppr : formatter -> Whnf.error -> unit



      (***************************)
      (* Regular Pretty Printers *)
      (***************************)

      val ppr : Whnf.error -> unit

    end

  end



  (********************************)
  (* Error Pretty Printer Functor *)
  (********************************)

  module Make = functor (R : CID_RENDERER) -> struct

    module IP = Int.Make (R)

    module Check = struct

      open Check.LF

      (********************************)
      (* Format Based Pretty Printers *)
      (********************************)

      let fmt_ppr ppf = function
        | CtxVarMisMatch _ ->
            fprintf ppf
              "ctx variable mismatch"

        | TypIllTyped (_cD, _cPsi, _tA, _tB) ->
            fprintf ppf
              "Inferred _tA but expected _tB"

        | ExpAppNotFun ->
            fprintf ppf
              "Expression is applied, but not a function"

        | KindMisMatch ->
            fprintf ppf
              "Kind mismatch"

        | SubIllTyped ->
            fprintf ppf
              "Substitution not well-typed"

        | TypMisMatch (_cD, _cPsi, (tA1, s1), (tA2, s2)) ->
            fprintf ppf
              "Type mismatch ** WARNING: Types not in context **:@ @[%a[%a]@ =/=@ %a[%a]@]"
              (* The 2 is for precedence.  Treat printing
                 below as if it were similar to an application context as
                 far as precedence is concerned -dwm *)
              (IP.fmt_ppr_typ 0)       tA1
              (IP.fmt_ppr_sub std_lvl) s1
              (IP.fmt_ppr_typ 0)       tA2
              (IP.fmt_ppr_sub std_lvl) s2

        | SigmaIllTyped (_cD, _cPsi, (_tArec, _s1), (_tBrec, _s2)) -> 
            fprintf ppf
              "Sigma Type mismatch"

        | IllTyped (_cD, _cPsi, (_tM, _s1), (_tA, _s2)) -> 
            fprintf ppf
              "Illtyped normal object" 


      (***************************)
      (* Regular Pretty Printers *)
      (***************************)

      let ppr = fmt_ppr std_formatter

    end



    module Whnf = struct

      open Whnf

      (********************************)
      (* Format Based Pretty Printers *)
      (********************************)

      let fmt_ppr ppf = function
        | ConstraintsLeft ->
            fprintf ppf
              "Constraint of functional type are not simplified"

        | NotPatSub       ->
            fprintf ppf
              "Not a pattern substitution"



      (***************************)
      (* Regular Pretty Printers *)
      (***************************)

      let ppr = fmt_ppr std_formatter

    end

  end



  (***********************************)
  (* Default CID_RENDERER for Errors *)
  (***********************************)

  module DefaultCidRenderer = Int.DefaultCidRenderer



  (******************************************************)
  (* Default Error Pretty Printer Functor Instantiation *)
  (******************************************************)

  module DefaultPrinter = Make (DefaultCidRenderer)

end
