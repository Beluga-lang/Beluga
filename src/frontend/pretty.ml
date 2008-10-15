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



module Id = struct

  open Core.Id



  (********************************)
  (* Format Based Pretty Printers *)
  (********************************)

  let fmt_ppr_name ppf = function
    | {string_of_name = x} -> fprintf ppf "%s" x



  (***************************)
  (* Default Pretty Printers *)
  (***************************)

  let ppr_name = fmt_ppr_name std_formatter

end



module Ext = struct

  open Id
  open Core.Syntax.Ext



  (*******************************************)
  (* Contextual Format Based Pretty Printers *)
  (*******************************************)

  let rec fmt_ppr_sgn_decl lvl ppf = function
    | SgnTyp (_, a, k)   ->
        fprintf ppf "%a : %a.@.@?"
           fmt_ppr_name      a
          (fmt_ppr_kind lvl) k

    | SgnConst (_, c, a) ->
        fprintf ppf "%a : %a.@.@?"
           fmt_ppr_name      c
          (fmt_ppr_type lvl) a

  and fmt_ppr_kind lvl ppf = function
    | Typ _               ->
        fprintf ppf "type"

    | PiKind (_, (x,a),k) ->
        let cond = lvl > 0 in
          fprintf ppf "@[<1>%s{%a : %a}@ %a%s@]"
            (l_paren_if cond)
             fmt_ppr_name    x
            (fmt_ppr_type 0) a
            (fmt_ppr_kind 0) k
            (r_paren_if cond)

  and fmt_ppr_type lvl ppf = function
    | Atom (_, a, Nil)   ->
        fprintf ppf "%a"
           fmt_ppr_name a

    | Atom (_, a, ms)    ->
        let cond = lvl > 1 in
          fprintf ppf "%s%a%a%s"
            (l_paren_if cond)
             fmt_ppr_name     a
            (fmt_ppr_spine 2) ms
            (r_paren_if cond)

    | PiTyp (_, (x,a),b) ->
        let cond = lvl > 0 in
          fprintf ppf "@[<1>%s{%a : %a}@ %a%s@]"
            (l_paren_if cond)
             fmt_ppr_name      x
            (fmt_ppr_type lvl) a
            (fmt_ppr_type lvl) b
            (r_paren_if cond)

  and fmt_ppr_term lvl ppf = function
    | Lam (_, x, m)    ->
        let cond = lvl > 0 in
          fprintf ppf "%s[%a] %a%s"
            (l_paren_if cond)
             fmt_ppr_name    x
            (fmt_ppr_term 0) m
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
        fprintf ppf "%a"
          fmt_ppr_name n

  and fmt_ppr_spine lvl ppf = function
    | Nil         ->
        fprintf ppf ""

    | App (m, ms) ->
        fprintf ppf " %a%a"
          (fmt_ppr_term  lvl) m
          (fmt_ppr_spine lvl) ms



  (***************************)
  (* Default Pretty Printers *)
  (***************************)

  let ppr_sgn_decl = fmt_ppr_sgn_decl std_lvl std_formatter

  let ppr_kind     = fmt_ppr_kind     std_lvl std_formatter

  let ppr_type     = fmt_ppr_type     std_lvl std_formatter

  let ppr_term     = fmt_ppr_term     std_lvl std_formatter

  let ppr_head     = fmt_ppr_head             std_formatter

  let ppr_spine    = fmt_ppr_spine    std_lvl std_formatter

end



module Int = struct

(*   let rec fmt_ppr_sgn_decl ppf = function *)
(*     | SgnTyp (a, k)   -> *)
(*         fprintf ppf "@[<1>%a : %a]" *)
(*           fmt_ppr_name a *)
(*           fmt_ppr_kind k *)

(*     | SgnConst (c, a) -> *)
(*         fprintf ppf "@[<1>%a : %a]" *)
(*           fmt_ppr_name c *)
(*           fmt_ppr_type a *)

(*   and fmt_ppr_kind ppf = function *)
(*     | Typ              -> *)
(*         fprintf ppf "type" *)

(*     | PiKind ((x,a),k) -> *)
(*         fprintf ppf "@[{%a : %a}@ %a@]" *)
(*           fmt_ppr_name x *)
(*           fmt_ppr_type a *)
(*           fmt_ppr_kind k *)

(*   and fmt_ppr_type ppf = function *)
(*     | Atom (a, ms)    -> *)
(*         fprintf ppf "@[%a%a@]" *)
(*           fmt_ppr_name  a *)
(*           fmt_ppr_spine ms *)

(*     | PiTyp ((x,a),b) -> *)
(*         fprintf ppf "@[{%a : %a}@ %a@]" *)
(*           fmt_ppr_name x *)
(*           fmt_ppr_type a *)
(*           fmt_ppr_type b *)

(*   and fmt_ppr_term ppf = function *)
(*     | Lam (x, m)   -> *)
(*         fprintf ppf "@[[%a]@ %a@]" *)
(*           fmt_ppr_name x *)
(*           fmt_ppr_term m *)

(*     | Root (h, ms) -> *)
(*         fprintf ppf "@[%a%a@]" *)
(*           fmt_ppr_head  h *)
(*           fmt_ppr_spine ms *)

(*   and fmt_ppr_head ppf = function *)
(*     | Name n -> *)
(*         fprintf ppf "%a" *)
(*           fmt_ppr_name n *)

(*   and fmt_ppr_spine ppf = function *)
(*     | Nil         -> *)
(*         fprintf ppf "" *)

(*     | App (m, ms) -> *)
(*         fprintf ppf "@ %a%a" *)
(*           fmt_ppr_term m *)
(*           fmt_ppr_spine ms *)

end
