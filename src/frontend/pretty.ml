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



type lvl = int

let std_lvl = 0



module Id = struct

  open Core.Id

  let ppr_name ppf = function
    | {string_of_name = x} -> fprintf ppf "%s" x

end



module Ext = struct

  open Id
  open Core.Syntax.Ext

  let rec ppr_sgn_decl lvl ppf = function
    | SgnTyp (a, k)   ->
        fprintf ppf "@[<1>%a : %a]"
           ppr_name      a
          (ppr_kind lvl) k

    | SgnConst (c, a) ->
        fprintf ppf "@[<1>%a : %a]"
           ppr_name      c
          (ppr_type lvl) a

  and ppr_kind lvl ppf = function
    | Typ              ->
        fprintf ppf "type"

    | PiKind ((x,a),k) ->
        fprintf ppf "@[{%a : %a}@ %a@]"
           ppr_name      x
          (ppr_type lvl) a
          (ppr_kind lvl) k

  and ppr_type lvl ppf = function
    | Atom (a, ms)    ->
        fprintf ppf "@[%a%a@]"
           ppr_name       a
          (ppr_spine lvl) ms

    | PiTyp ((x,a),b) ->
        fprintf ppf "@[{%a : %a}@ %a@]"
           ppr_name      x
          (ppr_type lvl) a
          (ppr_type lvl) b

  and ppr_term lvl ppf = function
    | Lam (x, m)   ->
        fprintf ppf "@[[%a]@ %a@]"
           ppr_name      x
          (ppr_term lvl) m

    | Root (h, ms) ->
        fprintf ppf "@[%a%a@]"
           ppr_head       h
          (ppr_spine lvl) ms

  and ppr_head ppf = function
    | Name n ->
        fprintf ppf "%a"
          ppr_name n

  and ppr_spine lvl ppf = function
    | Nil         ->
        fprintf ppf ""

    | App (m, ms) ->
        fprintf ppf "@ %a%a"
          (ppr_term  lvl) m
          (ppr_spine lvl) ms

end



module Int = struct

(*   let rec ppr_sgn_decl ppf = function *)
(*     | SgnTyp (a, k)   -> *)
(*         fprintf ppf "@[<1>%a : %a]" *)
(*           ppr_name a *)
(*           ppr_kind k *)

(*     | SgnConst (c, a) -> *)
(*         fprintf ppf "@[<1>%a : %a]" *)
(*           ppr_name c *)
(*           ppr_type a *)

(*   and ppr_kind ppf = function *)
(*     | Typ              -> *)
(*         fprintf ppf "type" *)

(*     | PiKind ((x,a),k) -> *)
(*         fprintf ppf "@[{%a : %a}@ %a@]" *)
(*           ppr_name x *)
(*           ppr_type a *)
(*           ppr_kind k *)

(*   and ppr_type ppf = function *)
(*     | Atom (a, ms)    -> *)
(*         fprintf ppf "@[%a%a@]" *)
(*           ppr_name  a *)
(*           ppr_spine ms *)

(*     | PiTyp ((x,a),b) -> *)
(*         fprintf ppf "@[{%a : %a}@ %a@]" *)
(*           ppr_name x *)
(*           ppr_type a *)
(*           ppr_type b *)

(*   and ppr_term ppf = function *)
(*     | Lam (x, m)   -> *)
(*         fprintf ppf "@[[%a]@ %a@]" *)
(*           ppr_name x *)
(*           ppr_term m *)

(*     | Root (h, ms) -> *)
(*         fprintf ppf "@[%a%a@]" *)
(*           ppr_head  h *)
(*           ppr_spine ms *)

(*   and ppr_head ppf = function *)
(*     | Name n -> *)
(*         fprintf ppf "%a" *)
(*           ppr_name n *)

(*   and ppr_spine ppf = function *)
(*     | Nil         -> *)
(*         fprintf ppf "" *)

(*     | App (m, ms) -> *)
(*         fprintf ppf "@ %a%a" *)
(*           ppr_term m *)
(*           ppr_spine ms *)

end
