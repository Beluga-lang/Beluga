open Syntax.Common
open Format

let print_wf_tag ppf : bool -> unit =
  function
  | true -> fprintf ppf "*"
  | false -> ()

let l_paren_if cond =
  if cond
  then "("
  else ""

let r_paren_if cond =
  if cond
  then ")"
  else ""

let fmt_ppr_lf_svar_class ppf : LF.svar_class -> unit =
  function
  | LF.Ren -> fprintf ppf "#"
  | LF.Subst -> ()

type depend_print_style =
  [ `depend
  | `inductive
  ]

let fmt_ppr_lf_depend (style : depend_print_style) ppf : LF.depend -> unit =
  fun d ->
  match style with
  | `depend ->
     begin match d with
     | LF.No -> fprintf ppf "^e"
     | LF.Maybe -> fprintf ppf "^i"
     | LF.Inductive -> fprintf ppf "*"
     end
  | `inductive ->
     begin match d with
     | LF.No -> fprintf ppf ""
     | LF.Maybe -> fprintf ppf ""
     | LF.Inductive -> fprintf ppf "*"
     end

let fmt_ppr_cmp_split_kind ppf = function
  | `split -> fprintf ppf "split"
  | `invert -> fprintf ppf "invert"
  | `impossible -> fprintf ppf "impossible"

let fmt_ppr_invoke_kind ppf : Harpoon.invoke_kind -> unit =
  function
  | `ih -> fprintf ppf "ih"
  | `lemma -> fprintf ppf "lemma"

let fmt_ppr_cmp_context_case f ppf = function
  | Comp.EmptyContext _ ->
     fprintf ppf "empty context"
  | Comp.ExtendedBy (_, a) ->
     fprintf ppf "@[<hov 2>extended by@ @[%a@]@]"
       f a
