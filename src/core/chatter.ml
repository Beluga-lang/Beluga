let level : int ref = ref 1

let ppf = Format.std_formatter

let print lvl x =
  let ppf =
    if lvl <= !level
    then ppf
    else Support.Fmt.null_formatter
  in
  Format.fprintf ppf x
