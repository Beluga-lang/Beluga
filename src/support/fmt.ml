open Format
   
type fmt =
  { fmt : 'a. ('a, formatter, unit) format -> 'a }

let stringify p x = fprintf str_formatter "%a" p x; flush_str_formatter ()
let comma (ppf : Format.formatter) () = fprintf ppf ",@ "
