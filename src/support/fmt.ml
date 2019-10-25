open Format

type fmt =
  { fmt : 'a. ('a, formatter, unit) format -> 'a }

let stringify p x = fprintf str_formatter "%a" p x; flush_str_formatter ()
let comma (ppf : Format.formatter) () = fprintf ppf ",@ "
let between before after inside ppf () =
  before ppf ();
  inside ppf ();
  after ppf ()

let surrounded
      (by : Format.formatter -> unit -> unit)
      (inside : Format.formatter -> 'a -> unit)
      (ppf : Format.formatter)
      (x : 'a)
    : unit =
  by ppf ();
  inside ppf x;
  by ppf ()

(** Constructs a formatting function that ignores its argument and
    prints the given string literally. *)
let string s = fun ppf _ -> fprintf ppf "%s" s
