open Format

(** The type of formatting functions. *)
type 'a t = formatter -> 'a -> unit

(** Polymorphic function that processes a format string. *)
type fmt =
  { fmt : 'a. ('a, formatter, unit) format -> 'a }

(** Converts something to a string using a formatting function. *)
let stringify p x = fprintf str_formatter "%a" p x; flush_str_formatter ()

(** Prints a comma followed by a (breaking) space. *)
let comma (ppf : Format.formatter) () = fprintf ppf ",@ "
let between before after inside ppf () =
  before ppf ();
  inside ppf ();
  after ppf ()

(** `surrounded by inside` constructs a formatting function that
    will print `by` then `inside` then `by` again.
 *)
let surrounded (by : unit t) (inside : 'a t) : 'a t =
  fun ppf x ->
  by ppf ();
  inside ppf x;
  by ppf ()

(** Constructs a formatting function that ignores its argument and
    prints the given string literally. *)
let string s = fun ppf _ -> fprintf ppf "%s" s
