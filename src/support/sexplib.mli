type symbol =
  | Symbol of string

val symbol : string -> symbol option

val symbol' : string -> symbol

type atom =
  | String of string
  | SymbolAtom of symbol
  | Number of int

(** The type of s-expressions. *)
type t =
  | Atom of atom
  | List of t list

(** Smart constructor for symbols that checks that the symbol is well-formed. *)
val symbola : string -> t option

(** Smart constructor for symbols that we assert are well-formed. *)
val symbola' : string -> t

(** Smart constructor for strings. *)
val string : string -> t

(** Smart constructor for number literals. *)
val number : int -> t

(** Constructs a pair s-expression. *)
val pair : t * t -> t

(** Constructs an association list from checked symbols, that are known to be correct. *)
val alist : (symbol * t) list -> t

(** Constructs an association list from unchecked symbols, asserting their correctness. *)
val alist' : (string * t) list -> t

(** Smart constructor for lists. *)
val list : t list -> t

val format_atom : atom -> Format.formatter -> unit

val format_sexp : t -> Format.formatter -> unit

(** A synonym for `t` for disambiguation, sometimes. *)
type sexp = t

(** Type of functions that convert from a type into s-expressions. *)
type 'a sexp_formatter = 'a -> t
