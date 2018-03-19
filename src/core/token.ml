(** Locations, used to locate a token within a file.  Since locations
    are slightly complicated, we just reuse the existing Camlp4
    definition. *)
module Loc = Syntax.Loc



(**********************************)
(* Token Type and Token Functions *)
(**********************************)

(** Tokens *)
type t =
  (** End of Input, usually the same thing as EOF. *)
  | EOI
  (** A keyword, see Lexer for examples. *)
  | KEYWORD of string
  (** Symbols. Can mean identifier, operator, etc. *)
  | SYMBOL  of string
  (** Symbols. Can mean identifier, operator, etc. *)
  | UPSYMBOL  of string
  (** A symbol of the form `?hole` *)
  | HOLE of string
  (** An integer literal. *)
  | INTLIT  of string
  (** A doc-comment. These are of the form %{{ ... %}} and are
   * remembered used Beluga for its literate programming. *)
  | COMMENT of string
  | DOTS of string
  (** Any string that would represent a module, e.g. 'Nat.z', 'List.Nat.z'.
   * NOTE: the regular expression for this DOES NOT match ordinary
   * symbols (i.e. 'z') and as such should be used in the parser as l =
   * [a = MODULESYM -> a | a = SYMBOL -> a] *)
  | MODULESYM of string
  | UPSYMBOL_LIST of string
(*   | TURNSTILE of string *)

let to_string =
  let p = Printf.sprintf "%s %S" in
  function
    | EOI       -> Printf.sprintf "EOI"
    | KEYWORD s -> p "KEYWORD" s
    | SYMBOL  s -> p "SYMBOL" s
    | UPSYMBOL  s -> p "UPSYMBOL" s
    | INTLIT s ->  p "INTEGER"  s
    | COMMENT s -> p "COMMENT" s
    | DOTS s -> p "DOTS"  s
    | MODULESYM s -> p "MODULESYM" s
    | UPSYMBOL_LIST s -> p "UPSYMBOL_LIST" s
    | HOLE s -> p "HOLE" s

(*   | TURNSTILE s -> Printf.sprintf "TURNSTILE %S"  s *)

(** Pretty print a token using {!Format} functionality. *)
let print ppf x = Format.pp_print_string ppf (to_string x)

(** Determine whether a token is a keyword or not.  Keywords are
    determined automatically by the extensible camlp4 grammar system.
    When a grammar is loaded, all string literals used in the grammar
    rules are treated as keywords.  But the lexer must also determine
    during lexical analysis if a symbol is a keyword. *)
let match_keyword kwd = function
  | KEYWORD kwd' when kwd' = kwd -> true
  | _                            -> false

(** Convert a token back to its textual representation. *)
let extract_string = function
  | EOI       ->
      invalid_arg ("Cannot extract string from token: " ^
                     to_string EOI)
  | KEYWORD s -> s
  | SYMBOL  s -> s
  | UPSYMBOL  s -> s
  | INTLIT  s -> s
  | COMMENT s -> s
  | DOTS s -> s
  | MODULESYM s -> s
  | UPSYMBOL_LIST s -> s
  | HOLE s -> s
(*   | TURNSTILE s -> s *)



(** Located Errors *)
module Error = Camlp4.Struct.EmptyError



(** Token stream filtering functionality. *)
module Filter = struct

  (** The camlp4 extensible grammar system relies on (dynamically
      updatable) stream filters.  This is the shape these stream filters
      take. *)
  type token_filter = (t, Loc.t) Camlp4.Sig.stream_filter

  (** A token filter can determine whether a token is a keyword
      and dynamically update its underlying filter function. *)
  type t = {
    is_kwd         : string -> bool;
    mutable filter : token_filter
  }

  (** Functionality to promote a token to a keyword.  This is
      necessary because if the grammar is updated during parsing, then
      what the lexer originally thought was only a symbol may actually
      be a keyword. *)
  let keyword_conversion tok is_kwd =
    match tok with
    | KEYWORD s              -> KEYWORD s
    | SYMBOL s when is_kwd s -> KEYWORD s
    | SYMBOL s               ->
        let firstChar = String.get s 0 in
          if firstChar >= 'A' && firstChar <= 'Z' then
            UPSYMBOL  s
          else
            SYMBOL s
    | tok -> tok  (* EOI, INTLIT *)

  (** Create a token filter given a function to determine keywords. *)
  let mk is_kwd = {
    is_kwd = is_kwd;
    filter = (fun s -> s)
  }

  (** Run a series of validation checks against a token. *)
  let validate_tok _ _ _ = ()

  (** Create a function mapping an unfiltered token stream to a
      filtered token stream. *)
  let filter x =
    let filter_tok tok loc =
      (* First promote the token to a keyword if necessary. *)
      let tok' = keyword_conversion tok x.is_kwd in
        (* Next, validate the token. *)
          validate_tok tok loc x.is_kwd
        ; (tok', loc)
    in
    let rec filter = parser
      | [< ' (tok, loc); s >] -> [< ' filter_tok tok loc; filter s >]
      | [<                 >] -> [<                                >]
    in
      fun strm -> x.filter (filter strm)

  let define_filter x f = x.filter <- f x.filter

  (** Called each time a keyword is added to the grammar *)
  let keyword_added _ _ _ = ()

  (** Called each time a keyword is removed from the grammar *)
  let keyword_removed _ _ = ()

end
