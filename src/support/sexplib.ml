type symbol =
  | Symbol of string

let symbol (s : string) : symbol option =
  Some (Symbol s)

let symbol' (s : string) : symbol =
  Symbol s
            
type atom =
  | String of string
  | SymbolAtom of symbol
  | Number of int

type t =
  | Atom of atom
  | List of t list

type sexp = t

let symbola (s : string) : t option =
  let open Maybe in
  symbol s $> fun sym -> Atom (SymbolAtom sym)

let symbola' (s : string) : t =
  Atom (SymbolAtom (symbol' s))

let string (s : string) : t =
  Atom (String s)

let number (n : int) : t =
  Atom (Number n)

let list (xs : t list) : t =
  List xs

let pair (x, y : t * t) : t =
  list [symbola' "cons"; x; y]

let alist (ps : (symbol * t) list) : t =
  List
    (List.map
       (fun (s, exp) ->
         pair (Atom (SymbolAtom s), exp))
       ps)

let alist' (ps : (string * t) list) : t =
  List
    (List.map
       (fun (s, exp) ->
         pair (symbola' s, exp))
       ps)

let format_atom (a : atom) ppf =
  let open Format in
  match a with
  | String s -> fprintf ppf "%S" s
  | SymbolAtom (Symbol s) -> fprintf ppf "%s" s
  | Number n -> fprintf ppf "%d" n

let rec format_sexp (exp : t) ppf =
  let open Format in
  match exp with
  | Atom a -> format_atom a ppf
  | List xs ->
     fprintf ppf "(";
     begin
      match xs with
      | [] -> ()
      | exp :: xs ->
         format_sexp exp ppf;
         List.iter
           (fun exp ->
             fprintf ppf " ";
             format_sexp exp ppf)
           xs
     end;
     fprintf ppf ")"

type 'a sexp_formatter = 'a -> t
