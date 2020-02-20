open Util

module OptSpecName = struct
  type t =
    | LongName of string
    | ShortName of string
    | LongAndShortName of string * string

  let to_list name =
    match name with
    | LongAndShortName (ln, sn) -> [ln; sn]
    | LongName ln -> [ln]
    | ShortName sn -> [sn]

  let to_string name =
    String.concat ", " (to_list name)
end

module OptSpec : sig
  type 'a t =
    { long_name : string option
    ; short_name : char option
    ; meta_vars : string list option
    ; help_msg : string option
    ; default_argument : 'a option
    ; condition : ('a -> bool) option
    ; optional : 'a option
    }

  val long_name : string -> 'a t
  val short_name : char -> 'a t
  val meta_vars : string list -> 'a t
  val help_msg : string -> 'a t
  val default_argument : 'a -> 'a t
  val condition : ('a -> bool) -> 'a t
  val optional : 'a -> 'a t

  val lift : unit t -> 'a t

  val merge : 'a t list -> 'a t

  type 'a checked =
    { name : OptSpecName.t
    ; meta_vars : string list
    ; help_msg : string option
    ; default_argument : 'a option
    ; condition : ('a -> bool) option
    ; optional : 'a option
    }

  type check_error =
    | NoName

  val check : 'a t -> ('a checked, check_error) result
end = struct
  type 'a t =
    { long_name : string option
    ; short_name : char option
    ; meta_vars : string list option
    ; help_msg : string option
    ; default_argument : 'a option
    ; condition : ('a -> bool) option
    ; optional : 'a option
    }

  let make_empty () : 'a t =
    { long_name = None
    ; short_name = None
    ; meta_vars = None
    ; help_msg = None
    ; default_argument = None
    ; condition = None
    ; optional = None
    }

  let long_name ln : 'a t = { (make_empty ()) with long_name = Some ln }
  let short_name sn : 'a t = { (make_empty ()) with short_name = Some sn }
  let help_msg hm : 'a t = { (make_empty ()) with help_msg = Some hm }
  let default_argument (dv : 'a) : 'a t = { (make_empty ()) with default_argument = Some dv }
  let condition cd : 'a t = { (make_empty ()) with condition = Some cd }
  let meta_vars mvs : 'a t = { (make_empty ()) with meta_vars = Some mvs }
  let optional op : 'a t = { (make_empty ()) with optional = Some op }

  let lift (spec : unit t) : 'a t =
    { long_name = spec.long_name
    ; short_name = spec.short_name
    ; meta_vars = spec.meta_vars
    ; help_msg = spec.help_msg
    ; default_argument = None
    ; condition = Option.map (fun f -> (fun _ -> f ())) spec.condition
    ; optional = None
    }

  let combine (spec0 : 'a t) (spec1 : 'a t) : 'a t =
    let open Option in
    { long_name = fold ~none:spec1.long_name ~some spec0.long_name
    ; short_name = fold ~none:spec1.short_name ~some spec0.short_name
    ; meta_vars = fold ~none:spec1.meta_vars ~some spec0.meta_vars
    ; help_msg = fold ~none:spec1.help_msg ~some spec0.help_msg
    ; default_argument = fold ~none:spec1.default_argument ~some spec0.default_argument
    ; condition = fold ~none:spec1.condition ~some spec0.condition
    ; optional = fold ~none:spec1.optional ~some spec0.optional
    }
  (* It's not possible to do eta-conversion.
     By eta-conversion, it loses its polymorphicity,
     and fails to check against its signature
   *)
  let merge (specs : 'a t list) : 'a t =
    List.fold_left combine (make_empty ()) specs

  type 'a checked =
    { name : OptSpecName.t
    ; meta_vars : string list
    ; help_msg : string option
    ; default_argument : 'a option
    ; condition : ('a -> bool) option
    ; optional : 'a option
    }

  type check_error =
    | NoName

  let check spec =
    let name_result =
      let open OptSpecName in
      match spec.long_name, spec.short_name with
      | None, None -> Error NoName
      | Some ln, None -> Ok (LongName ("--" ^ ln))
      | None, Some sn -> Ok (ShortName ("-" ^ String.make 1 sn))
      | Some ln, Some sn -> Ok (LongAndShortName ("--" ^ ln, "-" ^ String.make 1 sn))
    in
    match name_result with
    | Error e -> Error e
    | Ok name ->
       Ok
         { name
         ; meta_vars = Option.fold ~none:["args"] ~some:id spec.meta_vars
         ; help_msg = spec.help_msg
         ; default_argument = spec.default_argument
         ; condition = spec.condition
         ; optional = spec.optional
         }
end

type opt_parser_error =
  | MissingMandatory
    of string (* option name *)
  | InvalidArgLength
    of string (* option name *)
       * int (* expected number of arguments *)
       * int (* actual number of arguments *)
  | ArgReaderFailure
    of string (* option name *)
  | NotAnOption
    of string (* option name *)

type help_entry =
  OptSpecName.t (* option name *)
  * int (* expected number of arguments *)
  * string list (* names for arguments *)
  * string option (* help message for option *)

type 'a t =
  { opt_tbl : (string, int * ((string -> Format.formatter -> unit -> unit) -> string list -> unit)) Hashtbl.t
  ; get_value : string list -> ('a, opt_parser_error) result
  ; mandatory_help_entries : help_entry list
  ; optional_help_entries : help_entry list
  }

exception SpecError of OptSpec.check_error

let make spec arity arg_parser res_ref =
  { opt_tbl =
      OptSpecName.to_list spec.OptSpec.name
      |> List.to_seq
      |> Seq.map (fun n -> (n, (arity, arg_parser)))
      |> Hashtbl.of_seq
  ; get_value = (fun _ -> !res_ref)
  ; mandatory_help_entries = []
  ; optional_help_entries = []
  }

let opt0 (a : 'a) (specs : 'a OptSpec.t list) : 'a t =
  let open OptSpec in
  let arity = 0 in
  let spec =
    match check (merge specs) with
    | Error e -> raise (SpecError e)
    | Ok s -> s
  in
  let opt_name = OptSpecName.to_string spec.name in
  let initial_res =
    match spec.optional with
    | Some a -> Ok a
    | None -> Error (MissingMandatory opt_name)
  in
  let res_ref = ref initial_res in
  let arg_parser _ =
    function
    | [] ->
       res_ref := Ok a
    | args ->
       res_ref := Error (InvalidArgLength (opt_name, arity, List.length args))
  in
  let opt = make spec arity arg_parser res_ref in
  let help_entry = [(spec.name, arity, spec.meta_vars, spec.help_msg)] in
  match spec.optional with
  | Some _ ->
     { opt with
       optional_help_entries = opt.optional_help_entries @ help_entry
     }
  | None ->
     { opt with
       mandatory_help_entries = opt.mandatory_help_entries @ help_entry
     }

let opt1 (read_arg : string -> 'a option) (specs : 'a OptSpec.t list) : 'a t =
  let open OptSpec in
  let arity = 1 in
  let spec =
    match check (merge specs) with
    | Error e -> raise (SpecError e)
    | Ok s -> s
  in
  let opt_name = OptSpecName.to_string spec.name in
  let initial_res =
    match spec.optional with
    | Some a -> Ok a
    | None -> Error (MissingMandatory opt_name)
  in
  let res_ref = ref initial_res in
  let arg_parser _ =
    function
    | [] ->
       begin match spec.default_argument with
       | None ->
          res_ref := Error (InvalidArgLength (opt_name, arity, 0))
       | Some defArgVal ->
          res_ref := Ok defArgVal
       end
    | [arg] ->
       begin match read_arg arg with
       | None ->
          res_ref := Error (ArgReaderFailure opt_name)
       | Some x ->
          res_ref := Ok x
       end
    | args ->
       res_ref := Error (InvalidArgLength (opt_name, arity, List.length args))
  in
  let opt = make spec arity arg_parser res_ref in
  let help_entry = [(spec.name, arity, spec.meta_vars, spec.help_msg)] in
  match spec.optional with
  | Some _ ->
     { opt with
       optional_help_entries = opt.optional_help_entries @ help_entry
     }
  | None ->
     { opt with
       mandatory_help_entries = opt.mandatory_help_entries @ help_entry
     }

let bool_opt1 : bool OptSpec.t list -> bool t = opt1 bool_of_string_opt
let int_opt1 : int OptSpec.t list -> int t = opt1 int_of_string_opt
let string_opt1 : string OptSpec.t list -> string t = opt1 Option.some

let switch_opt (specs : unit OptSpec.t list) : bool t =
  let open OptSpec in
  specs
  |> List.map lift
  |> List.append [optional false]
  |> opt0 true

let impure_opt (impure_fn : unit -> 'a) (specs : 'a OptSpec.t list) : 'a t =
  let open OptSpec in
  let arity = 0 in
  let spec =
    match check (merge specs) with
    | Error e -> raise (SpecError e)
    | Ok s -> s
  in
  let opt_name = OptSpecName.to_string spec.name in
  let initial_res =
    match spec.optional with
    | Some a -> Ok a
    | None -> Error (MissingMandatory opt_name)
  in
  let res_ref = ref initial_res in
  let arg_parser _ =
    function
    | [] ->
       res_ref := Ok (impure_fn ())
    | args ->
       res_ref := Error (InvalidArgLength (opt_name, arity, List.length args))
  in
  let opt = make spec arity arg_parser res_ref in
  let help_entry = [(spec.name, arity, spec.meta_vars, spec.help_msg)] in
  match spec.optional with
  | Some _ ->
     { opt with
       optional_help_entries = opt.optional_help_entries @ help_entry
     }
  | None ->
     { opt with
       mandatory_help_entries = opt.mandatory_help_entries @ help_entry
     }

let help_opt (impure_fn : (string -> Format.formatter -> unit -> unit) -> 'a) (specs : 'a OptSpec.t list) : 'a t =
  let open OptSpec in
  let arity = 0 in
  let spec =
    match check (merge specs) with
    | Error e -> raise (SpecError e)
    | Ok s -> s
  in
  let opt_name = OptSpecName.to_string spec.name in
  let initial_res =
    match spec.optional with
    | Some a -> Ok a
    | None -> Error (MissingMandatory opt_name)
  in
  let res_ref = ref initial_res in
  let arg_parser build_help_string =
    function
    | [] ->
       res_ref := Ok (impure_fn build_help_string)
    | args ->
       res_ref := Error (InvalidArgLength (opt_name, arity, List.length args))
  in
  let opt = make spec arity arg_parser res_ref in
  let help_entry = [(spec.name, arity, spec.meta_vars, spec.help_msg)] in
  match spec.optional with
  | Some _ ->
     { opt with
       optional_help_entries = opt.optional_help_entries @ help_entry
     }
  | None ->
     { opt with
       mandatory_help_entries = opt.mandatory_help_entries @ help_entry
     }

let rest_args (impure_fn : string list -> 'a) : 'a t =
  { opt_tbl = Hashtbl.create 0
  ; get_value = (fun args -> Ok (impure_fn args))
  ; mandatory_help_entries = []
  ; optional_help_entries = []
  }

(**
   Following two functions basically forms an interface
   for optparser apply functor (semi-monoidal functor).

   Example usage:
   [ begin fun verbose skipInput ->
     { verbose
     ; skipInput
     }
     end
     <$ switch_opt
        [ OptSpec.long_name "verbose"
        ; OptSpec.short_name 'v'
        ; OptSpec.default_argument false
        ; OptSpec.help_msg
            "for verbose output"
        ]
     <& string_opt1
        [ OptSpec.long_name "skipInput"
        ; OptSpec.default_argument "^$"
        ; OptSpec.help_msg
            "REGEX specifying files to ignore"
        ]
   ]
 *)

let (<$) (f : 'a -> 'b) (opt : 'a t) : 'b t =
  { opt with get_value = fun args -> Result.map f (opt.get_value args)
  }
let (<&) (opt_f : ('a -> 'b) t) (opt_a : 'a t) : 'b t =
  let opt_tbl = Hashtbl.copy opt_f.opt_tbl in
  Hashtbl.add_seq opt_tbl (Hashtbl.to_seq opt_a.opt_tbl);
  { opt_tbl
  ; get_value =
      begin fun args ->
      match opt_f.get_value args with
      | Error e -> Error e
      | Ok f -> Result.map f (opt_a.get_value args)
      end
  ; mandatory_help_entries = opt_f.mandatory_help_entries @ opt_a.mandatory_help_entries
  ; optional_help_entries = opt_f.optional_help_entries @ opt_a.optional_help_entries
  }

(**
   reverse of [(<$)]
 *)
let ($>) opt f : 'b t = f <$ opt

let (<!) (opt_a : 'a t) (opt_impure : unit t) : 'a t =
  let opt_tbl = Hashtbl.copy opt_a.opt_tbl in
  Hashtbl.add_seq opt_tbl (Hashtbl.to_seq opt_impure.opt_tbl);
  { opt_tbl
  ; get_value = opt_a.get_value
  ; mandatory_help_entries = opt_a.mandatory_help_entries
  ; optional_help_entries =
      opt_a.optional_help_entries
      @ opt_impure.mandatory_help_entries
      @ opt_impure.optional_help_entries
  }


let is_opt arg = String.get arg 0 = '-'

let pp_print_help (opt : 'a t) (usage : string) ppf () : unit =
  let take_circularly n ls =
    let rec go n =
      function
      | _ when n <= 0 -> []
      | [] ->
         go n ls
      | x :: xs ->
         x :: go (n - 1) xs
    in
    if ls = []
    then raise (Invalid_argument "'ls' should have more than one element")
    else go n ls
  in
  let entry_to_help_fields (name, arity, meta_vars, desc) =
    let meta_names = take_circularly arity meta_vars in
    (OptSpecName.to_string name ^ " " ^ String.concat " " meta_names, desc)
  in
  let pp_print_desc ppf desc =
    let desc_words = String.split_on_char ' ' desc in
    Format.pp_open_hovbox ppf 0;
    List.iteri
      begin fun idx desc_word ->
      begin
        if idx != 0
        then Format.pp_print_space ppf ();
      end;
      Format.pp_print_string ppf desc_word;
      end
      desc_words;
    Format.pp_close_box ppf ()
  in
  let pp_print_fields max_title_len ppf (title, desc) =
    Format.fprintf ppf "%-*s%a"
      ((max_title_len + 3 + (8 - 1)) / 8 * 8)
      title
      pp_print_desc desc
  in
  let pp_print_fieldss max_title_len ppf fieldss =
    Format.fprintf ppf "@[<v 2>  %a@,@]"
      (Format.pp_print_list ~pp_sep:Format.pp_print_cut (pp_print_fields max_title_len)) fieldss
  in
  let mandatory_fieldss =
    opt.mandatory_help_entries
    |> List.filter_map
         begin fun (name, arity, meta_vars, msg_opt) ->
         Option.map (fun msg -> (name, arity, meta_vars, msg)) msg_opt
         end
    |> List.map entry_to_help_fields
  in
  let optional_fieldss =
    opt.optional_help_entries
    |> List.filter_map
         begin fun (name, arity, meta_vars, msg_opt) ->
         Option.map (fun msg -> (name, arity, meta_vars, msg)) msg_opt
         end
    |> List.map entry_to_help_fields
  in
  let max_title_len =
    mandatory_fieldss @ optional_fieldss
    |> List.map (fun (title, _) -> String.length title)
    |> List.fold_left max 0
  in
  Format.pp_open_vbox ppf 0;
  Format.fprintf ppf "%s@,@,"
    usage;
  Format.fprintf ppf "Mandatory options:@,";
  Format.fprintf ppf "%a"
    (pp_print_fieldss max_title_len) mandatory_fieldss;
  Format.pp_print_cut ppf ();
  Format.fprintf ppf "Optional options:@,";
  Format.fprintf ppf "%a"
    (pp_print_fieldss max_title_len) optional_fieldss;
  Format.pp_close_box ppf ();
  Format.pp_print_newline ppf ()

let parse (opt : 'a t) (args : string list) : ('a, opt_parser_error) result =
  let split n =
    let rec loop n =
      function
      | x :: xs when n > 0 ->
         let (xs', ys) = loop (n - 1) xs in
         (x :: xs', ys)
      | xs -> ([], xs)
    in
    loop n
  in
  let rec go rest_args =
    function
    | [] -> opt.get_value []
    | (arg :: sub_args) ->
       match () with
       | () when is_opt arg ->
          begin match Hashtbl.find_opt opt.opt_tbl arg with
          | Some (arity, fn) ->
             let (fn_args, next_args) = split arity sub_args in
             fn (pp_print_help opt) fn_args;
             go rest_args next_args
          | None ->
             Error (NotAnOption arg)
          end
       | () ->
          go (rest_args @ [arg]) sub_args
  in
  go [] args
