(** A module for the functions that operate on an option and a set of
    options. For example,

    - functions that lift option info into an option
    - functions that merge option sets
    - etc. are included.

    @author Clare Jang *)

type option_error = { option_name : string }

type invalid_arguments_length_error =
  { option_name : string
  ; expected_argument_count : int
  ; actual_argument_count : int
  }

type error =
  [ `Missing_mandatory_option of option_error
  | `Invalid_arguments_length of invalid_arguments_length_error
  | `Argument_reader_failure of option_error
  | `Not_an_option of option_error
  ]

module HelpEntry = struct
  type t =
    { option_name : OptName.t
    ; arguments : string list
    ; help_message : string option
    }
end

type help_printer = string -> Format.formatter -> unit -> unit

(** A type representing the specification of an option set. There are only
    three things a user can do with this type.

    - Add more options
    - Mapping a result value
    - Make a parse function by passing a value of this type to
      {!Parser.parse}

    @author Clare Jang *)
type 'a t =
  { opt_tbl :
      (string, int option * (help_printer -> string list -> unit)) Hashtbl.t
  ; comp_value : string list -> ('a, error) result
  ; mandatory_help_entries : HelpEntry.t list
  ; optional_help_entries : HelpEntry.t list
  }

exception SpecError of OptInfo.check_error

let make infos opt_arity build_arg_parser =
  let info =
    match OptInfo.check (OptInfo.Unchecked.make infos) with
    | Error e ->
        raise (SpecError e)
    | Ok s ->
        s
  in
  let open OptInfo.Checked in
  let option_name = OptName.to_string info.name in
  let initial_res =
    info.optional
    |> Option.to_result ~none:(`Missing_mandatory_option { option_name })
  in
  let res_ref = ref initial_res in
  let opt =
    { opt_tbl =
        OptName.to_list info.name
        |> List.to_seq
        |> Seq.map (fun n -> (n, (opt_arity, build_arg_parser info res_ref)))
        |> Hashtbl.of_seq
    ; comp_value = (fun _ -> !res_ref)
    ; mandatory_help_entries = []
    ; optional_help_entries = []
    }
  in
  let meta_names =
    match opt_arity with
    | Some arity ->
        List.take_circularly arity info.meta_variables
    | None ->
        [ "[" ^ List.hd info.meta_variables ^ "]" ]
  in
  let help_entry =
    [ { HelpEntry.option_name = info.name
      ; arguments = meta_names
      ; help_message = info.help_message
      }
    ]
  in
  match info.optional with
  | Some _ ->
      { opt with
        optional_help_entries = opt.optional_help_entries @ help_entry
      }
  | None ->
      { opt with
        mandatory_help_entries = opt.mandatory_help_entries @ help_entry
      }


let find_opt t name = Hashtbl.find_opt t.opt_tbl name

let get_comp_value t = t.comp_value

let get_mandatory_help_entries t = t.mandatory_help_entries

let get_optional_help_entries t = t.optional_help_entries

(** A function to define an option with no extra arguments.

    @author Clare Jang *)
let opt0 (a : 'a) (infos : 'a OptInfo.Unchecked.transform list) : 'a t =
  let arity = 0 in
  let build_arg_parser info res_ref _ = function
    | [] ->
        res_ref := Ok a
    | args ->
        res_ref :=
          Error
            (`Invalid_arguments_length
              { option_name = OptName.to_string info.OptInfo.Checked.name
              ; expected_argument_count = arity
              ; actual_argument_count = List.length args
              } )
  in
  make infos (Some arity) build_arg_parser


(** A function to define an option with one extra argument.

    @param read_arg a function that parses the extra argument.
    @author Clare Jang *)
let opt1
    (read_arg : string -> 'a option)
    (infos : 'a OptInfo.Unchecked.transform list) : 'a t =
  let arity = 1 in
  let build_arg_parser info res_ref _ =
    let opt_name = OptName.to_string info.OptInfo.Checked.name in
    function
    | [] ->
      ( match info.OptInfo.Checked.default_argument with
      | None ->
          res_ref :=
            Error
              (`Invalid_arguments_length
                { option_name = opt_name
                ; expected_argument_count = arity
                ; actual_argument_count = 0
                } )
      | Some defArgVal ->
          res_ref := Ok defArgVal )
    | [ arg ] ->
      ( match read_arg arg with
      | None ->
          res_ref :=
            Error (`Argument_reader_failure { option_name = opt_name })
      | Some x ->
          res_ref := Ok x )
    | args ->
        res_ref :=
          Error
            (`Invalid_arguments_length
              { option_name = opt_name
              ; expected_argument_count = arity
              ; actual_argument_count = List.length args
              } )
  in
  make infos (Some arity) build_arg_parser


(** A function to define an option with one extra argument which is "true" or
    "false".

    @author Clare Jang *)
let bool_opt1 : bool OptInfo.Unchecked.transform list -> bool t =
  opt1 bool_of_string_opt


(** A function to define an option with one extra argument which is an
    integer.

    @author Clare Jang *)
let int_opt1 : int OptInfo.Unchecked.transform list -> int t =
  opt1 int_of_string_opt


(** A function to define an option with one extra argument which is any
    string without a space.

    @author Clare Jang *)
let string_opt1 : string OptInfo.Unchecked.transform list -> string t =
  opt1 Option.some


(** A function to define an option which does not take any extra arguments,
    and acts as a switch (an option returning boolean based on whether it is
    set or not). Because this function defines a switch, the defined option
    is always optional even when [infos] does not include
    {!OptInfo.optional}. Furthermore, this function ignores
    {!OptInfo.optional} value inside of [infos].

    @author Clare Jang *)
let switch_opt (infos : bool OptInfo.Unchecked.transform list) : bool t =
  infos @ [ OptInfo.Unchecked.erase_default_argument; OptInfo.Unchecked.optional false ]
  |> opt0 true


(** A function to define an option taking all arguments after this, including
    the arguments (options) starting with "-".

    @author Clare Jang *)
let takes_all_opt (infos : string list OptInfo.Unchecked.transform list) :
    string list t =
  let build_arg_parser info res_ref _ = function
    | [] ->
      ( match info.OptInfo.Checked.default_argument with
      | None ->
          res_ref := Ok []
      | Some defArgVal ->
          res_ref := Ok defArgVal )
    | args ->
        res_ref := Ok args
  in
  make infos None build_arg_parser


(** A function to define a no-argument option which includes some impure
    behavior inside of its parsing step. A user probably want to use this
    with {!(<!)}.

    @author Clare Jang *)
let impure_opt0
    (impure_fn : unit -> 'a) (infos : 'a OptInfo.Unchecked.transform list) :
    'a t =
  let arity = 0 in
  let build_arg_parser info res_ref _ =
    let opt_name = OptName.to_string info.OptInfo.Checked.name in
    function
    | [] ->
        res_ref := Ok (impure_fn ())
    | args ->
        res_ref :=
          Error
            (`Invalid_arguments_length
              { option_name = opt_name
              ; expected_argument_count = arity
              ; actual_argument_count = List.length args
              } )
  in
  make infos (Some arity) build_arg_parser


(** A function to define a no-argument option which displays help messsage
    using [print_fn]. A user probably want to use this with {!(<!)}.

    @author Clare Jang *)
let help_opt0
    (print_fn : (string -> Format.formatter -> unit -> unit) -> 'a)
    (infos : 'a OptInfo.Unchecked.transform list) : 'a t =
  let arity = 0 in
  let arg_parser info res_ref build_help_string = function
    | [] ->
        res_ref := Ok (print_fn build_help_string)
    | args ->
        res_ref :=
          Error
            (`Invalid_arguments_length
              { option_name = OptName.to_string info.OptInfo.Checked.name
              ; expected_argument_count = arity
              ; actual_argument_count = List.length args
              } )
  in
  make infos (Some arity) arg_parser


(** A function to handle {i left-over arguments}. The {i left-over arguments}
    include an argument before any options, an argument after all options,
    and an argument between options but not handled by one of them.

    @author Clare Jang *)
let rest_args (impure_fn : string list -> 'a) : 'a t =
  { opt_tbl = Hashtbl.create 0
  ; comp_value = (fun args -> Ok (impure_fn args))
  ; mandatory_help_entries = []
  ; optional_help_entries = []
  }


(** Following two functions basically forms an interface for optparser apply
    functor (semi-monoidal functor).

    Example usage:
    [ begin fun verbose skipInput ->
     { verbose
     ; skipInput
     }
     end
     <$ switch_opt
        \[ OptInfo.Unchecked.long_name "verbose"
        ; OptInfo.Unchecked.short_name 'v'
        ; OptInfo.Unchecked.default_argument false
        ; OptInfo.Unchecked.help_msg
            "for verbose output"
        \]
     <& string_opt1
        \[ OptInfo.Unchecked.long_name "skipInput"
        ; OptInfo.Unchecked.default_argument "^$"
        ; OptInfo.Unchecked.help_msg
            "REGEX infoifying files to ignore"
        \]
   ] *)

(** The map function of optparser functor.

    @author Clare Jang *)
let ( <$ ) (f : 'a -> 'b) (opt : 'a t) : 'b t =
  { opt with comp_value = (fun args -> Result.map f (opt.comp_value args)) }


(** The ap function of optparser apply functor.

    @author Clare Jang *)
let ( <& ) (opt_f : ('a -> 'b) t) (opt_a : 'a t) : 'b t =
  let opt_tbl = Hashtbl.copy opt_f.opt_tbl in
  Hashtbl.add_seq opt_tbl (Hashtbl.to_seq opt_a.opt_tbl) ;
  { opt_tbl
  ; comp_value =
      (fun args ->
        match opt_f.comp_value args with
        | Error e ->
            Error e
        | Ok f ->
            Result.map f (opt_a.comp_value args) )
  ; mandatory_help_entries =
      opt_f.mandatory_help_entries @ opt_a.mandatory_help_entries
  ; optional_help_entries =
      opt_f.optional_help_entries @ opt_a.optional_help_entries
  }


(** reverse of {!(<$)}

    @author Clare Jang *)
let ( $> ) opt f : 'b t = f <$ opt

(** An operator only for adding impure behavior to parsing. This operator
    ignores the result value of the second parameter.

    @author Clare Jang *)
let ( <! ) (opt_a : 'a t) (opt_impure : unit t) : 'a t =
  let opt_tbl = Hashtbl.copy opt_a.opt_tbl in
  Hashtbl.add_seq opt_tbl (Hashtbl.to_seq opt_impure.opt_tbl) ;
  { opt_tbl
  ; comp_value = opt_a.comp_value
  ; mandatory_help_entries = opt_a.mandatory_help_entries
  ; optional_help_entries =
      opt_a.optional_help_entries
      @ opt_impure.mandatory_help_entries
      @ opt_impure.optional_help_entries
  }
