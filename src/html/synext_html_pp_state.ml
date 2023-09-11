open Support
open Beluga_syntax.Synext

module type HTML_PRINTING_STATE = sig
  type state

  include Format_state.S with type state := state

  include Format_state.S with type state := state

  val set_formatter : state -> Format.formatter -> Unit.t

  val fresh_id : state -> ?prefix:String.t -> Identifier.t -> String.t

  val preallocate_id : state -> ?prefix:String.t -> Identifier.t -> String.t

  val set_current_page : state -> String.t -> Unit.t

  val lookup_reference : state -> Qualified_identifier.t -> String.t

  val lookup_id : state -> Qualified_identifier.t -> String.t

  val open_module : state -> Qualified_identifier.t -> Unit.t

  val add_abbreviation :
    state -> Qualified_identifier.t -> Identifier.t -> Unit.t

  val set_default_associativity : state -> Associativity.t -> Unit.t

  val get_default_associativity : state -> Associativity.t

  val set_default_precedence : state -> Int.t -> Unit.t

  val get_default_precedence : state -> Int.t

  val add_lf_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_lf_term_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_schema_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_inductive_computation_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_stratified_computation_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_coinductive_computation_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_abbreviation_computation_type_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_computation_term_constructor :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_computation_term_destructor :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_program_constant :
    state -> ?location:'a -> Identifier.t -> id:String.t -> Unit.t

  val add_module :
       state
    -> ?location:'a
    -> Identifier.t
    -> id:String.t
    -> (state -> 'a)
    -> 'a

  val add_prefix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  val add_infix_notation :
       state
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  val add_postfix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  val add_postponed_prefix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  val add_postponed_infix_notation :
       state
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  val add_postponed_postfix_notation :
    state -> ?precedence:Int.t -> Qualified_identifier.t -> Unit.t

  val apply_postponed_fixity_pragmas : state -> unit

  val lookup_operator :
    state -> Qualified_identifier.t -> Operator.t Option.t

  val lookup_operator_precedence :
    state -> Qualified_identifier.t -> Int.t Option.t
end

module Html_reference = struct
  type t =
    { page : String.t  (** The relative path to the HTML file. *)
    ; id : String.t  (** The HTML element ID. *)
    }

  let make ~page ~id = { page; id }

  let id reference = reference.id

  let dir_sep_regexp = Str.regexp Filename.dir_sep

  let split_by_dir_sep = Str.split dir_sep_regexp

  (** [relative_file_path ~from ~to_] is the relative path from the file
      [from] to the file [to_].

      This implementation only supports computing the relative path between
      non-absolute paths. Normalization of paths (to remove redundant [..]
      segments) is not performed. *)
  let relative_file_path ~from ~to_ =
    let from_dirname = Filename.dirname from in
    let to_dirname = Filename.dirname to_
    and to_basename = Filename.basename to_ in
    let rec go from_dirname_segments to_dirname_segments =
      match (from_dirname_segments, to_dirname_segments) with
      | x :: xs, y :: ys when String.equal x y -> go xs ys
      | _ ->
          let parent_dir_segments =
            List.rev_map
              (fun _segment -> Filename.parent_dir_name)
              from_dirname_segments
          in
          let segments =
            parent_dir_segments @ to_dirname_segments @ [ to_basename ]
          in
          String.concat Filename.dir_sep segments
    in
    go (split_by_dir_sep from_dirname) (split_by_dir_sep to_dirname)

  let relative_reference ~from reference =
    if String.equal from reference.page then
      Format.asprintf "#%s" reference.id
    else
      Format.asprintf "%s#%s"
        (relative_file_path ~from ~to_:reference.page)
        reference.id
end

module Entry = struct
  type t =
    { reference : Html_reference.t
    ; operator : Operator.t Option.t
    }

  let id entry = Html_reference.id entry.reference

  let reference ~from entry =
    Html_reference.relative_reference ~from entry.reference

  let make_lf_type_constant_entry ?location:_ ~page ~id _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_lf_term_constant_entry ?location:_ ~page ~id _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_inductive_computation_type_constant_entry ?location:_ ~page ~id
      _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_stratified_computation_type_constant_entry ?location:_ ~page ~id
      _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_coinductive_computation_type_constant_entry ?location:_ ~page ~id
      _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_abbreviation_computation_type_constant_entry ?location:_ ~page ~id
      _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_computation_term_constructor_entry ?location:_ ~page ~id
      _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_computation_term_destructor_entry ?location:_ ~page ~id
      _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_program_constant_entry ?location:_ ~page ~id _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_schema_constant_entry ?location:_ ~page ~id _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let make_module_entry ?location:_ ~page ~id _identifier =
    { reference = Html_reference.make ~page ~id; operator = Option.none }

  let modify_operator f entry =
    let operator' = f entry.operator in
    { entry with operator = operator' } [@warning "-23"]
end

module Html_printing_state = struct
  type scope =
    | Module_scope of
        { bindings : Entry.t Binding_tree.t
        ; declarations : Entry.t Binding_tree.t
        ; default_associativity : Associativity.t
        ; default_precedence : Int.t
        }

  (** The type of fixity pragmas that are postponed to be applied at a later
      point. The default precedence and associativity to be used are
      determined where the pragma is declared, hence why those fields are not
      optional like in the external syntax. *)
  type postponed_fixity_pragma =
    | Prefix_fixity of
        { constant : Qualified_identifier.t
        ; precedence : Int.t
        }
    | Infix_fixity of
        { constant : Qualified_identifier.t
        ; precedence : Int.t
        ; associativity : Associativity.t
        }
    | Postfix_fixity of
        { constant : Qualified_identifier.t
        ; precedence : Int.t
        }

  type state =
    { mutable ids : String.Set.t
          (** The set of HTML IDs generated so far. *)
    ; mutable current_page : String.t
    ; mutable max_suffix_by_id : Int.t String.Hashtbl.t
          (** A mapping from HTML IDs to their respective maximum integer
              suffixes. This is an auxiliary data structure to optimize the
              generation of new HTML IDs. *)
    ; mutable formatter : Format.formatter
          (** The formatter for pretty-printing. *)
    ; mutable scopes : scope List1.t
    ; mutable default_precedence : Int.t
          (** The default precedence of user-defined operators. *)
    ; mutable default_associativity : Associativity.t
          (** The default associativity of user-defined operators. *)
    ; mutable postponed_fixity_pragmas : postponed_fixity_pragma List.t
          (** The list of fixity pragmas that refer to constants declared
              immediately after them instead of pragmas declared earlier. *)
    ; preallocated_ids : String.t Identifier.Hashtbl.t
          (** An association from constant identifiers to fresh IDs generated
              before the constant is declared. If an ID is preallocated for a
              given identifier, then generating a fresh ID for that
              identifier instead uses the preallocated ID. This allows for
              postponed fixity pragmas to create the ID for the constant
              declared later in the signature. *)
    }

  include (
    Format_state.Make (struct
      type nonrec state = state

      let get_formatter state = state.formatter
    end) :
      Format_state.S with type state := state)

  let create_module_scope ?(default_precedence = default_precedence)
      ?(default_associativity = default_associativity) () =
    Module_scope
      { bindings = Binding_tree.create ()
      ; declarations = Binding_tree.create ()
      ; default_precedence
      ; default_associativity
      }

  let create_initial_state ~current_page formatter =
    { current_page
    ; formatter
    ; ids = String.Set.empty
    ; max_suffix_by_id = String.Hashtbl.create 16
    ; scopes = List1.singleton (create_module_scope ())
    ; default_precedence
    ; default_associativity
    ; postponed_fixity_pragmas = []
    ; preallocated_ids = Identifier.Hashtbl.create 16
    }

  let set_current_page state current_page =
    state.current_page <- current_page;
    state.ids <- String.Set.empty;
    state.max_suffix_by_id <- String.Hashtbl.create 16

  (** Regular expression for non-digit characters. *)
  let non_digit_regexp = Str.regexp "[^0-9]"

  let search_backward_opt r s last =
    try Option.some (Str.search_backward r s last) with
    | Not_found -> Option.none

  (** [split_id s] is [(s', Option.Some n)] if [s = s' ^ string_of_int n],
      and [(s, Option.None)] if [s] does not end with digits, or if the
      integer suffix does not fit in an {!type:int}. *)
  let split_id s =
    match search_backward_opt non_digit_regexp s (String.length s) with
    | Option.Some first_non_digit_index -> (
        let number_suffix_start_index = first_non_digit_index + 1 in
        match
          Int.of_string_opt (Str.string_after s number_suffix_start_index)
        with
        | Option.None ->
            (* The number suffix is too large to be represented as an
               [int] *)
            (s, Option.none)
        | Option.Some n ->
            let s' = Str.string_before s number_suffix_start_index in
            (s', Option.some n))
    | Option.None -> (s, Option.none)

  (** [generate_id ?prefix identifier state] is a percent-encoded unique ID
      with respect to [state] starting with [prefix] and [identifier]. The ID
      needs to be percent-encoded because [identifier] may contain UTF-8
      characters which cannot be used in HTML anchors and URLs.

      [id] is guaranteed to be unique by optionally appending a numeric
      suffix. *)
  let generate_id state ?(prefix = "") identifier =
    let initial_id = Uri.pct_encode (prefix ^ Identifier.name identifier) in
    let base, suffix_opt = split_id initial_id in
    let id' =
      if String.Set.mem initial_id state.ids then (
        (* [initial_id] would conflict with other IDs, so renumber it *)
        let suffix' =
          match String.Hashtbl.find_opt state.max_suffix_by_id base with
          | Option.None -> 1
          | Option.Some max_suffix -> max_suffix + 1
        in
        String.Hashtbl.add state.max_suffix_by_id base suffix';
        base ^ Int.show suffix')
      else (
        (* [initial_id] won't conflict with other IDs *)
        (match suffix_opt with
        | Option.None -> ()
        | Option.Some suffix ->
            String.Hashtbl.add state.max_suffix_by_id base suffix);
        initial_id)
    in
    state.ids <- String.Set.add id' state.ids;
    id'

  let fresh_id state ?prefix identifier =
    match Identifier.Hashtbl.find_opt state.preallocated_ids identifier with
    | Option.Some id ->
        (* Claim the preallocated ID *)
        Identifier.Hashtbl.remove state.preallocated_ids identifier;
        id
    | Option.None ->
        (* Generate a new ID *)
        generate_id state ?prefix identifier

  let preallocate_id state ?prefix identifier =
    match Identifier.Hashtbl.find_opt state.preallocated_ids identifier with
    | Option.Some id -> (* Reuse already preallocated ID *) id
    | Option.None ->
        let id = generate_id state ?prefix identifier in
        Identifier.Hashtbl.add state.preallocated_ids identifier id;
        id

  let set_formatter state formatter = state.formatter <- formatter

  let get_scope_bindings = function
    | Module_scope { bindings; _ } -> bindings

  let get_current_scope state = List1.head state.scopes

  let get_current_scope_bindings state =
    get_scope_bindings (get_current_scope state)

  let push_scope state scope = state.scopes <- List1.cons scope state.scopes

  let pop_scope state =
    match state.scopes with
    | List1.T (x1, x2 :: xs) ->
        state.scopes <- List1.from x2 xs;
        x1
    | List1.T (_x, []) ->
        Error.raise_violation
          (Format.asprintf "[%s] cannot pop the last scope" __FUNCTION__)

  let set_default_associativity state default_associativity =
    state.default_associativity <- default_associativity

  let get_default_associativity state = state.default_associativity

  let get_default_associativity_opt state = function
    | Option.None -> get_default_associativity state
    | Option.Some associativity -> associativity

  let get_default_precedence state = state.default_precedence

  let set_default_precedence state default_precedence =
    state.default_precedence <- default_precedence

  let get_default_precedence_opt state = function
    | Option.None -> get_default_precedence state
    | Option.Some precedence -> precedence

  let add_binding state identifier ?subtree entry =
    match get_current_scope state with
    | Module_scope { bindings; _ } ->
        Binding_tree.add_toplevel identifier entry ?subtree bindings

  let add_declaration state identifier ?subtree entry =
    match get_current_scope state with
    | Module_scope
        { bindings
        ; declarations
        ; default_associativity = _
        ; default_precedence = _
        } ->
        Binding_tree.add_toplevel identifier entry ?subtree bindings;
        Binding_tree.add_toplevel identifier entry ?subtree declarations

  let add_lf_type_constant state ?location identifier ~id =
    add_declaration state identifier
      (Entry.make_lf_type_constant_entry ?location ~page:state.current_page
         ~id identifier)

  let add_lf_term_constant state ?location identifier ~id =
    add_declaration state identifier
      (Entry.make_lf_term_constant_entry ?location ~page:state.current_page
         ~id identifier)

  let add_schema_constant state ?location identifier ~id =
    add_declaration state identifier
      (Entry.make_schema_constant_entry ?location ~page:state.current_page
         ~id identifier)

  let add_inductive_computation_type_constant state ?location identifier ~id
      =
    add_declaration state identifier
      (Entry.make_inductive_computation_type_constant_entry ?location
         ~page:state.current_page ~id identifier)

  let add_stratified_computation_type_constant state ?location identifier ~id
      =
    add_declaration state identifier
      (Entry.make_stratified_computation_type_constant_entry ?location
         ~page:state.current_page ~id identifier)

  let add_coinductive_computation_type_constant state ?location identifier
      ~id =
    add_declaration state identifier
      (Entry.make_coinductive_computation_type_constant_entry ?location
         ~page:state.current_page ~id identifier)

  let add_abbreviation_computation_type_constant state ?location identifier
      ~id =
    add_declaration state identifier
      (Entry.make_abbreviation_computation_type_constant_entry ?location
         ~page:state.current_page ~id identifier)

  let add_computation_term_constructor state ?location identifier ~id =
    add_declaration state identifier
      (Entry.make_computation_term_constructor_entry ?location
         ~page:state.current_page ~id identifier)

  let add_computation_term_destructor state ?location identifier ~id =
    add_declaration state identifier
      (Entry.make_computation_term_destructor_entry ?location
         ~page:state.current_page ~id identifier)

  let add_program_constant state ?location identifier ~id =
    add_declaration state identifier
      (Entry.make_program_constant_entry ?location ~page:state.current_page
         ~id identifier)

  let add_module state ?location identifier ~id f =
    let default_associativity = get_default_associativity state in
    let default_precedence = get_default_precedence state in
    let module_scope =
      create_module_scope ~default_associativity ~default_precedence ()
    in
    push_scope state module_scope;
    let x = f state in
    (match get_current_scope state with
    | Module_scope
        { declarations; default_associativity; default_precedence; _ } ->
        ignore (pop_scope state);
        add_declaration state identifier ~subtree:declarations
          (Entry.make_module_entry ?location ~page:state.current_page ~id
             identifier);
        set_default_associativity state default_associativity;
        set_default_precedence state default_precedence);
    x

  let rec lookup_in_scopes scopes identifiers =
    match scopes with
    | [] ->
        Error.raise
          (Qualified_identifier.Unbound_qualified_identifier
             (Qualified_identifier.from_list1 identifiers))
    | scope :: scopes -> (
        match
          Binding_tree.maximum_lookup identifiers (get_scope_bindings scope)
        with
        | Binding_tree.Bound { entry; subtree; _ } -> (entry, subtree)
        | Binding_tree.Partially_bound { leading_segments; segment; _ } ->
            Error.raise
              (Qualified_identifier.Unbound_namespace
                 (Qualified_identifier.make ~namespaces:leading_segments
                    segment))
        | Binding_tree.Unbound _ -> lookup_in_scopes scopes identifiers)

  let lookup state query =
    let identifiers = Qualified_identifier.to_list1 query in
    try lookup_in_scopes (List1.to_list state.scopes) identifiers with
    | exn ->
        Error.re_raise
          (Error.located_exception1
             (Qualified_identifier.location query)
             exn)

  let lookup_id state query =
    let entry, _subtree = lookup state query in
    Entry.id entry

  let lookup_reference state query =
    let entry, _subtree = lookup state query in
    Entry.reference ~from:state.current_page entry

  let lookup_operator state constant =
    let entry, _subtree = lookup state constant in
    entry.Entry.operator

  let lookup_operator_precedence state constant =
    Option.map Operator.precedence (lookup_operator state constant)

  let modify_operator state identifier f =
    let entry, subtree = lookup state identifier in
    let entry' = Entry.modify_operator f entry in
    let bindings = get_current_scope_bindings state in
    if Binding_tree.mem identifier bindings then
      Binding_tree.replace identifier
        (fun _entry _subtree -> (entry', subtree))
        bindings
    else Binding_tree.add identifier ~subtree entry' bindings;
    match get_current_scope state with
    | Module_scope { declarations; _ } ->
        if Binding_tree.mem identifier declarations then
          Binding_tree.replace identifier
            (fun _entry subtree -> (entry', subtree))
            declarations
        else ()

  let add_prefix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    modify_operator state constant (fun _operator ->
        Option.some (Operator.make_prefix ~precedence))

  let add_infix_notation state ?precedence ?associativity constant =
    let precedence = get_default_precedence_opt state precedence in
    let associativity = get_default_associativity_opt state associativity in
    modify_operator state constant (fun _operator ->
        Option.some (Operator.make_infix ~precedence ~associativity))

  let add_postfix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    modify_operator state constant (fun _operator ->
        Option.some (Operator.make_postfix ~precedence))

  let add_postponed_notation state pragma =
    state.postponed_fixity_pragmas <-
      pragma :: state.postponed_fixity_pragmas

  let add_postponed_prefix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    add_postponed_notation state (Prefix_fixity { precedence; constant })

  let add_postponed_infix_notation state ?precedence ?associativity constant
      =
    let precedence = get_default_precedence_opt state precedence in
    let associativity = get_default_associativity_opt state associativity in
    add_postponed_notation state
      (Infix_fixity { precedence; associativity; constant })

  let add_postponed_postfix_notation state ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    add_postponed_notation state (Postfix_fixity { precedence; constant })

  let apply_postponed_fixity_pragmas =
    let apply_postponed_fixity_pragma state = function
      | Prefix_fixity { constant; precedence } ->
          add_prefix_notation state ~precedence constant
      | Infix_fixity { constant; precedence; associativity } ->
          add_infix_notation state ~precedence ~associativity constant
      | Postfix_fixity { constant; precedence } ->
          add_postfix_notation state ~precedence constant
    in
    fun state ->
      List.iter_rev
        (apply_postponed_fixity_pragma state)
        state.postponed_fixity_pragmas;
      state.postponed_fixity_pragmas <- []

  let open_namespace state identifier =
    let _entry, subtree = lookup state identifier in
    let bindings = get_current_scope_bindings state in
    Binding_tree.add_all bindings subtree

  let open_module state identifier = open_namespace state identifier

  let add_synonym state ?location:_ qualified_identifier synonym =
    let entry, subtree = lookup state qualified_identifier in
    add_binding state synonym ~subtree entry

  let add_abbreviation state module_identifier abbreviation =
    add_synonym state module_identifier abbreviation
end
