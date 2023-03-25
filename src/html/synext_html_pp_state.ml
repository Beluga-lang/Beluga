open Support
open Beluga_syntax
open Synext

module type HTML_PRINTING_STATE = sig
  include State.STATE

  include Format_state.S with type state := state

  val fresh_id : ?prefix:String.t -> Identifier.t -> String.t t

  val add_binding : Identifier.t -> id:String.t -> Unit.t t

  val add_module : Identifier.t -> id:String.t -> 'a t -> 'a t

  val lookup_id : Qualified_identifier.t -> String.t t

  val open_module : Qualified_identifier.t -> Unit.t t

  val add_abbreviation : Qualified_identifier.t -> Identifier.t -> Unit.t t

  val set_default_associativity : Associativity.t -> Unit.t t

  val get_default_associativity : Associativity.t t

  val set_default_precedence : Int.t -> Unit.t t

  val get_default_precedence : Int.t t

  val make_prefix : ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  val make_infix :
       ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t t

  val make_postfix : ?precedence:Int.t -> Qualified_identifier.t -> Unit.t t

  val lookup_operator : Qualified_identifier.t -> Operator.t Option.t t
end

module Html_printing_state : sig
  include HTML_PRINTING_STATE

  val make_initial_state : Format.formatter -> state
end = struct
  module Binding_tree = Binding_tree.Hamt

  type entry =
    { id : String.t
    ; operator : Operator.t Option.t
    }

  type state =
    { bindings : entry Binding_tree.t
          (** The binding tree of bound constants. *)
    ; ids : String.Set.t  (** The set of HTML IDs generated so far. *)
    ; max_suffix_by_id : Int.t String.Hamt.t
          (** A mapping from HTML IDs to their respective maximum integer
              suffixes. This is an auxiliary data structure to optimize the
              generation of new HTML IDs. *)
    ; formatter : Format.formatter  (** The formatter for pretty-printing. *)
    ; default_associativity : Associativity.t
          (** The default associativity of user-defined operators. *)
    ; default_precedence : Int.t
          (** The default precedence of user-defined operators. *)
    ; declarations : entry Binding_tree.t
          (** The active module's declarations. The signature counts as an
              outermost module. *)
    }

  module S = State.Make (struct
    type t = state
  end)

  include (S : State.STATE with type state := state)

  let with_formatter f =
    let* state = get in
    f state.formatter

  include (
    Format_state.Make (struct
      include S

      let with_formatter = with_formatter
    end) :
      Format_state.S with type state := state)

  let make_initial_state formatter =
    { bindings = Binding_tree.empty
    ; ids = String.Set.empty
    ; max_suffix_by_id = String.Hamt.empty
    ; formatter
    ; default_precedence = Synext.default_precedence
    ; default_associativity = Synext.default_associativity
    ; declarations = Binding_tree.empty
    }

  let get_bindings =
    let* state = get in
    return state.bindings

  let set_bindings bindings = modify (fun state -> { state with bindings })

  let[@inline] modify_bindings f =
    let* bindings = get_bindings in
    let bindings' = f bindings in
    set_bindings bindings'

  let get_ids =
    let* state = get in
    return state.ids

  let set_ids ids = modify (fun state -> { state with ids })

  let[@inline] modify_ids f =
    let* ids = get_ids in
    let ids' = f ids in
    set_ids ids'

  let get_max_suffix_by_id =
    let* state = get in
    return state.max_suffix_by_id

  let set_max_suffix_by_base max_suffix_by_id =
    modify (fun state -> { state with max_suffix_by_id })

  let[@inline] modify_max_suffix_by_id f =
    let* max_suffix_by_id = get_max_suffix_by_id in
    let max_suffix_by_id' = f max_suffix_by_id in
    set_max_suffix_by_base max_suffix_by_id'

  let add_declaration identifier =
    let* bindings = get_bindings in
    let entry, subtree = Binding_tree.lookup_toplevel identifier bindings in
    modify (fun state ->
        let declarations' =
          Binding_tree.add_toplevel identifier entry ~subtree
            state.declarations
        in
        { state with declarations = declarations' })

  (** Regular expression for non-digit characters. *)
  let non_digit_regexp = Str.regexp "[^0-9]"

  (** [split_id s] is [(s', Option.Some n)] if [s = s' ^ string_of_int n],
      and [(s, Option.None)] if [s] does not end with digits, or if the
      integer suffix does not fit in an {!type:int}. *)
  let split_id s =
    try
      let pos =
        Str.search_backward non_digit_regexp s (String.length s) + 1
      in
      let s' = Str.string_before s pos in
      let n = Int.of_string_opt (Str.string_after s pos) in
      (s', n)
    with
    | Not_found -> (* [Str.search_backward] failed *) (s, Option.none)

  (** [fresh_id ?prefix identifier state] is [(state', id)] where [id] is a
      percent-encoded unique ID with respect to [state] starting with
      [prefix] and [identifier]. The ID needs to be percent-encoded because
      [identifier] may contain UTF-8 characters which may not be used in HTML
      anchors.

      [id] is guaranteed to be unique by optionally appending a numeric
      suffix. *)
  let fresh_id ?(prefix = "") identifier =
    let initial_id = Uri.pct_encode (prefix ^ Identifier.name identifier) in
    let base, suffix_opt = split_id initial_id in
    let* ids = get_ids in
    let* max_suffix_by_id = get_max_suffix_by_id in
    let* id' =
      if String.Set.mem initial_id ids then
        (* [initial_id] would conflict with other IDs, so renumber it *)
        let* suffix' =
          match String.Hamt.find_opt base max_suffix_by_id with
          | Option.None -> return 1
          | Option.Some max_suffix -> return (max_suffix + 1)
        in
        let* () = modify_max_suffix_by_id (String.Hamt.add base suffix') in
        return (base ^ Int.show suffix')
      else
        (* [initial_id] won't conflict with other IDs *)
        let* () =
          match suffix_opt with
          | Option.None -> return ()
          | Option.Some suffix ->
              modify_max_suffix_by_id (String.Hamt.add base suffix)
        in
        return initial_id
    in
    let* () = modify_ids (String.Set.add id') in
    return id'

  let add_binding identifier ~id =
    modify_bindings
      (Binding_tree.add_toplevel identifier { id; operator = Option.none })
    <& add_declaration identifier

  let lookup identifier =
    let* bindings = get_bindings in
    return (Binding_tree.lookup identifier bindings)

  let lookup_id identifier =
    let* { id; _ }, _ = lookup identifier in
    return id

  let add_synonym qualified_identifier synonym =
    let* entry, subtree = lookup qualified_identifier in
    modify_bindings (Binding_tree.add_toplevel synonym entry ~subtree)

  let add_abbreviation = add_synonym

  let open_namespace qualified_identifier =
    modify_bindings (Binding_tree.open_namespace qualified_identifier)

  let open_module = open_namespace

  let add_module identifier ~id m =
    let* state = get in
    let* () = put { state with declarations = Binding_tree.empty } in
    let* x = m in
    let* state' = get in
    (* Restore the state to what it was before printing the module's
       declarations, but keep the final state's ID-generation data
       structures *)
    let* () =
      put
        { state with
          ids = state'.ids
        ; max_suffix_by_id = state'.max_suffix_by_id
        }
    in
    let* () =
      modify_bindings
        (Binding_tree.add_toplevel identifier ~subtree:state'.declarations
           { id; operator = Option.none })
      <& add_declaration identifier
    in
    return x

  let set_default_associativity default_associativity =
    modify (fun state -> { state with default_associativity })

  let get_default_associativity =
    let* state = get in
    return state.default_associativity

  let get_default_associativity_opt = function
    | Option.None -> get_default_associativity
    | Option.Some associativity -> return associativity

  let get_default_precedence =
    let* state = get in
    return state.default_precedence

  let set_default_precedence default_precedence =
    modify (fun state -> { state with default_precedence })

  let get_default_precedence_opt = function
    | Option.None -> get_default_precedence
    | Option.Some precedence -> return precedence

  let lookup_operator constant =
    let* { operator; _ }, _subtree = lookup constant in
    return operator

  let make_prefix ?precedence constant =
    let* precedence = get_default_precedence_opt precedence in
    modify_bindings (fun bindings ->
        Binding_tree.replace constant
          (fun entry subtree ->
            let entry' =
              { entry with
                operator = Option.some (Operator.make_prefix ~precedence)
              }
            in
            (entry', subtree))
          bindings)

  let make_infix ?precedence ?associativity constant =
    let* precedence = get_default_precedence_opt precedence in
    let* associativity = get_default_associativity_opt associativity in
    modify_bindings (fun bindings ->
        Binding_tree.replace constant
          (fun entry subtree ->
            let entry' =
              { entry with
                operator =
                  Option.some
                    (Operator.make_infix ~precedence ~associativity)
              }
            in
            (entry', subtree))
          bindings)

  let make_postfix ?precedence constant =
    let* precedence = get_default_precedence_opt precedence in
    modify_bindings (fun bindings ->
        Binding_tree.replace constant
          (fun entry subtree ->
            let entry' =
              { entry with
                operator = Option.some (Operator.make_postfix ~precedence)
              }
            in
            (entry', subtree))
          bindings)
end
