open Support
open Synext_definition
open Common

module type PRINTING_STATE = sig
  include State.STATE

  include Format_state.S with type state := state

  val add_binding : Identifier.t -> Unit.t t

  val add_module : Identifier.t -> 'a t -> 'a t

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

module Printing_state = struct
  type entry = { operator : Operator.t Option.t }

  type state =
    { bindings : entry Binding_tree.t
    ; formatter : Format.formatter
    ; default_precedence : Int.t
    ; default_associativity : Associativity.t
    ; declarations : entry Binding_tree.t
    }

  module S = State.Make (struct
    type t = state
  end)

  include (S : State.STATE with type state := state)

  let with_formatter f =
    let* { formatter; _ } = get in
    f formatter

  include (
    Format_state.Make (struct
      include S

      let with_formatter = with_formatter
    end) :
      Format_state.S with type state := state)

  let make_initial_state formatter =
    { bindings = Binding_tree.empty
    ; formatter
    ; default_precedence
    ; default_associativity
    ; declarations = Binding_tree.empty
    }

  let set_formatter formatter =
    modify (fun state -> { state with formatter })

  let get_bindings =
    let* state = get in
    return state.bindings

  let set_bindings bindings = modify (fun state -> { state with bindings })

  let[@inline] modify_bindings f =
    let* bindings = get_bindings in
    let bindings' = f bindings in
    set_bindings bindings'

  let add_declaration identifier =
    let* bindings = get_bindings in
    let entry, subtree = Binding_tree.lookup_toplevel identifier bindings in
    modify (fun state ->
        let declarations' =
          Binding_tree.add_toplevel identifier entry ~subtree
            state.declarations
        in
        { state with declarations = declarations' })

  let add_binding identifier =
    modify_bindings
      (Binding_tree.add_toplevel identifier { operator = Option.none })
    <& add_declaration identifier

  let lookup identifier =
    let* bindings = get_bindings in
    return (Binding_tree.lookup identifier bindings)

  let add_synonym qualified_identifier synonym =
    let* entry, subtree = lookup qualified_identifier in
    modify_bindings (Binding_tree.add_toplevel synonym entry ~subtree)

  let add_abbreviation = add_synonym

  let open_namespace qualified_identifier =
    modify_bindings (Binding_tree.open_namespace qualified_identifier)

  let open_module = open_namespace

  let add_module identifier declarations =
    let* state = get in
    let* () = put { state with declarations = Binding_tree.empty } in
    let* declarations' = declarations in
    let* state' = get in
    let* () = put state in
    let* () =
      modify_bindings
        (Binding_tree.add_toplevel identifier ~subtree:state'.declarations
           { operator = Option.none })
      <& add_declaration identifier
    in
    return declarations'

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

  let[@warning "-23"] make_prefix ?precedence constant =
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

  let[@warning "-23"] make_infix ?precedence ?associativity constant =
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

  let[@warning "-23"] make_postfix ?precedence constant =
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
