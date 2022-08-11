open Support
open Beluga
open Synprs_to_synext'

module Dictionary_constructors = struct
  type tag =
    | LF_term
    | LF_type_constant
    | LF_term_constant
    | Module

  type t = (QualifiedIdentifier.t * tag) List.t * Dictionary.t

  let tag_equal_to_dictionary_entry tag entry =
    match (tag, entry) with
    | LF_term, Dictionary.LF_term -> true
    | LF_term_constant, Dictionary.LF_term_constant _ -> true
    | LF_type_constant, Dictionary.LF_type_constant _ -> true
    | Module, Dictionary.Module _ -> true
    | _ -> false

  let symmetric_difference associations dictionary =
    let bindings = List.of_seq @@ Dictionary.to_seq dictionary in
    let a (* associations - dictionary *) =
      List.filter
        (fun (qualified_identifier, tag) ->
          Bool.not
          @@ List.exists
               (fun (qualified_identifier', entry) ->
                 QualifiedIdentifier.equal qualified_identifier
                   qualified_identifier'
                 && tag_equal_to_dictionary_entry tag entry)
               bindings)
        associations
    and b (* dictionary - associations *) =
      List.filter
        (fun (qualified_identifier, entry) ->
          Bool.not
          @@ List.exists
               (fun (qualified_identifier', tag) ->
                 QualifiedIdentifier.equal qualified_identifier
                   qualified_identifier'
                 && tag_equal_to_dictionary_entry tag entry)
               associations)
        bindings
    in
    (a, b)

  let empty = ([], Dictionary.empty)

  let add_enclosing_modules new_entry visible_bindings =
    let modules = QualifiedIdentifier.modules new_entry in
    let rec add k visible_bindings =
      if k = 0 then visible_bindings
      else
        let[@warning "-8"] modules, head :: _ = List.take (k - 1) modules in
        let qualified_identifier =
          QualifiedIdentifier.make ~location:Location.ghost ~modules head
        in
        add (k - 1)
          ((qualified_identifier, Module)
          :: List.remove_assoc qualified_identifier visible_bindings)
    in
    add (List.length modules) visible_bindings

  let add qualified_identifier tag action (visible_bindings, dictionary) =
    let visible_bindings' =
      (qualified_identifier, tag)
      :: List.remove_assoc qualified_identifier
           (add_enclosing_modules qualified_identifier visible_bindings)
    and dictionary' = action qualified_identifier dictionary in
    (visible_bindings', dictionary')

  let add_term identifier =
    let qualified_identifier = QualifiedIdentifier.make_simple identifier in
    add qualified_identifier LF_term (fun _ ->
        Dictionary.add_term identifier)

  let add_prefix_lf_type_constant qualified_identifier =
    add qualified_identifier LF_type_constant
      (Dictionary.add_prefix_lf_type_constant ~arity:0 ~precedence:0)

  let add_infix_lf_type_constant qualified_identifier =
    add qualified_identifier LF_type_constant
      (Dictionary.add_infix_lf_type_constant
         ~associativity:Associativity.left_associative ~precedence:0)

  let add_postfix_lf_type_constant qualified_identifier =
    add qualified_identifier LF_type_constant
      (Dictionary.add_postfix_lf_type_constant ~arity:0 ~precedence:0)

  let add_prefix_lf_term_constant qualified_identifier =
    add qualified_identifier LF_term_constant
      (Dictionary.add_prefix_lf_term_constant ~arity:0 ~precedence:0)

  let add_infix_lf_term_constant qualified_identifier =
    add qualified_identifier LF_term_constant
      (Dictionary.add_infix_lf_term_constant
         ~associativity:Associativity.left_associative ~precedence:0)

  let add_postfix_lf_term_constant qualified_identifier =
    add qualified_identifier LF_term_constant
      (Dictionary.add_postfix_lf_term_constant ~arity:0 ~precedence:0)
end

let id x = Identifier.make ~location:Location.ghost x

let qid ?m x =
  QualifiedIdentifier.make ~location:Location.ghost
    ?modules:(Option.map (List.map id) m)
    (id x)

let test_dictionary =
  let pp_symmetric_difference ppf (a, b) =
    Format.fprintf ppf
      "Recorded associations not in dictionary:@ [@[<2>%a@]]@.Dictionary \
       entries not in recorded associations:@ [@[<2>%a@]]@."
      (List.pp
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
         (fun ppf (qualified_identifier, _) ->
           Format.fprintf ppf "%a" QualifiedIdentifier.pp
             qualified_identifier))
      a
      (List.pp
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
         (fun ppf (qualified_identifier, _) ->
           Format.fprintf ppf "%a" QualifiedIdentifier.pp
             qualified_identifier))
      b
  in
  let test actions _test_ctxt =
    let associations, dictionary =
      List.fold_left ( |> ) Dictionary_constructors.empty actions
    in
    let ((a, b) as symmetric_difference) =
      Dictionary_constructors.symmetric_difference associations dictionary
    in
    OUnit2.assert_bool
      (Format.asprintf "%a" pp_symmetric_difference symmetric_difference)
      (List.null a && List.null b)
  in
  let test_cases =
    let open Dictionary_constructors in
    [ []
    ; [ add_prefix_lf_type_constant (qid "nat") ]
    ; [ add_prefix_lf_type_constant (qid "nat")
      ; add_prefix_lf_term_constant (qid "z")
      ; add_prefix_lf_term_constant (qid "s")
      ]
    ; [ add_prefix_lf_type_constant (qid ~m:[ "Nat" ] "nat")
      ; add_prefix_lf_term_constant (qid ~m:[ "Nat" ] "z")
      ; add_prefix_lf_term_constant (qid ~m:[ "Nat" ] "s")
      ]
    ; [ add_prefix_lf_type_constant (qid ~m:[ "Util"; "Nat" ] "nat")
      ; add_prefix_lf_term_constant (qid ~m:[ "Util"; "Nat" ] "z")
      ; add_prefix_lf_term_constant (qid ~m:[ "Util"; "Nat" ] "s")
      ]
    ; [ add_prefix_lf_term_constant (qid "z")
      ; add_prefix_lf_type_constant (qid "z")
      ]
    ; [ add_prefix_lf_term_constant (qid "nat")
      ; add_prefix_lf_type_constant (qid ~m:[ "nat" ] "z")
      ]
    ]
  in
  test_cases |> List.map (fun actions -> OUnit2.test_case @@ test actions)

let tests =
  let open OUnit2 in
  "Dictionary" >::: test_dictionary
