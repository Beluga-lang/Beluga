open Support
open Beluga

module Mock_dictionary = struct
  type data = Int.t

  type entry =
    | Entry of data
    | Module

  type dictionary = data QualifiedIdentifier.Dictionary.t

  type association = (QualifiedIdentifier.t * entry) List.t

  type t = association * dictionary

  let equal_entry x y =
    match (x, y) with
    | Entry x, QualifiedIdentifier.Dictionary.Entry y -> Stdlib.(x = y)
    | Module, QualifiedIdentifier.Dictionary.Module _ -> true
    | _ -> false

  let symmetric_difference (associations : association)
      (dictionary : dictionary) =
    let bindings =
      List.of_seq @@ QualifiedIdentifier.Dictionary.to_seq dictionary
    in
    let a (* associations - dictionary *) =
      List.filter
        (fun (qualified_identifier, entry) ->
          Bool.not
          @@ List.exists
               (fun (qualified_identifier', entry') ->
                 QualifiedIdentifier.equal qualified_identifier
                   qualified_identifier'
                 && equal_entry entry entry')
               bindings)
        associations
    and b (* dictionary - associations *) =
      List.filter
        (fun (qualified_identifier, entry) ->
          Bool.not
          @@ List.exists
               (fun (qualified_identifier', entry') ->
                 QualifiedIdentifier.equal qualified_identifier
                   qualified_identifier'
                 && equal_entry entry' entry)
               associations)
        bindings
    in
    (a, b)

  let empty : t = ([], QualifiedIdentifier.Dictionary.empty)

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

  let add : QualifiedIdentifier.t -> Int.t -> t -> t =
   fun qualified_identifier value (visible_bindings, dictionary) ->
    let visible_bindings' =
      (qualified_identifier, Entry value)
      :: List.remove_assoc qualified_identifier
           (add_enclosing_modules qualified_identifier visible_bindings)
    and dictionary' =
      QualifiedIdentifier.Dictionary.add_entry qualified_identifier value
        dictionary
    in
    (visible_bindings', dictionary')
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
      List.fold_left ( |> ) Mock_dictionary.empty actions
    in
    let ((a, b) as symmetric_difference) =
      Mock_dictionary.symmetric_difference associations dictionary
    in
    OUnit2.assert_bool
      (Format.asprintf "%a" pp_symmetric_difference symmetric_difference)
      (List.null a && List.null b)
  in
  let test_cases =
    let open Mock_dictionary in
    [ []
    ; [ add (qid "nat") 1 ]
    ; [ add (qid "nat") 1; add (qid "z") 2; add (qid "s") 3 ]
    ; [ add (qid "nat") 1
      ; add (qid "z") 2
      ; add (qid "s") 3
      ; add (qid "z") 4
      ]
    ; [ add (qid ~m:[ "Nat" ] "nat") 1
      ; add (qid ~m:[ "Nat" ] "z") 2
      ; add (qid ~m:[ "Nat" ] "s") 3
      ]
    ; [ add (qid ~m:[ "Util"; "Nat" ] "nat") 1
      ; add (qid ~m:[ "Util"; "Nat" ] "z") 2
      ; add (qid ~m:[ "Util"; "Nat" ] "s") 3
      ]
    ; [ add (qid "z") 1; add (qid "z") 2 ]
    ; [ add (qid "nat") 1; add (qid ~m:[ "nat" ] "z") 2 ]
    ]
  in
  test_cases |> List.map (fun actions -> OUnit2.test_case @@ test actions)

let tests =
  let open OUnit2 in
  "QualifiedIdentifier" >::: [ "Dictionary" >::: test_dictionary ]
