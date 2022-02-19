(** A module provides the {!parse} function which is a core API of this
    library. The function provides the only way to use {!OptSpec.t}.

    @author Clare Jang *)

let is_short_opt arg = String.get arg 0 = '-' && String.get arg 1 != '-'

let is_long_opt arg = String.get arg 0 = '-'

let pp_print_help (spec : 'a OptSpec.t) (usage : string) ppf () : unit =
  let entry_to_help_fields (name, meta_names, desc) =
    (OptName.to_string name ^ " " ^ String.concat " " meta_names, desc)
  in
  let collect_help_entries_to_help_fields :
      OptSpec.HelpEntry.t list -> (string * string) list =
   fun help_entries ->
    help_entries
    |> List.filter_map
         (fun { OptSpec.HelpEntry.option_name; arguments; help_message } ->
           help_message
           |> Option.map (fun message -> (option_name, arguments, message)) )
    |> List.map entry_to_help_fields
  in
  let pp_print_desc ppf desc =
    let desc_words = String.split_on_char ' ' desc in
    Format.pp_open_hovbox ppf 0 ;
    List.iteri
      (fun idx desc_word ->
        if idx != 0 then Format.pp_print_space ppf () ;
        Format.pp_print_string ppf desc_word )
      desc_words ;
    Format.pp_close_box ppf ()
  in
  let pp_print_fields max_title_len ppf (title, desc) =
    Format.fprintf
      ppf
      "%-*s%a"
      ((max_title_len + 3 + (8 - 1)) / 8 * 8)
      title
      pp_print_desc
      desc
  in
  let pp_print_fieldss max_title_len ppf fieldss =
    Format.fprintf
      ppf
      "@[<v 2>  %a@,@]"
      (Format.pp_print_list
         ~pp_sep:Format.pp_print_cut
         (pp_print_fields max_title_len) )
      fieldss
  in
  let mandatory_fieldss =
    OptSpec.get_mandatory_help_entries spec
    |> collect_help_entries_to_help_fields
  in
  let optional_fieldss =
    OptSpec.get_optional_help_entries spec
    |> collect_help_entries_to_help_fields
  in
  let max_title_len =
    mandatory_fieldss @ optional_fieldss
    |> List.map (fun (title, _) -> String.length title)
    |> List.maximum_element max 0
  in
  Format.pp_open_vbox ppf 0 ;
  Format.fprintf ppf "%s@,@," usage ;
  Format.fprintf ppf "Mandatory options:@," ;
  Format.fprintf ppf "%a" (pp_print_fieldss max_title_len) mandatory_fieldss ;
  Format.pp_print_cut ppf () ;
  Format.fprintf ppf "Optional options:@," ;
  Format.fprintf ppf "%a" (pp_print_fieldss max_title_len) optional_fieldss ;
  Format.pp_close_box ppf () ;
  Format.pp_print_newline ppf ()


(** A function parses command line arguments using ['a OptSpec.t], and
    returns ['a] as the result of the parsing.

    @author Clare Jang *)
let parse (spec : 'a OptSpec.t) (args : string list) :
    ('a, OptSpec.error) result =
  let rec go rest_args =
    let go_for_single_option name sub_args cont =
      match OptSpec.find_opt spec name with
      | Some (Some arity, fn) ->
          let fn_args, next_args = List.split arity sub_args in
          fn (pp_print_help spec) fn_args ;
          cont next_args
      | Some (None, fn) ->
          fn (pp_print_help spec) sub_args ;
          cont []
      | None ->
          Error OptSpec.(`Not_an_option { option_name = name })
    in
    function
    | [] ->
        OptSpec.get_comp_value spec rest_args
    | arg :: sub_args ->
      ( match () with
      | () when is_short_opt arg ->
          let number_of_options = String.length arg - 1 in
          let option_names =
            String.sub arg 1 number_of_options
            |> String.to_seq
            |> Array.of_seq
            |> Array.mapi (fun idx c ->
                   ( "-" ^ String.make 1 c
                   , if idx != number_of_options then [] else sub_args ) )
          in
          Array.fold_right
            (fun (name, sub_args) cont _ ->
              go_for_single_option name sub_args cont )
            option_names
            (go rest_args)
            []
      | () when is_long_opt arg ->
          go_for_single_option arg sub_args (go rest_args)
      | () ->
          go (rest_args @ [ arg ]) sub_args )
  in
  go [] args
