(** Timing utilities for monitoring the execution time of functions.

    This implementation is based on Celf's [Timing] and [Timers] modules.
    https://github.com/clf/celf/blob/404f5f1590fa2166b90312fddaf8a316d13c01af/Timing.sml
    https://github.com/clf/celf/blob/404f5f1590fa2166b90312fddaf8a316d13c01af/Timers.sml

    @author Dimitri Kirchner
    @author Marc-Antoine Ouimet *)

open Support

let on = ref false

let onf = ref false

let output_file = "time.txt"

type timer =
  { label : string
  ; mutable realtime_elapsed : float
  ; mutable utime_elapsed : float
  ; mutable stime_elapsed : float
  }

let timer (timer, f) =
  if !on || !onf then (
    let realtime_before = Unix.gettimeofday () in
    let times_before = Unix.times () in
    let result = f () in
    let times_after = Unix.times () in
    let realtime_after = Unix.gettimeofday () in

    timer.realtime_elapsed <-
      timer.realtime_elapsed +. (realtime_after -. realtime_before);
    timer.utime_elapsed <-
      timer.utime_elapsed
      +. (times_after.Unix.tms_utime -. times_before.Unix.tms_utime);
    timer.stime_elapsed <-
      timer.stime_elapsed
      +. (times_after.Unix.tms_stime -. times_before.Unix.tms_stime);

    result)
  else f ()

let add_all label timers =
  let realtime_elapsed, utime_elapsed, stime_elapsed =
    List.fold_left
      (fun (realtime_elapsed_acc, utime_elapsed_acc, stime_elapsed_acc)
           { realtime_elapsed; utime_elapsed; stime_elapsed; _ } ->
        ( realtime_elapsed +. realtime_elapsed_acc
        , utime_elapsed +. utime_elapsed_acc
        , stime_elapsed +. stime_elapsed_acc ))
      (0., 0., 0.) timers
  in
  { label; realtime_elapsed; utime_elapsed; stime_elapsed }

let make_timer label =
  { label; realtime_elapsed = 0.; utime_elapsed = 0.; stime_elapsed = 0. }

let type_abbrev_kind_check = make_timer "Type abbrev. : Kind Check"

let type_abbrev_type_check = make_timer "Type abbrev. : Type Check"

let ctype_elaboration = make_timer "CType Elaboration"

let ctype_abstraction = make_timer "CType Abstraction"

let ctype_check = make_timer "CType Check"

let datatype_constant_type_elaboration =
  make_timer "Data-type Constant: Type Elaboration"

let datatype_constant_type_abstraction =
  make_timer "Data-type Constant: Type Abstraction"

let datatype_constant_type_check =
  make_timer "Data-type Constant: Type Check"

let codatatype_constant_type_elaboration =
  make_timer "Codata-type Constant: Type Elaboration"

let codatatype_constant_type_abstraction =
  make_timer "Codata-type Constant: Type Abstraction"

let codatatype_constant_type_check =
  make_timer "Codata-type Constant: Type Check"

let type_elaboration = make_timer "Type Elaboration"

let type_abstraction = make_timer "Type Abstraction"

let type_check = make_timer "Type Check"

let function_type_elaboration = make_timer "Function Type Elaboration"

let function_type_abstraction = make_timer "Function Type Abstraction"

let function_type_check = make_timer "Function Type Check"

let function_elaboration = make_timer "Function Elaboration"

let function_abstraction = make_timer "Function Abstraction"

let function_check = make_timer "Function Check"

let constant_elaboration = make_timer "Constant Elaboration"

let constant_abstraction = make_timer "Constant Abstraction"

let constant_check = make_timer "Constant Check"

let normalisation = make_timer "Normalisation"

let elaboration_timers =
  [ ctype_elaboration
  ; datatype_constant_type_elaboration
  ; codatatype_constant_type_elaboration
  ; type_elaboration
  ; function_type_elaboration
  ; function_elaboration
  ; constant_elaboration
  ]

let abstraction_timers =
  [ ctype_abstraction
  ; datatype_constant_type_abstraction
  ; codatatype_constant_type_abstraction
  ; type_abstraction
  ; function_type_abstraction
  ; function_abstraction
  ; constant_abstraction
  ]

let check_timers =
  [ ctype_check
  ; type_abbrev_kind_check
  ; type_abbrev_type_check
  ; datatype_constant_type_check
  ; codatatype_constant_type_check
  ; type_check
  ; function_type_check
  ; function_check
  ; constant_check
  ]

let normalisation_timers = [ normalisation ]

let timers =
  [ `Simple type_abbrev_kind_check
  ; `Simple type_abbrev_type_check
  ; `Simple ctype_elaboration
  ; `Simple ctype_abstraction
  ; `Simple ctype_check
  ; `Simple datatype_constant_type_elaboration
  ; `Simple datatype_constant_type_abstraction
  ; `Simple datatype_constant_type_check
  ; `Simple codatatype_constant_type_elaboration
  ; `Simple codatatype_constant_type_abstraction
  ; `Simple codatatype_constant_type_check
  ; `Simple type_elaboration
  ; `Simple type_abstraction
  ; `Simple type_check
  ; `Simple function_type_elaboration
  ; `Simple function_type_abstraction
  ; `Simple function_type_check
  ; `Simple function_elaboration
  ; `Simple function_abstraction
  ; `Simple function_check
  ; `Simple constant_elaboration
  ; `Simple constant_abstraction
  ; `Simple constant_check
  ; `Simple normalisation
  ; `Aggregate ("Cumulative elaboration", elaboration_timers)
  ; `Aggregate ("Cumulative abstraction", abstraction_timers)
  ; `Aggregate ("Cumulative check", check_timers)
  ; `Aggregate ("Cumulative normalisation", normalisation_timers)
  ]

let whitespaces n = String.init n (fun _index -> ' ')

let indent_data4 data =
  let max_length1, max_length2, max_length3, max_length4 =
    List.fold_left
      (fun (max_length1, max_length2, max_length3, max_length4)
           (element1, element2, element3, element4) ->
        ( Int.max max_length1 (String.length element1)
        , Int.max max_length2 (String.length element2)
        , Int.max max_length3 (String.length element3)
        , Int.max max_length4 (String.length element4) ))
      (0, 0, 0, 0) data
  in
  List.map
    (fun (element1, element2, element3, element4) ->
      ( element1 ^ whitespaces (max_length1 - String.length element1)
      , element2 ^ whitespaces (max_length2 - String.length element2)
      , element3 ^ whitespaces (max_length3 - String.length element3)
      , element4 ^ whitespaces (max_length4 - String.length element4) ))
    data

let float_to_string = Format.asprintf "%.6f"

let pp_timers ppf timers =
  let timers' =
    List.map
      (function
        | `Simple timer -> timer
        | `Aggregate (label, timers) -> add_all label timers)
      timers
  in
  let data =
    ("Steps:", "Real time:", "User time:", "System time:")
    :: List.map
         (fun { label; realtime_elapsed; utime_elapsed; stime_elapsed } ->
           ( label
           , float_to_string realtime_elapsed
           , float_to_string utime_elapsed
           , float_to_string stime_elapsed ))
         timers'
  in
  let data' = indent_data4 data in
  Format.fprintf ppf "@[<v 0>## Timer Information: ##@,%a@]"
    (List.pp ~pp_sep:Format.pp_print_cut
       (fun ppf (element1, element2, element3, element4) ->
         Format.fprintf ppf "@[<h 0>%s  |  %s  |  %s  |  %s  @]" element1
           element2 element3 element4))
    data'

let print_timers () =
  if !on then Format.fprintf Format.std_formatter "@[%a@]@." pp_timers timers
  else if !onf then
    Out_channel.with_open_bin output_file (fun out_channel ->
        Format.fprintf
          (Format.formatter_of_out_channel out_channel)
          "@[%a@]@." pp_timers timers)
