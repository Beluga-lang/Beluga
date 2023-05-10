open Support

module O = Options

open Beluga
open Beluga_syntax.Syncom
open Synint

module P = Prettyint.DefaultPrinter

module Disambiguation_state = Beluga_parser.Parser.Disambiguation_state
module Indexing_state = Beluga.Index_state.Indexing_state

(** A computed value of type 'a or a function to print an error. *)
type 'a e = (Format.formatter -> unit -> unit, 'a) Either.t

(** Runs the given function, trapping exceptions in Either.t
    and converting the exception to a function that prints the
    error with a given formatter.
 *)
let run_safe (f : unit -> 'a) : 'a e =
  try
    Either.right (f ())
  with
  | IO.Io_error e ->
     let s = Printexc.to_string e in
     Either.left (fun ppf () -> Format.fprintf ppf "%s@\n" s)
  | Prover.Prover_error e ->
     let s = Printexc.to_string e in
     Either.left (fun ppf () -> Format.fprintf ppf "%s@\n" s)
  | e ->
     let s = Printexc.to_string e in
     let bt = Printexc.get_backtrace () in
     Either.left (fun ppf () ->
       Format.fprintf ppf
         "@[<v>Internal error. (State may be undefined.)@,%s@,%s@]"
         s bt)

let rec loop (s : HarpoonState.t) : unit =
  let printf x = HarpoonState.printf s x in
  match HarpoonState.next_substate s with
  | exception HarpoonState.No_session ->
     if HarpoonState.session_configuration_wizard s then
       loop s
     else
       printf "@,Harpoon terminated.@,"
  | exception HarpoonState.No_theorem c ->
     printf "@,No theorems left. Checking translated proofs.@,";
     begin match Session.check_translated_proofs c with
     | `ok ->
        printf "- Translated proofs successfully checked.@,"
     | `some_translations_failed ->
        printf "- @[%a@]@,"
          Format.pp_print_text
          "Skipped checking translated proofs because some translations failed.";
          if HarpoonState.interaction_mode s = `stop then
            exit 1
     | `check_error e ->
        printf "- @[<v>An error occurred when checking the translated proofs.\
                @,Please report this as a bug.\
                @,@[%s@]@]@,"
          (Printexc.to_string e);
        if HarpoonState.interaction_mode s = `stop then
          exit 1
     end;
     printf "@,@[<v>Proof complete! (No theorems left.)@,@]";
     HarpoonState.on_session_completed s c;
     loop s
  | exception HarpoonState.No_subgoal { session = c; theorem = t } ->
     (* TODO: record the proof into the Store *)
     let e_trans = Translate.entry (Theorem.get_entry t) in
     printf
       "@[<v>Subproof complete! (No subgoals left.)\
        @,Full proof script:\
        @,  @[<v>%a@]\
        @,@[<v>%a@]@]"
       Theorem.dump_proof t
       Translate.fmt_ppr_result e_trans;
     Session.mark_current_theorem_as_proven c (Either.to_option e_trans);
     loop s
  | { HarpoonState.session = c; theorem = t; proof_state = g } as substate -> (
      (* Show the proof state and the prompt *)
      printf "@,@[<v>@,Theorem: %a@,%a@,@]@?" Name.pp (Theorem.get_name t)
        P.fmt_ppr_cmp_proof_state g;

      (* Parse the input and run the command *)
      match
        run_safe (fun () ->
            HarpoonState.with_io s (fun io ->
                Session.with_disambiguation_state c
                  (fun disambiguation_state ->
                    Session.with_indexing_state c (fun indexing_state ->
                        IO.prompt_input io ~msg:"> " ~history_file:None
                          (fun location input ->
                            Prover.process_command
                              ( disambiguation_state
                              , indexing_state
                              , s
                              , substate )
                              location input)))))
      with
      | Either.Left f ->
          printf "%a" f ();
          if HarpoonState.interaction_mode s = `stop then exit 1
      | Either.Right () -> loop s)

let start
      (disambiguation_states, disambiguation_state)
      (indexing_states, indexing_state)
      save_back
      (stop : O.interaction_mode)
      (sig_path : string)
      (all_paths : string list)
      (gs : Comp.open_subgoal list)
      (io : IO.t)
    : unit =
  let s =
    HarpoonState.make
      (disambiguation_states, disambiguation_state)
      (indexing_states, indexing_state)
      save_back
      stop
      sig_path
      all_paths
      io
      gs
  in
  (* If no sessions were created by loading the subgoal list
     then (it must have been empty so) we need to create the default
     session and configure it. *)
  Gensym.reset ();
  if HarpoonState.is_complete s then
    (if HarpoonState.session_configuration_wizard s then loop s else ())
  else loop s
