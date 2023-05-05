open Support

module O = Options

open Beluga
open Beluga_syntax.Syncom
open Synint

module P = Prettyint.DefaultPrinter

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
     Either.left
       begin fun ppf () ->
       Format.fprintf ppf "@[<v>%t@]@\n"
         (Error.find_printer e)
       end
  | Prover.Prover_error e ->
     Either.left
       begin fun ppf () ->
       Format.fprintf ppf "@[<v>%t@]@\n"
         (Error.find_printer e)
       end
  | e ->
     let s = Printexc.to_string e in
     let bt = Printexc.get_backtrace () in
     Either.left
       begin fun ppf () ->
       Format.fprintf ppf "@[<v>Internal error. (State may be undefined.)@,%s@,%s@]"
         s bt
       end

(** Parses the user input string and executes it in the given state
    substate.
    The input command sequence must be fully executable in the
    current theorem.
    Returns:
    - `ok: all commands were executed in the current theorem
    - `stopped_short: some commands were not executed because the
      current theorem is over.
    - `error: an error occurred. Commands beyond the failed one were
      not executed.
 *)
let[@warning "-32"] process_command_sequence (index_state, s, substate) cmds =
  let printf x = HarpoonState.printf s x in
  (* Idea:
     - count the commands to run
     - count the commands we were able to process
   *)
  let n = List.length cmds in
  match
    run_safe
      begin fun () ->
      let (k, _) =
        List.fold_left
          begin fun (k, g) cmd ->
          match g with
          | Option.None -> (k, g)
          | Option.Some g ->
             Prover.process_command (index_state, s, { substate with HarpoonState.proof_state = g }) cmd;
             (k + 1, Theorem.next_subgoal substate.HarpoonState.theorem)
          end
          (0, Option.some substate.HarpoonState.proof_state)
          cmds
      in
      n = k
      end
  with
  | Either.Left f ->
     printf "%a" f ();
     if HarpoonState.interaction_mode s = `stop then
       exit 1;
     `error
  | Either.Right b ->
     if b then `ok else `stopped_short

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
  | { HarpoonState.session = c; theorem = t; proof_state = g } ->
    (* Show the proof state and the prompt *)
    printf "@,@[<v>@,Theorem: %a@,%a@,@]@?"
      Name.pp (Theorem.get_name t)
      P.fmt_ppr_cmp_proof_state g;
    (*
      printf "@,@[<v>@,%a@,There are %d IHs.@,@]@?"
      P.fmt_ppr_cmp_proof_state g
      (Context.length Comp.(g.context.cIH));
     *)

    (* Parse the input and run the command *)
    match Obj.magic () (* TODO: Parse, elaborate and process commands *) with
    | `ok | `error -> loop s
    | `stopped_short ->
       printf "@,Warning: theorem proven before all commands were processed.@,"

let start
      save_back
      (stop : O.interaction_mode)
      (sig_path : string)
      (all_paths : string list)
      (gs : Comp.open_subgoal list)
      (io : IO.t)
    : unit =
  let s = HarpoonState.make save_back stop sig_path all_paths io gs in
  (* If no sessions were created by loading the subgoal list
     then (it must have been empty so) we need to create the default
     session and configure it. *)
  Gensym.reset ();
  if HarpoonState.is_complete s then
    (if HarpoonState.session_configuration_wizard s then loop s)
  else loop s
