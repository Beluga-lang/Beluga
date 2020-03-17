open Support

module O = Options

open Beluga
open Syntax.Int

module P = Pretty.Int.DefaultPrinter

(** A computed value of type 'a or a function to print an error. *)
type 'a e = (Format.formatter -> unit -> unit, 'a) Either.t

(** Runs the given function, trapping exceptions in Either.t
    and converting the exception to a function that prints the
    error with a given formatter.
 *)
let run_safe (f : unit -> 'a) : 'a e =
  try
    Either.Right (f ())
  with
  | IO.Error.E e ->
     Either.Left
       begin fun ppf () ->
       Format.fprintf ppf "@[<v>%a@]@."
         IO.Error.fmt_ppr e
       end
  | Prover.Error.E e ->
     Either.Left
       begin fun ppf () ->
       Format.fprintf ppf "@[<v>%a@]@."
         Prover.Error.fmt_ppr e
       end
  | e ->
     let s = Printexc.to_string e in
     let bt = Printexc.get_backtrace () in
     Either.Left
       begin fun ppf () ->
       Format.fprintf ppf "@[<v>Internal error. (State may be undefined.)@,%s@,%s@]"
         s bt
       end

(** Parses the user input string and executes it in the given state
    triple.
    The input command sequence must be fully executable in the
    current theorem.
    Returns:
    - `ok: all commands were executed in the current theorem
    - `stopped_short: some commands were not executed because the
      current theorem is over.
    - `error: an error occurred. Commands beyond the failed one were
      not executed.
 *)
let process_command_sequence s (c, t, g) cmds =
  let printf x = State.printf s x in
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
          | None -> (k, g)
          | Some g ->
             Prover.process_command s (c, t, g) cmd;
             (k + 1, Theorem.next_subgoal t)
          end
          (0, Some g)
          cmds
      in
      n = k
      end
  with
  | Either.Left f ->
     printf "%a" f ();
     if State.interaction_mode s = `stop then
       exit 1;
     `error
  | Either.Right b ->
     if b then `ok else `stopped_short

let rec loop (s : State.t) : unit =
  let printf x = State.printf s x in
  match State.next_triple s with
  | Either.Left `no_session ->
     if State.session_configuration_wizard s then
       loop s
     else
       printf "@,Harpoon terminated.@,"
  | Either.Left (`no_theorem c) ->
     printf "@,@[<v>Proof complete! (No theorems left.)@,";
     begin match Session.check_translated_proofs c with
     | `ok ->
        printf "- Translated proofs successfully checked.@,"
     | `some_translations_failed ->
        printf "- @[%a@]@,"
          Format.pp_print_string
          "Skipped checking translated proofs because some translations failed."
     | `check_error e ->
        printf "- @[<v>An error occurred when checking the translated proofs.\
                @,@[%s@]@]@,"
          (Printexc.to_string e)
     end;
     printf "@]";
     State.on_session_completed s;
     loop s
  | Either.Left (`no_subgoal (c, t)) ->
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
  | Either.Right (c, t, g) ->
    (* Show the proof state and the prompt *)
    printf "@,@[<v>@,%a@,@]@?"
      P.fmt_ppr_cmp_proof_state g;
    (*
      printf "@,@[<v>@,%a@,There are %d IHs.@,@]@?"
      P.fmt_ppr_cmp_proof_state g
      (Context.length Comp.(g.context.cIH));
     *)

    (* Parse the input and run the command *)
    match
      State.parsed_prompt s "> " None Parser.interactive_harpoon_command_sequence
      |> process_command_sequence s (c, t, g)
    with
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
  let s = State.make save_back stop sig_path all_paths io gs in
  (* If no sessions were created by loading the subgoal list
     then (it must have been empty so) we need to create the default
     session and configure it. *)
  Gensym.reset ();
  match State.completeness s with
  | `complete ->
    if State.session_configuration_wizard s then
      loop s
  | `incomplete -> loop s
