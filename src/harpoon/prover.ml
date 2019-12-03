open Support

module B = Beluga
module Check = B.Check
module Command = B.Syntax.Ext.Harpoon
module Context = B.Context
module Comp = B.Syntax.Int.Comp
module HoleId = B.HoleId
module Holes = B.Holes
module Id = B.Id
module Interactive = B.Interactive
module LF = B.Syntax.Int.LF
module Logic = B.Logic
module P = B.Pretty.Int.DefaultPrinter
module Total = B.Total
module Whnf = B.Whnf
module Debug = B.Debug

let dprintf, _, dprnt = Debug.(makeFunctions' (toFlags [13]))
open Debug.Fmt


exception EndOfInput

let _ =
  B.Error.register_printer
    begin fun EndOfInput ->
    B.Error.print
      begin fun ppf ->
      Format.fprintf ppf "End of input."
      end
    end

module Prover = struct
  open Theorem

  type state =
    { theorems : Theorem.t DynArray.t
    (* ^ The theorems currently being proven. *)
    
    ; automation_state : Automation.automation_state
    ; prompt : InputPrompt.t
    ; ppf : Format.formatter
    }

  let printf (s : state) x =
    Format.fprintf s.ppf x
    
  (** Gets the list of mutual declarations corresponding to the
      currently loaded theorems.
   *)
  let get_mutual_decs (s : state) : Total.dec list =
    let get_dec ts =
      Total.make_total_dec
        ts.name
        Comp.(Whnf.cnormCTyp ts.initial_state.goal |> Total.strip)
        ts.order
    in
    List.map get_dec (DynArray.to_list s.theorems)
    
  let make_state
        (ppf : Format.formatter)
        (prompt : InputPrompt.t)
      : state =
    let theorems = DynArray.make 16 in
    { theorems
    ; automation_state = Automation.make_automation_state ()
    ; prompt
    ; ppf
    }

    (*
  (** Removes the theorem with a given name from the list of theorems. *)
  let remove_theorem s name =
    let n = DynArray.length s.theorems in
    let rec loop = function
      | i when i >= n -> ()
      | i when Id.equals name (DynArray.get s.theorems i).Theorem.name ->
         DynArray.delete s.theorems i
      | i -> loop (i + 1)
    in
    loop 0
     *)

  let remove_current_theorem s =
    DynArray.delete s.theorems 0

  let defer_theorem s =
    let t = DynArray.get s.theorems 0 in
    remove_current_theorem s;
    DynArray.add s.theorems t

  (** Gets the next theorem from the interpreter state.
      Returns `None` if there are no theorems left,
      i.e. all theorems in the mutual block have been proven.
   *)
  let next_theorem (s : state) : Theorem.t option =
    match s.theorems with
    | ts when DynArray.empty ts -> None
    | ts -> Some (DynArray.get ts 0)

  (** Decides whether a given `cid` is in among the currently being
      proven theorems. *)
  let cid_is_in_current_theorem_set s c =
    List.exists (fun t -> t.cid = c) (DynArray.to_list s.theorems)

  (** Runs proof automation on a given subgoal. *)
  let run_automation (s : state) (t : theorem) (g : Comp.proof_state) =
    ignore (Automation.exec_automation s.automation_state t g)

  type invocation_status =
    [ `ok
    | `not_an_ih
    ]

  (** Checks that the given term corresponds to the given kind of invocation.
      Without this, it is possible to invoke lemmas using `by ih`.
   *)
  let check_invocation s (k : Comp.invoke_kind) (i : Comp.exp_syn) : invocation_status =
    match k with
    | `lemma -> `ok
    | `ih ->
       match Comp.head_of_application i with
       | Comp.Const (_, c) when cid_is_in_current_theorem_set s c -> `ok
       | _ -> `not_an_ih

  (** Elaborates a synthesizable expression in the given contexts. *)
  let elaborate_exp' cIH cD cG mfs t =
    let (hs, (i, tau)) =
      Holes.catch
        begin fun _ ->
        let (i, (tau, theta)) =
          Interactive.elaborate_exp' cD cG t
        in
        let _ = Check.Comp.syn ~cIH: cIH cD cG mfs i in  (* (tau, theta); *)
        (i, Whnf.cnormCTyp (tau, theta))
        end
    in
    (hs, i, tau)

  (** Elaborates a checkable expression in the given contexts against the given type. *)
  let elaborate_exp cIH cD cG mfs t ttau =
    Holes.catch
      begin fun _ ->
      let e = Interactive.elaborate_exp cD cG t ttau in
      Check.Comp.check ~cIH: cIH cD cG mfs e ttau;
      e
      end

  let process_command
        (s : state)
        (t : theorem)
        (g : Comp.proof_state)
        (cmd : Command.command)
      : unit =
    let mfs = lazy (get_mutual_decs s) in

    let open Comp in
    
    let solve_hole (id, Holes.Exists (w, h)) =
      let open Holes in
      dprintf
        begin fun p ->
        p.fmt "[harpoon] [solve_hole] processing hole %s"
          (HoleId.string_of_name_or_id (h.Holes.name, id))
        end;
      let { name; Holes.cD = cDh; info; _ } = h in
      match w with
      | Holes.CompInfo -> failwith "computational holes not supported"
      | Holes.LFInfo ->
         let { lfGoal; cPsi; lfSolution } = h.info in
         assert (lfSolution = None);
         let typ = Whnf.normTyp lfGoal in
         dprintf
           begin fun p ->
           p.fmt "[harpoon] [solve] [holes] @[<v>goal: @[%a@]@]"
             (P.fmt_ppr_lf_typ cDh cPsi P.l0) typ
           end;
         Logic.prepare ();
         let (query, skinnyTyp, querySub, instMVars) =
           Logic.Convert.typToQuery cPsi cDh (typ, 0)
         in
         try
           Logic.Solver.solve cDh cPsi query
             begin fun (cPsi, tM) ->
             printf s "found solution: @[%a@]@,@?"
               (P.fmt_ppr_lf_normal cDh cPsi P.l0) tM;
             h.info.lfSolution <- Some (tM, LF.Shift 0);
             raise Logic.Frontend.Done
             end
         with
         | Logic.Frontend.Done ->
            printf s "logic programming finished@,@?";
            ()
    in

    let { cD; cG; cIH } = g.context in

    match cmd with
    (* Administrative commands: *)
    | Command.ShowProof ->
       Theorem.show_proof t
    | Command.Rename (x_src, x_dst, level) ->
       Theorem.rename_variable x_src x_dst level t g
    | Command.Defer k ->
       begin match k with
       | `theorem -> defer_theorem s
       | `subgoal -> Theorem.defer_subgoal t
       end
    | Command.ShowIHs ->
       let f i =
         printf s "%d. %a@,"
           (i + 1)
           (P.fmt_ppr_cmp_ctyp_decl g.context.cD P.l0)
       in
       printf s "There are %d IHs:@,"
         (Context.length g.context.cIH);
       Context.to_list g.context.cIH |> List.iteri f

    | Command.ShowSubgoals ->
       Theorem.show_subgoals t
       
    | Command.ToggleAutomation (automation_kind, automation_change) ->
       Automation.toggle_automation s.automation_state automation_kind automation_change
      
    (* Real tactics: *)
    | Command.Unbox (i, name) ->
       let (hs, m, tau) = elaborate_exp' cIH cD cG (Lazy.force mfs) i in
       Tactic.unbox m tau name t g
       
    | Command.Intros names ->
       Tactic.intros names t g

    | Command.Split (split_kind, i) ->
       let (hs, m, tau) = elaborate_exp' cIH cD cG (Lazy.force mfs) i in
       Tactic.split split_kind m tau (Lazy.force mfs) t g
    | Command.By (k, i, name, b) ->
       let (hs, i, tau) = elaborate_exp' cIH cD cG (Lazy.force mfs) i in
       dprintf
         begin fun p ->
         p.fmt "@[<v>[harpoon-By] elaborated invocation:@,%a@ : %a@]"
           (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
           (P.fmt_ppr_cmp_typ cD P.l0) tau
         end;
       List.iter solve_hole hs;
       (* validate the invocation and call the suspension if it passes. *)
       begin match check_invocation s k i with
       | `ok -> Tactic.invoke k b i tau name t g
       | `not_an_ih ->
          printf s "@[<v>The expression@,  @[%a@]@,\
                    is not an appeal to an induction hypothesis.@]"
            (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
       end
       
    | Command.Solve e ->
       let (hs, e) = elaborate_exp cIH cD cG (Lazy.force mfs) e g.goal in
       dprnt "[harpoon] [solve] elaboration finished";
       printf s "Found %d hole(s) in solution@." (List.length hs);
       List.iter solve_hole hs;
       Check.Comp.check cD cG (Lazy.force mfs) e g.goal;
       (Comp.solve e |> Tactic.solve) t g

  (** Displays the given prompt `msg` and awaits a line of input from the user.
      The line is parsed using the given parser.
      In case of a parse error, the prompt is repeated.
      The user can abort the prompt by giving an empty string.
   *)
  let rec prompt_with s msg use_history (p : 'a B.Parser.t) : 'a option =
    let open InputPrompt in
    match s.prompt.get_input msg use_history () with
    | None -> raise EndOfInput
    | Some "" -> None
    | Some line ->
       B.Runparser.parse_string "<prompt>" line (B.Parser.only p)
       |> snd
       |> B.Parser.handle
            begin fun err ->
            printf s "@[<v>Parse error.@,@[%a@]@]@."
              B.Parser.print_error err;
            prompt_with s msg use_history p
            end
            Maybe.pure

  (** Repeats the prompt even if the user gives an empty response. *)
  let rec prompt_forever_with s msg use_history p =
    match prompt_with s msg use_history p with
    | None -> prompt_forever_with s msg use_history p
    | Some x -> x

  (** Runs the theorem configuration prompt to set up the next batch of theorems.
   *)
  let theorem_configuration_wizard s : unit =
    assert (DynArray.length s.theorems = 0);
    let rec do_prompts i : Theorem.Conf.t list =
      printf s "Configuring theorem #%d@." i;
      (* prompt for name, and allow using empty to signal we're done. *)
      let open InputPrompt in
      s.prompt.set_hints (Misc.const None);
      match prompt_with s "  Name of theorem (empty name to finish): " None B.Parser.name with
      | None -> []
      | Some name ->
         let stmt, k =
           (* XXX These calls are sketchy as hell.
              There must be a better place to put them -je
            *)
           B.Reconstruct.reset_fvarCnstr ();
           B.Store.FCVar.clear ();
           (* Now prompt for the statement, and disallow empty to signal we're done. *)
           prompt_forever_with s "  Statement of theorem: " None B.Parser.cmp_typ
           |> Interactive.elaborate_typ LF.Empty
         in
         let order =
           prompt_with s "  Induction order (empty for none): " None B.Parser.numeric_total_order
           |> Maybe.map (Interactive.elaborate_numeric_order k)
         in
         printf s "@]";
         { Theorem.Conf.name; order; stmt } :: do_prompts (i + 1)
    in

    let confs = do_prompts 1 in
    let thms = Theorem.configure_set s.ppf [run_automation s] confs in
    Misc.DynArray.append_list s.theorems thms
end

(** A computed value of type 'a or a function to print an error. *)
type 'a error = (Format.formatter -> unit -> unit, 'a) Either.t

(** Parses the given string to a Syntax.Ext.Harpoon.command or an
    error-printing function.
 *)
let parse_input (input : string) : Command.command error =
  let open B in
  Runparser.parse_string "<prompt>" input Parser.(only interactive_harpoon_command)
  |> snd |> Parser.to_either
  |> Either.lmap (fun e ppf () -> Parser.print_error ppf e)

(** Runs the given function, trapping exceptions in Either.t
    and converting the exception to a function that prints the
    error with a given formatter.
 *)
let run_safe (f : unit -> 'a) : 'a error =
  let show_error e ppf () =
    Format.fprintf ppf "@[<v>Internal error. (State may be undefined.)@,%s@]"
      (Printexc.to_string e)
  in
  Either.trap f |> Either.lmap show_error

let rec loop (s : Prover.state) : unit =
  let printf x = Prover.printf s x in
  (* Get the next subgoal *)
  match Prover.next_theorem s with
  | None ->
     printf "@,Proof complete! (No theorems left.)@,";
     Prover.theorem_configuration_wizard s;
     (* s will be populated with theorems; if there are none it's
        because the session is over. *)
     if DynArray.length Prover.(s.theorems) > 0 then
       loop s
     else
       printf "@,Session terminated.@,"
  | Some t ->
     match Theorem.next_subgoal t with
     | None ->
        printf "@,Subproof complete! (No subgoals left.)@,";
        Theorem.show_proof t;
        Prover.remove_current_theorem s;
        loop s
     | Some g ->
        (* Show the proof state and the prompt *)
        printf "@,@[<v>@,%a@,There are %d IHs.@,@]@?"
          P.fmt_ppr_cmp_proof_state g
          (Context.length Comp.(g.context.cIH));

        (* Parse the input and run the command *)
        let input =
          let open InputPrompt in
          let open Prover in
          (* The lambda character (or any other UTF-8 characters)
             does not work with linenoise.
             See https://github.com/ocaml-community/ocaml-linenoise/issues/13
             for detail.
           *)
          s.prompt.set_hints (Misc.const (Some ("abc", true)));
          s.prompt.get_input "> " None ()
          |> Maybe.get' EndOfInput
        in
        let e =
          let open Either in
          parse_input input
          $ fun cmd ->
            run_safe (fun () -> Prover.process_command s t g cmd)
        in
        Either.eliminate
          (fun f -> printf "%a" f ())
          (Misc.const ())
          e;
        loop s

let start_toplevel
      (prompt : InputPrompt.t)
      (ppf : Format.formatter) (* The formatter used to display messages *)
    : unit =
  let s = Prover.make_state ppf prompt in
  Prover.theorem_configuration_wizard s;
  loop s
