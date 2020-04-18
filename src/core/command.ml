open Support.Equality
(**
 * Top level functions invoked by the interactive mode.
 * Each interactive mode command corresponds with a `command` record in this file.
 * Available commands are added to a registry at the bottom of this file.
 *)

open Support
open ExtString.String
open Store.Cid
module P = Pretty.Int.DefaultPrinter
open Format

open Syntax.Int

(* the type of commands  *)
type command =
  { name : string
  ; run : Format.formatter -> string list -> unit
  ; help : string
  }

(* The built in commands *)

(** Used to define command bodies requiring a certain number of arguments.
 * This function checks the length of the argument list against the
 * given number, and in case of success runs the given command body
 * function. *)
let command_with_arguments (n : int) f ppf arglist =
  let n' = List.length arglist in
  if n' = n
  then f ppf arglist
  else fprintf ppf "- Command requires %d arguments, but %d were given;\n@?" n n'

let reg : command list ref = ref []

let countholes =
  { name = "countholes"
  ; run =
      command_with_arguments 0
        begin fun ppf _ ->
        fprintf ppf "%d;\n@?"
          (Holes.count ())
        end
  ; help = "Print the total number of holes"
  }

let chatteron =
  { name = "chatteron"
  ; run =
      command_with_arguments 0
        begin fun ppf _ ->
        Chatter.level := 1;
        fprintf ppf "The chatter is on now;\n@?"
        end
  ; help = "Turn on the chatter"
  }

let chatteroff =
  { name = "chatteroff"
  ; run =
      command_with_arguments 0
        begin fun ppf _ ->
        Chatter.level := 0;
        fprintf ppf "The chatter is off now;\n@?"
        end
  ; help = "Turn off the chatter"
  }


let types =
  { name = "types"
  ; run =
      command_with_arguments 0
        begin fun ppf _ ->
        let entrylist =
          List.map snd (Typ.current_entries ())
        in
        let dctx = Synint.LF.Null in
        fprintf ppf "@[<v>%a@];\n@?"
          (pp_print_list ~pp_sep:pp_print_cut
             (fun ppf x ->
               fprintf ppf "%a : %a"
                 Id.print x.Typ.Entry.name
                 (P.fmt_ppr_lf_kind dctx P.l0) x.Typ.Entry.kind))
          entrylist
        end
  ; help = "Print out all types currently defined"
  }

let reset =
  { name = "reset"
  ; run =
      command_with_arguments 0
        begin fun ppf _ ->
        Store.clear ();
        Typeinfo.clear_all ();
        Holes.clear();
        fprintf ppf "Reset successful;\n@?"
        end
  ; help = "Reset the store"
  }

let clearholes =
  { name = "clearholes"
  ; run =
      command_with_arguments 0
        begin fun _ _ ->
        Holes.clear()
        end
  ; help = "Clear all computation level holes"
  }

let reload, load =
  let do_load ppf path =
    ignore (Load.load ppf path);
    fprintf ppf "The file %s has been successfully loaded;\n@?"
      path
  in
  let last_load : string option ref = ref None in
  { name = "reload"
  ; run =
      command_with_arguments 0
        begin fun ppf arglist ->
        match !last_load with
        | None -> fprintf ppf "- No load to repeat;@?"
        | Some path -> do_load ppf path
        end
  ; help = "Repeats the last load command."
  },
  { name = "load"
  ; run =
      command_with_arguments 1
        begin fun ppf arglist ->
        let path = List.hd arglist in (* .bel or .cfg *)
        do_load ppf path;
        last_load := Some path
        end
  ; help = "Load the file \"filename\" into the interpreter"
  }

(** Parses the given hole lookup strategy string, and retrieves a hole
 * using that strategy.
 *
 * If the string is invalid, or the lookup fails, an error is
 * displayed. Otherwise, the given function is executed with the hole
 * identifier and information. *)
let with_hole_from_strategy_string ppf (strat : string) (f : HoleId.t * Holes.some_hole -> unit) : unit =
  match Holes.parse_lookup_strategy strat with
  | None -> fprintf ppf "- Failed to parse hole identifier `%s';\n@?" strat
  | Some s ->
     begin match Holes.get s with
     | Some id_and_hole -> f id_and_hole
     | None -> fprintf ppf "- No such hole %s;\n@?" (Holes.string_of_lookup_strategy s)
     end

let requiring_hole_satisfies
      (check : Holes.some_hole -> bool)
      (on_error : HoleId.t * Holes.some_hole -> unit)
      (f : HoleId.t * Holes.some_hole -> unit)
      (p : HoleId.t * Holes.some_hole)
    : unit =
  let g =
    match p with
    | (_, h) when check h -> f
    | _ -> on_error
  in
  g p

(** Requires that an list of checks on the hole pass before invoking
    the continuation `f`.
 *)
let rec require checks f p =
  match checks with
  | [] -> f p
  | (check, on_error) :: checks ->
     requiring_hole_satisfies check on_error
       (require checks f)
       p

let string_of_id_hole (i, h) =
  HoleId.string_of_name_or_id (h.Holes.name, i)

let check_is_unsolved ppf =
  Holes.is_unsolved,
  fun (id, Holes.Exists (_, h)) ->
  fprintf ppf "- Hole %s is already solved;\n@?"
    (string_of_id_hole (id, h))

let requiring_computation_hole
      ppf
      (f : HoleId.t * Holes.comp_hole_info Holes.hole -> unit)
      (p : HoleId.t * Holes.some_hole)
    : unit =
  let open Holes in
  require [check_is_unsolved ppf]
    begin fun (id, Exists (w, h)) ->
    match w with
    | CompInfo -> f (id, h)
    | _ ->
       fprintf ppf "- Hole %s is not a computational hole;\n@?"
         (string_of_id_hole (id, h))
    end
    p

let requiring_lf_hole
      ppf
      (f : HoleId.t * Holes.lf_hole_info Holes.hole -> unit)
      (p : HoleId.t * Holes.some_hole)
    : unit =
  let open Holes in
  require [check_is_unsolved ppf]
    begin fun (id, Exists (w, h)) ->
    match w with
    | LFInfo -> f (id, h)
    | _ ->
       fprintf ppf "- Hole %s is not an LF hole;\n@?"
         (string_of_id_hole (id, h))
    end
    p

let printhole =
  { name = "printhole"
  ; run =
      command_with_arguments 1
        begin fun ppf arglist ->
        let s = List.hd arglist in
        with_hole_from_strategy_string ppf s
          (fprintf ppf "%a;\n" Interactive.fmt_ppr_hole)
        end
  ; help = "Print out all the information of the i-th hole passed as a parameter@?";
  }

let lochole =
  { name = "lochole"
  ; run =
      command_with_arguments 1
        begin fun ppf arglist ->
        with_hole_from_strategy_string ppf (List.hd arglist)
          begin fun (_, Holes.Exists (w, {Holes.loc; _})) ->
          let file_name = Location.filename loc in
          let start_line = Location.start_line loc in
          let start_bol = Location.start_bol loc in
          let start_off = Location.start_offset loc in
          let stop_line = Location.stop_line loc in
          let stop_bol = Location.stop_bol loc in
          let stop_off = Location.stop_offset loc in
          fprintf
            ppf
            "(\"%s\" %d %d %d %d %d %d);\n@?"
            file_name
            start_line start_bol start_off
            stop_line stop_bol stop_off
          end
        end
  ; help = "Print out the location information of the i-th hole passed as a parameter"
  }

let solvelfhole =
  { name = "solve-lf-hole"
  ; run =
      command_with_arguments 1
        begin fun ppf [name] ->
        with_hole_from_strategy_string ppf name
          (requiring_lf_hole ppf
             begin fun (i, h) ->
             let Holes.{ cD; info = { lfGoal = (lfTyp, _); cPsi; _ }; _ } =
               h
             in
             let (lfTyp', i) = Abstract.typ lfTyp in
             (* Not too sure what I'm doing here. *)
             Logic.prepare ();
             let (query, skinnyTyp, querySub, instMVars) =
               Logic.Convert.typToQuery cPsi cD (lfTyp', i)
             in
             begin
               (* Count the solutions that are found so we only
                      emit a maximum number of them.
                      Raise the "Done" exception to stop the search.
                *)
               try
                 let n = ref 0 in
                 Logic.Solver.solve cD cPsi query
                   begin
                     fun (ctx, norm) ->
                     Pretty.Int.DefaultPrinter.fmt_ppr_lf_normal
                       cD
                       ctx
                       P.l0
                       ppf
                       norm;

                     fprintf ppf "\n";
                     incr n;
                     if !n = 10
                     then raise Logic.Frontend.Done
                   end
               with
               | Logic.Frontend.Done -> ()
               | e -> raise e
             end;
             fprintf ppf ";\n@?";
             end
          )
        end
  ; help = "Use logic programming to solve an LF hole"
  }

let constructors =
  { name = "constructors"
  ; run =
      command_with_arguments 1
        begin fun ppf arglist ->
        let typ_name = Id.(mk_name (SomeString (List.hd arglist))) in
        let entry =
          Typ.index_of_name typ_name |> Typ.get
        in
        let termlist =
          List.map Term.get !(entry.Typ.Entry.constructors)
        in
        fprintf ppf "@[<v>%a@]@.;@."
          (pp_print_list ~pp_sep: pp_print_cut
             (fun ppf x ->
               fprintf ppf "%a : [%d] %a"
                 Id.print x.Term.Entry.name
                 x.Term.Entry.implicit_arguments
                 (P.fmt_ppr_lf_typ LF.Empty LF.Null P.l0) x.Term.Entry.typ))
          termlist
        end
  ; help = "Print all constructors of a given type passed as a parameter"
  }

let helpme =
  { name = "help"
  ; run =
      command_with_arguments 0
        begin fun ppf _ ->
        List.iter (fun x -> fprintf ppf "%%:%20s\t %s\n@?" x.name x.help) !reg
        end
  ; help = "list all available commands with a short description"
  }

(**
 * Actually does a split on a variable in a hole.
 * Requires that the hole be a computation hole.
 *)
let do_split ppf (hi : HoleId.t * Holes.comp_hole_info Holes.hole) (var : string) : unit =
  match Interactive.split var hi with
  | None -> fprintf ppf "- No variable %s found;\n@?" var
  | Some exp ->
     let (_, h) = hi in
     let { Holes.cG; _ } = h.Holes.info in
     Printer.Control.printNormal := true;
     fprintf ppf "%a;\n@?" (P.fmt_ppr_cmp_exp_chk h.Holes.cD cG P.l0) exp;
     Printer.Control.printNormal := false

let split =
  { name = "split"
  ; run =
      command_with_arguments 2
        begin fun ppf [strat_s; var] ->
        with_hole_from_strategy_string ppf strat_s
          (requiring_computation_hole ppf
             (fun hi -> do_split ppf hi var))
        end
  ; help = "`split H V` tries to split on variable V in hole H (specified by name or number)"
  }

let intro =
  { name = "intro"
  ; run =
      command_with_arguments 1
        begin fun ppf [strat] ->
        with_hole_from_strategy_string ppf strat
          (requiring_computation_hole ppf
             begin fun (i, h) ->
             let exp = Interactive.intro h in
             let Holes.{ cD; info = { Holes.cG; _ }; _ } = h in
             Printer.Control.printNormal := true;
             fprintf ppf "%a;\n@?"
               (P.fmt_ppr_cmp_exp_chk cD cG P.l0) exp;
             Printer.Control.printNormal := false
             end
          )
        end
  ; help = "- intro n tries to introduce variables in the nth hole"
  }

let compconst =
  { name = "constructors-comp"
  ; run =
      command_with_arguments 1
        begin fun ppf [arg] ->
        let name = Id.(mk_name (SomeString arg)) in
        try
          let entry =
            CompTyp.index_of_name name |> CompTyp.get
          in
          let termlist =
            List.map CompConst.get !(entry.CompTyp.Entry.constructors)
          in
          fprintf ppf "@[<v>%a@]@.;@."
            (pp_print_list ~pp_sep: pp_print_cut
               (fun ppf x ->
                 fprintf ppf "%s : [%d] %a"
                   (Id.string_of_name x.CompConst.Entry.name)
                   x.CompConst.Entry.implicit_arguments
                   (P.fmt_ppr_cmp_typ LF.Empty P.l0) x.CompConst.Entry.typ))
            termlist;
        with
        | Not_found -> fprintf ppf "- The type %s does not exist;\n@?" arg
        end
  ; help = "Print all constructors of a given computational datatype passed as a parameter"
  }

let signature =
  { name = "fsig"
  ; run =
      command_with_arguments 1
        begin fun ppf [arg] ->
        try
          let name = Id.(mk_name (SomeString arg)) in
          let entry =
            Store.Cid.Comp.index_of_name name |> Store.Cid.Comp.get
          in
          fprintf ppf "%a : %a;@."
            Id.print entry.Store.Cid.Comp.Entry.name
            (P.fmt_ppr_cmp_typ LF.Empty P.l0) entry.Store.Cid.Comp.Entry.typ
        with
        | Not_found -> fprintf ppf "- The function does not exist;\n@?"
        end
  ; help = "fsig e : Prints the signature of the function e, if such function is currently defined"
  }

let printfun =
  { name = "fdef"
  ; run =
      command_with_arguments 1
        begin fun ppf [arg] ->
        try
          let n = Id.(mk_name (SomeString arg)) in
          let entry = Store.Cid.Comp.(index_of_name n |> get) in
          match Store.Cid.Comp.Entry.(entry.prog) with
          | Some (Synint.Comp.ThmValue (thm_name, thm_body, _ms, _env)) ->
             let d =
               let open Syntax.Int.Sgn in
               { thm_name
               ; thm_typ = Store.Cid.Comp.Entry.(entry.typ)
               ; thm_body
               ; thm_loc = Syntax.Loc.ghost
               }
             in
             P.fmt_ppr_sgn_decl ppf (Synint.Sgn.Theorem [d])
          | _  -> fprintf ppf "- %s is not a function.;\n@?" arg
        with
        | Not_found ->
           fprintf ppf "- The function %s does not exist;\n@?" arg
        end
  ; help = "Print all the type of the functions currently defined"
  }

let quit =
  { name = "quit"
  ; run =
      begin fun ppf _ ->
      fprintf ppf "Bye bye;@?";
      exit 0
      end
  ; help = "Exit interactive mode"
  }

let query =
  { name = "query"
  ; run =
      begin fun ppf arglist ->
      try
        begin
          let [Synext.Sgn.Query (_, name, extT, expected, tries)] =
            let expected = List.hd arglist in
            let tries = List.hd (List.tl arglist) in
            let str = String.concat " " (List.tl (List.tl arglist)) in
            let input = "%query " ^ expected ^ " " ^ tries ^ " " ^ str in
            Runparser.parse_string (Location.initial "<query>") input Parser.sgn
            |> Parser.extract
          in
          let (_, apxT) = Index.typ Index.disambiguate_to_fvars extT in
          Store.FVar.clear ();
          let tA =
            Monitor.timer
              ( "Constant Elaboration"
              , fun () ->
                let tA = Reconstruct.typ Lfrecon.Pi apxT in
                Reconstruct.solve_fvarCnstr Lfrecon.Pi;
                tA
              )
          in
          (* let cD       = Synint.LF.Empty in *)
          Unify.StdTrail.forceGlobalCnstr ();
          let (tA', i) =
            Monitor.timer
              ( "Constant Abstraction"
              , fun () -> Abstract.typ tA
              )
          in
          Reconstruct.reset_fvarCnstr ();
          Unify.StdTrail.resetGlobalCnstrs ();
          Monitor.timer
            ( "Constant Check"
            , fun () ->
              Check.LF.checkTyp Synint.LF.Empty Synint.LF.Null (tA', Substitution.LF.id)
            );
          Logic.storeQuery name (tA', i) expected tries;
          Logic.runLogic ();
          fprintf ppf ";\n@?"
        end
      with
      | e -> fprintf ppf "- Error in query : %s;\n@?" (Printexc.to_string e)
      end
  ; help = "%:query EXPECTED TRIES TYP.\tQuery solutions to a given type"
  }

let get_type =
  { name = "get-type"
  ; run =
      command_with_arguments 2
      begin fun ppf [line; col] ->
      let line = to_int line in
      let col = to_int col in
      let typ = Typeinfo.type_of_position line col in
      fprintf ppf "%s;\n@?"
        typ
      end
  ; help = "get-type [line] [column] Get the type at a location (for use in emacs)"
  }

let lookup_hole =
  { name = "lookuphole"
  ; run =
      command_with_arguments 1
        begin fun ppf [strat] ->
        with_hole_from_strategy_string ppf strat
          begin fun (i, _) ->
          fprintf ppf "%s;\n@?"
            (HoleId.string_of_hole_id i)
          end
        end
  ; help = "looks up a hole's number by its name"
  }

(* the default registered commands *)
let _ =
  reg :=
    [ helpme
    ; chatteroff
    ; chatteron
    ; load
    ; reload
    ; clearholes
    ; countholes
    ; lochole
    ; printhole
    ; types
    ; constructors
    ; split
    ; intro
    ; compconst
    ; signature
    ; printfun
    ; query
    ; get_type
    ; reset
    ; quit
    ; lookup_hole
    ; solvelfhole
    ]

let register cmd f hp =
  reg := { name = cmd; run = f; help = hp } :: !reg

let is_command str =
  let str' = strip str in
  let l = String.length str' in
  if l > 1 && Misc.String.(equals (sub str' 0 2) "%:")
  then
    begin
      let (_, cmd) = ExtString.String.split str' ":" in
      `Cmd (strip cmd)
    end
  else
    `Input str

let do_command ppf cmd =
  let e =
    let open Either in
    trap (fun () -> ExtString.String.nsplit cmd " ") $
      fun args ->
      match args with
      | [] -> pure ()
      | cmd_name :: args ->
         begin match
           List.find_opt
             (fun x -> Misc.String.equals cmd_name x.name)
             !reg
         with
         | None -> pure (fprintf ppf "- No such command %s;\n@?" cmd_name)
         | Some command -> trap (fun () -> command.run ppf args)
         end
  in
  Either.eliminate
    (fun e ->
      try
        raise e
      with
      | ExtString.Invalid_string -> fprintf ppf "- Failed to split command line by spaces;\n@?"
      | e -> fprintf ppf "- Unhandled exception: %s;\n@?" (Printexc.to_string e))
    (fun () -> ())
    e

let print_usage ppf =
  fprintf ppf "Usage: \n";
  helpme.run ppf []
