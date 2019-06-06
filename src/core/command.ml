(**
 * Top level functions invoked by the interactive mode.
 * Each interactive mode command corresponds with a `command` record in this file.
 * Available commands are added to a registry at the bottom of this file.
 *)

open ExtString.String
open Store.Cid
open Pretty.Int.DefaultPrinter
open Format

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
  if n' = n then
    f ppf arglist
  else
    fprintf ppf "- Command requires %d arguments, but %d were given;\n" n n'

let reg : command list ref = ref []

let countholes =
  { name = "countholes";
    run =
      command_with_arguments 0
        (fun ppf _ ->
          fprintf ppf "%d;\n" (Holes.count ()));
    help = "Print the total number of holes"
  }

let prove =
  { name = "prove"
  ; run =
      command_with_arguments 1
        begin
          fun ppf [name] ->
          let open Either in
          fprintf ppf "Statement to prove (C-d to abort): @?";
          let prompt message entry sc fc =
            fprintf ppf "%s: @?" message;
            trap read_line |> lmap (fun _ _ -> ())
            $ fun input ->
              trap
                (fun () ->
                  Parser.parse_string ~name: "<prompt>" ~input: input entry
                  |> sc)
              |> lmap fc
          in
          begin
            prompt "Statement to prove" Parser.cmp_typ
              (fun x -> x |> Index.comptyp |> Reconstruct.comptyp |> Abstract.comptyp)
              (fun e ppf -> fprintf ppf "- Error interpreting statement:\n%s;" (Printexc.to_string e))
            $ fun (stmt, k) -> (* k is the number of added implicit vars *)
              prompt "Induction order" Parser.numeric_total_order
                (fun x -> x |> Syntax.Ext.Comp.map_order (fun n -> n + k) |> Order.of_numeric_order)
                (fun e ppf -> fprintf ppf "- Error interpreting induction order:\n%s" (Printexc.to_string e))
              $ fun order ->
                Order.list_of_order order
                |> Either.of_option'
                     (fun _ ppf -> fprintf ppf "- Induction order too complicated;")
                $ fun order_list ->
                  Total.annotate stmt order_list
                  |> Either.of_option'
                       (fun _ ppf ->
                         fprintf ppf "- Induction order doesn't match statement;")
                  $> fun stmt ->
                     (stmt, order)

          end
          |> Either.eliminate
               (fun f -> f ppf)
               (fun (stmt, order) ->
                 Harpoon.Prover.start_toplevel
                   ppf
                   (Id.mk_name (Id.SomeString name))
                   (stmt, Syntax.Int.LF.MShift 0)
                   order)
        end
  ; help = "Interactively prove a theorem"
  }

let chatteron =
  { name = "chatteron";
    run =
      command_with_arguments 0
        (fun ppf _ ->
          Debug.chatter := 1; fprintf ppf "The chatter is on now;\n"
        );
    help = "Turn on the chatter"
  }

let chatteroff =
  { name = "chatteroff";
    run =
      command_with_arguments 0
        (fun ppf _ ->
          Debug.chatter := 0; fprintf ppf "The chatter is off now;\n"
        );
    help = "Turn off the chatter"
  }


let types =
  { name = "types";
    run =
      command_with_arguments 0
        (fun ppf _ ->
          let entrylist =
            List.rev_map Typ.get
              (List.fold_left (fun acc l -> acc@(!l)) [] (DynArray.to_list Typ.entry_list))
          in
          let dctx = Synint.LF.Null in
          List.iter
            (fun x ->
              fprintf ppf "%s : "
                (Id.string_of_name x.Typ.name);
              ppr_lf_kind dctx x.Typ.kind; fprintf ppf "\n")
            entrylist;
          fprintf ppf ";\n"
        );
    help = "Print out all types currently defined"
  }

let reset =
  { name= "reset";
    run=
      command_with_arguments 0
        (fun ppf _ ->
          Store.clear ();
          Typeinfo.clear_all ();
          Holes.clear();
          fprintf ppf "Reset successful;\n"
        );
    help="Reset the store"}

let clearholes =
  { name = "clearholes";
    run =
      command_with_arguments 0
        (fun _ _ -> Holes.clear(););
    help = "Clear all computation level holes"
  }

let load_files ppf file_name files =
	let per_file f =
    let sgn = Parser.parse_file ~name:f Parser.sgn in
    let sgn = Recsgn.apply_global_pragmas sgn in
    let sgn' =
      begin match Recsgn.recSgnDecls sgn with
	    | sgn', None -> sgn'
	    | _, Some _ -> raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))
	    end
    in
    if !Debug.chatter <> 0 then
      List.iter (fun x -> let _ = Pretty.Int.DefaultPrinter.ppr_sgn_decl x in ()) sgn'
	in
  Holes.clear ();
  List.iter per_file files;
  fprintf ppf "The file %s has been successfully loaded;\n" (Filename.basename file_name)

let reload, load =
  let last_load : (string * string list) option ref = ref None in
  { name = "reload"
  ; run =
      command_with_arguments 0
        (fun ppf arglist ->
          match !last_load with
          | None -> fprintf ppf "- No load to repeat;"
          | Some (file_name, files) ->
             load_files ppf file_name files
        )
  ; help = "Repeats the last load command."
  },
  { name = "load"
  ; run =
      command_with_arguments 1
        (fun ppf arglist ->
          let file_name = List.hd arglist in (* .bel or .cfg *)
		      let files = Cfg.process_file_argument file_name in
          last_load := Some (file_name, files);
          load_files ppf file_name files
        )
  ; help = "Load the file \"filename\" into the interpreter"
  }

(** Parses the given hole lookup strategy string, and retrieves a hole
 * using that strategy.
 *
 * If the string is invalid, or the lookup fails, an error is
 * displayed. Otherwise, the given function is executed with the hole
 * identifier and information. *)
let with_hole_from_strategy_string ppf (strat : string) (f : Holes.hole_id * Holes.hole -> unit) : unit =
  match Holes.parse_lookup_strategy strat with
  | None -> fprintf ppf "- Failed to parse hole identifier `%s';\n" strat
  | Some s ->
     match Holes.get s with
     | Some id_and_hole -> f id_and_hole
     | None -> fprintf ppf "- No such hole %s;\n" (Holes.string_of_lookup_strategy s)

let requiring_hole_satisfies
      (check : Holes.hole -> bool)
      (on_error : Holes.hole_id * Holes.hole -> unit)
      (f : Holes.hole_id * Holes.hole -> unit)
      (p : Holes.hole_id * Holes.hole)
    : unit =
  match p with
  | (i, h) when check h -> f (i, h)
  | (i, h) -> on_error (i, h)

let requiring_computation_hole
      ppf
      (f : Holes.hole_id * Holes.hole -> unit)
      (p : Holes.hole_id * Holes.hole)
    : unit =
  requiring_hole_satisfies
    Holes.is_comp_hole
    (fun (i, h) ->
      fprintf ppf "- Hole %s is not a computational hole;\n"
        (Holes.string_of_name_or_id (h.Holes.name, i)))
    f
    p

let requiring_lf_hole
      ppf
      (f : Holes.hole_id * Holes.hole -> unit)
      (p : Holes.hole_id * Holes.hole)
    : unit =
  requiring_hole_satisfies
    Holes.is_lf_hole
    (fun (i, h) ->
      fprintf ppf "- Hole %s is not an LF hole;\n"
     (Holes.string_of_name_or_id (h.Holes.name, i)))
    f
    p

let printhole =
  { name = "printhole";
    run =
      command_with_arguments 1
        (fun ppf arglist ->
          let s_ = List.hd arglist in
          with_hole_from_strategy_string ppf s_
            (fun (i, h) -> fprintf ppf "%s;\n" (Holes.format_hole i h)));
    help = "Print out all the information of the i-th hole passed as a parameter";
  }

let lochole =
  { name = "lochole"
  ; run =
      command_with_arguments 1
        (fun ppf arglist ->
          with_hole_from_strategy_string ppf (List.hd arglist)
            (fun (_, {Holes.loc; _}) ->
              let ( file_name,
                    start_line,
                    start_bol,
                    start_off,
                    stop_line,
                    stop_bol,
                    stop_off,
                    _ghost ) = Syntax.Loc.to_tuple loc in
              fprintf
                ppf
                "(\"%s\" %d %d %d %d %d %d);\n"
                file_name
                start_line start_bol start_off
                stop_line stop_bol stop_off))
  ; help = "Print out the location information of the i-th hole passed as a parameter"
  }

let solvelfhole =
  { name = "solve-lf-hole"
  ; run =
      command_with_arguments 1
        (fun ppf [name] ->
          with_hole_from_strategy_string ppf name
            (requiring_lf_hole ppf
               (fun (i, h) ->
                 let { Holes.name
                     ; Holes.cD
                     ; Holes.info =
                         Holes.LfHoleInfo
                           { Holes.lfGoal = (lfTyp, lfSub)
                           ; Holes.cPsi
                           }
                     ; Holes.loc = _
                     } = h
                 in
                 let (lfTyp', i) = Abstract.typ lfTyp in
                 (* Not too sure what I'm doing here. *)
                 let _ = Logic.prepare () in
                 let (query, skinnyTyp, querySub, instMVars) =
                   Logic.Convert.typToQuery cPsi cD (lfTyp', i) in
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
                           Pretty.std_lvl
                           ppf
                           norm;

                         fprintf ppf "\n" ;
                         incr n;
                         if !n = 10 then raise Logic.Frontend.Done
                       end
                   with
                   | Logic.Frontend.Done -> ()
                   | e -> raise e
                 end;
                 fprintf ppf ";\n";
               )))
  ; help = "Use logic programming to solve an LF hole"
  }

let constructors =
  { name = "constructors";
    run =
      command_with_arguments 1
        (fun ppf arglist ->
          let arg = List.hd arglist in
          let entrylist = List.rev_map Typ.get (List.fold_left (fun acc l -> acc@(!l)) [] (DynArray.to_list Typ.entry_list)) in
          let entry = List.find (fun x ->
                          arg = (Id.string_of_name x.Typ.name)) entrylist in
          let mctx = Synint.LF.Empty in
          let dctx = Synint.LF.Null in
          let termlist = List.rev_map (Term.get ~fixName:true) !(entry.Typ.constructors) in
          List.iter
            (fun x ->
              fprintf ppf "%s : [%d] "
                (Id.string_of_name x.Term.name)
                x.Term.implicit_arguments;
              ppr_lf_typ mctx dctx x.Term.typ;
              fprintf ppf "\n")
            termlist;
          fprintf ppf ";\n"
        );
    help = "Print all constructors of a given type passed as a parameter"}

let helpme =
  { name = "help";
    run =
      command_with_arguments 0
        (fun ppf _ ->
          List.iter (fun x -> fprintf ppf "%%:%20s\t %s\n" x.name x.help) !reg
        );
    help = "list all availale commands with a short description"
  }

(* The fill command is actually broken when you use it to fill in an
   induction hypothesis since the check at the end will not verify that
   the recursive call is well-founded.
   You could fix this by traversing the whole syntax tree to find the
   hole and recover the totality declarations that surround it, but
   that's a lot of work. Another solution could be to augment the hole
   datatype with the information about the totality declarations that
   were in scope at the moment that the hole was reconstructed. This
   is probably simpler.
 *)
let fill =
  { name = "fill"
  ; run =
      (fun ppf args ->
        try
          begin
            let strat_s = List.hd args in
            let eq = List.hd (List.tl args) in
            let str = String.concat " " (List.tl (List.tl args)) in
            if not (eq = "with") then failwith "- second argument must be `with`; see help;";
            let exp = Parser.parse_string ~name:"<fill>" ~input:str Parser.cmp_exp_chk in
            with_hole_from_strategy_string ppf strat_s
              (requiring_computation_hole ppf
                 (fun hi ->
                   let ( _ ,
                         { Holes.loc
                         ; Holes.name
                         ; Holes.cD
                         ; Holes.info =
                             Holes.CompHoleInfo
                               { Holes.compGoal = tclo
                               ; Holes.cG
                               }
                         }
                       ) = hi
                   in
                   let exp = Interactive.elaborate_exp cD cG exp tclo in
                   Check.Comp.check cD cG None exp tclo; (* checks that exp fits the hole *)
                   Interactive.replace_hole hi exp))
          end
        with
        | e ->
           fprintf ppf "- Error in fill:\n%s\n" (Printexc.to_string e))
  ; help = "`fill H with EXP` fills hole H with EXP"
  }

(**
 * Actually does a split on a variable in a hole.
 * Requires that the hole be a computation hole.
 *)
let do_split ppf (hi : Holes.hole_id * Holes.hole) (var : string) : unit =
  match Interactive.split var hi with
  | None -> fprintf ppf "- No variable %s found;\n" var
  | Some exp ->
     let (_, h) = hi in
     let Holes.CompHoleInfo { Holes.cG; _ } = h.Holes.info in
     Pretty.Control.printNormal := true;
     fprintf ppf "%a;\n" (fmt_ppr_cmp_exp_chk h.Holes.cD cG Pretty.std_lvl) exp;
     Pretty.Control.printNormal := false

let split =
  { name = "split"
  ; run =
      command_with_arguments 2
        (fun ppf [strat_s; var] ->
          with_hole_from_strategy_string ppf strat_s
            (requiring_computation_hole ppf
               (fun hi -> do_split ppf hi var))
        )
  ; help = "`split H V` tries to split on variable V in hole H (specified by name or number)"
  }

let intro =
  { name = "intro"
  ; run =
      command_with_arguments 1
        (fun ppf [strat] ->
          with_hole_from_strategy_string ppf strat
            (requiring_computation_hole ppf
               (fun (i, h) ->
                 let exp = Interactive.intro h in
                 let { Holes.cD
                     ; Holes.info = Holes.CompHoleInfo { Holes.cG; _ }
                     ; _
                     } = h
                 in
                 begin
                   Pretty.Control.printNormal := true;
                   fprintf ppf "%s;\n" (expChkToString cD cG exp);
                   Pretty.Control.printNormal := false
                 end)))
  ; help = "- intro n tries to introduce variables in the nth hole"
  }

let compconst =
  { name = "constructors-comp";
    run =
      command_with_arguments 1
        (fun ppf [arg] ->
          try
            let entrylist = List.rev_map CompTyp.get (List.fold_left (fun acc l -> acc@(!l)) [] (DynArray.to_list CompTyp.entry_list)) in
            let entry = List.find (fun x -> arg = (Id.string_of_name x.CompTyp.name)) entrylist in
            let mctx = Synint.LF.Empty in
            let termlist = List.rev_map (CompConst.get ~fixName:true) (!(entry.CompTyp.constructors)) in
            List.iter
              (fun x ->
                fprintf ppf "%s: [%d] "
                  (Id.string_of_name x.CompConst.name)
                  x.CompConst.implicit_arguments;
                ppr_cmp_typ mctx x.CompConst.typ;
                fprintf ppf "\n")
              termlist;
            fprintf ppf ";\n"
          with
          | Not_found -> fprintf ppf "- The type %s does not exist;\n" arg);
    help = "Print all constructors of a given computational datatype passed as a parameter"
  }

let signature =
  { name = "fsig";
    run =
      command_with_arguments 1
        (fun ppf [arg] ->
          try
            let (cidlist, _) = List.split (List.fold_left (fun acc l -> acc@(!l)) [] (DynArray.to_list Comp.entry_list)) in
            let entrylist = List.rev_map Comp.get cidlist in
            let entry = List.find (fun x -> arg = (Id.string_of_name x.Comp.name)) entrylist in

            let mctx = Synint.LF.Empty in
            fprintf ppf "%s: " (Id.string_of_name entry.Comp.name);
            ppr_cmp_typ mctx entry.Comp.typ;
            fprintf ppf ";\n";
          with
          | Not_found -> fprintf ppf "- The function does not exist;\n");
    help = "fsig e : Prints the signature of the function e, if such function is currently defined" }

let printfun =
  { name = "fdef";
    run =
      command_with_arguments 1
        (fun ppf [arg] ->
          try
            let (cidlist, _) =
              List.split
                (List.fold_left
                   (fun acc l -> acc@(!l))
                   []
                   (DynArray.to_list Comp.entry_list))
            in
            let entrylist = List.rev_map Comp.get cidlist in
            let entry =
              List.find
                (fun x -> arg = (Id.string_of_name x.Comp.name)) entrylist
            in
            match entry.Comp.prog with
            | Synint.Comp.RecValue (prog, ec, _ms, _env) ->
               ppr_sgn_decl (Synint.Sgn.Rec[(prog,entry.Comp.typ ,ec)])
            | _  -> fprintf ppf "- %s is not a function.;\n" arg
          with
          | Not_found ->
             fprintf ppf "- The function %s does not exist;\n" arg
        );
    help = "Print all the type of the functions currently defined" }

let quit =
  { name = "quit";
    run =
      (fun ppf _ ->
        fprintf ppf "Bye bye;";
        exit 0
      );
    help = "Exit interactive mode"
  }

let query =
  { name = "query";
    run =
      (fun ppf arglist ->
        try
          begin
            let expected = List.hd arglist in
            let tries = List.hd (List.tl arglist) in
            let str = String.concat " " (List.tl (List.tl arglist)) in
            let input = "%query " ^ expected ^ " " ^ tries ^ " " ^ str in
            let [Synext.Sgn.Query (_loc, name, extT, expected, tries)] = Parser.parse_string ~name:"<query>" ~input:input Parser.sgn in
            let (apxT, _ ) = Index.typ extT in
            let _ = Store.FVar.clear () in
            let tA =
              Monitor.timer
                ( "Constant Elaboration"
                , fun () ->
                  let tA = Reconstruct.typ Lfrecon.Pi apxT in
                  Reconstruct.solve_fvarCnstr Lfrecon.Pi;
                  tA)
            in
            (* let cD       = Synint.LF.Empty in *)
            let _ = Unify.StdTrail.forceGlobalCnstr (!Unify.StdTrail.globalCnstrs) in
            let (tA', i) =
              Monitor.timer
                ( "Constant Abstraction"
                , fun () -> Abstract.typ tA)
            in
            let _ = Reconstruct.reset_fvarCnstr () in
            let _ = Unify.StdTrail.resetGlobalCnstrs () in
            let _ =
              Monitor.timer
                ( "Constant Check"
                , fun () ->
                  Check.LF.checkTyp Synint.LF.Empty Synint.LF.Null (tA', Substitution.LF.id))
            in
            let _c' = Logic.storeQuery name (tA', i) expected tries in
            let _ = Logic.runLogic() in
            fprintf ppf ";\n"
          end
        with
        | e -> fprintf ppf "- Error in query : %s;\n" (Printexc.to_string e));
    help = "%:query EXPECTED TRIES TYP.\tQuery solutions to a given type"}

let get_type =
  { name = "get-type";
    run =
      command_with_arguments 2
      (fun ppf [line; col] ->
        let line = to_int line in
        let col = to_int col in
        let typ = Typeinfo.type_of_position line col in
        fprintf ppf "%s" typ
      );
    help = "get-type [line] [column] Get the type at a location (for use in emacs)"}

let lookup_hole =
  { name = "lookuphole"
  ; run =
      command_with_arguments 1
        (fun ppf [strat] ->
          with_hole_from_strategy_string ppf strat
            (fun (i, _) -> fprintf ppf "%s;" (Holes.string_of_hole_id i)))
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
    ; fill
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
    ; prove
    ]

let register cmd f hp = reg := {name = cmd; run = f; help = hp} :: !reg

let is_command str =
  let str' = strip str in
  let l = String.length str' in
  if l > 1 && String.sub str' 0 2 = "%:" then
    let (_, cmd) = ExtString.String.split str' ":" in
    `Cmd (strip cmd)
  else
    `Input str

let do_command ppf cmd =
  let e =
    let open Either in
    trap (fun () -> ExtString.String.nsplit cmd " ") $
      fun args ->
      match args with
      | [] -> pure (fprintf ppf "- Empty command line;\n")
      | cmd_name :: args ->
         match trap (fun () -> List.find (fun x -> cmd_name = x.name) !reg) with
         | Left _ -> pure (fprintf ppf "- No such command %s;\n" cmd_name)
         | Right command -> trap (fun () -> command.run ppf args)
  in
  Either.eliminate
    (fun e ->
      try
        raise e
      with
      | ExtString.Invalid_string -> fprintf ppf "- Failed to split command line by spaces;\n"
      | e -> fprintf ppf "- Unhandled exception: %s;\n" (Printexc.to_string e))
    (fun () -> ())
    e

let print_usage ppf =
  let _ = fprintf ppf "Usage: \n" in
  helpme.run ppf []
