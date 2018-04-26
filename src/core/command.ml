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

(* args = (i, e, []) where
   i : hole number
   e : name of a variable appearing in the ith hole
let split = {name = "split";
              run = (fun ppf args ->
                let i = args.hd in
                let e = args.tl.hd in
                 let (loc, cD,cG,(tau,theta)) = Holes.getHole i  in
                 try
                 Interactive.split e cD cG
                     with _ -> "?"
                 );
              help = " ... " }
*)

let reg : command list ref = ref []

let countholes = {name = "countholes";
                  run = (fun ppf _ -> fprintf ppf "- Computation Level Holes: %d\n - LF Level Holes: %d;\n" (Holes.count ()) (Lfholes.getNumHoles()));
                  help = "Print the total number of LF and computation level holes"}

let numholes =
  { name = "numholes";
    run = (fun ppf _ -> fprintf ppf "%d;\n" (Holes.count ()));
    help = "Print the total number of holes";
  }

let numlfholes =
  { name = "numlfholes";
    run = (fun ppf _ -> fprintf ppf "%d;\n" (Lfholes.getNumHoles()));
    help = "Print the total number of lf holes";
  }

let chatteron = {name = "chatteron";
                 run = (fun ppf _ -> Debug.chatter :=1; fprintf ppf "- The chatter is on now.\n");
                 help = "Turn on the chatter"}


let chatteroff = {name = "chatteroff";
                  run = (fun ppf _ -> Debug.chatter := 0; fprintf ppf "- The chatter is off now.\n");
                  help = "Turn off the chatter"}


let types = {name = "types";
             run = (fun ppf _ ->
               let entrylist = List.rev_map Typ.get (List.fold_left (fun acc l -> acc@(!l)) [] (DynArray.to_list Typ.entry_list)) in
               let dctx = Synint.LF.Null in
               List.iter (fun x -> fprintf ppf "- %s:" (Id.string_of_name x.Typ.name); ppr_lf_kind dctx x.Typ.kind; fprintf ppf " \n") entrylist);
             help = "Print out all types currently defined"}

let reset = {name= "reset";
             run=
                (fun ppf _ ->
                  Store.clear ();
                  Typeinfo.clear_all ();
                  Holes.clear();
                  Lfholes.clear (); fprintf ppf "Reset successful@\n");
              help="Reset the store"}

let clearholes = {name = "clearholes";
                  run = (fun _ _ ->
                          Holes.clear(); Lfholes.clear ());
                  help= "Clear all computation level holes"}

let load = { name = "load"
           ; run = (fun ppf arglist ->
	     let per_file f =
               let sgn = Parser.parse_file ~name:f Parser.sgn in
               let sgn'= begin match Recsgn.recSgnDecls sgn with
	       	 | sgn', None -> sgn'
	       	 | _, Some _ -> raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))
	       end in
                 if !Debug.chatter <> 0 then
                   List.iter (fun x -> let _ = Pretty.Int.DefaultPrinter.ppr_sgn_decl x in ()) sgn'
	      in
              try
                let _ = Holes.clear() in
                let _ = Lfholes.clear () in
                let file_name = List.hd arglist in (* .bel or .cfg *)
		let files = Cfg.process_file_argument file_name in
		List.iter per_file files ;
                fprintf ppf "- The file %s has been successfully loaded;\n" (Filename.basename file_name)
              with
              |Failure _ -> fprintf ppf "- Please provide the file name;\n"
              | e -> fprintf ppf "- Error: %s;\n" (Printexc.to_string e))
           ; help = "Load the file \"filename\" into the interpreter"}

let printhole =
  { name = "printhole";
    run = (fun ppf arglist ->
      try
        let s_ = List.hd arglist in
        let s =
          match Holes.parse_lookup_strategy s_ with
          | None -> failwith "Failed to parse hole identifier."
          | Some s -> s in
        match Holes.get s with
        | None -> fprintf ppf "- No such hole %s" s_
        | Some (i, h) -> fprintf ppf "%s" (Holes.format_hole i h)
      with
      | Failure _ ->
         fprintf ppf "- Error occurs when analyzing argument list;\n" );
    help = "Print out all the information of the i-th hole passed as a parameter";
  }

let printlfhole = {name = "printhole-lf";
                 run = (fun ppf arglist ->
                   try
                     let arg = List.hd arglist in
                     Lfholes.printOneHole (to_int arg); fprintf ppf ";\n"
                   with
                   |Failure _ -> fprintf ppf "- Error occurs when analyzing argument list;\n");
                 help = "Print out all the information of the i-th LF hole passed as a parameter"}

let lochole =
  { name = "lochole"
  ; run = (fun ppf arglist ->
      try
        let strat = Holes.unsafe_parse_lookup_strategy (List.hd arglist) in
        match Holes.get strat with
        | Some (_, {Holes.loc; _}) ->
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
             stop_line stop_bol stop_off
        | None ->
           fprintf ppf "- No such hole %s;\n"
             (Holes.string_of_lookup_strategy strat)
      with
      | Failure s ->
         fprintf ppf "- Error occured when analyzing argument list: %s\n" s)
  ; help = "Print out the location information of the i-th hole passed as a parameter"
  }

let loclfhole = {name = "lochole-lf";
               run = (fun ppf arglist ->
                 try
                   let arg = List.hd arglist in
                   match Lfholes.getHolePos (to_int arg) with
                   | Some loc ->
                       let (file_name,
                            start_line,
                            start_bol,
                            start_off,
                            stop_line,
                            stop_bol,
                            stop_off,
                            _ghost) = Syntax.Loc.to_tuple loc in
                       fprintf ppf
                         "(\"%s\" %d %d %d %d %d %d);\n"
                         file_name
                         start_line start_bol start_off
                         stop_line stop_bol stop_off
                   | None -> fprintf ppf "- Error no such hole"
                 with
                 |Failure _ -> fprintf ppf "- Error occured when analyzing argument list\n");
               help = "Print out the location information of the i-th hole passed as a parameter"}

let constructors = {name = "constructors";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let entrylist = List.rev_map Typ.get (List.fold_left (fun acc l -> acc@(!l)) [] (DynArray.to_list Typ.entry_list)) in
                        let entry = List.find (fun x ->
                            arg = (Id.string_of_name x.Typ.name)) entrylist in
                        let mctx = Synint.LF.Empty in
                        let dctx = Synint.LF.Null in
                        let termlist = List.rev_map (Term.get ~fixName:true) !(entry.Typ.constructors) in
                        List.iter (fun x -> fprintf ppf "- %s: [%d] " (Id.string_of_name x.Term.name) x.Term.implicit_arguments; ppr_lf_typ mctx dctx x.Term.typ; fprintf ppf "\n") termlist;
                        fprintf ppf ";\n"
                      with
                      | Not_found -> fprintf ppf "- Such type does not exist!!\n"
                      | Failure _ -> fprintf ppf "- An error occured when analyzing argument list\n");
                    help = "Print all constructors of a given type passed as a parameter"}



let helpme = {name = "help";
              run = (fun ppf _ -> List.iter (fun x -> fprintf ppf "%%:%20s\t %s\n" x.name x.help) !reg);
              help = "list all availale commands with a short description"}



let fill =
  { name = "fill"
  ; run = (fun ppf args ->
    try
      begin
        let strat_s = List.hd args in
        let strat = Holes.unsafe_parse_lookup_strategy strat_s in
        let eq = List.hd (List.tl args) in
        let str = String.concat " " (List.tl (List.tl args)) in
        let input = "rec t : [ |- t] = " ^ str ^ ";" in
        if eq = "with" then
          let sgn = Parser.parse_string ~name:"<fill>" ~input:input Parser.sgn in
          let Syntax.Ext.Sgn.Rec (_, (Synext.Comp.RecFun(_,_,_, _, outexp))::[])::[] = sgn in
          try
            let ( _ ,
                  { Holes.loc
                  ; Holes.name
                  ; Holes.cD
                  ; Holes.cG
                  ; Holes.goal = tclo
                  }
                ) =
              match Holes.get strat with
              | None -> failwith ("No such hole " ^ strat_s)
              | Some h -> h in
            (if !Debug.chatter != 0 then fprintf ppf "- Fill: EXT done\n");
            let vars = Interactive.gctxToVars cG in
            let cvars = Interactive.mctxToCVars cD in
            let apxexp = Index.hexp cvars vars outexp in
            (if !Debug.chatter != 0 then fprintf ppf "- Fill: APX done\n");
            let intexp = Reconstruct.elExp cD cG apxexp tclo in
            (if !Debug.chatter != 0 then fprintf ppf "- Fill: INT done\n");
            Check.Comp.check cD cG intexp tclo; (* checks that exp fits the hole *)
            let intexp' =
              Interactive.mapHoleChk
                (fun _ ll _ ->
                  let (i, _) =
                    match Holes.staged_at ll with
                    | None -> failwith "No such hole."
                    | Some h -> h in
                  let loc' = Interactive.nextLoc loc in
                  Holes.set_staged_hole_pos i loc';
                  Synint.Comp.Hole
                    ( loc'
                    , Holes.option_of_name name
                    , fun () ->
                      match Holes.at loc' with
                      | None -> failwith "no such hole"
                      | Some (i, _) -> i
                    )
                )
                intexp in (* makes sure that new holes have unique location *)
            Interactive.replaceHole strat intexp'
          with
          | e ->
             fprintf
               ppf
               "- Error while replacing hole with expression : %s"
               (Printexc.to_string e)
        else
          failwith "- See help"
      end
    with
    | e ->
       fprintf ppf "- \nError in fill: %s\n" (Printexc.to_string e))
  ; help = "\"fill\" i \"with\" exp fills the ith hole with exp"
  }

let do_split ppf (strat : Holes.lookup_strategy) (var : string) : unit =
  match Holes.get strat with
  | None -> fprintf ppf "- No such hole %s" (Holes.string_of_lookup_strategy strat)
  | Some hi ->
     match Interactive.split var hi with
     | None -> fprintf ppf "- No variable %s found;\n" var
     | Some exp ->
        let (_, h) = hi in
        Pretty.Control.printNormal := true;
        fprintf ppf "%s;\n" (expChkToString h.Holes.cD h.Holes.cG exp);
        Pretty.Control.printNormal := false

let split =
  { name = "split"
  ; run = (fun ppf args ->
    Printexc.record_backtrace true;
    try
      match args with
      | [strat_s; e] -> (
        match Holes.parse_lookup_strategy strat_s with
        | None -> fprintf ppf "- Invalid hole identifier %s;" strat_s
        | Some strat -> do_split ppf strat e
      )
      | _ -> fprintf ppf "- 2 arguments expected: hole identifier and variable to split on;\n"
    with
    | e -> fprintf ppf "- Error in split.\n%s;\n" (Printexc.to_string e))
  ; help = "split h e tries to split on variable e in hole h (specified by name or number)"
  }

let intro =
  { name = "intro"
  ; run = (fun ppf args ->
    try
      let strat_s = List.hd args in
      let strat = Holes.unsafe_parse_lookup_strategy strat_s in
      match (Interactive.intro strat) with
      | None -> fprintf ppf "- Nothing to introduce in hole %s;\n" strat_s
      | Some exp ->
         let { Holes.cD
             ; Holes.cG
             ; _ } =
           match Holes.get strat with
           | None -> failwith "No such hole."
           | Some (_, h) -> h in
         Pretty.Control.printNormal := true;
         fprintf ppf "%s;\n" (expChkToString cD cG exp);
         Pretty.Control.printNormal := false
    with
    | Failure s -> fprintf ppf "- Error in intro: %s;\n" s
    |  _ ->      fprintf ppf "- Error in intro;\n")
  ; help = "- intro n tries to introduce variables in the nth hole"
  }

let compconst = {name = "constructors-comp";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let entrylist = List.rev_map CompTyp.get (List.fold_left (fun acc l -> acc@(!l)) [] (DynArray.to_list CompTyp.entry_list)) in
                        let entry = List.find (fun x -> arg = (Id.string_of_name x.CompTyp.name)) entrylist in
                        let mctx = Synint.LF.Empty in
                        let termlist = List.rev_map (CompConst.get ~fixName:true) (!(entry.CompTyp.constructors)) in
                        List.iter (fun x -> fprintf ppf "- %s: [%d] " (Id.string_of_name x.CompConst.name) x.CompConst.implicit_arguments; ppr_cmp_typ mctx x.CompConst.typ; fprintf ppf "\n") termlist;
                        fprintf ppf ";\n"
                      with
                      | Not_found -> fprintf ppf "- Such type does not exist;\n"
                      | Failure _ -> fprintf ppf "- Error occured when analyzing argument list;\n");
                    help = "Print all constructors of a given computational datatype passed as a parameter"}


let signature = {name = "fsig";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let (cidlist,_) = List.split (List.fold_left (fun acc l -> acc@(!l)) [] (DynArray.to_list Comp.entry_list)) in
                        let entrylist = List.rev_map Comp.get cidlist in
                        let entry = List.find (fun x -> arg = (Id.string_of_name x.Comp.name)) entrylist in

                        let mctx = Synint.LF.Empty in
                        fprintf ppf "- %s:  " (Id.string_of_name entry.Comp.name); ppr_cmp_typ mctx entry.Comp.typ; fprintf ppf "\n";
                        fprintf ppf ";\n"
                      with
                      | Not_found -> fprintf ppf "- Such function does not exist!;\n"
                      | Failure _ -> fprintf ppf "- Error occurs when analyzing argument list;\n");
                    help = "fsig e : Prints the signature of the function e, if such function is currently defined" }


let printfun = {name = "fdef";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let (cidlist,_) = List.split (List.fold_left (fun acc l -> acc@(!l)) [] (DynArray.to_list Comp.entry_list)) in
                        let entrylist = List.rev_map Comp.get cidlist in
                        let entry = List.find (fun x -> arg = (Id.string_of_name x.Comp.name)) entrylist in
                        (match entry.Comp.prog with
                        | Synint.Comp.RecValue (prog, ec, _ms, _env) ->
                            ppr_sgn_decl (Synint.Sgn.Rec[(prog,entry.Comp.typ ,ec)]);
                            fprintf ppf ";\n"
                        |     _  -> fprintf ppf "- %s is not a function.;\n" arg
                            )
                      with
                      | Not_found -> fprintf ppf "- Such function does not exist!;\n"
                      | Failure _ -> fprintf ppf "- Error occurs when analyzing argument list;\n");
                    help = "Print all the type of the functions currently defined" }


let quit = {name = "quit";
            run = (fun _ ->
                    exit 0);
            help = "Exit Interactive Mode"}

let query = {name = "query";
              run = (fun ppf arglist ->
                    try
                      begin
                        let expected = List.hd arglist in
                        let tries = List.hd (List.tl arglist) in
                        let str = String.concat " " (List.tl (List.tl arglist)) in
                        let input = "%query " ^ expected ^ " " ^ tries ^ " " ^ str in
                        let [Synext.Sgn.Query (_loc, name, extT, expected, tries)] = Parser.parse_string ~name:"<query>" ~input:input Parser.sgn in
                        let (apxT, _ ) = Index.typ extT in
                        let _        = Store.FVar.clear () in
                        let tA       = Monitor.timer ("Constant Elaboration",
                                                      fun () -> (let tA = Reconstruct.typ Lfrecon.Pi apxT in
                                                                 Reconstruct.solve_fvarCnstr Lfrecon.Pi;
                                                                 tA)) in
                        (* let cD       = Synint.LF.Empty in *)
                        let _        = Unify.StdTrail.forceGlobalCnstr (!Unify.StdTrail.globalCnstrs) in

                        let (tA', i) = Monitor.timer ("Constant Abstraction",
                                                      fun () -> Abstract.typ tA) in

                        let _        = Reconstruct.reset_fvarCnstr () in
                        let _        = Unify.StdTrail.resetGlobalCnstrs () in
                        let _        = Monitor.timer ("Constant Check",
                                                      fun () -> Check.LF.checkTyp Synint.LF.Empty Synint.LF.Null (tA', Substitution.LF.id)) in
                        let _c'      = Logic.storeQuery name (tA', i) expected tries in
                        let _ = Logic.runLogic() in
                        fprintf ppf ";\n"
                      end
                    with
                    | e -> fprintf ppf "- Error in query : %s;\n" (Printexc.to_string e));
            help = "%:query EXPECTED TRIES TYP.\tQuery solutions to a given type"}


let get_type = {name = "get-type";
                run =
                  (fun ppf args ->
                    try
                      let line = int_of_string (List.hd args) in
                      let col = int_of_string (List.hd (List.tl args)) in
                      let typ = Typeinfo.type_of_position line col in fprintf ppf "%s" typ
                    with e -> fprintf ppf "- Error in get-type : %s;\n" (Printexc.to_string e));
                help = "get-type [line] [column] Get the type at a location (for use in emacs)"}
(* Registering built-in commands *)

let lookup_hole =
  { name = "lookuphole"
  ; run = (fun ppf args ->
    let strat = Holes.unsafe_parse_lookup_strategy (List.hd args) in
    match Holes.get strat with
    | None -> fprintf ppf "- No such hole."
    | Some (i, _) -> fprintf ppf "%d" i)
  ; help = "looks up a hole's number by its name"
  }

let _ =
  reg :=
    [ helpme
    ; chatteroff
    ; chatteron
    ; load
    ; clearholes
    ; countholes
    ; numholes
    ; numlfholes
    ; lochole
    ; loclfhole
    ; printhole
    ; printlfhole
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
    ]

(* registered commands *)

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
  try
    let head :: arglist = ExtString.String.nsplit cmd " " in
    let command = List.find (fun x -> head = x.name) !reg in
    command.run ppf arglist
  with
  | Not_found -> fprintf ppf "Such command does not exist!\n";
      let command = List.find (fun x -> "help" = x.name) !reg in
      command.run ppf []
  | ExtString.Invalid_string-> fprintf ppf "Splitting error\n"
  | _ -> helpme.run ppf []

let print_usage ppf =
  let _ = fprintf ppf "Usage: \n" in
  helpme.run ppf []
