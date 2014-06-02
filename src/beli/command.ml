open Core
open ExtString.String
open Store.Cid
open Pretty.Int.DefaultPrinter
open Format

(* the type of commands  *)
type command = { name : string ;
                 run : Format.formatter -> string list -> unit ;
                   help : string }



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
                  run = (fun ppf _ -> fprintf ppf " - Computation Level Holes: %d\n - LF Level Holes: %d\n" (Holes.getNumHoles()) (Lfholes.getNumHoles()));
                  help = "Print the total number of holes"}

let chatteron = {name = "chatteron";
                 run = (fun ppf _ -> Debug.chatter :=1; fprintf ppf " - The chatter is on now.\n");
                 help = "Turn on the chatter"}


let chatteroff = {name = "chatteroff";
                  run = (fun ppf _ -> Debug.chatter :=0; fprintf ppf " - The chatter is off now.\n");
                  help = "Turn off the chatter"}


let types = {name = "types";
             run = (fun ppf _ ->
               let entrylist = List.rev_map Typ.get (!Typ.entry_list) in
               let dctx = Synint.LF.Null in
               List.iter (fun x -> fprintf ppf " - %s:" x.Typ.name.Id.string_of_name; ppr_lf_kind dctx x.Typ.kind; fprintf ppf " \n") entrylist);
             help = "Print out all types currently defined"}


let load = {name = "load";
            run = (fun ppf arglist ->
              try
                let arg = List.hd arglist in
                let sgn = Parser.parse_file ~name:arg Parser.sgn in
                Recsgn.recSgnDecls sgn;
                fprintf ppf " - The file has been successfully loaded.\n"
              with
              |Failure _ -> fprintf ppf " - Please provide the file name\n");
            help = "Load the file \"filename\" into the interpreter"}



let printhole = {name = "printhole";
                 run = (fun ppf arglist ->
                   try
                     let arg = List.hd arglist in
                     Holes.printOneHole (to_int arg)
                   with
                   |Failure _ -> fprintf ppf " - Error occurs when analyzing argument list\n");
                 help = "Print out all the information of the i-th hole passed as a parameter"}

let printlfhole = {name = "printhole-lf";
                 run = (fun ppf arglist ->
                   try
                     let arg = List.hd arglist in
                     Lfholes.printOneHole (to_int arg)
                   with
                   |Failure _ -> fprintf ppf " - Error occurs when analyzing argument list\n");
                 help = "Print out all the information of the i-th LF hole passed as a parameter"}

let lochole = {name = "lochole";
               run = (fun ppf arglist ->
                 try
                   let arg = List.hd arglist in
                   match Holes.getHolePos (to_int arg) with
                   | Some loc ->
                       let (file_name,
                            start_line,
                            start_bol,
                            start_off,
                            stop_line,
                            stop_bol,
                            stop_off,
                            _ghost) = Core.Syntax.Loc.to_tuple loc in
                       fprintf ppf
                         " - (\"%s\" %d %d %d %d %d %d)\n"
                         file_name
                         start_line start_bol start_off
                         stop_line stop_bol stop_off
                   | None -> fprintf ppf " - Error no such hole"
                 with
                 |Failure _ -> fprintf ppf " - Error occured when analyzing argument list\n");
               help = "Print out the location information of the i-th hole passed as a parameter"}

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
                            _ghost) = Core.Syntax.Loc.to_tuple loc in
                       fprintf ppf
                         " - (\"%s\" %d %d %d %d %d %d)\n"
                         file_name
                         start_line start_bol start_off
                         stop_line stop_bol stop_off
                   | None -> fprintf ppf " - Error no such hole"
                 with
                 |Failure _ -> fprintf ppf " - Error occured when analyzing argument list\n");
               help = "Print out the location information of the i-th hole passed as a parameter"}

let constructors = {name = "constructors";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let entrylist = List.rev_map Typ.get (!Typ.entry_list) in
                        let entry = List.find (fun x -> arg = x.Typ.name.Id.string_of_name) entrylist in
                        let mctx = Synint.LF.Empty in
                        let dctx = Synint.LF.Null in
                        let termlist = List.rev_map Term.get (entry.Typ.constructors) in
                        List.iter (fun x -> fprintf ppf " - %s: [%d] " x.Term.name.Id.string_of_name x.Term.implicit_arguments; ppr_lf_typ mctx dctx x.Term.typ; fprintf ppf "\n") termlist
                      with
                      | Not_found -> fprintf ppf " - Such type does not exist!!\n"
                      | Failure _ -> fprintf ppf " - An error occured when analyzing argument list\n");
                    help = "Print all constructors of a given type passed as a parameter"}



let helpme = {name = "help";
              run = (fun ppf _ -> List.iter (fun x -> fprintf ppf "%%:%15s\t %s\n" x.name x.help) !reg);
              help = "list all availale commands with a short description"}



let fill = { name = "fill" ;
             run = (fun ppf args ->
               try
                 let i = to_int (List.hd args) in
                 let eq = List.hd (List.tl args) in
                 let str = String.concat " " (List.tl (List.tl args)) in
                 let input = "rec t : [ |- t] = "^str^";" in
                 if eq = "with" then (
                   let sgn = Parser.parse_string ~name:"<fill>" ~input:input Parser.sgn in
                   let Syntax.Ext.Sgn.Rec (_, (Synext.Comp.RecFun(_,_,outexp))::[])::[] = sgn in
                   (try
                     let (loc, cD, cG, tclo) = Holes.getOneHole i in
                     (if !Debug.chatter != 0 then fprintf ppf " - Fill: EXT done\n");
                     let vars = Interactive.gctxToVars cG in
                     let cvars = Interactive.mctxToCVars cD in
                     let apxexp = Index.hexp cvars vars outexp in
                     (if !Debug.chatter != 0 then fprintf ppf " - Fill: APX done\n");
                     let intexp = Reconstruct.elExp cD cG apxexp tclo in
                     (if !Debug.chatter != 0 then fprintf ppf " - Fill: INT done\n");
                     Check.Comp.check cD cG intexp tclo; (* checks that exp fits the hole *)
                     let intexp' = Interactive.mapHoleChk (fun ll -> fun _ ->
                       let i = Holes.getStagedHoleNum ll in
                       let loc' = Interactive.nextLoc loc in
                       Holes.setStagedHolePos i loc';
                       Synint.Comp.Hole (loc', (fun () -> Holes.getHoleNum loc'))) intexp in (* makes sure that new holes have unique location *)
                     Interactive.replaceHole i intexp'
                   with
                   | e -> fprintf ppf " - Error while replacing hole with expression : %s" (Printexc.to_string e) ))
                 else
                   failwith " - See help"
               with
               | e -> fprintf ppf " - \nError in fill: %s\n" (Printexc.to_string e));
             help = "\"fill\" i \"with\" exp fills the ith hole with exp"}

(* let fill-lf = { name = "filllf" ;
                run = (fun ppf args ->
                  try
                 let i = to_int (List.hd args) in
                 let eq = List.hd (List.tl args) in
                 let str = String.concat " " (List.tl (List.tl args)) in
                 let input = "let t = "^str^";" in
                 if eq = "with" then (
                   let sgn = Parser.parse_string ~name:"<fill>" ~input:input Parser.sgn in
                   let Syntax.Ext.Sgn.Rec (_, (Synext.Comp.RecFun(_,_,outexp))::[])::[] = sgn in
                   (try
                     let (loc, cD, psi, tclo) = Lfholes.getOneHole i in
                     (if !Debug.chatter != 0 then fprintf ppf " - LF Fill: EXT done\n");
                     let vars = Interactive.dctxToMVars psi in
                     let cvars = Interactive.mctxToCVars cD in
                     let apxexp = Index.hexp cvars vars outexp in
                     (if !Debug.chatter != 0 then fprintf ppf " - LF Fill: APX done\n");
                     let intexp = Reconstruct.elExp cD cG apxexp tclo in
                     (if !Debug.chatter != 0 then fprintf ppf " - LF Fill: INT done\n");
                     Check.Comp.check cD cG intexp tclo; (* checks that exp fits the hole *)
                     let intexp' = Interactive.mapHoleChk (fun ll -> fun _ ->
                       let i = Holes.getStagedHoleNum ll in
                       let loc' = Interactive.nextLoc loc in
                       Holes.setStagedHolePos i loc';
                       Synint.Comp.Hole (loc', (fun () -> Holes.getHoleNum loc'))) intexp in (* makes sure that new holes have unique location *)
                     Interactive.replaceHole i intexp'
                   with
                   | e -> fprintf ppf " - Error while replacing LF hole with expression : %s" (Printexc.to_string e) ))
                 else
                   failwith " - See help"
               with
               | e -> fprintf ppf " - \nError in fill-lf: %s\n" (Printexc.to_string e));
              help = "'fill-lf' i 'with' exp fills the ith lf hole with exp" } *)

let split = { name = "split" ;
              run = (fun ppf args ->
                Printexc.record_backtrace true;
                try
                  if (List.length args) < 2 then failwith "2 arguments expected, 1 - name of the variable 2 - hole #" else (
                  let e = (List.hd args) in
                  let i = to_int (List.hd (List.tl args)) in
                  (match (Interactive.split e i) with
                  | None -> fprintf ppf " - No variable %s found\n" e
                  | Some exp -> Interactive.replaceHole i exp ))
                with
                | Failure s  -> fprintf ppf " - Error in split: %s \n" s;  (Printexc.print_backtrace stdout)
                | _  -> fprintf ppf " - Error in split. \n";  (Printexc.print_backtrace stdout)
                      );
              help = "split e n  tries to split on variable e in the nth hole"}

let intro = {name = "intro";
              run = (fun ppf args ->
                try
                  let i = to_int (List.hd args) in
                  (match (Interactive.intro i) with
                  | None -> fprintf ppf " - Nothing to introduce in hole %d. \n" i
                  | Some exp -> Interactive.replaceHole i exp)
                with
                | Failure s -> fprintf ppf " - Error in intro: %s\n" s
                |  _ ->      fprintf ppf " - Error in intro\n"  );
              help = " - intro n tries to introduce variables in the nth hole"}


let compconst = {name = "Constructors";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let entrylist = List.rev_map CompTyp.get (!CompTyp.entry_list) in
                        let entry = List.find (fun x -> arg = x.CompTyp.name.Id.string_of_name) entrylist in
                        let mctx = Synint.LF.Empty in
                        let termlist = List.rev_map CompConst.get (entry.CompTyp.constructors) in
                        List.iter (fun x -> fprintf ppf " - %s: [%d] " x.CompConst.name.Id.string_of_name x.CompConst.implicit_arguments; ppr_cmp_typ mctx x.CompConst.typ; fprintf ppf "\n") termlist
                      with
                      | Not_found -> fprintf ppf " - Such type does not exist!!\n"
                      | Failure _ -> fprintf ppf " - Error occured when analyzing argument list\n");
                    help = "Print all constructors of a given computational datatype passed as a parameter"}


let signature = {name = "fsig";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let (cidlist,_) = List.split (!Comp.entry_list) in
                        let entrylist = List.rev_map Comp.get cidlist in
                        let entry = List.find (fun x -> arg = x.Comp.name.Id.string_of_name) entrylist in

                        let mctx = Synint.LF.Empty in
                        fprintf ppf " - %s:  " entry.Comp.name.Id.string_of_name; ppr_cmp_typ mctx entry.Comp.typ; fprintf ppf "\n"
                      with
                      | Not_found -> fprintf ppf " - Such function does not exist!\n"
                      | Failure _ -> fprintf ppf " - Error occurs when analyzing argument list\n");
                    help = "fsig e : Prints the signature of the function e, if such function is currently defined" }


let printfun = {name = "fdef";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let (cidlist,_) = List.split (!Comp.entry_list) in
                        let entrylist = List.rev_map Comp.get cidlist in
                        let entry = List.find (fun x -> arg = x.Comp.name.Id.string_of_name) entrylist in
                        (match entry.Comp.prog with
                        | Synint.Comp.RecValue (prog, ec, _ms, _env) ->
                            fprintf ppf " - "; ppr_sgn_decl (Synint.Sgn.Rec(prog,entry.Comp.typ ,ec))
                        |     _  -> fprintf ppf " - %s is not a function. \n" arg
                            )
                      with
                      | Not_found -> fprintf ppf " - Such function does not exist!\n"
                      | Failure _ -> fprintf ppf " - Error occurs when analyzing argument list\n");
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
                        ()
                      end
                    with
                    | e -> fprintf ppf " - Error in query : %s\n" (Printexc.to_string e));
            help = "%:query EXPECTED TRIES TYP.\tQuery solutions to a given type"}

(* let save = {name = "save";
            run = (fun ppf arglist ->
              let name = if List.length arglist <> 1 then "out.bel" else List.hd arglist in
              let oc = open_out name in
              let 

                    );
            help = "Save working file with a given filename. If no filename is provided, fill with be \"out.bel\""
            } *)
(* Registering built-in commands *)

let _ = reg := [
        helpme       ;
        chatteroff   ;
        chatteron    ;
        countholes   ;
        load         ;
        printhole    ;
        printlfhole  ;
        lochole      ;
        loclfhole    ;
        constructors ;
        types        ;
        fill         ;
        split        ;
        intro        ;
        compconst    ;
        signature    ;
        printfun     ;
        quit         ;
        query        ;
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