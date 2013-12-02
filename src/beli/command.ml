open Core
open ExtString.String
open Store.Cid
open Pretty.Int.DefaultPrinter
open Format

(* the type of commands  *)
type command = { name : string ;
                 run : Format.formatter -> string list -> unit ;
                   help : string }

(* registered commands *)
let reg : command list ref = ref []

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

let countholes = {name = "countholes";
                  run = (fun ppf _ -> fprintf ppf "%d\n" (Holes.getNumHoles()));
                  help = "Print the total number of holes"} in

let chatteron = {name = "chatteron";
                 run = (fun ppf _ -> Debug.chatter :=1; fprintf ppf "The chatter is on now.\n");
                 help = "Turn on the chatter"} in

let chatteroff = {name = "chatteroff";
                  run = (fun ppf _ -> Debug.chatter :=0; fprintf ppf "The chatter is off now.\n");
                  help = "Turn off the chatter"} in

let types = {name = "types";
             run = (fun ppf _ ->
               let entrylist = List.rev_map Typ.get (!Typ.entry_list) in
               let dctx = Synint.LF.Null in
               List.iter (fun x -> fprintf ppf "%s:" x.Typ.name.Id.string_of_name; ppr_lf_kind dctx x.Typ.kind; fprintf ppf " \n") entrylist);
             help = "Print out all types currently defined"} in


let load = {name = "load";
            run = (fun ppf arglist ->
              try
                let arg = List.hd arglist in
                let sgn = Parser.parse_file ~name:arg Parser.sgn in
                Recsgn.recSgnDecls sgn;
                fprintf ppf "The file has been successfully loaded.\n"
              with
              |Failure _ -> fprintf ppf "Please provide the file name\n");
            help = "Load the file \"filename\" into the interpreter"} in



let printhole = {name = "printhole";
                 run = (fun ppf arglist ->
                   try
                     let arg = List.hd arglist in
                     Holes.printOneHole (to_int arg)
                   with
                   |Failure _ -> fprintf ppf "Error occurs when analyzing argument list\n");
                 help = "Print out all the information of the i-th hole passed as a parameter"} in

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
                         "(\"%s\" %d %d %d %d %d %d)\n"
                         file_name
                         start_line start_bol start_off
                         stop_line stop_bol stop_off
                   | None -> fprintf ppf "Error no such hole"
                 with
                 |Failure _ -> fprintf ppf "Error occurs when analyzing argument list\n");
               help = "Print out the location information of the i-th hole passed as a parameter"} in

let constructors = {name = "constructors";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let entrylist = List.rev_map Typ.get (!Typ.entry_list) in
                        let entry = List.find (fun x -> arg = x.Typ.name.Id.string_of_name) entrylist in
                        let mctx = Synint.LF.Empty in
                        let dctx = Synint.LF.Null in
                        let termlist = List.rev_map Term.get (entry.Typ.constructors) in
                        List.iter (fun x -> fprintf ppf "%s: [%d] " x.Term.name.Id.string_of_name x.Term.implicit_arguments; ppr_lf_typ mctx dctx x.Term.typ; fprintf ppf "\n") termlist
                      with
                      | Not_found -> fprintf ppf "Such type does not exist!!\n"
                      | Failure _ -> fprintf ppf "Error occurs when analyzing argument list\n");
                    help = "Print all constructors of a given type passed as a parameter"} in



let helpme = {name = "help";
              run = (fun ppf _ -> List.iter (fun x -> fprintf ppf "%%:%15s\t %s\n" x.name x.help) !reg);
              help = "list all availale commands with a short description"} in



let fill = { name = "fill" ;
             run = (fun ppf args ->
               try
                 let i = to_int (List.hd args) in
                 let eq = List.hd (List.tl args) in
                 let str = String.concat " " (List.tl (List.tl args)) in
                 let input = "rec t : [. t] = "^str^";" in
                 if eq = "with" then (
                   let sgn = Parser.parse_string ~name:"<fill>" ~input:input Parser.sgn in
                   let Syntax.Ext.Sgn.Rec (_, (Synext.Comp.RecFun(_,_,outexp))::[])::[] = sgn in
                   (try
                     let (loc, cD, cG, tclo) = Holes.getOneHole i in
                     (if !Debug.chatter != 0 then fprintf ppf "Fill: EXT done\n");
                     let vars = Interactive.gctxToVars cG in
                     let cvars = Interactive.mctxToCVars cD in
                     let apxexp = Index.hexp cvars vars outexp in
                     (if !Debug.chatter != 0 then fprintf ppf "Fill: APX done\n");
                     let intexp = Reconstruct.elExp cD cG apxexp tclo in
                     (if !Debug.chatter != 0 then fprintf ppf "Fill: INT done\n");
                     Check.Comp.check cD cG intexp tclo; (* checks that exp fits the hole *)
                     let intexp' = Interactive.mapHoleChk (fun ll -> fun _ ->
                       let i = Holes.getStagedHoleNum ll in
                       let loc' = Interactive.nextLoc loc in
                       Holes.setStagedHolePos i loc';
                       Synint.Comp.Hole (loc', (fun () -> Holes.getHoleNum loc'))) intexp in
                     Interactive.replaceHole i intexp'
                   with
                   | e -> fprintf ppf "Error while replacing hole with expression : %s" (Printexc.to_string e) ))
                 else
                   failwith "See help"
               with
               | _ -> fprintf ppf "Error in fill\n");
             help = "\"fill\" i \"with\" exp fills the ith hole with exp"} in


let split = { name = "split" ;
              run = (fun ppf args ->
                Printexc.record_backtrace true;
                try
                  let e = (List.hd args) in
                  let i = to_int (List.hd (List.tl args)) in
                  (match (Interactive.split e i) with
                  | None -> fprintf ppf "No variable %s found\n" e
                  | Some exp -> Interactive.replaceHole i exp )
                with
                | Failure s  -> fprintf ppf "Error in split: %s \n" s;  (Printexc.print_backtrace stdout)
                | _  -> fprintf ppf "Error in split. \n";  (Printexc.print_backtrace stdout)
                      );
              help = "split e n  tries to split on variable e in the nth hole"} in

let intro = {name = "intro";
              run = (fun ppf args ->
                try
                  let i = to_int (List.hd args) in
                  (match (Interactive.intro i) with
                  | None -> fprintf ppf "Nothing to introduce in hole %d. \n" i
                  | Some exp -> Interactive.replaceHole i exp)
                with
                | Failure s -> fprintf ppf "Error in intro: %s\n" s
                |  _ ->      fprintf ppf "Error in intro\n"  );
              help = "intro n tries to introduce variables in the nth hole"} in


let compconst = {name = "Constructors";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let entrylist = List.rev_map CompTyp.get (!CompTyp.entry_list) in
                        let entry = List.find (fun x -> arg = x.CompTyp.name.Id.string_of_name) entrylist in
                        let mctx = Synint.LF.Empty in
                        let termlist = List.rev_map CompConst.get (entry.CompTyp.constructors) in
                        List.iter (fun x -> fprintf ppf "%s: [%d] " x.CompConst.name.Id.string_of_name x.CompConst.implicit_arguments; ppr_cmp_typ mctx x.CompConst.typ; fprintf ppf "\n") termlist
                      with
                      | Not_found -> fprintf ppf "Such type does not exist!!\n"
                      | Failure _ -> fprintf ppf "Error occurs when analyzing argument list\n");
                    help = "Print all constructors of a given computational datatype passed as a parameter"} in


let signature = {name = "fsig";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let (cidlist,_) = List.split (!Comp.entry_list) in
                        let entrylist = List.rev_map Comp.get cidlist in
                        let entry = List.find (fun x -> arg = x.Comp.name.Id.string_of_name) entrylist in

                        let mctx = Synint.LF.Empty in
                        fprintf ppf "%s:  " entry.Comp.name.Id.string_of_name; ppr_cmp_typ mctx entry.Comp.typ; fprintf ppf "\n"
                      with
                      | Not_found -> fprintf ppf "Such function does not exist!\n"
                      | Failure _ -> fprintf ppf "Error occurs when analyzing argument list\n");
                    help = "fsig e : Prints the signature of the function e, if such function is currently defined" } in


let printfun = {name = "fdef";
                    run = (fun ppf arglist ->
                      try
                        let arg = List.hd arglist in
                        let (cidlist,_) = List.split (!Comp.entry_list) in
                        let entrylist = List.rev_map Comp.get cidlist in
                        let entry = List.find (fun x -> arg = x.Comp.name.Id.string_of_name) entrylist in
                        (match entry.Comp.prog with
                        | Synint.Comp.RecValue (prog, ec, _ms, _env) ->
                            ppr_sgn_decl (Synint.Sgn.Rec(prog,entry.Comp.typ ,ec))
                        |     _  -> fprintf ppf "%s is not a function. \n" arg
                            )
                      with
                      | Not_found -> fprintf ppf "Such function does not exist!\n"
                      | Failure _ -> fprintf ppf "Error occurs when analyzing argument list\n");
                    help = "Print all the type of the functions currently defined" } in


(* Registering built-in commands *)

reg := [helpme       ;
        chatteroff   ;
        chatteron    ;
        countholes   ;
        load         ;
        printhole    ;
        lochole      ;
        constructors ;
        types        ;
        fill         ;
        split        ;
        intro        ;
        compconst    ;
         signature   ;
        printfun
       ]
