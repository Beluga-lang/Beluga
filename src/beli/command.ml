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
    | Not_found -> fprintf ppf "Such command does not exist!!\n";
      List.iter (fun x -> fprintf ppf "%s" x.help) !reg;
    | ExtString.Invalid_string-> fprintf ppf "Splitting error\n"


(* The built in commands *)
let countholes = {name = "countholes";
                  run = (fun _ppf _ -> Holes.printNumHoles ());
                  help = "countholes                Print the total number of holes\n"} in
reg := countholes :: !reg


let chatteron = {name = "chatteron";
                 run = (fun ppf _ -> Debug.chatter :=1; fprintf ppf "The chatter is on now.\n");
                 help = "chatteron                 Turn on the chatter\n"} in
reg := chatteron :: !reg


let chatteroff = {name = "chatteroff";
                  run = (fun ppf _ -> Debug.chatter :=0; fprintf ppf "The chatter is off now.\n");
                  help = "chatteroff                Turn off the chatter\n"} in
reg := chatteroff :: !reg


let types = {name = "types";
             run = (fun ppf _ ->
               let entrylist = List.rev_map Typ.get (!Typ.entry_list) in
               let dctx = Synint.LF.Null in
               List.iter (fun x -> fprintf ppf "%s:" x.Typ.name.Id.string_of_name; ppr_lf_kind dctx x.Typ.kind; fprintf ppf " \n") entrylist);
             help = "types                     Print out all types\n"} in
reg := types :: !reg


let load = {name = "load";
            run = (fun ppf arglist ->
              try
                let arg = List.hd arglist in
                let sgn = Parser.parse_file ~name:arg Parser.sgn in
                Recsgn.recSgnDecls sgn;
                fprintf ppf "The file has been successfully loaded.\n"
              with
                |Failure _ -> fprintf ppf "Please provide the file name\n");
            help = "load filename             Load the file \"filename\" into the interpreter\n"} in
reg := load :: !reg


let printhole = {name = "printhole";
                 run = (fun ppf arglist ->
                   try
                     let arg = List.hd arglist in
                     Holes.printOneHole (to_int arg)
                   with
                     |Failure _ -> fprintf ppf "Error occurs when analyzing argument list\n");
                 help = "printhole i               Print out all the information of the i-th hole\n"} in
reg := printhole :: !reg


let lochole = {name = "lochole";
               run = (fun ppf arglist ->
                   try
                     let arg = List.hd arglist in
                     Holes.printHolePos (to_int arg)
                   with
                     |Failure _ -> fprintf ppf "Error occurs when analyzing argument list\n");
               help = "lochole i                 Print out the location information of the i-th hole\n"} in
reg := lochole :: !reg


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
                    help = "constructors tpname       Print all constructors of a given type\n"} in
reg := constructors :: !reg


let helpme = {name = "help";
              run = (fun ppf _ -> List.iter (fun x -> fprintf ppf "%s" x.help) !reg);
              help = "======================help manual======================\n"} in
reg := helpme :: !reg

(* ... *)
