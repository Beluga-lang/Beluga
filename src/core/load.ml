(* Loading files *)

open Support
module F = Misc.Function

let (dprintf, _, _) = Debug.(makeFunctions' (toFlags [11]))
open Debug.Fmt

let is_cfg filename =
  Filename.check_suffix filename ".cfg"

(** Loads an entire input channel as a list of strings, each of which
    representing one line.
 *)
let rec accum_lines input =
  try
    let res = input_line input in
    res :: accum_lines input
  with
    | End_of_file -> []

let rec trim_comment str =
  let len = String.length str in
  match str with
  | "" -> ""
  | s when Misc.Char.equals s.[0] ' ' -> trim_comment (String.sub s 1 (len - 1))
  | s when Misc.Char.equals s.[0] '\t' -> trim_comment (String.sub s 1 (len - 1))
  | s when Misc.Char.equals s.[0] '%' -> ""
  | s when Misc.Char.equals s.[len - 1] ' ' -> trim_comment (String.sub s 0 (len - 1))
  | s -> s

let filter_lines files =
  let files' = List.map trim_comment files in
  List.filter (fun s -> String.length s != 0) files'

(** Given a path to a cfg file and an open input channel to it,
    computes the paths to all the referenced beluga files.
 *)
let process_cfg_chan filename chan =
  let lines = accum_lines chan in
  close_in chan;
  let dir = Filename.dirname filename ^ "/" in
  List.map (fun x -> dir ^ x) (filter_lines lines)

(** Given a path to a cfg file, computes the paths to all the
    references beluga files.
 *)
let resolve_cfg_paths filename =
  let cfg = open_in filename in
  process_cfg_chan filename cfg

(** Resolves a path specified to be loaded.
    If the path is a CFG file, it is immediately loaded and the list
    of paths contained therein is returned.
    If the path is not a CFG file, it is returned verbatim.
 *)
let resolve_path f =
  (* XXX should this recursively allow cfg paths within cfg files? -je *)
  if is_cfg f
  then resolve_cfg_paths f
  else [f]

let forbid_leftover_vars path = function
  | None -> ()
  | Some vars ->
     Chatter.print 1
       "@[<v>## Leftover variables: %s  ##\
        @,  @[%a@]@]@."
       path
       Recsgn.fmt_ppr_leftover_vars vars;
     raise (Abstract.Error (Syntax.Loc.ghost, Abstract.LeftoverVars))

let load_file ppf file_name =
  let sgn =
    Parser.(Runparser.parse_file (Loc.initial file_name) (only sgn) |> extract)
    (* If the file starts with global pragmas then process them now. *)
    |> F.through
         begin fun sgn ->
         if !Options.Testing.print_external_syntax then
           begin
             Chatter.print 1
               "## External syntax dump: %s ##@." file_name;
             Format.fprintf ppf "@[%a@]"
               Pretty.Ext.DefaultPrinter.fmt_ppr_sgn sgn
           end
         end
    |> Recsgn.apply_global_pragmas
  in

  Chatter.print 1 "## Type Reconstruction begin: %s ##@." file_name;

  let sgn', leftoverVars = Recsgn.recSgnDecls sgn in
  let _ = Store.Modules.reset () in

  Chatter.print 2
    "@[<v>## Internal syntax dump: %s ##@,@[<v>%a@]@]@." file_name
    Pretty.Int.DefaultPrinter.fmt_ppr_sgn sgn';

  Chatter.print 1 "## Type Reconstruction done:  %s ##@." file_name;

  (* XXX pretty sure the list of cov problems is never added to -je
     So this call to Coverage.iter never does anything.
     Coverage.iter
     begin function
     | Coverage.Success -> ()
     | Coverage.Failure message ->
     if !Coverage.warningOnly then
     Error.addInformation ("WARNING: Cases didn't cover: " ^ message)
     else
     raise (Coverage.Error (Syntax.Loc.ghost, Coverage.NoCover message))
     end;
   *)

  if !Coverage.enableCoverage then
    Chatter.print 2 "## Coverage checking done: %s  ##@." file_name;

  Logic.runLogic (); (* TODO Logic needs to accept a formatter -je *)
  if not (Holes.none ()) then
    begin
      let open Format in
      Chatter.print 1
        "@[<v>## Holes: %s  ##@,@[<v>%a@]@]@."
        file_name
        (pp_print_list Interactive.fmt_ppr_hole) (Holes.list ());
    end;

  forbid_leftover_vars file_name leftoverVars;

  if !Typeinfo.generate_annotations then
    Typeinfo.print_annot file_name;
  if !Monitor.on || !Monitor.onf then
    Monitor.print_timer () ;

  if !Html.generate then Html.generatePage file_name

let load_one ppf path =
  try
    load_file ppf path
  with
  | e ->
     dprintf
       begin fun p ->
       p.fmt
         "@[<v 2>[load_one] %s backtrace:@,@[%a@]@]"
         path
         Format.pp_print_string (Printexc.get_backtrace ())
       end;
     raise e

let load ppf f =
  let all_paths = resolve_path f in
  Gensym.reset ();
  Store.clear ();
  Typeinfo.clear_all ();
  Holes.clear();
  List.iter
    (load_one ppf)
    all_paths;
  all_paths
