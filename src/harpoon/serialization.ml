open Support
open Beluga
open Syntax.Int

module F = Misc.Function
module Loc = Syntax.Loc
module P = Pretty.Int.DefaultPrinter

let dprintf, _, _ = Debug.(makeFunctions' (toFlags [15]))
open Debug.Fmt

(**
 * TODO: Move this util into a dedicated module
 * TODO: Add more abstraction layers for system level operations
 *)
let replace_locs (replacees : (Loc.t * (Format.formatter -> unit -> unit)) list) : unit =
  replacees
  |> Misc.Hashtbl.group_by F.(Loc.filename ++ fst)
  (* iterate over replacee groups
   (* open file stream *)
   (* sort items in the group *)
   (* iterate over the items
   (* iterate over file stream and print uchars until it meets the item hole *)
   (* print the item value *)
   *)
   *)
  |> Hashtbl.iter
       begin fun file_name replacees ->
       dprintf begin fun p ->
         p.fmt "[replace_locs] opening file %s" file_name
         end;
       Files.with_in_channel file_name
         begin fun in_ch ->
         let in_lexbuf = Sedlexing.Utf8.from_channel in_ch in
         let read_length = ref 0 in
         let indentation = ref 0 in
         let raise_edited_error () =
           Error.violation "[harpoon] [serialize] original file is edited"
         in
         let with_uchar n f =
           match Sedlexing.next in_lexbuf with
           | None -> n ()
           | Some v ->
              incr read_length;
              if v != Uchar.of_char '\n'
              then incr indentation
              else indentation := 0;
              f v
         in
         dprintf (fun p -> p.fmt "[replace_locs] opening temp file beluga_harpoon");
         Filename.(Files.with_temp_file (dirname file_name) (basename file_name))
           begin fun temp_file_name out_ch ->
           dprintf (fun p -> p.fmt "[replace_locs] opened %s" temp_file_name);
           let outbuf = Buffer.create 4 in
           replacees
           |> List.sort (Misc.on fst Loc.compare_start)
           |> List.iter
                begin fun (loc, printer) ->
                let start_offset = Loc.start_offset loc in
                let stop_offset = Loc.stop_offset loc in
                Misc.Function.until
                  begin fun _ ->
                  if !read_length < start_offset
                  then
                    with_uchar raise_edited_error
                      begin fun v ->
                      Buffer.clear outbuf;
                      Buffer.add_utf_8_uchar outbuf v;
                      Buffer.output_buffer out_ch outbuf;
                      true
                      end
                  else
                    false
                  end;
                let ppf = Format.formatter_of_out_channel out_ch in
                Format.pp_open_vbox ppf !indentation;
                printer ppf ();
                Format.pp_close_box ppf ();
                Format.pp_print_flush ppf ();
                Misc.Function.until
                  begin fun _ ->
                  if !read_length < stop_offset
                  then
                    with_uchar raise_edited_error (Fun.const true)
                  else
                    false
                  end
                end;
           Misc.Function.until
             begin fun _ ->
             with_uchar (Fun.const false)
               begin fun v ->
               Buffer.clear outbuf;
               Buffer.add_utf_8_uchar outbuf v;
               Buffer.output_buffer out_ch outbuf;
               true
               end
             end;
           close_in in_ch;
           close_out out_ch;
           dprintf begin fun p ->
             p.fmt "[replace_locs] moving %s -> %s" temp_file_name file_name
             end;
           Sys.rename temp_file_name file_name
           end
         end
       end

let update_existing_holes existing_holes =
  let open Maybe in
  existing_holes
  |> filter_map
       begin fun (loc, ps) ->
       let open Comp in
       !(ps.solution)
       $> fun p ->
          ( loc
          , fun fmt _ -> P.fmt_ppr_cmp_proof ps.context.cD ps.context.cG fmt p
          )
       end
  |> replace_locs

let append_sessions target_file_name new_mutual_rec_thmss =
  let out_ch = open_out_gen [Open_append; Open_text] 0o600 target_file_name in
  let out_ppf = Format.formatter_of_out_channel out_ch in
  let printf_out fmt = Format.fprintf out_ppf fmt in
  new_mutual_rec_thmss
  |> List.iter
       begin fun thms ->
       printf_out "@.";
       printf_out "@[<v>";
       thms
       |> List.iteri
            begin fun i thm ->
            if i != 0
            then printf_out "and@,";
            Format.fprintf out_ppf "%a" Theorem.serialize thm
            end;
       printf_out ";@]@."
       end;
  close_out out_ch
