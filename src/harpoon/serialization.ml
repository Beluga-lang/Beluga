open Support
open Beluga
open Beluga_syntax
open Synint

module F = Fun
module P = Prettyint.DefaultPrinter

let dprintf, _, _ = Debug.(makeFunctions' (toFlags [15]))
open Debug.Fmt

(**
 * TODO: Move this util into a dedicated module
 * TODO: Add more abstraction layers for system level operations
 *)
let replace_locs (replacees : (Location.t * (Format.formatter -> unit -> unit)) list) : unit =
  replacees
  |> Hashtbl.group_by F.(Location.filename ++ Pair.fst)
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
         p.fmt "[%s] opening file %s" __FUNCTION__ file_name
         end;
       In_channel.with_open_bin file_name
         begin fun in_ch ->
         let in_lexbuf = Sedlexing.Utf8.from_channel in_ch in
         let read_length = ref 0 in
         let indentation = ref 0 in
         let raise_edited_error () =
           Error.raise_violation "[harpoon] [serialize] original file is edited"
         in
         let with_uchar n f =
           match Sedlexing.next in_lexbuf with
           | None -> n ()
           | Some v ->
              incr read_length;
              if v <> Uchar.of_char '\n'
              then incr indentation
              else indentation := 0;
              f v
         in
         dprintf (fun p -> p.fmt "[%s] opening temp file beluga_harpoon" __FUNCTION__);
         Filename.(Files.with_temp_file (dirname file_name) (basename file_name))
           begin fun temp_file_name out_ch ->
           dprintf (fun p -> p.fmt "[%s] opened %s" __FUNCTION__ temp_file_name);
           let outbuf = Buffer.create 4 in
           replacees
           |> List.sort (fun (l1, _) (l2, _) -> Location.compare_start l1 l2)
           |> List.iter
                begin fun (loc, printer) ->
                let start_offset = Location.start_offset loc in
                let stop_offset = Location.stop_offset loc in
                Fun.until
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
                Fun.until
                  begin fun _ ->
                  if !read_length < stop_offset
                  then
                    with_uchar raise_edited_error (Fun.const true)
                  else
                    false
                  end
                end;
           Fun.until
             begin fun _ ->
             with_uchar (Fun.const false)
               begin fun v ->
               Buffer.clear outbuf;
               Buffer.add_utf_8_uchar outbuf v;
               Buffer.output_buffer out_ch outbuf;
               true
               end
             end;
           dprintf begin fun p ->
             p.fmt "[%s] moving %s -> %s" __FUNCTION__ temp_file_name file_name
             end;
           Sys.rename temp_file_name file_name
           end
         end
       end

let update_existing_holes existing_holes =
  existing_holes
  |> List.filter_map
      begin fun (loc, _cid, ps) ->
        let open Option in
        let open Comp in
        !(ps.solution)
        $> fun p ->
           ( loc
           , fun fmt _ -> P.fmt_ppr_cmp_proof ps.context.cD ps.context.cG fmt p
           )
      end
  |> replace_locs

let append_sessions target_file_name new_mutual_rec_thmss =
  Out_channel.with_open_gen [ Open_append; Open_text ] 0o600 target_file_name
    (fun out_ch ->
      List.pp
        ~pp_sep:(fun _ppf () -> ())
        (fun ppf thms ->
          Format.fprintf ppf "@\n@[<v>%a;@]@\n"
            (List.pp
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "and@,")
               Theorem.serialize)
            thms)
        (Format.formatter_of_out_channel out_ch)
        new_mutual_rec_thmss)
