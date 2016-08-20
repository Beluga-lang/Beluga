open Printf


module Printer = struct

  open Store
  module P = Pretty.Int.DefaultPrinter


  let printSchemasLatex mainFile =
    try
      let outMaccros = 
        open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 "latex/maccros.tex" 
      in
      let outMain =
        open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 mainFile 
      in
      let store = DynArray.get Cid.Schema.store !(Modules.current) in
      DynArray.iter (fun schema -> fprintf outMain "%s\n\n" (P.schemaToLatex schema.Cid.Schema.schema)) store;
      DynArray.clear store;
      close_out outMaccros;
      close_out outMain
    with _ -> ()


end