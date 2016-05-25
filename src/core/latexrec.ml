open Syntax.Int
open Printf

type theorem =
  | Theorem of Comp.typ

type proof =
  | Proof of Comp.value



module Convert = struct

  let compTypToTheorem tau = Theorem (tau)

  let compValueToProof v = Proof (v)


end


module Index = struct

  open Store

  (* Hashtb.
     key : (Id.cid_prog * Loc.t)
     value : (theorem * proof)
   *)
  let recTypes = Hashtbl.create 0

  (* val addEntry : (Id.cid_prog * Loc.t) -> (Comp.Typ, Comp.value) -> () *)
  let addBinding (cidProg, loc) (tau, v) =
    Hashtbl.add recTypes (cidProg, loc) 
      ((Convert.compTypToTheorem tau), (Convert.compValueToProof v))

  let storeEntry (cidProg, loc) =
    let compEntry = Cid.Comp.get cidProg in
    let compTyp = compEntry.Cid.Comp.typ in 
    let compProg = compEntry.Cid.Comp.prog in
    addBinding (cidProg, loc) (compTyp, compProg)

  let robStore () =
    try
      List.iter storeEntry !(DynArray.get Cid.Comp.entry_list !(Modules.current));
    with
    | _ -> ()

  (* clearIndex () = ()
    Empty the local storage.
   *)
  let clearIndex () = Hashtbl.clear recTypes


end


module Printer = struct

  module P = Pretty.Int.DefaultPrinter
  open Index

  (* val compTypToLatex : LF.mctx -> Comp.typ -> string *)
  let compTypToLatex cD tau =
    P.compTypToLatex cD tau

  (* val cdeclToLatex : LF.mctx -> LF.ctyp_decl -> string *)
  let cdeclToLatex cD cdecl =
    P.cdeclToLatex cD cdecl

  let theoremToLatex (Theorem (tau)) cidProg =
    let sCl = Latexinductive.Convert.typToClause tau in
    let name = Id.string_of_name_latex (Store.Cid.Comp.get cidProg).Store.Cid.Comp.name in
    sprintf "\\begin{theorem}\n[%s] %s\n\\end{theorem}"
      name (Latexinductive.Printer.clauseToLatex sCl)

  (*let cidProgToMaccro cidProg =
    (* get name of prog constant *)
    let compEntry = Store.Cid.Comp.get cidProg in
    let compName = compEntry.Store.Cid.Comp.name in
    let name = Id.string_of_name_latex compName in
    (* get number of arguments  *)
    let n = *)



  let proofToLatex (Proof (v)) =
    "PROOF"

  let printSignatureLatex mainFile =
    let outMaccros = 
      open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 "latex/maccros.tex" 
    in
    let outMain =
      open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 mainFile 
    in
    (* takes as input one binding (k, v) of recTypes : 
       k : (Id.cid_prog * Loc.t), v : (theorem * proof) 
     *)
    let recToLatex (cidProg, loc) (theorem, proof) =
    	fprintf outMain "%s\n\n%s\n\n" (theoremToLatex theorem cidProg) (proofToLatex proof)
   	in 
   	Hashtbl.iter recToLatex recTypes;
   	close_out outMaccros;
    close_out outMain

    let printRecLatex mainFile =
      robStore ();
      printSignatureLatex mainFile;
      clearIndex ()


end









