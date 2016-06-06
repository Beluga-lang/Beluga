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
  open Store


  let theoremToLatex (Theorem (tau)) cidProg =
    let sCl = Latexinductive.Convert.typToClause tau in
    let name = Id.string_of_name_latex (Cid.Comp.get cidProg).Cid.Comp.name in
    sprintf "\\begin{theorem}\n[%s] %s\n\\end{theorem}"
      name (Latexinductive.Printer.clauseToLatex sCl)

  (* printArguments n = "\\;#1\\;#2 ... \\;#n" - only called with n > 0 *)
  let rec printArguments n = match n with
    | 1 -> "\\;#1"
    | n -> (printArguments (n-1)) ^ (sprintf "\\;#%d" n)

  let cidProgToMaccro cidProg =
    (* get name of prog constant *)
    let compEntry = Cid.Comp.get cidProg in
    let compName = compEntry.Cid.Comp.name in
    let name = Id.string_of_name_latex compName in
    (* get number of arguments  *)
    let n = Cid.Comp.args_of_name compName in
    match n with 
      | 0 -> sprintf "\\newcommand{\\COMP%s}{\\mathsf{%s}}" 
              name name
      | n -> sprintf "\\newcommand{\\COMP%s}[%d]{\\mathsf{%s}%s}" 
              name n name (printArguments n)



  (* expChkToString    : LF.mctx -> Comp.gctx -> Comp.exp_chk -> string *)

  (* val ann : Syntax.Int.LF.ctyp_decl Syntax.Int.LF.ctx
               -> Syntax.Int.Comp.ctyp_decl Syntax.Int.LF.ctx
               -> Syntax.Int.Comp.exp_chk
               -> (Syntax.Int.Comp.typ * Syntax.Int.LF.msub)
               -> Annotated.Comp.exp_chk
   *)

  let proofToLatex (Proof (v)) cidProg =
    (*let Comp.RecValue (cidProg, expChk, msub, env) = v in 
    let annExpChk = Annotate.Comp.ann LF.Empty LF.Empty expChk tclo in 
    Latexproof.parse annExpChk;*)

    "PROOF"
    (*
    sprintf "PROOF :\n\n%s" 
      (Annotate.PrettyAnn.expChkToString LF.Empty LF.Empty annExpChk)
     *)



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
    	fprintf outMain "%s\n\n%s\n\n" (theoremToLatex theorem cidProg) (proofToLatex proof cidProg);
      fprintf outMaccros "%s\n\n" (cidProgToMaccro cidProg)
   	in 
   	Hashtbl.iter recToLatex recTypes;
   	close_out outMaccros;
    close_out outMain

    let printRecLatex mainFile =
      robStore ();
      printSignatureLatex mainFile;
      clearIndex ()


end









