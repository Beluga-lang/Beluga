open Syntax
open Substitution
open Id
open Ast
open Pretty
(**

   @author Marie-Andree B.Langlois
*)

module Loc = Syntax.Loc
let out_channel = open_out "reconstruct.out";

exception Error of string

let printLocation loc = Parser.Grammar.Loc.print Format.std_formatter loc

(* Terminal and Helper Functions Section *)

(* string -> string list -> bool *)
(** use map instead *)
let rec checkString s lt = List.fold_left (fun x y -> if y = s then true else x) false lt

type jdef = Jdef of string * string list

let rec findJu s lju = List.fold_left (fun x y -> let (Jdef(s1, lsym)) = y in if (checkString s lsym) then (Jdef(s1, lsym)) else x) (Jdef("",[])) lju

let rec printL l = List.fold_left (fun x y -> output_string out_channel y; output_string out_channel " print list \n") () l

let rec printLju l = List.fold_left (fun x y -> let Jdef(h1,h2) = y in output_string out_channel h1; output_string out_channel " : print list of symbols: \n"; printL h2) () l

type bind = Paire of alternative * (string * string) list

let rec findJ va lju = (** should check if you have all the symbols of the judgement *)
  match va with
    | VAltAtomic(l, s, Some(vao)) -> let Jdef(s1, lsym) = findJu s lju in if (s1 = "") then findJ vao lju else (s1, lsym) 
                                     (*raise (Error ("This theorem statement should refer to a judgment."))*)
    | VAltAtomic(l, s, None) -> let Jdef(s1, lsym) = findJu s lju in if s1 = "" then (s,[]) else (s1, lsym)
    | VAltBin(l, va) -> findJ va lju
    | VAltLam(l, _, va) -> findJ va lju
    | VAltFn(l, _, _, Some(va)) -> findJ va lju
    | VAltFn(l, _, _, None) -> ("",[])
    | VAltPar(l,a,Some(va)) -> let (s1,l1) = findJ a lju in if s1 = "" then findJ va lju else (s1,l1)
    | VAltPar(l,a,None) -> let (s1,l1) = findJ a lju in if s1 = "" then raise (Error ("This theorem statement should refer to a judgment.")) else (s1,l1)
    | VAltOftBlock (l,_,Some(va)) -> findJ va lju
    | VAltOftBlock (l,_,None) -> let s = locToString(l) in let s1 = s ^ " There should be a premisse after this context block." in raise (Error (s1))

(* Declaration section *)

let rec checkString2 s lt = List.fold_left (fun x y -> let (h1,h2) = y in if h1 = s then (true,h2) else x) (false, "") lt

let rec printL2 l = List.fold_left (fun x y -> let (h1,h2) = y in output_string out_channel h1; output_string out_channel ", "; 
                    output_string out_channel h2; output_string out_channel " print list of vars\n") () l

let rec findBind l a ty lv ac =
  match a with
    | AltAtomic(l1,t1,a1) -> (begin match a1 with
                                | None -> let s = locToString(l) in let s1 = s ^ " This alternative needs a variable binding." in raise (Error (s1))
                                | Some(a2) -> output_string out_channel "print list of vars: \n"; printL2 lv; 
                                              let (b, ty1) = checkString2 t1 lv  in if b then findBind l a2 ty lv ((t1,ty1)::ac) 
                                              else let s = locToString(l1) in let s1 = s ^ " Did you forget to declare " ^ t1 ^ " as a variable?" in raise (Error (s1)) 
                              end )
    | AltBin(l1, a) -> output_string out_channel "found bin \n"; Paire(AltBin(l1, a), ac) 
    | _ -> let s = locToString(l) in let s1 = s ^ " Syntax error in alternative." in raise (Error (s1))

let rec diff_type ty lvar = List.fold_left (fun x y -> let (s1, s2) = y in if ty = s2 then [] else (s1, s2)::x ) [] lvar

let rec altList l ty lty lt lv llam la =
  match la with
    | [] -> let s = locToString(l) in let s1 = s ^ " Can't have empty list here according to parser." in raise (Error (s1))
    | h::[] -> alts l ty lty lt lv llam h
    | h::t -> Ext.LF.ArrTyp(l, alts l ty lty lt lv llam h, altList l ty lty lt lv llam t)

(* this is for any alternative *)
(* Loc.t -> string -> string list -> terminal list -> alternative list -> Ext.LF.typ *)
and alts l ty lty lt lv llam a = 
  match a with
    | AltAtomic(l1, t1, a1) -> if (checkString t1 lty ) then
                                  (* this is a type is theres is an alternative after it just skip to next*)
                                  ( begin match a1 with
                                      | None -> Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil)
                                      | Some(a2) -> output_string out_channel "AltAtomic typ \n"; 
                                                    (*alts l1 ty lty lt lv llam a2 *) (* try to remember why it was implemented this way in the first place*)
                                                    Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t1),Ext.LF.Nil), alts l1 ty lty lt lv llam a2)
                                    end )
                                  else(* if (checkString t1 lt) then *)
                                  ( begin match a1 with
                                      | None -> Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil)
                                      | Some(a2) -> Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t1),Ext.LF.Nil), alts l1 ty lty lt lv llam a2 )
                                    end ) 
                                 (* else raise (Error ("Alternatives must be only types or terminals"))*)

    | AltLam(l1, AName(t1), a1) -> output_string out_channel "alts AltLam \n";
                                        if checkString t1 lt then
                                        (begin match a1 with
                                           | None -> let s = locToString(l1) in let s1 = s ^ " Must indicate variable binding in this alternative" in 
                                                     raise (Error (s1))
                                           | Some(a2) -> let Paire(a3, lv1) = findBind l a2 ty lv [] in alts l1 ty lty lt lv1 (t1::llam) a3 
                                        end) 
                                        else let s = locToString(l1) in let s1 = s ^ " " ^ t1 ^ " was not declared terminal" in raise (Error (s1) )

    | AltFn(l1, Typ(l2, t1), t_or_l, a1) -> (begin match t_or_l with
                                                  | Ty(Typ(l3, t2)) -> (begin match a1 with 
                                                                          | None -> output_string out_channel "altfn Ty(typ)) None\n"; 
                                                                                    Ext.LF.Atom(l1, Id.mk_name(Id.SomeString t2),Ext.LF.Nil)
                                                                          | Some(a2) -> output_string out_channel "altfn Ty(typ)) Some \n"; 
                                                                                        Ext.LF.ArrTyp(l, Ext.LF.Atom(l1, Id.mk_name(Id.SomeString t2),Ext.LF.Nil), 
                                                                                        alts l1 ty lty lt lv llam a2)
                                                                       end)
                                                  | La(la2) -> (begin match a1 with 
                                                                  | None -> output_string out_channel "altfn La(la)) None\n";
                                                                            Ext.LF.ArrTyp(l,Ext.LF.ArrTyp(l,Ext.LF.Atom(l1,Id.mk_name(Id.SomeString t1),Ext.LF.Nil)
                                                                            , altList l1 ty lty lt lv llam la2), Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),
                                                                            Ext.LF.Nil))
                                                                  | Some(a2) -> output_string out_channel "altfn La(la)) Some\n";(** what about ar2*)
                                                                                let Ext.LF.ArrTyp(l4,ar1,ar2) = alts l1 ty lty lt lv llam 
                                                                                                                (AltFn(l1,Typ(l2, t1), t_or_l, None)) in
                                                                                Ext.LF.ArrTyp(l,ar1, alts l1 ty lty lt lv llam a2)
                                                                            
                                                                end)
                                               end )


    | AltBin(l1, a) -> output_string out_channel "AltBin\n"; alts l1 ty lty lt lv llam a

    | AltOft(l1, a1, a2) -> alts l1 ty lty lt lv llam a2  
    | _ -> raise (Error ("Unvalid alternative/Not implemented yet"))

(* this is for the first element at the begginig of an alternative *)
(* val sgnAlts : Parser.Grammar.Loc.t -> string -> string list -> string list -> string list -> string list -> Ast.alternative list -> Syntax.Ext.Sgn.decl list *)
let rec sgnAlts l ty lty lt lv llam la = 
  match la with
    | [] -> []
    | AltAtomic(l1, t1, a1)::t -> output_string out_channel "sgn AltAtomic \n";
                                  if (checkString t1 lty ) then
                                  (* skip to next and dont care about this type, we are at the beggining of the alternative so there cant be only this atom*)
                                  ( begin match a1 with
                                      | None -> let s = locToString(l1) in let s1 = s ^ " Illegal alternative" in raise (Error (s1))
                                      | Some(a2) -> output_string out_channel "sgn AltAtomic typ\n"; 
                                                    Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1),  alts l1 ty lty lt lv llam a2)::sgnAlts l ty lty lt lv llam t 
                                    end )
                                  else if (checkString t1 lt) then 
                                  ( begin match a1 with
                                      | None -> Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), Ext.LF.Atom(l, Id.mk_name (Id.SomeString ty),Ext.LF.Nil))
                                                ::sgnAlts l ty lty lt lv llam t
                                      | Some(a2) -> output_string out_channel "sgn altAtomic terminal \n"; 
                                                    Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), Ext.LF.ArrTyp(l,
                                                    Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil), alts l1 ty lty lt lv llam a2))
                                                    ::sgnAlts l ty lty lt lv llam t 
                                    end )
                                   else ( begin match a1 with
                                      | None -> sgnAlts l ty lty lt lv llam t (** *)
                                      | Some(a2) -> let s = locToString(l1) in 
                                                    let s1 = s ^ " An Alternative must start with a terminal or declare a variable, 
                                                                   maybe you forgot to declare " ^ t1 ^ " terminal."
                                                    in raise (Error (s1))
                                    end )

    | AltLam(l1, AName(t1), a1)::t -> output_string out_channel "sgn AltLam\n"; if checkString t1 lt 
                                      then 
                                      (begin match a1 with
                                           | None -> raise (Error ("Must indicate variable binding in this alternative"))
                                           | Some(a2) ->  let Paire(a3, lv1) = findBind l a2 ty lv [] in  let ldv = diff_type ty lv1 in if ldv = []
                                                          then
                                                          Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), alts l1 ty lty lt lv1 llam a3)
                                                          ::sgnAlts l ty lty lt lv (t1::llam) t
                                                          else let arrty = List.fold_right (fun t s -> let (s1, s2) = t in
                                                          Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString s2),Ext.LF.Nil),s)) 
                                                          ldv (alts l1 ty lty lt lv1 llam a3) in 
                                                          Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), arrty)::sgnAlts l ty lty lt lv (t1::llam) t


                                        end) 
                                      else let s = locToString(l1) in let s1 = s ^ " " ^ t1 ^ " was not declared terminal" in raise (Error (s1) )
                                      

    | AltFn(l1, Typ(l2, t1), Ty(Typ(l3, t2)), a1)::t -> output_string out_channel "sgn AltFn \n"; (** might cause prob. with AltLet*)
                                                        (begin match a1 with 
                                                            | None -> Ext.Sgn.Const(l, Id.mk_name (Id.SomeString "arr"), 
                                                                      Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t1),Ext.LF.Nil), 
                                                                      Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t2),Ext.LF.Nil), 
                                                                      Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil))))::sgnAlts l ty lty lt lv llam t
                                                            | Some(a2)-> let s = locToString(l1) in let s1 = s ^ "Sorry, this feature is not implemented yet." in raise (Error (s1))
                                                         end)

    | AltLet(l1, a1, a2, a3)::t -> output_string out_channel "sgn AltLet \n"; 
                                      (begin match a3 with (** should not ignore whats in AltFn *)
                                           | AltFn(_) -> Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString "letv"), Ext.LF.ArrTyp(l, 
                                                         Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil),  alts l1 ty lty lt lv llam a3))
                                                         ::sgnAlts l ty lty lt lv llam t
                                           | _ -> let s = locToString(l1) in let s1 = s ^ "Unvalid alternative" in raise (Error (s1))
                                        end)

    | AltPar::t ->  sgnAlts l ty lty lt lv llam t

    | AltCtx( _ )::t -> let s = locToString(l) in let s1 = s ^ ", unvalid start of alternative context" in raise (Error (s1))

    | _ -> let s = locToString(l) in let s1 = s ^ ", unvalid start of alternative" in raise (Error (s1))

let rec find_var lt ltyp las = List.fold_left (fun x y -> match y with | (AltAtomic(l1, t1, None)::t,s1) -> if checkString t1 lt then x@(find_var lt ltyp [(t,s1)]) 
                                                                                                            else (t1,s1)::x@(find_var lt ltyp [(t,s1)])
                                                                       | (h::t,s1)-> x@(find_var lt ltyp [(t,s1)]) | _ -> []) 
                                                          [] las

let rec find_var_prep lp = (List.fold_left (fun x y -> let Production(l1, Typ(l2, t1), la) = y in ((la,t1)::x) )) [] lp

(* string list -> string list -> production list -> Ext.Sgn.decl list, first list types second terminals *)
let rec sgnTypes lt lty lvar lp =
  match lp with
    | [] -> []
    | Production(l1, Typ(l2, t1), la)::t -> let sgn1 = sgnAlts l2 t1 lty lt lvar [] la in [Ext.Sgn.Typ(l1, Id.mk_name (Id.SomeString t1), Ext.LF.Typ(l1))]@ sgn1 @ sgnTypes lt lty lvar t

(* Judgment Section *)

(* Loc.t -> string -> judge list -> string list -> Ext.Sgn.decl list *)
let rec typ_or_sym l js ltyp =
  match js with
    | [] -> output_string out_channel "typ or sym [] \n"; Ext.LF.Typ(l) 
    | h::t -> let Judge(l1,s1) = h in if (checkString s1 ltyp ) then (output_string out_channel " typ or sym then \n"; 
                                   Ext.LF.ArrKind(l, Ext.LF.Atom(l1, Id.mk_name(Id.SomeString s1),Ext.LF.Nil), typ_or_sym l1 t ltyp) )
                                   else (output_string out_channel " typ or sym else \n"; typ_or_sym l1 t ltyp)

(* checks the judgement if its not a type its a symbol indicating the syntax of the judgement *)
(* judge list -> string list -> string list *)
let rec typ_or_sym_list lj ltyp = 
  match lj with
    | [] -> output_string out_channel "typ or sym list [] \n"; []
    | h::t -> let Judge(l1,s1) = h in if (checkString s1 ltyp ) then (output_string out_channel s1; output_string out_channel " check string then \n"; 
              typ_or_sym_list t ltyp) else (output_string out_channel s1; output_string out_channel " check string else \n"; s1 :: typ_or_sym_list t ltyp  )

(* Loc.t -> jName -> jSyntax -> string list -> (string list , Ext.Sgn.decl list) *)
let sgnJudge l jn js ltyp =
   let JName(j) = jn in let JSyntax(l, a, lj) = js in ( typ_or_sym_list lj ltyp, Ext.Sgn.Typ(l,Id.mk_name (Id.SomeString j), typ_or_sym l lj ltyp))


let rec valtslist lva =
  match lva with 
    | [] -> None
    | VAltAtomic(l, s, None)::t -> Some(VAltAtomic(l, s, valtslist t ))
    | VAltFn(l1, VName(n1), VLa([va1]), None)::t -> Some(VAltFn(l1, VName(n1), VLa([va1]), valtslist t))
    | _ -> raise (Error ("Oops never thaught this case will show up"))
    
(* Loc.t -> string list -> var_alternative -> Ext.LF.spine *)
let rec valtsPar l lsym a =
  match a with 
    | VAltAtomic(l, s, vao) -> (begin match vao with 
                                 | None -> output_string out_channel "valtsPar none in altpar \n";
                                           Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil)

                                 | Some(VAltBin(l2, va)) -> if checkString s lsym 
                                                            then (output_string out_channel s; output_string out_channel "valtspar some valtbin then \n"; 
                                                                  raise (Error ("Error in Lamdba term."))) 
                                                            else (output_string out_channel s; output_string out_channel " valtspar some valtbin else \n";
                                                                 Ext.LF.Lam(l2, Id.mk_name(Id.SomeString s), valtsPar l lsym va) )

                                 | Some(va) -> output_string out_channel "valtspar some then in altpar \n";  (** might want to check if its a symbol *)
                                              Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), valts l lsym va) 

                              end)


    | VAltLam(l, AName(n), va) -> output_string out_channel "valts par valtlam\n";
                                  Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString n)), valts l lsym va)

    | VAltFn(l1, VName(n1), v, vao) -> output_string out_channel n1; output_string out_channel " valtspar valtfn\n"; 
                                              (begin match v with 
                                                 | VLa(lva) ->  let Some(va1) = valtslist lva in
                                                               (begin match vao with
                                                                  | None -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1)
                                                                  | Some(VAltBin(l2, va)) -> output_string out_channel " valtspar valtfn valtbin else \n";
                                                                                             Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), Ext.LF.Root(l, 
                                                                                             Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1))
                                                                                             (*, valts l1 lsym va)*)
                                                                  | Some(a2) -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym a2)
                                                                end)

                                                 | VTy(Typ(l2,t2)) -> let va2 = VAltAtomic(l2,t2,None) in let va1 = valts l2 lsym va2 in
                                                                     (begin match vao with
                                                                        | None -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString "arr")), Ext.LF.App(l2,Ext.LF.Root(l2, 
                                                                                                   Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)),Ext.LF.Nil),va1)) 


(*Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), va1)*) | Some(VAltBin(l2, va)) -> output_string out_channel " valtspar valtfn valtbin else \n"; (** you dont use va*)
                                                                                                   Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), Ext.LF.Root(l, 
                                                                                                   Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)), va1))
                                                                                                  (*, valts l1 lsym va)*)
                                                                        | Some(a2) -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym a2)
                                                                      end) 

                                               end)

    | VAltLet(l, va) -> output_string out_channel " valts valtfn\n"; let lsym1 = "="::lsym in
                             Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString "letv")), valts l lsym1 va)

    | VAltOft _ -> raise (Error ("Valtoft")) 

    | _ -> let s = locToString(l) in let s1 = s ^ " Not implemented yet (in valtsPar)." in raise (Error (s1)) 

(* Loc.t -> string list -> var_alternative -> Ext.LF.spine *)
and valts l lsym va =
  match va with 
    | VAltAtomic(l, s, vao) -> (begin match vao with 
                                 | None -> if checkString s lsym 
                                           then (output_string out_channel s; output_string out_channel " valts none then \n"; Ext.LF.Nil ) 
                                           else (output_string out_channel s; output_string out_channel " valts none else \n";
                                                   Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil), Ext.LF.Nil) )

                                 | Some(VAltBin(l2, va)) -> if checkString s lsym 
                                                            then (output_string out_channel s; output_string out_channel " valts some valtbin then \n"; 
                                                                  raise (Error ("Error in Lamdba term."))) 
                                                            else (output_string out_channel s; output_string out_channel " valts some valtbin else \n"; 
                                                            (begin match va with (** mght want to make a function instead*)
                                                               | VAltFn(l3,v2,vl2,Some(VAltBin(l4,vaoo))) -> Ext.LF.App(l, Ext.LF.Lam(l2, 
                                                                                                             Id.mk_name(Id.SomeString s), 
                                                                                                             valtsPar l lsym (VAltFn(l3,v2,vl2,None))), 
                                                                                                             Ext.LF.App(l, 
                                                                                                             Ext.LF.Lam(l4, Id.mk_name(Id.SomeString s), 
                                                                                                             valtsPar l4 lsym vaoo), Ext.LF.Nil))
                                                               | _ -> Ext.LF.App(l, Ext.LF.Lam(l2, Id.mk_name(Id.SomeString s), valtsPar l lsym va), Ext.LF.Nil)
                                                             end)  )
 

                                 | Some(va) -> if checkString s lsym 
                                              then (output_string out_channel s; output_string out_channel "valts some then \n"; valts l lsym va) 
                                              else (output_string out_channel s; output_string out_channel " valts some else \n";
                                                   Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil), valts l lsym va) )
                                 end)

    | VAltPar(l, a, vao) -> (begin match vao with 
                                 | None -> let v1 = valtsPar l lsym a in output_string out_channel "valts altpar none \n";
                                                   Ext.LF.App(l, v1, Ext.LF.Nil) 


                                 | Some(vb) -> let v1 = valtsPar l lsym a in output_string out_channel "valts altpar some \n";
                                                   Ext.LF.App(l, v1, valts l lsym vb) 

                              end)


    | VAltLam(l, AName(n), va) -> output_string out_channel "valts valtlam\n";
                                  Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString n)), valts l lsym va), Ext.LF.Nil)
    
    | VAltFn(l1, VName(n1), VLa([va1]), vao) -> output_string out_channel n1; output_string out_channel " valts valtfn\n"; (**assuming only 1 element in list *)
                                                (begin match vao with
                                                   | None -> Ext.LF.App(l, Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1), 
                                                             Ext.LF.Nil)
                                                   | Some(VAltBin(l2, va)) -> output_string out_channel " valts valtfn valtbin else \n";
                                                                              Ext.LF.App(l, Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), valtsPar l1 lsym va1), 
                                                                              valts l1 lsym va)
                                                   | Some(a2) -> Ext.LF.App(l, Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1), 
                                                                 valts l1 lsym a2)
                                                 end)

    | VAltOft(_) -> raise (Error ("Valtoft")) 


    | VAltBin(l1,va) -> raise (Error ("Problem from binding")) 

    | _ -> let s = locToString(l) in let s1 = s ^ " Not implemented yet (in valts)." in raise (Error (s1))

(* function that deals with the list of premises *)

let rec judges' jn lsym lp l2 va =
   match lp with
     | [] -> Ext.LF.Atom(l2, Id.mk_name(Id.SomeString jn), valts l2 lsym va)
     | h::t -> let Premisse(l3, b1, c1, va1) = h in 
                begin match va1 with
                | (*VAltOft(l, VName(n), Typ(l1, n1), va2)*) VAltOft(l, [(n, n1)], va2) -> 
                                                            Ext.LF.PiTyp(l, Ext.LF.TypDecl( Id.mk_name(Id.SomeString n), Ext.LF.Atom(l2, Id.mk_name(Id.SomeString n1), Ext.LF.Nil)), 
                                                            Ext.LF.ArrTyp(l2, Ext.LF.Atom(l2, Id.mk_name(Id.SomeString jn), valts l3 lsym va2), judges' jn lsym t l2 va))
                | _ -> Ext.LF.ArrTyp(l2, Ext.LF.Atom(l2, Id.mk_name(Id.SomeString jn), valts l3 lsym va1), judges' jn lsym t l2 va)
              end

(* string list -> rule list -> Ext.Sgn.decl list *)
let rec judges jn lsym lr = output_string out_channel "judges \n";
   match lr with
    | [] -> []
    | h::t -> let Rule(l1, a, RName(s), Premisse(l2, b, c, va)) = h in let JName(s1) = jn in
              begin match a with
                | [] -> output_string out_channel  s; output_string out_channel " judges [] s s1 \n";
                        let lv = [Ext.Sgn.Const(l1, Id.mk_name(Id.SomeString s), Ext.LF.Atom(l2, Id.mk_name(Id.SomeString s1), valts l2 lsym va))] 
                        in lv @ judges jn lsym t
                | la -> let lv = [Ext.Sgn.Const(l1, Id.mk_name(Id.SomeString s), judges' s1 lsym la l2 va)] in lv @ judges jn lsym t
              end

(* Context Section *)

let rec context_sch l lv lsym lju va = 
   match va with
    | VAltOftBlock (l1,[(x1,x2)],Some(va)) -> let ( s1, ls) = findJ va lju in let va2 = valts l1 lsym va in Ext.LF.SigmaElem(Id.mk_name(Id.SomeString x1),Ext.LF.Atom(l1, Id.mk_name(Id.SomeString x2), Ext.LF.Nil), Ext.LF.SigmaLast( Ext.LF.Atom(l1, Id.mk_name(Id.SomeString s1), va2)))
    | VAltOftBlock (l1,_,None) -> let s = locToString(l1) in let s1 = s ^ " There should be a premisse after this context block." in raise (Error (s1))
    | _ -> let ( s1, ls) = findJ va lju in let va2 = valts l lsym va in Ext.LF.SigmaLast( Ext.LF.Atom(l, Id.mk_name(Id.SomeString s1), va2))


let rec context lv lsym lju lva = 
   match lva with
    | [] -> (*let s1 = " Not implemented yet in context." in raise (Error (s1)) *) []
    | VAltEmpty(l)::t -> context lv lsym lju t
    | VAltOft(l, ltd, va1)::t -> let lfd = List.fold_left (fun y (x1,x2) -> Ext.LF.Dec(y, Ext.LF.TypDecl(Id.mk_name(Id.SomeString x1), Ext.LF.Atom(l, Id.mk_name(Id.SomeString x2), Ext.LF.Nil))))
                                 Ext.LF.Empty ltd in let sc2 = context_sch l lv lsym lju va1 in [Ext.LF.SchElem(l, lfd, sc2)]@context lv lsym lju t


(* Theorems Section *)

let rec valtpPar l lt lsym a =
  match a with 
    | VAltAtomic(l, s, vao) -> (begin match vao with (** probably want to check if is a symbol *)
                                 | None -> output_string out_channel "valtpPar none in altpar \n";
                                           if checkString s lt 
                                           then Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil)
                                           else Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.EmptySub(l)), Ext.LF.Nil)

                               (*  | Some(VAltBin(l2, va)) -> if checkString s lsym 
                                                            then (output_string out_channel s; output_string out_channel "valtspar some valtbin then \n"; 
                                                                  raise (Error ("Error in Lamdba term."))) 
                                                            else (output_string out_channel s; output_string out_channel " valtspar some valtbin else \n";
                                                                 Ext.LF.Lam(l2, Id.mk_name(Id.SomeString s), valtpPar l lsym va) )*)

                                 | Some(va) ->     if checkString s lt 
                                                   then (output_string out_channel s; output_string out_channel " valtppar some else terminal then \n";
                                                   Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), valtp l lt lsym va))
                                                   else 
                                                   (output_string out_channel "valtppar some then in altpar \n";
                                                   Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.EmptySub(l)), valtp l lt lsym va))
  


                              end)

(*
    | VAltLam(l, AName(n), va) -> output_string out_channel "valts par valtlam\n";
                                  Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString n)), valtp l lsym va)

    | VAltFn(l1, VName(n1), VLa(lva), vao) -> output_string out_channel n1; output_string out_channel " valtspar valtfn\n"; 
                                              (**assuming only 1 element in list *) let Some(va1) = valtslist lva in
                                                (begin match vao with
                                                   | None -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valtp l1 lsym va1)
                                                   | Some(VAltBin(l2, va)) -> output_string out_channel " valtspar valtfn valtbin else \n";
                                                                              Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), Ext.LF.Root(l, 
                                                                              Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)), valtp l1 lsym va1))
                                                   | Some(a2) -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valtp l1 lsym a2)
                                                 end)

    | VAltLet(l, va) -> output_string out_channel " valts valtfn\n"; 
                             Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString "letv")), valtp l lsym va)
*)
    | VAltPar(l, a, vao) -> (begin match vao with 
                                 | None -> output_string out_channel "valtp altpar none \n"; valtpPar l lt lsym a


                                 | Some(vb) -> let s = locToString(l) in let s1 = s ^ " Needs more brackets." in raise (Error (s1))

                              end)
    | _ -> let s = locToString(l) in let s1 = s ^ " Not implemented yet (in valtpPar)." in raise (Error (s1)) 


and valtp l lt lsym va =
  match va with 
    | VAltAtomic(l, s, vao) -> (begin match vao with 
                                 | None -> if checkString s lsym 
                                           then (output_string out_channel s; output_string out_channel " valtp none then \n"; Ext.LF.Nil ) 
                                           else (output_string out_channel s; output_string out_channel " valtp none else \n";
                                                if checkString s lt
                                                then  Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil), Ext.LF.Nil)
                                                else  Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.EmptySub(l)), Ext.LF.Nil), 
                                                      Ext.LF.Nil ))         


                                (* | Some(VAltBin(l2, va)) -> if checkString s lsym 
                                                            then (output_string out_channel s; output_string out_channel " valts some valtbin then \n"; 
                                                                  raise (Error ("Error in Lamdba term."))) 
                                                            else (output_string out_channel s; output_string out_channel " valts some valtbin else \n"; 
                                                            (begin match va with (** mght want to make a function instead*)
                                                               | VAltFn(l3,v2,vl2,Some(VAltBin(l4,vaoo))) -> 
                                                                                  Ext.LF.App(l, Ext.LF.Lam(l2, Id.mk_name(Id.SomeString s), 
                                                                                  valtsPar l lsym (VAltFn(l3,v2,vl2,None))), Ext.LF.App(l, 
                                                                                  Ext.LF.Lam(l4, Id.mk_name(Id.SomeString s), valtsPar l4 lsym vaoo), Ext.LF.Nil))
                                                               | _ -> Ext.LF.App(l, Ext.LF.Lam(l2, Id.mk_name(Id.SomeString s), valtsPar l lsym va), Ext.LF.Nil)
                                                             end)  ) *)
 

                                 | Some(va) -> if checkString s lsym 
                                               then (output_string out_channel s; output_string out_channel "valtp some then \n"; valtp l lt lsym va) 
                                               else (if checkString s lt 
                                                   then (output_string out_channel s; output_string out_channel " valtp some else terminal then \n";
                                                   Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil), valtp l lt lsym va)) 
                                                   else (output_string out_channel s; output_string out_channel " valtp some terminal else \n";
                                                   Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.EmptySub(l)), Ext.LF.Nil), 
                                                   valtp l lt lsym va)))
                              end)
 | VAltPar(l, a, vao) -> (begin match vao with 
                                 | None -> let vp1 = valtpPar l lt lsym a in  output_string out_channel "valtp altpar none \n";
                                                   Ext.LF.App(l, vp1, Ext.LF.Nil) 


                                 | Some(vb) -> let vp2 = valtpPar l lt lsym a in output_string out_channel "valtp altpar some \n";
                                                   Ext.LF.App(l, vp2, valtp l lt lsym vb ) 

                              end)


(*    | VAltLam(l, AName(n), va) -> output_string out_channel "valts valtlam\n";
                                  Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString n)), valtp l lsym va), Ext.LF.Nil)
    
    | VAltFn(l1, VName(n1), VLa([va1]), vao) -> output_string out_channel n1; output_string out_channel " valts valtfn\n"; (**assuming only 1 element in list *)
                                                (begin match vao with
                                                   | None -> Ext.LF.App(l, Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), 
                                                                        valtp l1 lsym va1), Ext.LF.Nil)
                                                   | Some(VAltBin(l2, va)) -> output_string out_channel " valts valtfn valtbin else \n";
                                                                              Ext.LF.App(l, Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), valtsPar l1 lsym va1), 
                                                                                         valtp l1 lsym va)
                                                   | Some(a2) -> Ext.LF.App(l, Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), 
                                                                            valtp l1 lsym va1), valtp l1 lsym a2)
                                                 end)

    | VAltBin(l1,va) -> raise (Error ("Problem from valbin")) *)

    | _ -> raise (Error ("Not implemented yet (in valtp).")) 


let rec conTypArr l lt lju lsym ltp = let s = locToString(l) in let s1 = " contyparr " ^ s in raise (Error (s1))

let stmt_to_prove l lt st lju lsym = 
  match st with (** assuming a list of 1 element, find example where it is not *) 
    | ForAllExist (l1, tp, p) -> ( match (tp,p) with (** assuming list of 1 element *) (** dummy string n might want to write a findtyp fun *) 
                                    | ([TPremisse(l2,nao1,None,va1)],Premisse(l3,nao2,None,va2)) -> 
                                   
                                       (begin match va1 with
                                          |VAltAtomic(l4,s1,None) ->  output_string out_channel " stmttoprove forall n n\n";
                                                                      let (jn,lsym1)= findJ va2 lju in let v1 = valtp l3 lt lsym1 va2
                                                                      in output_string out_channel jn; output_string out_channel " : jn stmtp\n"; 
                                                                      (Ext.Comp.TypPiBox(l1,Ext.LF.MDecl(l2,Id.mk_name(Id.SomeString s1),
                                                                      Ext.LF.Atom(l2,Id.mk_name(Id.SomeString "n"),Ext.LF.Nil)(*valts l2 lsym va1*),
                                                                      Ext.LF.Null), 
                                                                      Ext.Comp.TypBox(l3,Ext.LF.Atom(l3,Id.mk_name(Id.SomeString jn),v1),Ext.LF.Null))
                                                                      ,Some(s1))

                                          | _ -> output_string out_channel " stmttoprove forall _\n";
                                                 (begin match nao1 with
                                                    | Some(PName(n1)) ->  
                                                         let (jn,lsym1)= findJ va2 lju in
                                                         let  aa1  = valtp l2 lt lsym1 va1  in let v1 = valtp l3 lt lsym1 va2
                                                         in output_string out_channel jn; output_string out_channel " : jn stmtp\n"; 
                                                         (Ext.Comp.TypPiBox(l1,Ext.LF.MDecl(l2,Id.mk_name(Id.SomeString n1),
                                                         Ext.LF.Atom(l2,Id.mk_name(Id.SomeString jn),aa1), Ext.LF.Null), 
                                                         Ext.Comp.TypBox(l3,Ext.LF.Atom(l3,Id.mk_name(Id.SomeString jn),v1),Ext.LF.Null))
                                                         ,Some(n1))

                                                    | None -> let s = locToString(l2) in let s1 = "This premise needs a name.  " ^ s in raise (Error (s1))
                                                  end) 

                                                
                                        end)

                                    | (TPremisse(l2,nao1,Some(c1),va1)::t ,Premisse(l3,nao2,co,va2)) -> 
                                                 (begin match c1 with
                                                    | LCD [(s1,s2)] -> let lp1 = [TPremisse(l2,nao1,Some(Con(s1)),va1)] @ t @ [TPremisse(l3,nao2,co,va2)] in let cta = conTypArr l1 lt lju lsym lp1 in
                                                                       (Ext.Comp.TypCtxPi(l1, (Id.mk_name(Id.SomeString s1), Id.mk_name(Id.SomeString s2), Ext.Comp.Explicit), cta), None) (**shouldnt be none*)

                                                    | Con(s) -> let s = locToString(l2) in let s1 = "This is not implemented yet.  " ^ s in raise (Error (s1))
                                                  end) 


                                    | _ -> let s = locToString(l) in let s1 = "Sorry, try again later. " ^ s in raise (Error (s1)) 
                                  )

    | Exist (l1, p) -> (begin match p with
                          | Premisse( l2, None, None, va) -> output_string out_channel " stmttoprove n n\n";  let (jn, lsym) = findJ va lju in
                                                            (Ext.Comp.TypBox(l1, Ext.LF.Atom(l1, Id.mk_name(Id.SomeString jn), valts l2 lsym va), Ext.LF.Null),None)
                          | Premisse _ -> raise (Error ("Sorry, i am not implemented yet."))
                        end) 

let rec comp_branch l lt n omlam lsym al = 
  match al with 
    | [] -> []
    | Arg(l1, va, pl)::t -> output_string out_channel "comp_branch arg \n"; let v1 = valtpPar l1 lt lsym va in let p1 = proofs l1 lt n omlam pl lsym in 
                            let cb = Ext.Comp.BranchBox(l, Ext.LF.Empty, (Ext.LF.Null, Ext.Comp.NormalPattern(v1, p1), None)) in
                            cb :: comp_branch l lt n omlam lsym t
    | Argument(l1, Rule(l2,lp1,RName(rn),p),lp)::t ->  let lp2 = List.filter (fun (Premisse(l3, no,c, va)) -> no <> None) (p::lp1) in if lp2 = []

                                                       then (output_string out_channel "comp_branch argument then \n"; 
                                                       let v1 = Ext.LF.Root(l2, Ext.LF.Name( l2, Id.mk_name(Id.SomeString rn)), Ext.LF.Nil) in  let p1 = proofs l1 lt n omlam lp lsym in
                                                       let cb = Ext.Comp.BranchBox(l, Ext.LF.Empty, (Ext.LF.Null, Ext.Comp.NormalPattern(v1, p1), None)) in
                                                       cb :: comp_branch l lt n omlam lsym t)
                                                      
                                                       (** only deals with one nmaned premisse in rule *)
                                                       else (output_string out_channel "comp_branch argument else \n"; let [Premisse(l3, Some(PName(n1)),c, va)] = lp2 in 
                                                       let va2 = VAltAtomic(l1,n1,None) in let va1 = valtp l1 lt lsym va2 in 
                                                       let v1 = Ext.LF.Root(l2, Ext.LF.Name( l2, Id.mk_name(Id.SomeString rn)), va1) in  let p1 = proofs l1 lt n omlam lp lsym in
                                                       let cb = Ext.Comp.BranchBox(l, Ext.LF.Empty, (Ext.LF.Null, Ext.Comp.NormalPattern(v1, p1), None)) in
                                                       cb :: comp_branch l lt n omlam lsym t)
(* if List.exists (fun (Premisse(l3, no,c, va)) -> no <> None) (p::lp1) *)
and proofs l lt n omlam pl lsym = 
  match pl with 
    | [] -> raise (Error ("Sorry, I am not implemented yet.[]"))
    | h::t ->  (** in some cases nothing happens with t *)
              (begin match h with
                | URule (l1, tp, RName(n1), lvno) -> output_string out_channel n; output_string out_channel " : urule \n"; (** why do we ignore the tp *) 
                                                    (begin match (lvno,omlam) with
                                                       | (None,_) -> Ext.Comp.Box(l, [], Ext.LF.Root(l1, Ext.LF.Name( l1, Id.mk_name(Id.SomeString n1)), Ext.LF.Nil))
                                                       | (Some(vn),Some(s1)) -> let va = VAltAtomic(l1,s1,None) in let v1 = valtp l1 lt lsym va in
                                                                                Ext.Comp.Box(l, [], Ext.LF.Root(l1, Ext.LF.Name( l1, Id.mk_name(Id.SomeString n1)), v1))
                                                     end)
                | Proof (l1, tp, VName(s), al) -> output_string out_channel "proof \n";
                                                  (begin match omlam with 
                                                     | Some(s1) -> output_string out_channel "proof some  \n";
                                                                   let va = VAltAtomic(l1,s1,None) in let v1 = valtpPar l1 lt lsym va in 
                                                                   Ext.Comp.MLam(l1,Id.mk_name(Id.SomeString s1),Ext.Comp.Case(l1,RegularCase,
                                                                   Ext.Comp.BoxVal(l1,Ext.LF.Null, v1), comp_branch l1 lt n omlam lsym al))
                                                     | None -> raise (Error ("forall missing in this proof."))
                                                   end)

                | PRule (l1, tp, pf, [VName(n1)]) -> output_string out_channel n1;output_string out_channel " : n1 Prule \n";
                                             (* write fun get MVar *) 
                                             (begin match pf with 
                                                | InductionHyp(l2) -> let v1 = VAltAtomic(l1,n1,None) in 
                                                                      let TPremisse(_,Some(PName(s1)),_,_) = tp in
                                                                      let v2 = VAltAtomic(l1,s1,None) in 
                                                                      let ag = Arg(l1,v2,t) in
                                                                      Ext.Comp.Case(l1,Syntax.RegularCase,Ext.Comp.MApp(l1,Ext.Comp.Var(l1,Id.mk_name(Id.SomeString n)),
                                                                      ([],valtpPar l1 lt lsym v1)), comp_branch l lt n (Some(s1)) lsym [ag])
                                                | _ -> raise (Error ("Sorry not implemented yet in prule."))
                                              end)
                | InductionHyp (l1) -> raise (Error ("Sorry, I am not implemented yet (IH)."))
                | CaseAn (l1, tp, lvn, al) -> raise (Error ("Sorry, I am not implemented yet (CaseAn)."))
                | PTheorem (l1, tn) -> raise (Error ("Sorry, I am not implemented yet (PTheorem)."))
                | _ -> raise (Error ("Error in theorem."))
              end)

let theorem l lt n st pl lju lsym = output_string out_channel " theorem translation \n"; 
                                    let (ctb,omlam) =  stmt_to_prove l lt st lju lsym in let prf = proofs l lt n omlam pl lsym in 
                                    [Ext.Sgn.Rec(l, [Ext.Comp.RecFun( Id.mk_name(Id.SomeString n), ctb, prf)])]


(* string list -> string list -> Ext.Sgn.decl list, first list terminals secong types *)
let rec recSectionDecl lt ltyp lv ls lju lsym = 
  match ls with 
    | [] -> []
    | h::t -> begin match h with
                | Grammar (_, lp) -> let las = find_var_prep lp in let lvar = find_var lt ltyp las in output_string out_channel "print list of var after find var \n"; printL2 lvar; 
                                     let ls = sgnTypes lt ltyp lvar lp in output_string out_channel "Grammar decl \n"; (ls @ recSectionDecl lt ltyp lvar t lju lsym)
                | Judgement(l, jn, js, a, lr) -> output_string out_channel "Judgement \n"; output_string out_channel "print list in judgement \n";printL ltyp; 
                                                 let (lsym1, sgnj) = sgnJudge l jn js ltyp in let lj = judges jn lsym1 lr in let JName(s1)=jn in 
                                                                                           [sgnj] @ lj @ recSectionDecl lt ltyp lv t (Jdef(s1,lsym1)::lju) (lsym1@lsym)
                | ContextDecl (l, CName(cn), lva) -> let c =  context lv lsym lju lva in [Ext.Sgn.Schema(l, Id.mk_name(Id.SomeString cn), Ext.LF.Schema(c))] @ recSectionDecl lt ltyp lv t lju lsym
                | Theorems (l, TName(n), st, pl) -> output_string out_channel "Theorems \n"; printLju lju;
                                                    let t1 = theorem l lt n st pl lju lsym in t1 @ recSectionDecl lt ltyp lv t lju lsym
              end

(* section list -> string list *)
let rec recSectionDeclGram l ls =
  match ls with
    | [] -> []
    | Grammar (_, Production(l1, Typ(l2, t1), la)::t2):: t -> output_string out_channel t1; output_string out_channel " gram decl \n"; 
                                                              let rec ltails lp acc = match lp with | [] -> acc | Production(l3, Typ(l4, t3), la)::t4 -> ltails t4 (t3::acc)  in
                                                              let tails = ltails t2 [] in t1 :: tails @ recSectionDeclGram l t 
    | Judgement _ ::t -> recSectionDeclGram l t
    | ContextDecl (l, cn, lva)::t -> recSectionDeclGram l t
    | Terminals_decl _:: t -> let s = locToString(l) in let s1 = s ^ " Should only have one declaration of terminals" in raise (Error (s1))
    | Theorems _ :: t-> recSectionDeclGram l t

(* string list -> string list -> Syntax.section list -> Syntax.Ext.Sgn.decl list *)
let sectionDecls ls = 
  match ls with
    | Terminals_decl(l,lt):: t -> let lt1 = List.map (fun x -> let Terminal(_, t1) = x in t1) lt in let ltyp = recSectionDeclGram l t in output_string out_channel "Section Decls \n"; 
                                  printL ltyp; recSectionDecl lt1 ltyp [] t [] []
    | _ -> raise (Error ("No terminal declaration or grammar at the beginnig of file"))
