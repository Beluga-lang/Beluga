(**

   @author Marie-Andree B.Langlois
*)

open Core
open Syntax
open Ast

(* variable naming convention: the variable names are usually the first(s) character(s) of what they stand for*)

module Loc = Syntax.Loc
exception Error of string

let locToString loc =
  Parser.Grammar.Loc.print Format.str_formatter loc;
  Format.flush_str_formatter()

(* Terminal and Helper Functions Section *)

(* checks if a sting is present in the given list, string -> string list -> bool *)
let checkString s lt = List.fold_left (fun x y -> if y = s then true else x) false lt

type jdef = Jdef of string * string list

(* given a var_alternative, find to which judgment it corresonds to*)
let findJu s lju = List.fold_left (fun x y -> let (Jdef(s1, lsym)) = y in
                                       if (checkString s lsym) then (Jdef(s1, lsym)) else x) (Jdef("",[])) lju

type bind = Paire of alternative * (string * string) list

(* given a var_alternative, find to which judgment it corresonds to*)
let rec findJ va lju =
  match va with
    | VAltAtomic(l, s, Some(vao)) -> let Jdef(s1, lsym) = findJu s lju in
                                     if (s1 = "") then findJ vao lju else (s1, lsym)
    | VAltAtomic(l, s, None) -> let Jdef(s1, lsym) = findJu s lju in
                                if s1 = "" then (s,[]) else (s1, lsym)
    | VAltBin(l, va) -> findJ va lju
    | VAltLam(l, _, va) -> findJ va lju
    | VAltId(l, _, _, Some(va)) -> findJ va lju
    | VAltId(l, _, _, None) -> ("",[])
    | VAltFn(l, _, _, Some(va)) -> findJ va lju
    | VAltFn(l, _, _, None) -> ("",[])
    | VAltPar(l,a,Some(va)) -> let (s1,l1) = findJ a lju in
                               if s1 = "" then findJ va lju else (s1,l1)
    | VAltPar(l,a,None) -> let (s1,l1) = findJ a lju in
                           if s1 = "" then raise (Error ("This theorem statement should refer to a judgment.")) else (s1,l1)
    | VAltOftBlock (l,_,Some(va)) -> findJ va lju
    | VAltOftBlock (l,_,None) -> ("",[])

(* Declaration section *)

(* finds the lambda terms in a production *)
let find_lams lp = List.fold_left (fun x y -> let Production (l, t, la) = y in [(List.fold_left ((fun x y -> begin match y with | AltLam(l1, AName(n),va) -> n | _ -> x end))"" la )]::x ) [] lp

let checkString2 s lt = List.fold_left (fun x y -> let (h1,h2) = y in
                                            if h1 = s then (true,h2) else x) (false, "") lt

(* finds in which variable the alternative in binded *)
let rec findBind l a ty lv ac =
  match a with
    | AltAtomic(l1,t1,a1) -> begin match a1 with
                               | None -> let s = locToString(l) in
                                         let s1 = s ^ " This alternative needs a variable binding." in raise (Error (s1))
                               | Some(a2) ->
                                             let (b, ty1) = checkString2 t1 lv  in
                                             if b then findBind l a2 ty lv ((t1,ty1)::ac)
                                             else let s = locToString(l1) in
                                             let s1 = s ^ " Did you forget to declare " ^ t1 ^ " as a variable?" in raise (Error (s1))
                              end
    | AltBin(l1, a) -> Paire(AltBin(l1, a), ac)
    | _ -> let s = locToString(l) in
           let s1 = s ^ " Syntax error in alternative." in raise (Error (s1))

let diff_type ty lvar = List.fold_left (fun x y -> let (s1, s2) = y in
                                            if ty = s2 then [] else (s1, s2)::x ) [] lvar

let rec altList l ty lty lt lv llam la =
  match la with
    | [] -> let s = locToString(l) in
            let s1 = s ^ " Can't have empty list here according to parser." in raise (Error (s1))
    | h::[] -> alts l ty lty lt lv llam h
    | h::t -> Ext.LF.ArrTyp(l, alts l ty lty lt lv llam h, altList l ty lty lt lv llam t)

(* got through the alternatives, this is for any alternative *)
(* Loc.t -> string -> string list -> terminal list -> alternative list -> Ext.LF.typ *)
and alts l ty lty lt lv llam a =
  match a with
    | AltAtomic(l1, t1, a1) -> if (checkString t1 lty ) then
                                  (* this is a type is theres is an alternative after it just skip to next*)
                               begin match a1 with
                                 | None -> Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil)
                                 | Some(a2) -> Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t1),Ext.LF.Nil), alts l1 ty lty lt lv llam a2)
                               end
                               else
                               begin match a1 with
                                 | None -> Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil)
                                 | Some(a2) -> Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t1),Ext.LF.Nil), alts l1 ty lty lt lv llam a2 )
                               end


    | AltLam(l1, AName(t1), a1) ->
                                   if checkString t1 lt
                                   then
                                   begin match a1 with
                                     | None -> let s = locToString(l1) in
                                               let s1 = s ^ " Must indicate variable binding in this alternative" in
                                               raise (Error (s1))
                                     | Some(a2) -> let Paire(a3, lv1) = findBind l a2 ty lv [] in
                                                   alts l1 ty lty lt lv1 (t1::llam) a3
                                   end
                                   else let s = locToString(l1) in
                                   let s1 = s ^ " " ^ t1 ^ " was not declared terminal" in
                                   raise (Error (s1) )

    | AltFn(l1, Typ(l2, t1), t_or_l, a1) ->
            begin match t_or_l with
              | Ty(Typ(l3, t2)) -> begin match a1 with
                                     | None ->
                                               Ext.LF.Atom(l1, Id.mk_name(Id.SomeString t2),Ext.LF.Nil)
                                     | Some(a2) ->
                                                   Ext.LF.ArrTyp(l, Ext.LF.Atom(l1, Id.mk_name(Id.SomeString t2),Ext.LF.Nil),
                                                   alts l1 ty lty lt lv llam a2)
                                    end
              | La(la2) -> begin match a1 with
                             | None ->
                                       Ext.LF.ArrTyp(l,Ext.LF.ArrTyp(l,Ext.LF.Atom(l1,Id.mk_name(Id.SomeString t1),Ext.LF.Nil)
                                       , altList l1 ty lty lt lv llam la2), Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),
                                       Ext.LF.Nil))
                             | Some(a2) -> let Ext.LF.ArrTyp(l4,ar1,ar2) = alts l1 ty lty lt lv llam (AltFn(l1,Typ(l2, t1), t_or_l, None)) in
                                           Ext.LF.ArrTyp(l,ar1, alts l1 ty lty lt lv llam a2)
                           end
            end


    | AltBin(l1, a) ->  alts l1 ty lty lt lv llam a

    | AltOft(l1, a1, a2) -> alts l1 ty lty lt lv llam a2
    | _ -> raise (Error ("Unvalid alternative/Not implemented yet"))

(* this is for the first element at the begginig of an alternative *)
(* val sgnAlts : Parser.Grammar.Loc.t -> string -> string list -> string list -> string list -> string list -> Ast.alternative list -> Syntax.Ext.Sgn.decl list *)
let rec sgnAlts l ty lty lt lv llam la =
  match la with
    | [] -> []
    | AltAtomic(l1, t1, a1)::t ->
                if (checkString t1 lty )
                then
                (* skip to next and dont care about this type, we are at the beggining of the alternative so there cant be only this atom*)
                begin match a1 with
                  | None -> let s = locToString(l1) in
                            let s1 = s ^ " Illegal alternative" in
                            raise (Error (s1))
                  | Some(a2) ->
                                Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1),  alts l1 ty lty lt lv llam a2)::sgnAlts l ty lty lt lv llam t
                end
                else if (checkString t1 lt)
                then
                begin match a1 with
                  | None -> Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), Ext.LF.Atom(l, Id.mk_name (Id.SomeString ty),Ext.LF.Nil))
                            ::sgnAlts l ty lty lt lv llam t
                  | Some(a2) ->
                                Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), Ext.LF.ArrTyp(l,
                                Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil), alts l1 ty lty lt lv llam a2))
                                ::sgnAlts l ty lty lt lv llam t
                end
                else begin match a1 with
                       | None -> sgnAlts l ty lty lt lv llam t
                       | Some(a2) -> let s = locToString(l1) in
                                     let s1 = s ^ " An Alternative must start with a terminal or declare a variable,
                                              maybe you forgot to declare " ^ t1 ^ " terminal."
                                     in raise (Error (s1))
                end


    | AltLam(l1, AName(t1), a1)::t ->
             if checkString t1 lt
             then
             begin match a1 with
               | None -> raise (Error ("Must indicate variable binding in this alternative"))
               | Some(a2) ->  let Paire(a3, lv1) = findBind l a2 ty lv [] in
                              let ldv = diff_type ty lv1 in
                              if ldv = []
                              then
                              Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), alts l1 ty lty lt lv1 llam a3)
                              ::sgnAlts l ty lty lt lv (t1::llam) t
                              else let arrty = List.fold_right (fun t s -> let (s1, s2) = t in
                              Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString s2),Ext.LF.Nil),s))
                              ldv (alts l1 ty lty lt lv1 llam a3) in
                              Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString t1), arrty)::sgnAlts l ty lty lt lv (t1::llam) t
             end
             else let s = locToString(l1) in
             let s1 = s ^ " " ^ t1 ^ " was not declared terminal" in
             raise (Error (s1) )


    | AltFn(l1, Typ(l2, t1), Ty(Typ(l3, t2)), a1)::t ->
            begin match a1 with
              | None -> Ext.Sgn.Const(l, Id.mk_name (Id.SomeString "arr"),
                        Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t1),Ext.LF.Nil),
                        Ext.LF.ArrTyp(l,Ext.LF.Atom(l1, Id.mk_name (Id.SomeString t2),Ext.LF.Nil),
                        Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil))))::sgnAlts l ty lty lt lv llam t
              | Some(a2)-> let s = locToString(l1) in
                           let s1 = s ^ "Sorry, this feature is not implemented yet." in
                           raise (Error (s1))
            end

    | AltLet(l1, a1, a2, a3)::t ->

             begin match a3 with
               | AltFn(_) -> Ext.Sgn.Const(l1, Id.mk_name (Id.SomeString "letv"), Ext.LF.ArrTyp(l,
                             Ext.LF.Atom(l1, Id.mk_name (Id.SomeString ty),Ext.LF.Nil),  alts l1 ty lty lt lv llam a3))
                             ::sgnAlts l ty lty lt lv llam t
               | _ -> let s = locToString(l1) in
                      let s1 = s ^ "Unvalid alternative" in
                      raise (Error (s1))
             end

    | AltPar::t ->  sgnAlts l ty lty lt lv llam t

    | AltCtx( _ )::t -> let s = locToString(l) in
                        let s1 = s ^ ", unvalid start of alternative context" in
                        raise (Error (s1))

    | _ -> let s = locToString(l) in
           let s1 = s ^ ", unvalid start of alternative" in
           raise (Error (s1))

let rec find_var lt ltyp las = List.fold_left (fun x y ->
                               match y with | (AltAtomic(l1, t1, None)::t,s1) -> if checkString t1 lt
                                                                                 then x@(find_var lt ltyp [(t,s1)])
                                                                                 else (t1,s1)::x@(find_var lt ltyp [(t,s1)])
                                            | (h::t,s1)-> x@(find_var lt ltyp [(t,s1)]) | _ -> [])
                               [] las

let find_var_prep lp = (List.fold_left (fun x y -> let Production(l1, Typ(l2, t1), la) = y in
                                                       ((la,t1)::x) )) [] lp

(* creates new types, string list -> string list -> production list -> Ext.Sgn.decl list, first list types second terminals *)
let rec sgnTypes lt lty lvar llam lp =
  match lp with
    | [] -> []
    | Production(l1, Typ(l2, t1), la)::t ->
                 let sgn1 = sgnAlts l2 t1 lty lt lvar llam la in
                 [Ext.Sgn.Typ(l1, Id.mk_name (Id.SomeString t1), Ext.LF.Typ(l1))]@ sgn1 @ sgnTypes lt lty lvar llam t

(* Judgment Section *)

(* find if the keyword is a type or a symbol, Loc.t -> string -> judge list -> string list -> Ext.Sgn.decl list *)
let rec typ_or_sym l js ltyp =
  match js with
    | [] ->  Ext.LF.Typ(l)
    | h::t -> let Judge(l1,s1) = h in
              if (checkString s1 ltyp )
              then (
              Ext.LF.ArrKind(l, Ext.LF.Atom(l1, Id.mk_name(Id.SomeString s1),Ext.LF.Nil), typ_or_sym l1 t ltyp) )
              else ( typ_or_sym l1 t ltyp)

(* checks the judgement if its not a type its a symbol indicating the syntax of the judgement *)
(* judge list -> string list -> string list *)
let rec typ_or_sym_list lj ltyp =
  match lj with
    | [] ->  []
    | h::t -> let Judge(l1,s1) = h in
              if (checkString s1 ltyp )
              then (
              typ_or_sym_list t ltyp)
              else ( s1 :: typ_or_sym_list t ltyp  )

(* translate the beggining of a judgment, Loc.t -> jName -> jSyntax -> string list -> (string list , Ext.Sgn.decl list) *)
let sgnJudge l jn js ltyp = let JName(j) = jn in
                            let JSyntax(l, a, lj) = js in
                            (typ_or_sym_list lj ltyp, Ext.Sgn.Typ(l,Id.mk_name (Id.SomeString j), typ_or_sym l lj ltyp))


(* put a list of var_alternative in one alternative *)
let rec valtslist lva =
  match lva with
    | [] -> None
    | VAltAtomic(l, s, None)::t -> Some(VAltAtomic(l, s, valtslist t ))
    | VAltFn(l1, VName(n1), VLa([va1]), None)::t -> Some(VAltFn(l1, VName(n1), VLa([va1]), valtslist t))
    | _ -> raise (Error ("Oops never thaught this case will show up"))

(* same as alts but for var_alternatives, Loc.t -> string list -> var_alternative -> Ext.LF.spine *)
let rec valtsPar l lsym a =
  match a with
    | VAltAtomic(l, s, vao) ->
                 begin match vao with
                   | None ->
                             Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil)

                   | Some(VAltBin(l2, va)) -> if checkString s lsym
                                              then (
                                              raise (Error ("Error in Lamdba term.")))
                                              else (
                                              Ext.LF.Lam(l2, Id.mk_name(Id.SomeString s), valtsPar l lsym va) )

                   | Some(va) ->  Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), valts l lsym va)

                 end


    | VAltLam(l, AName(n), va) ->
                                  Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString n)), valts l lsym va)

    | VAltFn(l1, VName(n1), v, vao) ->
             begin match v with
               | VLa(lva) ->  let Some(va1) = valtslist lva in
                     begin match vao with
                       | None -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1)
                       | Some(VAltBin(l2, va)) ->
                                                  Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), Ext.LF.Root(l,
                                                  Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1))
                       | Some(a2) -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym a2)
                     end

               | VTy(Typ(l2,t2)) -> let va2 = VAltAtomic(l2,t2,None) in
                                    let va1 = valts l2 lsym va2 in
                     begin match vao with
                       | None -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString "arr")), Ext.LF.App(l2,Ext.LF.Root(l2,
                                 Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)),Ext.LF.Nil),va1))
                       | Some(VAltBin(l2, va)) -> Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), Ext.LF.Root(l,
                                                  Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)), va1))
                       | Some(a2) -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym a2)
                     end
            end

    | VAltLet(l, va) -> let lsym1 = "="::lsym in
                        Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString "letv")), valts l lsym1 va)

    | VAltOft _ -> raise (Error ("Valtoft"))

    | _ -> let s = locToString(l) in
           let s1 = s ^ " Not implemented yet (in valtsPar)." in
           raise (Error (s1))

(* Loc.t -> string list -> var_alternative -> Ext.LF.spine *)
and valts l lsym va =
  match va with
    | VAltId(l, s, lpr, vao) ->
             begin match lpr with
               | [] -> begin match vao with
                         | None -> Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.Id(l)), Ext.LF.Nil),
                                   Ext.LF.Nil )
                         | Some(va) -> Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.Id(l)), Ext.LF.Nil),
                                       valts l lsym va)
                       end
               | h::t -> let s = locToString(l) in
                         let s1 = s ^ " List of projections1." in
                         raise (Error (s1))
             end

    | VAltAtomic(l, "_", vao) ->
                 begin match vao with
                   | None -> Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Hole(l), Ext.LF.Nil), Ext.LF.Nil)

                   | Some(va) -> let va1 = valts l lsym va in
                                 Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Hole(l), Ext.LF.Nil), va1)
                 end

    | VAltAtomic(l, s, vao) ->
                 begin match vao with
                   | None -> if checkString s lsym
                             then (Ext.LF.Nil )
                             else (
                             Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil), Ext.LF.Nil) )

                   | Some(VAltBin(l2, va)) -> if checkString s lsym
                                              then (raise (Error ("Error in Lamdba term.")))
                                              else (
                                              begin match va with
                                                | VAltFn(l3,v2,vl2,Some(VAltBin(l4,vaoo))) -> Ext.LF.App(l, Ext.LF.Lam(l2,
                                                                                              Id.mk_name(Id.SomeString s),
                                                                                              valtsPar l lsym (VAltFn(l3,v2,vl2,None))),
                                                                                              Ext.LF.App(l,
                                                                                              Ext.LF.Lam(l4, Id.mk_name(Id.SomeString s),
                                                                                              valtsPar l4 lsym vaoo), Ext.LF.Nil))
                                                | _ -> Ext.LF.App(l, Ext.LF.Lam(l2, Id.mk_name(Id.SomeString s), valtsPar l lsym va), Ext.LF.Nil)
                                              end)

                   | Some(va) -> if checkString s lsym
                                 then (valts l lsym va)
                                 else (
                                 Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil), valts l lsym va) )
                 end

    | VAltPar(l, a, vao) -> (begin match vao with
                                 | None -> let v1 = valtsPar l lsym a in
                                                   Ext.LF.App(l, v1, Ext.LF.Nil)


                                 | Some(vb) -> let v1 = valtsPar l lsym a in
                                                   Ext.LF.App(l, v1, valts l lsym vb)

                              end)


    | VAltLam(l, AName(n), va) ->
                                  Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString n)), valts l lsym va), Ext.LF.Nil)

    | VAltFn(l1, VName(n1), VLa([va1]), vao) ->
             begin match vao with
               | None -> Ext.LF.App(l, Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1),
                         Ext.LF.Nil)
               | Some(VAltBin(l2, va)) ->
                                          Ext.LF.App(l, Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), valtsPar l1 lsym va1),
                                          valts l1 lsym va)
               | Some(a2) -> Ext.LF.App(l, Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1),
                             valts l1 lsym a2)
              end

    | VAltFn(l1, VName(n1), VTy(Typ(l2,t2)), vao) ->
             let va2 = VAltAtomic(l2,t2,None) in
             let va1 = valts l2 lsym va2 in
             begin match vao with
               | None -> Ext.LF.App(l,Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString "arr")), Ext.LF.App(l2,Ext.LF.Root(l2,
                         Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)),Ext.LF.Nil),va1)), Ext.LF.Nil)
               | Some(a2) -> Ext.LF.App(l,Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym a2), Ext.LF.Nil)
             end
    | VAltOft(_) -> raise (Error ("Valtoft"))

    | VAltOftBlock(_) -> raise (Error ("Valtoftblock"))

    | VAltBin(l1,va) -> raise (Error ("Problem from binding"))

    | _ -> let s = locToString(l) in
           let s1 = s ^ " Not implemented yet (in valts)." in
           raise (Error (s1))

(* function that deals with the list of premises *)

let rec judges' jn lsym lp l2 va lju =
   match lp with
     | [] -> Ext.LF.Atom(l2, Id.mk_name(Id.SomeString jn), valts l2 lsym va)
     | h::[] -> let Premisse(l3, b1, c1, va1) = h in
               begin match va1 with
    (*             | VAltOft(l, [(n, va3)], VAltPar(l5,va5,Some(VAltPar(l6,va6,None)))) ->*)
                 | VAltOft(l, (n, va3), Some(va5), VAltPar(l6,va6,None)) ->
                             let VAltAtomic(l4, s, vao) = va3 in
                             begin match vao with
                                | None -> let v5 = valts l lsym va5 in
                                          let v6 = valts l lsym va6 in
                                          Ext.LF.ArrTyp(l2, Ext.LF.PiTyp(l, Ext.LF.TypDecl( Id.mk_name(Id.SomeString n),
                                          Ext.LF.Atom(l2, Id.mk_name(Id.SomeString s), Ext.LF.Nil)), Ext.LF.ArrTyp(l,
                                          Ext.LF.Atom(l2, Id.mk_name(Id.SomeString jn), v5),
                                          Ext.LF.Atom(l, Id.mk_name(Id.SomeString jn), v6))),
                                          judges' jn lsym [] l2 va lju)


                                | Some(_) -> let s = locToString(l) in
                                             let s1 = s ^ " Non atomic type declaration for a variable." in
                                             raise (Error (s1))
                             end
                | _ -> Ext.LF.ArrTyp(l2, Ext.LF.Atom(l2, Id.mk_name(Id.SomeString jn), valts l3 lsym va1), judges' jn lsym ([]) l2 va lju)
              end
     | h::t -> let Premisse(l3, b1, c1, va1) = h in
               begin match va1 with
                 | VAltOft(l, (n, va3), _, va2) ->
                           let VAltAtomic(l4, s, vao) = va3 in
                             begin match vao with
                                | None -> Ext.LF.PiTyp(l, Ext.LF.TypDecl( Id.mk_name(Id.SomeString n),
                                          Ext.LF.Atom(l2, Id.mk_name(Id.SomeString s), Ext.LF.Nil)),
                                          Ext.LF.ArrTyp(l2, Ext.LF.Atom(l2, Id.mk_name(Id.SomeString jn), valts l3 lsym va2),
                                          judges' jn lsym t l2 va lju))
                                | Some(_) -> let ( s1, ls) = findJ va3 lju in
                                             let va4 = valts l lsym va3 in
                                             Ext.LF.PiTyp(l, Ext.LF.TypDecl( Id.mk_name(Id.SomeString n),
                                             Ext.LF.Atom(l2, Id.mk_name(Id.SomeString s1), va4)),
                                             Ext.LF.ArrTyp(l2, Ext.LF.Atom(l2, Id.mk_name(Id.SomeString jn),
                                             valts l3 lsym va2), judges' jn lsym t l2 va lju))
                             end
                | _ -> Ext.LF.ArrTyp(l2, Ext.LF.Atom(l2, Id.mk_name(Id.SomeString jn), valts l3 lsym va1), judges' jn lsym t l2 va lju)
              end

(* translate rules, string list -> rule list -> Ext.Sgn.decl list *)
let rec judges jn lsym lr lju =
   match lr with
    | [] -> []
    | h::t -> let Rule(l1, a, RName(s), Premisse(l2, b, c, va)) = h in
              let JName(s1) = jn in
              begin match a with
                | [] ->
                        let lv = [Ext.Sgn.Const(l1, Id.mk_name(Id.SomeString s), Ext.LF.Atom(l2, Id.mk_name(Id.SomeString s1), valts l2 lsym va))] in
                        lv @ judges jn lsym t lju
                | la -> let ju = judges' s1 lsym la l2 va lju in
                        let lv = [Ext.Sgn.Const(l1, Id.mk_name(Id.SomeString s), ju)] in
                        lv @ judges jn lsym t lju
              end

(* Context Section *)

let context_sch l lv lsym lju va =
   match va with
    | VAltOftBlock (l1,ltd,Some(va1)) -> let (s1, ls) = findJ va1 lju in
                                        let va2 = valts l1 lsym va1 in
                                        let ltd' = List.rev ltd in
                                        let sl = Ext.LF.SigmaLast( Ext.LF.Atom(l1, Id.mk_name(Id.SomeString s1), va2)) in
                                        List.fold_left (fun y (x1,x2) -> let VAltAtomic(l4, s, vao) = x2 in
                                                  (begin match vao with
                                                     | None ->
                                                               Ext.LF.SigmaElem(Id.mk_name(Id.SomeString x1),
                                                               Ext.LF.Atom(l1, Id.mk_name(Id.SomeString s), Ext.LF.Nil), y)
                                                     | Some(_) -> let (s2, ls2) = findJ x2 lju in
                                                                  let va3 = valts l1 lsym x2 in
                                                                  Ext.LF.SigmaElem(Id.mk_name(Id.SomeString x1),
                                                                  Ext.LF.Atom(l1, Id.mk_name(Id.SomeString s2), va3), y)
                                                   end)) sl ltd'

    | VAltOftBlock (l1,_,None) -> let s = locToString(l1) in
                                  let s1 = s ^ " There should be a premisse after this context block." in
                                  raise (Error (s1))
    | _ -> let ( s1, ls) = findJ va lju in
           let va2 = valts l lsym va in
           Ext.LF.SigmaLast( Ext.LF.Atom(l, Id.mk_name(Id.SomeString s1), va2))


let rec context lv lsym lju lva =
   match lva with
    | [] ->  []
    | VAltEmpty(l)::t -> context lv lsym lju t
    | VAltOft(l, ltd, _, va1)::t -> let lfd = List.fold_left (fun y (x1,x2) -> let VAltAtomic(l4, s, vao) = x2 in
                                                           begin match vao with
                                                             | None -> Ext.LF.Dec(y, Ext.LF.TypDecl(Id.mk_name(Id.SomeString x1),
                                                                       Ext.LF.Atom(l, Id.mk_name(Id.SomeString s), Ext.LF.Nil)))
                                                             | Some(_) -> let (s2, ls2) = findJ x2 lju in
                                                                          let va2 = valts l lsym x2 in
                                                                          Ext.LF.Dec(y, Ext.LF.TypDecl(Id.mk_name(Id.SomeString x1),
                                                                          Ext.LF.Atom(l, Id.mk_name(Id.SomeString s2), va2)))
                                                           end) Ext.LF.Empty [ltd] in
                                let sc2 = context_sch l lv lsym lju va1 in
                                [Ext.LF.SchElem(l, lfd, sc2)]@context lv lsym lju t
    | VAltOftBlock (l1,td,vao)::t -> let sc2 = context_sch l1 lv lsym lju (VAltOftBlock (l1,td,vao)) in
                                     [Ext.LF.SchElem(l1, Ext.LF.Empty, sc2)]@context lv lsym lju t


(* Theorem Section *)

let rec find_nil vp vp1 =
  match vp with
    | Ext.LF.Root(l, nor, Ext.LF.Nil) -> Ext.LF.Root(l, nor, vp1)
    | Ext.LF.Root(l, hd, Ext.LF.App(l1, nor,sp)) -> Ext.LF.Root(l, hd, Ext.LF.App(l1, find_nil nor vp1,sp))

(* same as valts but for the theorem section, deals with context *)
let rec valtpPar l lt lsym a =
  match a with
    | VAltAtomic(l, s, vao) ->
                 begin match vao with
                   | None ->
                             if checkString s lt
                             then (Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil))
                             else Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.EmptySub(l)), Ext.LF.Nil)


                   | Some(va) -> if checkString s lt
                                 then (
                                 Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), valtp l lt lsym va))
                                 else
                                 (
                                 Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.EmptySub(l)), valtp l lt lsym va))
                 end

    | VAltId(l, s, lpr, vao) ->
             begin match lpr with
               | [] -> begin match vao with
                         | None ->
                                   if checkString s lt
                                   then (
                                         Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil))
                                   else Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.Id(l)), Ext.LF.Nil)
                         | Some(va) -> if checkString s lt
                                       then
                                       Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), valtp l lt lsym va)
                                       else
                                      (
                                       Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.Id(l)), valtp l lt lsym va))
                       end
               | lp -> begin match vao with
                         | None ->
                                   let rlp = List.rev lp in
                                   let ds = List.fold_left (fun x (Proj(l1, s1, i1)) -> Ext.LF.Dot(l1, x,
                                            Ext.LF.Head(Ext.LF.ProjName(l1, i1, Id.mk_name(Id.SomeString s1))) ) ) (Ext.LF.Id(l)) (List.rev rlp) in
                                   Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),ds), Ext.LF.Nil)
                         | Some(va) -> let s = locToString(l) in
                                       let s1 = s ^ " There should be parentheses around the alternative with the list of projections." in
                                       raise (Error (s1))
                       end
             end


    | VAltLam(l, AName(n), va) -> let s = locToString(l) in
                                  let s1 = s ^ " Not implemented yet (in valtpPar) valtlam." in
                                  raise (Error (s1))

    | VAltFn(l1, VName(n1), tyva, vao) ->
             begin match tyva with
               | VTy(Typ(l2,t2)) -> let va2 = VAltAtomic(l2,t2,None) in
                                    let va1 = valts l2 lsym va2 in
                     begin match vao with
                       | None -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString "arr")), Ext.LF.App(l2,Ext.LF.Root(l2,
                                 Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)),Ext.LF.Nil),va1))
                       | Some(VAltBin(l2, va)) -> Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), Ext.LF.Root(l,
                                                  Ext.LF.Name(l, Id.mk_name(Id.SomeString n1)), va1))

                       | Some(a2) -> Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym a2)
                     end
               | VLa(la) -> let s = locToString(l) in
                            let s1 = s ^ " Not implemented yet (in valtpPar) valtfn." in
                            raise (Error (s1))
             end

    | VAltLet(l, va) -> let s = locToString(l) in
                        let s1 = s ^ " Not implemented yet (in valtpPar) valtlet." in
                        raise (Error (s1))

    | VAltBin(_) -> let s = locToString(l) in
                    let s1 = s ^ " Not implemented yet (in valtpPar) valtbin." in
                    raise (Error (s1))

    | VAltOft(_) -> let s = locToString(l) in
                    let s1 = s ^ " Not implemented yet (in valtpPar) valtoft." in
                    raise (Error (s1))

    | VAltOftBlock(_) -> let s = locToString(l) in
                         let s1 = s ^ " Not implemented yet (in valtpPar) valtoftblock." in
                         raise (Error (s1))

    | VAltCtx(_) -> let s = locToString(l) in
                    let s1 = s ^ " Not implemented yet (in valtpPar) valtctx." in
                    raise (Error (s1))

    | VAltEmpty(_) -> let s = locToString(l) in
                      let s1 = s ^ " Not implemented yet (in valtpPar) valtempty." in
                      raise (Error (s1))

    | VAltPar(l, a, vao) -> begin match vao with
                              | None ->  valtpPar l lt lsym a
                              | Some(vb) -> let vp2 = valtpPar l lt lsym a in

                                            let vp3 = valtp l lt lsym vb in
                                            find_nil vp2 vp3
                            end



and valtp l lt lsym va =
  match va with
    | VAltId(l, s, lpr, vao) ->
             begin match lpr with
               | [] -> begin match vao with
                         | None -> Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.Id(l)), Ext.LF.Nil),
                                   Ext.LF.Nil )
                         | Some(va) -> Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.Id(l)), Ext.LF.Nil),
                                       valtp l lt lsym va)
                       end
               | h::t -> let s = locToString(l) in
                         let s1 = s ^ " List of projections." in
                         raise (Error (s1))
             end

    | VAltAtomic(l, s, vao) ->
                 begin match vao with
                   | None -> if checkString s lsym
                             then (Ext.LF.Nil )
                             else (
                                   if checkString s lt
                                   then  Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l,
                                         Id.mk_name(Id.SomeString s)), Ext.LF.Nil), Ext.LF.Nil)
                                   else  Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.MVar(l,
                                         Id.mk_name(Id.SomeString s),Ext.LF.EmptySub(l)), Ext.LF.Nil),
                                         Ext.LF.Nil ))

                   | Some(va) -> if checkString s lsym
                                 then ( valtp l lt lsym va)
                                 else (if checkString s lt
                                       then (
                                       Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s)), Ext.LF.Nil), valtp l lt lsym va))
                                       else (
                                       Ext.LF.App(l, Ext.LF.Root(l, Ext.LF.MVar(l, Id.mk_name(Id.SomeString s),Ext.LF.EmptySub(l)), Ext.LF.Nil),
                                      valtp l lt lsym va)))
                 end

  | VAltPar(l, a, vao) -> begin match vao with
                            | None -> let vp1 = valtpPar l lt lsym a in

                                      Ext.LF.App(l, vp1, Ext.LF.Nil)
                            | Some(vb) -> let vp2 = valtpPar l lt lsym a in

                                          Ext.LF.App(l, vp2, valtp l lt lsym vb )

                              end


    | VAltFn(l1, VName(n1), VLa([va1]), vao) ->
             begin match vao with
               | None -> Ext.LF.App(l, Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1),
                         Ext.LF.Nil)
               | Some(VAltBin(l2, va)) ->
                                          Ext.LF.App(l, Ext.LF.Lam(l2, Id.mk_name(Id.SomeString n1), valtsPar l1 lsym va1),
                                          valts l1 lsym va)
               | Some(a2) -> Ext.LF.App(l, Ext.LF.Root(l1, Ext.LF.Name(l1, Id.mk_name(Id.SomeString n1)), valts l1 lsym va1),
                             valts l1 lsym a2)
              end

    | VAltFn(l1, VName(n1), VTy(Typ(l2, t1)), vao) ->  raise (Error ("ValtFn vty not implemented."))


    |  VAltOftBlock(l1, [h], vao) -> raise (Error ("oue oue"))


    | _ -> raise (Error ("Not implemented yet (in valtp)."))


let rec conTypArr l lt lju lsym ltp =
  match ltp with
    | [] -> let s = locToString(l) in
            let s1 = s ^ " Let me know if you raise this error, it shouldn't happen. " in
            raise (Error (s1))
    | TPremisse(l2,nao1,co,va1)::[] ->
                let (jn,lsym1)= findJ va1 lju in
                let v1 = valtp l lt lsym1 va1 in
                begin match co with
                  | None ->
                            Ext.Comp.TypBox(l2, Ext.LF.Atom(l2,Id.mk_name(Id.SomeString jn),v1),Ext.LF.Null)
                  | Some([Con(s)]) ->
                                    let c = Ext.LF.CtxVar(l2, Id.mk_name(Id.SomeString s)) in
                                    Ext.Comp.TypBox(l2, Ext.LF.Atom(l2,Id.mk_name(Id.SomeString jn),v1), c)
                  | _ -> let s = locToString(l2) in
                         let s1 = s ^ " Let me know if you raise this error. " in
                         raise (Error (s1))
                end
    | TPremisse(l2,nao1,co,va1)::t ->
                let (jn,lsym1)= findJ va1 lju in let v1 = valtp l lt lsym1 va1 in
                begin match co with
                  | None ->
                            Ext.Comp.TypArr(l2, Ext.Comp.TypBox(l2, Ext.LF.Atom(l2,Id.mk_name(Id.SomeString jn),v1),
                            Ext.LF.Null), conTypArr l2 lt lju lsym t)
                  | Some([Con(s)]) ->
                                    let c = Ext.LF.CtxVar(l2, Id.mk_name(Id.SomeString s)) in
                                    Ext.Comp.TypArr(l2, Ext.Comp.TypBox(l2,
                                    Ext.LF.Atom(l2,Id.mk_name(Id.SomeString jn),v1), c), conTypArr l2 lt lju lsym t)
                  | _ -> let s = locToString(l2) in
                         let s1 = s ^ " Let me know if you raise this error. " in
                         raise (Error (s1))
                end


(* translation of what the theorem is proving *)
let stmt_to_prove l lt st lju lsym =
  match st with
    | ForAllExist (l1, tp, p) ->
        (match (tp,p) with
           | ([TPremisse(l2,nao1,None,va1)],Premisse(l3,nao2,None,va2)) ->
               begin match va1 with
                 |VAltAtomic(l4,s1,None) ->
                    let (jn,lsym1)= findJ va2 lju in
                    let v1 = valtp l3 lt lsym1 va2 in
                      (Ext.Comp.TypPiBox(l1,(Ext.LF.MDecl(l2,
                                                          Id.mk_name(Id.SomeString s1),
                                                          Ext.LF.Atom(l2,Id.mk_name(Id.SomeString "n"),Ext.LF.Nil),
                                                          Ext.LF.Null),
                                             Ext.Comp.Explicit),
                                         Ext.Comp.TypBox(l3,Ext.LF.Atom(l3,Id.mk_name(Id.SomeString jn),v1),Ext.LF.Null)),
                       Some([s1]))

                 | _ ->
                     begin match nao1 with
                       | Some(PName(n1)) ->
                           let (jn,lsym1)= findJ va1 lju in
                           let  aa1  = valtp l2 lt lsym va1  in
                           let (jn2,lsym2)= findJ va2 lju in
                           let v1 = valtp l3 lt lsym va2 in
                             (Ext.Comp.TypPiBox(l1,(Ext.LF.MDecl(l2,Id.mk_name(Id.SomeString n1),
                                                                 Ext.LF.Atom(l2,Id.mk_name(Id.SomeString jn),aa1),
                                                                 Ext.LF.Null),
                                                    Ext.Comp.Explicit),
                                                Ext.Comp.TypBox(l3,Ext.LF.Atom(l3,Id.mk_name(Id.SomeString jn2),v1),Ext.LF.Null)),
                              Some([n1]))
                       | None -> let s = locToString(l2) in
                         let s1 = "This premise needs a name.  " ^ s in
                           raise (Error (s1))
                     end
               end

           | (TPremisse(l2,nao1,Some(c1),va1)::t ,Premisse(l3,nao2,co,va2)) ->
               begin match c1 with
                 | [NewCon(s1,x2)] -> let lp1 = [TPremisse(l2,nao1,Some([Con(s1)]),va1)] @ t @ [TPremisse(l3,nao2,co,va2)] in
                   let (s2, ls2) = findJ x2 lju in
                     begin match va1 with
                       | VAltOftBlock(l4, [(s3, VAltAtomic(l5,s5,None))],None) ->
                           let (jn, lsym1) = findJ va2 lju in
                           let va4 = valts l2 lsym va2 in
                           let va3 = Ext.LF.Atom(l1, Id.mk_name(Id.SomeString jn), va4) in
                           let tbox = Ext.Comp.TypBox(l5, va3,Ext.LF.CtxVar(l4,Id.mk_name(Id.SomeString s1)))in
                           let cta = Ext.Comp.TypPiBox(l4, (Ext.LF.MDecl(l4,Id.mk_name(Id.SomeString s3),
                                                                         Ext.LF.Atom(l2,Id.mk_name(Id.SomeString s5), Ext.LF.Nil),
                                                                         Ext.LF.CtxVar(l4,Id.mk_name(Id.SomeString s1))),
                                                            Ext.Comp.Explicit), tbox) in
                           let ls = List.fold_left (fun x y ->
                                                      match y with |TPremisse(_,Some(PName(s)),_,_) -> s::x
                                                        |TPremisse(_,None,_,_) -> x) [] t in
                             (Ext.Comp.TypCtxPi(l1, (Id.mk_name(Id.SomeString s1), Id.mk_name(Id.SomeString s2),
                                                     Ext.Comp.Explicit), cta), Some(ls))

                       | VAltOftBlock(l4, _,Some(va3)) -> let s = locToString(l2) in
                         let s1 = "Stmt to prove valtoftblock some.  " ^ s in
                           raise (Error (s1))
                       | _ -> let cta = conTypArr l1 lt lju lsym lp1 in
                           begin match nao1 with
                             | Some(PName(n1)) -> let ls = List.fold_left (fun x y ->
                                                                             match y with |TPremisse(_,Some(PName(s)),_,_) -> s::x
                                                                               |TPremisse(_,None,_,_) -> x) [] t in
                                 (Ext.Comp.TypCtxPi(l1, (Id.mk_name(Id.SomeString s1), Id.mk_name(Id.SomeString s2),
                                                         Ext.Comp.Implicit), cta), Some(n1::ls))
                             | None -> let s = locToString(l2) in
                               let s1 = "This premise needs a name.  " ^ s in
                                 raise (Error (s1))
                           end
                     end
                 | [Con(s)] -> let s2 = locToString(l2) in
                   let s1 = "Specify the type of " ^ s ^ " " ^ s2 in
                                    raise (Error (s1))
                      end
                   | _ -> let s = locToString(l) in
                          let s1 = "Context problem. " ^ s in
                          raise (Error (s1))
                   )
    | Exist (l1, p) ->
             begin match p with
               | Premisse( l2, None, None, va) ->
                                                  let (jn, lsym) = findJ va lju in
                                                  let va1 = valts l2 lsym va in
                                                  (Ext.Comp.TypBox(l1, Ext.LF.Atom(l1, Id.mk_name(Id.SomeString jn), va1), Ext.LF.Null),None)
               | Premisse _ -> raise (Error ("Not implemented."))
             end

let comp_box l lt lsym co va =
  match co with
    | Some([Con(s)]) -> let va1 = valtpPar l lt lsym va in
                      Ext.Comp.Box(l, [Id.mk_name(Id.SomeString s)],va1)
    | _ -> raise (Error ("Should use a context that has already been specified \n"))

(* check if you have alambda term *)
let rec contain_lam llam va =
  match va with
    | VAltAtomic(l, s, Some(vao)) -> if (checkString s llam) then true else contain_lam llam vao
    | VAltAtomic(l, s, None) -> if (checkString s llam) then true else false
    | VAltBin(l, va) -> contain_lam llam va
    | VAltLam(l, _, va) -> contain_lam llam va
    | VAltId(l, _, _, Some(va)) -> contain_lam llam va
    | VAltId(l, _, _, None) -> false
    | VAltFn(l, _, _, Some(va)) -> contain_lam llam va
    | VAltFn(l, _, _, None) -> false
    | VAltPar(l,a,Some(va)) -> if (contain_lam llam a) then true else contain_lam llam va
    | VAltPar(l,a,None) -> contain_lam llam a
    | VAltOftBlock (l,_,Some(va)) -> contain_lam llam va
    | VAltOftBlock (l,_,None) -> false
    | VAltLet (l,va) -> contain_lam llam va

let get_comp_var var =
  match var with
    | "x" -> "u"
    | "y" -> "v"
    | "z" -> "w"
    | "u" -> "q"
    | "v" -> "r"

let rec get_var va1 =
  match va1 with
    | VAltOftBlock(l1 , [(t, d)], _) -> t
    | VAltAtomic(l1, v, vao) -> begin match vao with
                                | Some(va) -> get_var va
                                | None ->  let s1 = " Couldn't find the correponding variable. " in
                                           raise (Error (s1))
                                end

    | VAltOft(l1, (t, d), _, _) -> t

    | _ -> let s1 = " This should have the proper syntax for context declaration, couldn't find the corresponding variable. " in
           raise (Error (s1))

let count = ref 0

let rec count_valt lju va1 va2 =
  match va1 with
    | VAltOftBlock(l1 , ltd, Some(va)) -> begin match va2 with
                                            | VAltOftBlock(l1 , ltd, vao) -> (count := !count + 1; !count)
                                            | _ -> (count := !count + 1; count_valt lju va va2)
                                          end
    | VAltAtomic(l1, v, a) -> let (s1, ls1) = findJ (VAltAtomic(l1, v, a)) lju in
                              let (s2, ls2) = findJ va2 lju in
                              if s1 = s2
                              then (count := !count + 1; !count)
                              else let s = locToString(l1) in
                                   let s1 = " This should have the proper syntax for context declaration. " ^ s in
                                   raise (Error (s1))
    | _ -> let s1 = " This should have the proper syntax for context declaration. " in
           raise (Error (s1))

(* translate theorem branches *)
let rec comp_branch l lt n omlam lsym llam lju al cb cano =
  match al with
    | [] -> []
    | Arg(l1, TPremisse(l2, None, None, va), pl)::t -> if cb
                            then
                            let s = locToString(l) in
                            let s1 = s ^ " Not implemented in context comp_branch arg with context." in
                            raise (Error (s1))
                            else
                            let v1 = valtpPar l1 lt lsym va in
                            let p1 = proofs l1 lt n omlam pl lsym llam lju cb cano in
                            let cb1 = Ext.Comp.Branch(l, Ext.LF.Empty, Ext.Comp.PatMetaObj(l1, Ext.Comp.MetaObjAnn(l1, Ext.LF.Null, v1)),  p1) in
                            cb1 :: comp_branch l lt n omlam lsym llam lju t cb cano

    | Arg(l1, TPremisse(l2, None, Some(c), va), pl)::t ->
                       begin match c with
                         |[NewCon(n1, va1)] -> count := 0;
                                              let k = count_valt lju va1 va in
                                              let v = get_var va1 in
                                              let s1 = get_comp_var v in
                                              let pvar = Ext.LF.Root(l2, Ext.LF.ProjPVar(l2, k, (Id.mk_name(Id.SomeString s1), Ext.LF.Id(l2))), Ext.LF.Nil) in
                                              let p1 = proofs l1 lt n omlam pl lsym llam lju cb cano in
                                              let cb1 = Ext.Comp.Branch(l, Ext.LF.Empty, Ext.Comp.PatMetaObj(l1,
                                                        Ext.Comp.MetaObjAnn(l1, Ext.LF.CtxVar(l2,Id.mk_name(Id.SomeString n1)), pvar)),  p1) in
                                              cb1 :: comp_branch l lt n omlam lsym llam lju t cb cano

                         | [Con(c)] -> let va1 = valtpPar l1 lt lsym va in
                                       let p1 = proofs l1 lt n omlam pl lsym llam lju cb cano in
                                       let cb1 = Ext.Comp.Branch(l, Ext.LF.Empty, Ext.Comp.PatMetaObj(l1,
                                                 Ext.Comp.MetaObjAnn(l1, Ext.LF.CtxVar(l2,Id.mk_name(Id.SomeString c)), va1)),  p1) in
                                       cb1 :: comp_branch l lt n omlam lsym llam lju t cb cano

                         | _ -> let s = locToString(l1) in
                                let s1 = "Need to specify what has been added to the context. " ^ s in
                                raise (Error (s1))
                       end


    | Argument(l1, Rule(l2,lp1,RName(rn),p),lp)::t ->
               let lp2 = List.map (fun (Premisse(l3, no,c, va)) -> match no with | Some(PName(n1))-> [n1]
                                                                                 | _ -> []) (lp1@[p]) in
               if lp2 = []
               then (
               let Premisse(l4, _, co, va) = p in
               begin match co with
                      | None -> let v1 = Ext.LF.Root(l2, Ext.LF.Name( l2, Id.mk_name(Id.SomeString rn)), Ext.LF.Nil) in

                                let p1 = proofs l1 lt n omlam lp lsym llam lju cb cano in
                                let cb1 = Ext.Comp.Branch(l, Ext.LF.Empty, Ext.Comp.PatMetaObj(l1, Ext.Comp.MetaObjAnn(l1, Ext.LF.Null, v1)), p1) in
                                cb1 :: comp_branch l lt n omlam lsym llam lju t cb  cano
                      | Some([Con(c)]) -> let v1 = Ext.LF.Root(l2, Ext.LF.Name(l2, Id.mk_name(Id.SomeString rn)), Ext.LF.Nil)in

                                        let p1 = proofs l1 lt n omlam lp lsym llam lju cb cano in
                                        let cb1 = Ext.Comp.Branch(l, Ext.LF.Empty, Ext.Comp.PatMetaObj(l1, Ext.Comp.MetaObjAnn(l1,
                                                  Ext.LF.CtxVar(l4,Id.mk_name(Id.SomeString c)), v1)), p1)in
                                        cb1 :: comp_branch l lt n omlam lsym llam lju t cb cano
                     |  _ -> let s = locToString(l) in
                             let s1 = s ^ " Not implemented in context comp_branch" in
                             raise (Error (s1))
               end
               )
               else (let Premisse(l4, _, co, va) = p in
                   if contain_lam llam va
                   then
                   begin match co with
                      | None -> let s = locToString(l) in
                                let s1 = s ^ " This lambda term expects a context." in
                                raise (Error (s1))

                      | Some([Con(c)]) -> let Premisse(l5,_,_,va5)::t1 = lp1 in
                                          let var = get_var va5 in
                                          let cvar = get_comp_var var in
                                          let va2 = (List.fold_left (fun x y -> match y with |[] -> x | n1::[] ->
                                                     let dots = Ext.LF.Dot(l2, Ext.LF.Id(l2), Ext.LF.Head(Ext.LF.Name(l2, Id.mk_name(Id.SomeString var)))) in
                                                     let dots1 = Ext.LF.Dot(l2, dots, Ext.LF.Head(Ext.LF.Name( l2, Id.mk_name(Id.SomeString cvar)))) in
                                                     let norm = Ext.LF.Root(l2, Ext.LF.MVar(l2, Id.mk_name(Id.SomeString n1), dots1),Ext.LF.Nil) in
                                                     let lam = Ext.LF.Lam(l2, Id.mk_name(Id.SomeString cvar), norm) in
                                                     let lam1 = Ext.LF.Lam(l2, Id.mk_name(Id.SomeString var), lam ) in
                                                     Ext.LF.App(l2, lam1, x))) Ext.LF.Nil lp2 in

                                         let v1 = Ext.LF.Root(l2, Ext.LF.Name( l2, Id.mk_name(Id.SomeString rn)), va2) in


                                        let p1 = proofs l1 lt n omlam lp lsym llam lju cb cano in
                                        let cb1 = Ext.Comp.Branch(l, Ext.LF.Empty, Ext.Comp.PatMetaObj(l1,
                                        Ext.Comp.MetaObjAnn(l1, Ext.LF.CtxVar(l4, Id.mk_name(Id.SomeString c)), v1)), p1) in
                                        cb1 :: comp_branch l lt n omlam lsym llam lju t cb cano
                      |  _ -> let s = locToString(l) in
                              let s1 = s ^ " Not implemented in context comp_branch" in
                              raise (Error (s1))
                   end
                   else
                   begin match co with
                      | None ->  let va1 = (List.fold_left (fun x y -> match y with
                                            |[] -> x | n1::t -> Ext.LF.App(l1, Ext.LF.Root(l2, Ext.LF.MVar(l2,
                                                                Id.mk_name(Id.SomeString n1),Ext.LF.EmptySub(l1)),Ext.LF.Nil),x))) Ext.LF.Nil (List.rev lp2) in
                                                                let v1 = Ext.LF.Root(l2, Ext.LF.Name( l2, Id.mk_name(Id.SomeString rn)), va1) in
                                                                let p1 = proofs l1 lt n omlam lp lsym llam lju cb cano in
                                                                let cb1 = Ext.Comp.Branch(l, Ext.LF.Empty,
                                                                Ext.Comp.PatMetaObj(l1, Ext.Comp.MetaObjAnn(l1, Ext.LF.Null, v1)), p1) in
                                                                cb1 :: comp_branch l lt n omlam lsym llam lju t cb cano

                      | Some([Con(c)]) -> let va1 = (List.fold_left (fun x y -> match y with |[] -> x | n1::[] -> Ext.LF.App(l1, Ext.LF.Root(l2, Ext.LF.MVar(l2,
                                                                   Id.mk_name(Id.SomeString n1),Ext.LF.Id(l1)),Ext.LF.Nil),x))) Ext.LF.Nil (List.rev lp2) in
                                        let v1 = Ext.LF.Root(l2, Ext.LF.Name( l2, Id.mk_name(Id.SomeString rn)), va1) in
                                        let p1 = proofs l1 lt n omlam lp lsym llam lju cb cano in
                                        let cb1 = Ext.Comp.Branch(l, Ext.LF.Empty, Ext.Comp.PatMetaObj(l1,
                                        Ext.Comp.MetaObjAnn(l1, Ext.LF.CtxVar(l4, Id.mk_name(Id.SomeString c)), v1)), p1) in
                                        cb1 :: comp_branch l lt n omlam lsym llam lju t cb cano
                      |  _ -> let s = locToString(l) in
                              let s1 = s ^ " Not implemented in context comp_branch" in
                              raise (Error (s1))
                    end
                    )

(* translate justifications *)
and proofs l lt n omlam pl lsym llam lju cb cano =
  match pl with
    | [] -> raise (Error ("Sorry, I am not implemented yet.[]"))
    | h::t ->
       begin match h with
         | URule (l1, tp, RName(n1), lvno) ->
                  begin match (lvno,omlam) with
                    | (None,_) ->
                                  Ext.Comp.Syn(l1, Ext.Comp.BoxVal(l, Ext.LF.Null, Ext.LF.Root(l1, Ext.LF.Name( l1, Id.mk_name(Id.SomeString n1)), Ext.LF.Nil)))

                    | (Some(vn),Some([s1])) -> let va = VAltAtomic(l1,s1,None) in
                                               let v1 = valtp l1 lt lsym va in
                                               Ext.Comp.Box(l, [], Ext.LF.Root(l1, Ext.LF.Name( l1, Id.mk_name(Id.SomeString n1)),v1))
                    |  (_, Some(l)) -> let s1 = "more than one element in mlam  1  "  in
                                       raise (Error (s1)) (* see case below if you raise this error *)
                  end
         | Proof (l1, tp, TPremisse(_, None, None, VAltAtomic(_,s,None)), al) ->
                  begin match omlam with
                    | Some(h1::t1) -> if cb
                                      then (
                                      let cbranch = comp_branch l1 lt n omlam lsym llam lju al cb  cano in
                                      let cc = Ext.Comp.Case(l1,Pragma.RegularCase, Ext.Comp.Var(l1,Id.mk_name(Id.SomeString s)),
                                               cbranch) in
                                      let ls = h1::t1 in
                                      let lcf = List.fold_left (fun x y -> Ext.Comp.Fun(l1,Id.mk_name(Id.SomeString y),x) ) cc ls in
                                      lcf)
                                      else
                                      let cbranch = comp_branch l1 lt n omlam lsym llam lju al cb  cano in
                                      let cc = Ext.Comp.Case(l1,Pragma.RegularCase, Ext.Comp.BoxVal(l1, Ext.LF.Null,
                                      Ext.LF.Root(l1 ,Ext.LF.MVar(l1 ,Id.mk_name(Id.SomeString s),Ext.LF.EmptySub(l1)),
                                      Ext.LF.Nil)), cbranch) in
                                      let ls = h1::t1 in
                                      List.fold_left (fun x y -> Ext.Comp.MLam(l1,(Id.mk_name(Id.SomeString y),Ext.Comp.MObj),x) ) cc ls

                    | Some([]) -> let s1 = "Weird empty string list. "  in
                                  raise (Error (s1))
                    | None -> let s = locToString(l1) in
                              let s1 = "forall missing in this proof.  " ^ s in
                              raise (Error (s1))
                  end

         | Proof (l1, tp, tp1, al) ->
                  begin match omlam with
                    | Some([]) -> begin match tp1 with
                                    | TPremisse(l2, None, Some([Con(c)]), va) ->
                                            let VAltId(l3, s1, _, None) = va in
                                            let cbranch = comp_branch l1 lt n omlam lsym llam lju al cb  cano in
                                            let va1 = valtpPar l2 lt lsym va in
                                            let cc = Ext.Comp.Case(l1,Pragma.RegularCase, Ext.Comp.BoxVal(l2,
                                                     Ext.LF.CtxVar(l2, Id.mk_name(Id.SomeString c)), va1), cbranch) in

                                            Ext.Comp.CtxFun(l1, Id.mk_name(Id.SomeString c),Ext.Comp.MLam(l1, (Id.mk_name(Id.SomeString s1),Ext.Comp.MObj),cc))

                                    | _ -> let s = locToString(l1) in
                                               let s1 = "This is not a valid induction variable.  " ^ s in
                                               raise (Error (s1))
                                  end

                    | _ -> let s = locToString(l1) in
                           let s1 = "This is not a valid induction variable.  " ^ s in
                          raise (Error (s1))
                  end

         | PRule (l1, tp, pf, lva) ->
                  begin match lva with
                    | [] -> raise (Error ("Sorry, I am not implemented yet (PR1)."))
                    | [TPremisse(l2,None,_,VAltAtomic(l3,s,None))] ->
                       begin match pf with
                         | InductionHyp(l2) -> let v1 = VAltAtomic(l1,s,None) in
                                               begin match tp with
                                                 | TPremisse(_,Some(PName(s1)),_,_) ->
                                                             let v2 = VAltAtomic(l1,s1,None) in
                                                             let ag = Arg(l1,TPremisse(l1, None, None, v2),t) in
                                                             let v3 = valtpPar l1 lt lsym v1 in
                                                             let cbranch = comp_branch l lt n (Some([s1])) lsym llam lju [ag] cb  cano in
                                                             Ext.Comp.Case(l1,Pragma.RegularCase,Ext.Comp.MApp(l1,Ext.Comp.Var(l1,Id.mk_name(Id.SomeString n)),
                                                             ([], v3)), cbranch)
                                                 | _ ->      let v3 = valtpPar l1 lt lsym v1 in
                                                             Ext.Comp.Syn(l1,Ext.Comp.MApp(l1,Ext.Comp.Var(l1,Id.mk_name(Id.SomeString n)), ([], v3)))
                                               end
                         | _ -> raise (Error ("Sorry not implemented yet in prule1."))
                       end
                    | [TPremisse(l2,Some(PName(s2)),_,VAltAtomic(l3,s,None))] -> let s = locToString(l1) in
                                                                                 let s1 = "This premisse should'nt have a name." ^ s in
                                                                                 raise (Error (s1))
                    | lvn1 -> begin match pf with
                                | InductionHyp(l2) ->
                                  begin match tp with
                                    | TPremisse(_,Some(PName(s1)),_,_) ->
                                                let v2 = VAltAtomic(l1,s1,None) in
                                                let ag = Arg(l1,TPremisse(l1, None, None, v2),t) in
                                                let cv = Ext.Comp.Var(l1,Id.mk_name(Id.SomeString n)) in

                                                let lca = List.fold_left (fun x (TPremisse(l3,None,c,va1)) ->
                                                          let cbox = comp_box l3 lt lsym c va1 in
                                                          Ext.Comp.Apply(l1, x, cbox )  ) cv lvn1 in
                                                let cbranch = comp_branch l lt n (Some([s1])) lsym llam lju [ag] cb cano in


                                                Ext.Comp.Case(l1,Pragma.RegularCase, lca, cbranch)

                                    | TPremisse(l4,None,_,v2) ->

                                                let cv = Ext.Comp.Var(l1,Id.mk_name(Id.SomeString n)) in

                                                let lca = List.fold_left (fun x (TPremisse(l3,None,c,va1)) ->
                                                          begin match c with
                                                            | Some([Con(s)]) -> let va3 = valtpPar l lt lsym va1 in
                                                                                Ext.Comp.MAnnApp(l1, x, (Ext.LF.CtxVar(l1, Id.mk_name(Id.SomeString s)), va3))

                                                            | Some(Con(s)::[NewCon(s1, va4)]) -> let va3 = valtpPar l lt lsym va1 in
                                                                                                 let ctxv = Ext.LF.CtxVar(l1, Id.mk_name(Id.SomeString s)) in
                                                                        let va5 = context_sch l4 (["x"]) lsym lju va4 in
                                                                        let td = Ext.LF.TypDecl(Id.mk_name(Id.SomeString s1), Ext.LF.Sigma(l4, va5)) in
                                                                        let dd = Ext.LF.DDec(ctxv, td) in
                                                                        Ext.Comp.MAnnApp(l1, x, (dd, va3))

                                                            | Some(Con(s)::[Con(s1)]) -> let va3 = valtpPar l lt lsym va1 in
                                                                        let dd = (Id.mk_name(Id.SomeString s))::[Id.mk_name(Id.SomeString s1)] in
                                                                        Ext.Comp.MApp(l1, x, (dd, va3))

                                                            | _ -> let s = locToString(l4) in
                                                                           let s1 = "Problem with the context of your premisse." ^ s in
                                                                           raise (Error (s1))


                                                          end
                                                           ) cv (lvn1) in

                                                begin match v2 with
                                                  | VAltAtomic(l5, s5, None) -> let v1 = Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s5)),
                                                                                         Ext.LF.Nil) in
                                                                                let Some(c1) = cano in
                                                                                let cb1 = Ext.Comp.Branch(l, Ext.LF.Empty, Ext.Comp.PatMetaObj(l1,
                                                                                Ext.Comp.MetaObjAnn(l1, Ext.LF.Null, v1)), c1) in
                                                                                Ext.Comp.Case(l1,Pragma.RegularCase, lca, [cb1])

                                                  | VAltId(l5, s5, [], None) ->
                                                                                let cb1 = comp_branch l lt n None lsym llam lju [] cb None in
                                                                                Ext.Comp.Case(l1,Pragma.RegularCase, lca, cb1)

                                                  | _ -> let s = locToString(l4) in
                                                         let s1 = "Sorry not implemented yet in prule2." ^ s in
                                                         raise (Error (s1))
                                                end
                                  end
                                | _ -> raise (Error ("Sorry not implemented yet in prule valt."))
                              end

                  end

         | InductionHyp (l1) -> raise (Error ("Sorry, I am not implemented yet (IH)."))

         | CaseAn (l1, tp, [VName(vn)], al) -> if t = []
                                               then
                                               let cbranch = comp_branch l lt n (Some([vn])) lsym llam lju al cb None in
                                               Ext.Comp.Case(l1,Pragma.RegularCase,Ext.Comp.Var(l1,Id.mk_name(Id.SomeString vn)), cbranch)
                                               else
                                               let pt = proofs l lt n None t lsym llam lju cb cano in
                                               let cbranch = comp_branch l lt n (Some([vn])) lsym llam lju al cb (Some(pt)) in
                                               Ext.Comp.Case(l1,Pragma.RegularCase,Ext.Comp.Var(l1,Id.mk_name(Id.SomeString vn)), cbranch)

         | PTheorem (l1, tn) -> raise (Error ("Sorry, I am not implemented yet (PTheorem)."))

         | Unique(l1, np) -> begin match np with
                               | TPremisse(l2, None, None, VAltAtomic(l3, s1, None)) -> Ext.Comp.Syn(l1, Ext.Comp.BoxVal(l1, Ext.LF.Null,
                                                                                        Ext.LF.Root(l, Ext.LF.Name(l, Id.mk_name(Id.SomeString s1)), Ext.LF.Nil)))

                               | TPremisse(l2, None, _, va) -> let va1 = valtpPar l lt lsym va in
                                                               Ext.Comp.Syn(l1, Ext.Comp.BoxVal(l1, Ext.LF.Null, va1))
                               | _ -> let s = locToString(l) in
                                      let s1 = s ^ " This shouldn't have a context" in
                                      raise (Error (s1))
                              end

         | _ -> raise (Error ("Error in theorem."))
       end

let theorem l lt n st pl lju lsym llam cb = (* omlam = [d,f] *)
                                       let (ctb,omlam) =  stmt_to_prove l lt st lju lsym in
                                       let prf = proofs l lt n omlam pl lsym llam lju cb None in
                                       [Ext.Sgn.Rec(l, [Ext.Comp.RecFun( Id.mk_name(Id.SomeString n), ctb, prf)])]


(* string list -> string list -> Ext.Sgn.decl list, first list terminals secong types *)
let rec recSectionDecl lt ltyp lv ls lju lsym llam cb =
  match ls with
    | [] -> []
    | h::t -> begin match h with
                | Grammar (_, lp) -> let las = find_var_prep lp in
                                     let lvar = find_var lt ltyp las in

                                     let ls = sgnTypes lt ltyp lvar llam lp in
                                     let llam1 = List.flatten(find_lams lp) in
                                     (ls @ recSectionDecl lt ltyp lvar t lju lsym llam1 cb)
                | Judgement(l, jn, js, a, lr) ->
                                                 let (lsym1, sgnj) = sgnJudge l jn js ltyp in
                                                 let lj = judges jn lsym1 lr lju in
                                                 let JName(s1)=jn in
                                                 [sgnj] @ lj @ recSectionDecl lt ltyp lv t (Jdef(s1,lsym1)::lju) (lsym1@lsym) llam cb
                | ContextDecl (l, CName(cn), lva) -> let c =  context lv lsym lju lva in
                                                     [Ext.Sgn.Schema(l, Id.mk_name(Id.SomeString cn), Ext.LF.Schema(c))]
                                                     @ recSectionDecl lt ltyp lv t lju lsym llam true
                | Theorems (l, TName(n), st, pl) ->
                                                    let t1 = theorem l lt n st pl lju lsym llam cb in
                                                    t1 @ recSectionDecl lt ltyp lv t lju lsym llam cb
              end

(* section list -> string list *)
let rec recSectionDeclGram l ls =
  match ls with
    | [] -> []
    | Grammar (_, Production(l1, Typ(l2, t1), la)::t2):: t ->
                                                              let rec ltails lp acc = match lp with
                                                                                        | [] -> acc
                                                                                        | Production(l3, Typ(l4, t3), la)::t4 -> ltails t4 (t3::acc)  in
                                                              let tails = ltails t2 [] in
                                                              t1 :: tails @ recSectionDeclGram l t
    | Judgement _ ::t -> recSectionDeclGram l t
    | ContextDecl (l, cn, lva)::t -> recSectionDeclGram l t
    | Terminals_decl _:: t -> let s = locToString(l) in
                              let s1 = s ^ " Should only have one declaration of terminals" in
                              raise (Error (s1))
    | Theorems _ :: t-> recSectionDeclGram l t

(* string list -> string list -> Syntax.section list -> Syntax.Ext.Sgn.decl list *)
let sectionDecls ls =
  match ls with
    | Terminals_decl(l,lt):: t -> let lt1 = List.map (fun x -> let Terminal(_, t1) = x in t1) lt in
                                  let ltyp = recSectionDeclGram l t in
                                  recSectionDecl lt1 ltyp [] t [] [] [] false
    | _ -> raise (Error ("No terminal declaration or grammar at the beginnig of file"))
