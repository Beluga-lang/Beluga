(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

open Syntax


module Cid = struct

  module Typ = struct

    type entry = {
      name               : Id.name;
      implicit_arguments : int;
      kind               : Int.LF.kind;
      var_generator      : (unit -> string) option;
      mvar_generator     : (unit -> string) option;
      mutable constructors : Id.cid_term list;
      mutable subordinates : BitSet.t;
      mutable typesubordinated : BitSet.t
    }
    
    let entry_list  = ref []

    let mk_entry name kind implicit_arguments =
      {
        name               = name;
        implicit_arguments = implicit_arguments;
        kind               = kind;
        var_generator      = None;
        mvar_generator     = None;
        constructors       = [];
        subordinates       = BitSet.empty ();
        typesubordinated   = BitSet.empty ()
      }
    
    type t = Id.name DynArray.t

    (*  store : {!entry DynArray.t} *)
    (*  store is used for storing the information associated with a cid *)
    let store = DynArray.create ()
    
    (*  directory : {!(Id.name, Id.cid_type) Hashtbl.t} *)
    (*  directory keeps track of which cid a name is associated with
        and provides a way to quickly look up this information. *)
    let directory = Hashtbl.create 0
    
    let index_of_name n = Hashtbl.find directory n
    
    let get = DynArray.get store
    
    let addNameConvention cid_name var_name_generator mvar_name_generator =
      let cid_tp = index_of_name cid_name in 
      let entry = get cid_tp in
      let new_entry = {name   = entry.name ;
                       implicit_arguments = entry.implicit_arguments ; 
                       kind  = entry.kind ;
                       var_generator    = var_name_generator; 
                       mvar_generator   =  mvar_name_generator;
                       constructors     = entry.constructors;
                       subordinates     = entry.subordinates;
                       typesubordinated = entry.typesubordinated
                      } in 
        (DynArray.set store cid_tp new_entry; 
         cid_tp)


    let var_gen cid_tp =  (get cid_tp).var_generator 
    let mvar_gen cid_tp =  (get cid_tp).mvar_generator 

    let rec gen_var_name tA = match tA with 
      | Int.LF.Atom (_, a, _ ) -> var_gen a
      | Int.LF.PiTyp(_, tA) -> gen_var_name tA
      | Int.LF.Sigma typRec -> gen_var_name_typRec typRec

    and gen_var_name_typRec = function
      | Int.LF.SigmaLast tA -> gen_var_name tA
      | Int.LF.SigmaElem(_, _, rest) -> gen_var_name_typRec rest

    let rec gen_mvar_name tA = match tA with 
      | Int.LF.Atom (_, a, _ ) -> mvar_gen a
      | Int.LF.PiTyp(_, tA)    -> gen_mvar_name tA
      | Int.LF.TClo(tA, _)     -> gen_mvar_name tA
      | Int.LF.Sigma typRec    -> gen_mvar_name_typRec typRec

    and gen_mvar_name_typRec = function
      | Int.LF.SigmaLast tA -> gen_mvar_name tA
      | Int.LF.SigmaElem(_, _, rest) -> gen_mvar_name_typRec rest
    
 
    let subord_read arr i =
      if i >= DynArray.length arr then
        false
      else DynArray.get arr i

    let rec subord_write arr i =
      if i >= DynArray.length arr then
        (DynArray.add arr false;
         subord_write arr i)
      else DynArray.set arr i true

    let subord_iter f arr =
      DynArray.iteri (fun n flag -> if flag then f n) arr

    let subord_iter f arr =
      Enum.iter f (BitSet.enum arr)
 
    (* add the subordination:  b-terms can contain a-terms *)
    let rec addSubord a b =
      let a_e = get a in
      let b_e = get b in
      let _ = print_string ("addSubord " ^ a_e.name.Id.string_of_name ^ " " ^ b_e.name.Id.string_of_name ^ "\n") in
        if BitSet.is_set b_e.subordinates a then
          ()
        else
          (BitSet.set b_e.subordinates a;
           (* Take transitive closure:
              If b-terms can contain a-terms, then b-terms can contain everything a-terms can contain. *)
           subord_iter (fun aa -> addSubord aa b) a_e.subordinates;
          );
      subord_iter (fun bb -> addTypesubord a bb) b_e.typesubordinated

    (* add the type-level subordination:  b-types can contain a-terms *)
    and addTypesubord a b =
      let a_e = get a in
      let b_e = get b in
      let _ = print_string ("addTypesubord " ^ a_e.name.Id.string_of_name ^ " " ^ b_e.name.Id.string_of_name ^ "\n") in
        if BitSet.is_set a_e.typesubordinated b then
          ()
        else
          (BitSet.set a_e.typesubordinated b;
           (* If b-types can contain a-terms, then b-types can contain everything a-terms can contain. *)
           subord_iter (fun bb -> addTypesubord bb a) b_e.subordinates)
    
    let updateTypesubord cid entry =
      let rec doTypDecl = function
            Int.LF.TypDecl(_name, typ) -> doTyp typ
      and doTyp = function
        | Int.LF.Atom (_loc, a, _spine) ->
            addTypesubord a cid
        | Int.LF.PiTyp ((typdecl, _depend), typ) ->
            doTypDecl typdecl;
            doTyp typ
          
      and update = function
        | Int.LF.Typ -> ()
        | Int.LF.PiKind ((typdecl, _depend), kind) ->
            doTypDecl typdecl;
            update kind
(*          List.iter (fun dependentArgType -> addTypesubord dependentArgType cid_tp) typesubords;
*)
      in
        update entry.kind



    let add entry =
      let cid_tp = DynArray.length store in
        DynArray.add store entry;
        Hashtbl.replace directory entry.name cid_tp;
        entry_list := cid_tp :: !entry_list;
        updateTypesubord cid_tp entry;
        cid_tp
    
    
    let rec inspect acc = function
      | Int.LF.Atom(_, b, spine) ->
          List.iter (fun acc1 -> addSubord acc1 b) acc;
          [b]

      | Int.LF.PiTyp((Int.LF.TypDecl(_name, tA1), _depend), tA2) ->      
          inspect (acc @ (inspect [] tA1)) tA2
    (*  | Sigma _ -> *)

    let addConstructor typ c tA =
      let e = get typ in
      let _ = e.constructors <- c :: e.constructors in
      let _ = inspect [] tA in
        ()
    
    let clear () =
      entry_list := [];
      DynArray.clear store;
      Hashtbl.clear directory

    let is_subordinate_to a b =
      let a_e = get a in
        (*subord_read*)BitSet.is_set a_e.subordinates b

    let is_typesubordinate_to a b =
      let b_e = get b in
        (*subord_read*)BitSet.is_set b_e.typesubordinated a

  end


  module Term = struct

    type entry = {
      name               : Id.name;
      implicit_arguments : int;
      typ                : Int.LF.typ
    }

    let mk_entry n t i = {
      name               = n;
      implicit_arguments = i;
      typ                = t
    }


    type t = Id.name DynArray.t

    (*  store : entry DynArray.t *)
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name name = Hashtbl.find directory name

    let add e_typ entry =
      let cid_tm = DynArray.length store in
        DynArray.add store entry;
        Hashtbl.replace directory entry.name cid_tm;
        Typ.addConstructor e_typ cid_tm entry.typ;
        cid_tm

    let get = DynArray.get store

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear store;
      Hashtbl.clear directory

  end


  module Schema = struct

    type entry = {
      name   : Id.name;
      schema : Int.LF.schema
    }

    let mk_entry name schema = {
      name   = name;
      schema = schema
    }

    type t = Id.name DynArray.t

    (*  store : entry DynArray.t *)
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name n = Hashtbl.find directory n

    let add entry =
      let cid_tm = DynArray.length store in
        DynArray.add store entry;
        Hashtbl.replace directory entry.name cid_tm;
        cid_tm

    let get = DynArray.get store

    let get_schema name = (get name).schema

    let clear () =
      DynArray.clear store;
      Hashtbl.clear directory

  end



  module Comp = struct

    type entry = {
      name               : Id.name;
      implicit_arguments : int;
      typ                : Int.Comp.typ;
      prog               : Int.Comp.exp_chk;
      mut_rec            : Id.name list
    }

    let mk_entry name typ implicit_arguments exp name_list =  {
      name               = name;
      implicit_arguments = implicit_arguments;
      typ                = typ;
      prog               = exp;
      mut_rec            = name_list  (* names of functions with which n is mutually recursive *)
    }

    type t = Id.name DynArray.t

    (*  store : entry DynArray.t *)
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name n = Hashtbl.find directory n

    let add e =
      let cid_prog = DynArray.length store in
        DynArray.add store e;
        Hashtbl.replace directory e.name cid_prog;
        cid_prog

    let get = DynArray.get store

    let clear () =
      DynArray.clear store;
      Hashtbl.clear directory

  end
end



(* LF Bound variables *)
module BVar = struct

  type entry = { name : Id.name }

  let mk_entry n = { name = n }

  type t = entry list

  let index_of_name store n =
    let rec loop i = function
      | []      -> raise Not_found
      | e :: es ->
          if e.name = n then
            i
          else
            loop (i + 1) es
    in
      loop 1 store
  
  let create ()    = []
  let extend ctx e = e :: ctx
  let length       = List.length
  let get          = List.nth

end



(* Free Bound Variables *)
module FVar = struct

(*
  let store    = Hashtbl.create 25
  let add      = Hashtbl.add store
  let get      = Hashtbl.find store
  let clear () = Hashtbl.clear store

*)

  let store    = ref []

  let add x tA = 
    let rec update str = match str with
      | ((y, tA')::str') -> 
          if x = y then 
            begin match (tA, tA') with 
              | (Int.LF.Type tB, 
                 Int.LF.TypVar (Int.LF.TInst ({contents = None} as r, _, _, {contents = []}))) -> 
                  (r := Some tB ; 
                  (x, Int.LF.Type tB)::str')
            end 
          else 
            (y, tA'):: update str'
      | [] -> [(x, tA)]
    in 
      store := update (!store)
    

  let get x    = 
    let rec lookup str = match str with
      | ((y, tA)::str') -> 
          if x = y then tA else lookup str'
      | _ -> raise Not_found
    in 
      lookup (!store)


  let clear () = (store := [])

  let fvar_list () = !store


end



(* Free meta-variables *)
module FMVar = struct

  let store    = Hashtbl.create 0
  let add      = Hashtbl.add store
  let get      = Hashtbl.find store
  let clear () = Hashtbl.clear store

end



(* Free parameter variables *)
module FPVar = struct

  let store    = Hashtbl.create 0
  let add      = Hashtbl.add store
  let get      = Hashtbl.find store
  let clear () = Hashtbl.clear store

end



(* Computation-level variables *)
module Var = struct

  type entry = { name : Id.name }

  let mk_entry n = { name = n }

  type t = entry list

  let index_of_name store n =
    let rec loop i = function
      | []        -> raise Not_found
      | (e :: es) ->
          if e.name = n then
            i
          else
            loop (i + 1) es
    in
      loop 1 store

  let create ()    = []
  let extend ctx e = e :: ctx
  let get          = List.nth

end



(* Contextual variables *)
module CVar = struct

  type entry = { name : Id.name }

  let mk_entry n = { name = n }

  type t = entry list

  let index_of_name store n =
    let rec loop i = function
      | []        -> raise Not_found
      | (e :: es) ->
          if e.name = n then
            i
          else
            loop (i + 1) es
    in
      loop 1 store

  let create ()     = []
  let extend cvars e = e :: cvars
  let get           = List.nth
  let append cvars cvars' = cvars @ cvars'
  let length cvars = List.length cvars 

end

let clear () =
  Cid.Typ.clear ();
  Cid.Term.clear ();
  Cid.Schema.clear ();
  Cid.Comp.clear ()
