(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

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
      mutable subordinates : bool DynArray.t
    }
    
    let entry_list  = ref []

    let mk_entry n k i =
      {
        name               = n;
        implicit_arguments = i;
        kind               = k;
        var_generator      = None;
        mvar_generator     = None;
        constructors       = [];
        subordinates       = DynArray.create ()
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
    
    let add e =
      let cid_tp = DynArray.length store in
        DynArray.add store e;
        Hashtbl.replace directory e.name cid_tp;
        entry_list := cid_tp :: !entry_list;
        cid_tp
    
    let get = DynArray.get store
    
    let addNameConvention cid_name var_name_generator mvar_name_generator =
      let cid_tp = index_of_name cid_name in 
      let entry = get cid_tp in
      let new_entry = {name   = entry.name ;
                        implicit_arguments = entry.implicit_arguments ; 
                        kind  = entry.kind ;
                        var_generator  = var_name_generator; 
                        mvar_generator =  mvar_name_generator;
                        constructors   = [];
                        subordinates   = DynArray.create()
                      } in 
        (DynArray.set store cid_tp new_entry ; 
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
 
    (* add the subordination:  b-terms can contain a-terms *)
    let rec addSubord a b =
      let a_e = get a in
      let b_e = get b in
        if subord_read b_e.subordinates a then
          ()
        else
          (subord_write b_e.subordinates a;
           (* Take transitive closure:
              If b-terms can contain a-terms, then b-terms can contain everything a-terms can contain. *)
           subord_iter (fun aa -> addSubord aa b) a_e.subordinates)


    let rec inspect acc = function
      | Int.LF.Atom(_, b, _spine) ->
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
        subord_read a_e.subordinates b

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

    let index_of_name n = Hashtbl.find directory n

    let add e_typ e =
      let cid_tm = DynArray.length store in
        DynArray.add store e;
        Hashtbl.replace directory e.name cid_tm;
        Typ.addConstructor e_typ cid_tm e.typ;
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

    let mk_entry n t = {
      name   = n;
      schema = t
    }

    type t = Id.name DynArray.t

    (*  store : entry DynArray.t *)
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name n = Hashtbl.find directory n

    let add e =
      let cid_tm = DynArray.length store in
        DynArray.add store e;
        Hashtbl.replace directory e.name cid_tm;
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

    let mk_entry n t i e n_list =  {
      name               = n;
      implicit_arguments = i;
      typ                = t;
      prog               = e;
      mut_rec            = n_list  (* names of function with which n is mutual recursive *)
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
