(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Syntax



module Cid = struct

  module Typ = struct

    type entry =
      { name               : Id.name
      ; implicit_arguments : int
      ; kind               : Int.LF.kind }

    let mk_entry n k i =
      { name               = n
      ; implicit_arguments = i
      ; kind               = k }


    type t = Id.name DynArray.t

    (*  store : {!entry DynArray.t} *)
    (*  store is used for storing the information associated with a cid *)
    let store = DynArray.create ()

    (*  directory : {!(Id.name, Id.cid_type) Hashtbl.t} *)
    (*  directory keeps track of which cid a name is associated with
        and provides a way to quickly look this information up. *)
    let directory = Hashtbl.create 0


    let index_of_name n = Hashtbl.find directory n

    let add e =
      let cid_tp = DynArray.length store in
          DynArray.add store e
        ; Hashtbl.replace directory e.name cid_tp
        ; cid_tp

    let get = DynArray.get store

    let clear () =
        DynArray.clear store
      ; Hashtbl.clear directory

  end



  module Term = struct

    type entry =
      { name               : Id.name
      ; implicit_arguments : int
      ; typ                : Int.LF.typ }

    let mk_entry n t i =
      { name               = n
      ; implicit_arguments = i
      ; typ                = t }


    type t = Id.name DynArray.t

    (*  store : entry DynArray.t *)
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0 (* FIXME: investigate better initial size *)

    let index_of_name n = Hashtbl.find directory n

    let add e =
      let cid_tm = DynArray.length store in
          DynArray.add store e
        ; Hashtbl.replace directory e.name cid_tm
        ; cid_tm

    let get = DynArray.unsafe_get store

    let clear () =
        DynArray.clear store
      ; Hashtbl.clear directory

  end

  module Schema = struct

    type entry =
      { name               : Id.name
      ; schema             : Int.LF.schema }

    let mk_entry n t =
      { name               = n
      ; schema             = t }


    type t = Id.name DynArray.t

    (*  store : entry DynArray.t *)
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0 (* FIXME: investigate better initial size *)

    let index_of_name n = Hashtbl.find directory n

    let add e =
      let cid_tm = DynArray.length store in
          DynArray.add store e
        ; Hashtbl.replace directory e.name cid_tm
        ; cid_tm

    let get = DynArray.unsafe_get store

    let clear () =
        DynArray.clear store
      ; Hashtbl.clear directory

  end

  module Comp = struct

    type entry =
      { name               : Id.name
      ; implicit_arguments : int
      ; typ                : Int.Comp.typ 
      ; prog               : Int.Comp.exp_chk
      }

    let mk_entry n t i e =
      { name               = n
      ; implicit_arguments = i
      ; typ                = t 
      ; prog               = e}


    type t = Id.name DynArray.t

    (*  store : entry DynArray.t *)
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0 (* FIXME: investigate better initial size *)

    let index_of_name n = Hashtbl.find directory n

    let add e =
      let cid_prog = DynArray.length store in
          DynArray.add store e
        ; Hashtbl.replace directory e.name cid_prog
        ; cid_prog

    let get = DynArray.unsafe_get store

    let clear () =
        DynArray.clear store
      ; Hashtbl.clear directory

  end

end

(* LF Bound variables *)
module BVar = struct

  type entry =
    { name : Id.name }

  let mk_entry n =
    { name = n }


  type t = entry list

  let index_of_name store n =
    let rec loop i = function
      | []      -> raise Not_found
      | (e::es) -> if e.name = n
                   then i
                   else loop (i+1) es in
      loop 1 store

  let create () = []

  let extend ctx e = e :: ctx

  let length = List.length

  let get = List.nth

end

(* Free Bound Variables *)
module FVar = struct

  let store = Hashtbl.create 0

  let add = Hashtbl.add store

  let get = Hashtbl.find store

  let clear () = Hashtbl.clear store

end


(* Free meta-variables *)
module FMVar = struct

  let store = Hashtbl.create 0

  let add = Hashtbl.add store

  let get = Hashtbl.find store

  let clear () = Hashtbl.clear store

end


(* Free parameter-variables *)
module FPVar = struct

  let store = Hashtbl.create 0

  let add = Hashtbl.add store

  let get = Hashtbl.find store

  let clear () = Hashtbl.clear store

end


(* Computation-level variables *)
module Var = struct

  type entry =
    { name : Id.name }

  let mk_entry n =
    { name = n }


  type t = entry list

  let index_of_name store n =
    let rec loop i = function
      | []      -> raise Not_found
      | (e::es) -> if e.name = n
                   then i
                   else loop (i+1) es in
      loop 1 store

  let create () = []

  let extend ctx e = e :: ctx

  let get = List.nth

end

(* Contextual variables *)
module CVar = struct

  type entry =
    { name : Id.name }

  let mk_entry n =
    { name = n }


  type t = entry list

  let index_of_name store n =
    let rec loop i = function
      | []      -> raise Not_found
      | (e::es) -> if e.name = n
                   then i
                   else loop (i+1) es in
      loop 1 store

  let create () = []

  let extend dctx e = e :: dctx

  let get = List.nth

end

let clear () =
    Cid.Typ.clear    ()
  ; Cid.Term.clear   ()
  ; Cid.Schema.clear ()
  ; Cid.Comp.clear   ()
