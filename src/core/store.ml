(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



module Int = Syntax.Int



module Cid = struct

  module Typ = struct

    type entry =
      { name : Id.name
      ; kind : Int.kind }

    let mk_entry n k =
      { name = n
      ; kind = k }

    let string_of_entry e = Id.string_of_name e.name


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
      { name : Id.name
      ; typ  : Int.typ }

    let mk_entry n t =
      { name = n
      ; typ  = t }

    let string_of_entry e = Id.string_of_name e.name


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

end



module BVar = struct

  type entry =
    { name : Id.name }

  let mk_entry n =
    { name = n }

  let string_of_entry e = Id.string_of_name e.name


  type t = entry list

  let index_of_name store n =
    let rec loop i = function
      | []      -> raise Not_found
      | (e::es) -> if e.name = n
                   then i
                   else loop (i+1) es in
      loop 0 store

  let create () = []

  let extend ctx e = e :: ctx

  let get = List.nth

end
