open Syntax

type error =
  | FrozenType of Id.cid_typ

exception Error of Syntax.Loc.t * error

(* Register error printer at the end of this module. *)

module Modules = struct

  exception NotUnique of string

  let current : string list ref = ref []

  let opened : string list list ref = ref []

  let modules : (string list, Int.Sgn.decl list ref) Hashtbl.t = Hashtbl.create 0

  let signatures : (string list, Int.Sgn.module_sig list ref) Hashtbl.t = Hashtbl.create 0

  let is_signature (n : string list) : bool =
    try
      ignore(Hashtbl.find signatures n); true
      with | Not_found -> try
        ignore(Hashtbl.find signatures (!current @ n)); true
      with | Not_found -> false

  let open_module (l : string list) : unit =
    let x = try let _ = Hashtbl.find modules l in l 
      with Not_found -> let _ = Hashtbl.find modules (!current @ l) in !current @ l
    in opened := x :: !opened

  let find (x : (string list, 'a) Hashtbl.t) (f : 'a -> 'b) : 'b =
    try
      f (Hashtbl.find x !current)
    with
    | Not_found ->
      let rec iter_find (l : string list list) : 'b = match l with 
        | [] -> raise Not_found
        | h::t -> try f (Hashtbl.find x h) with Not_found -> iter_find t
      in iter_find !opened

  let addSgnToCurrent (decl : Int.Sgn.decl) : unit = 
    try let l = (Hashtbl.find modules !current) in l := decl :: !l 
    with Not_found -> Hashtbl.add modules !current (ref [decl])

  let addSigToCurrent (sgn : Int.Sgn.module_sig) : unit =
    try let l = (Hashtbl.find signatures !current) in l := sgn :: !l
    with Not_found -> let l = ref [sgn] in Hashtbl.add signatures !current l

  
  let instantiateModule (name : string) : unit =
    let l = !current @ [name] in
    try
      let _ = Hashtbl.find modules l in
      raise (NotUnique name)
    with
    | Not_found -> try
        let _ = Hashtbl.find signatures l in
        raise (NotUnique name)
      with | Not_found -> current := l; Hashtbl.add modules l (ref [])

  let instantiateModuleType (name : string) : unit =
    let l = !current @ [name] in
    try
      let _ = Hashtbl.find modules l in
      raise (NotUnique name)
    with
    | Not_found -> try
        let _ = Hashtbl.find signatures l in
        raise (NotUnique name)
      with | Not_found -> current := l; Hashtbl.add signatures l (ref [])

  let decl_to_sig : Ext.Sgn.decl -> Ext.Sgn.module_sig = function
    | Ext.Sgn.Const(l, n, t) -> Ext.Sgn.ConstSig(l, n, t)
    | Ext.Sgn.Typ(l, n, k) -> Ext.Sgn.TypSig(l, n, k)
    | Ext.Sgn.CompTyp(l, n, k) -> Ext.Sgn.CompTypSig(l, n, k)
    | Ext.Sgn.CompCotyp(l, n, k) -> Ext.Sgn.CompCotypSig(l, n, k)
    | Ext.Sgn.CompConst(l, n, t) -> Ext.Sgn.CompConstSig(l, n, t)
    | Ext.Sgn.CompDest(l, n, t) -> Ext.Sgn.CompDestSig(l, n, t)
    | Ext.Sgn.CompTypAbbrev(l, n, k, t) -> Ext.Sgn.CompTypAbbrevSig(l, n, k, t)
    | Ext.Sgn.Schema(l, n, sw) -> Ext.Sgn.SchemaSig(l, n, sw)

  let rec forceTyp = function [] -> (fun x -> x) | ml -> function
    | Int.LF.Atom (loc, (l,m,x), s) -> Int.LF.Atom(loc, (ml@l, m, x), s)
    | Int.LF.PiTyp(l, tA) -> Int.LF.PiTyp(forceTypDecl ml l, forceTyp ml tA)
    | Int.LF.Sigma tRec -> Int.LF.Sigma(forceTRec ml tRec)
    | Int.LF.TClo (tA, s) -> Int.LF.TClo(forceTyp ml tA, s)
  and forceTRec = function [] -> (fun x -> x) | ml -> function
    | Int.LF.SigmaLast(n, tA) -> Int.LF.SigmaLast(n, forceTyp ml tA)
    | Int.LF.SigmaElem(n, tA, tRec) -> (Int.LF.SigmaElem(n, forceTyp ml tA, forceTRec ml tRec))
  and forceTypDecl = function [] -> (fun x -> x) | ml -> function
    | (Int.LF.TypDecl (n, tA), dep) -> (Int.LF.TypDecl(n, forceTyp ml tA), dep)
    | (Int.LF.TypDeclOpt _ , _) as x -> x

  let forceCTypDecl = function [] -> (fun x -> x) | ml -> function
    | Int.LF.Decl(n, Int.LF.MTyp(tA, cD, dep)) -> Int.LF.Decl(n, Int.LF.MTyp(forceTyp ml tA, cD, dep))
    | Int.LF.Decl(n, Int.LF.PTyp(tA, cD, dep)) -> Int.LF.Decl(n, Int.LF.PTyp(forceTyp ml tA, cD, dep))
    | Int.LF.Decl(n, Int.LF.STyp _ ) as x -> x
    | Int.LF.Decl(n, Int.LF.CTyp _ ) as x -> x
    | Int.LF.DeclOpt n -> Int.LF.DeclOpt n

  let rec forceCompTyp = function [] -> (fun x -> x) | ml -> function
    | Int.Comp.TypBox(l, tA, cD) -> Int.Comp.TypBox(l, forceTyp ml tA, cD)
    | Int.Comp.TypParam(l, tA, cD) -> Int.Comp.TypParam(l, forceTyp ml tA, cD)
    | Int.Comp.TypArr(a,b) -> Int.Comp.TypArr(forceCompTyp ml a, forceCompTyp ml b)
    | Int.Comp.TypCross(a,b) -> Int.Comp.TypCross(forceCompTyp ml a, forceCompTyp ml b)
    | Int.Comp.TypPiBox(cTypDecl, t) -> Int.Comp.TypPiBox(forceCTypDecl ml cTypDecl, forceCompTyp ml t)
    | Int.Comp.TypClo(t, mSub) -> Int.Comp.TypClo(forceCompTyp ml t, mSub)
    | x -> x

  let rec forceKind = function [] -> (fun x -> x) | ml -> function
    | Int.LF.Typ -> Int.LF.Typ
    | Int.LF.PiKind(tDecl, k) -> Int.LF.PiKind(forceTypDecl ml tDecl, forceKind ml k)    

  let rec forceCompKind = function [] -> (fun x -> x) | ml -> function
    | Int.Comp.Ctype l -> Int.Comp.Ctype l
    | Int.Comp.PiKind (l, cTypDecl, k) -> 
        Int.Comp.PiKind(l, forceCTypDecl ml cTypDecl, forceCompKind ml k)

end


module Cid = struct

  module Typ = struct

    type entry = {
      name                 : Id.name;
      implicit_arguments   : int;
      kind                 : Int.LF.kind;
      var_generator        : (unit -> string) option;
      mvar_generator       : (unit -> string) option;
      mutable frozen       : bool;
      mutable constructors : Id.cid_term list;
      mutable subordinates : BitSet.t;    (* bit array: if cid is a subordinate of this entry, then the cid-th bit is set *)
      mutable typesubordinated : BitSet.t (* unused at the moment *)
    }

    let entry_list : (string list, Id.cid_typ list ref) Hashtbl.t = Hashtbl.create 0

    let mk_entry name kind implicit_arguments =
      {
        name               = name;
        implicit_arguments = implicit_arguments;
        kind               = kind;
        var_generator      = None;
        mvar_generator     = None;
        frozen             = false;
        constructors       = [];
        subordinates       = BitSet.empty ();
        typesubordinated   = BitSet.empty ()
      }


    (*  store is used for storing the information associated with a cid *)
    let store : (string list, entry DynArray.t) Hashtbl.t = 
      Hashtbl.create 0


    (*  directory keeps track of which cid a name is associated with
        and provides a way to quickly look up this information. *)
    let directory : (string list, (Id.name, Id.cid_typ) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

    let index_of_name : Id.name -> Id.cid_typ = function
    | n when n.Id.modules = [] -> 
        Modules.find directory (fun x -> Hashtbl.find x n)
        (* Hashtbl.find (Hashtbl.find directory (!Modules.current)) n *)
    | n -> 
      if Modules.is_signature n.Id.modules then raise Not_found else
      let m = n.Id.modules in
      let n' = Id.mk_name (Id.SomeString n.Id.string_of_name) in
      let (_,l,i) = 
        try Hashtbl.find (Hashtbl.find directory n.Id.modules) n'
        with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ n.Id.modules)) n' in
      (m,l,i)

    let get = function
    | (m, [], n) -> 
        let e = Modules.find store (fun x -> DynArray.get x n) in
        (* let e = DynArray.get (Hashtbl.find store (!Modules.current)) n in *)
        {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); kind = Modules.forceKind m e.kind}
    | (m, l, n) -> 
      let e = try DynArray.get (Hashtbl.find store l) n
      with Not_found -> DynArray.get (Hashtbl.find store (!Modules.current @ l)) n in
      {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); kind = Modules.forceKind m e.kind}

    let freeze a =
          (get a).frozen <- true

    let addNameConvention cid_name var_name_generator mvar_name_generator =
      let cid_tp = index_of_name cid_name in
      let entry = get cid_tp in
      let new_entry = {name   = entry.name ;
                       implicit_arguments = entry.implicit_arguments ;
                       kind  = entry.kind ;
                       var_generator    = var_name_generator;
                       mvar_generator   = mvar_name_generator;
                       frozen           = entry.frozen;
                       constructors     = entry.constructors;
                       subordinates     = entry.subordinates;
                       typesubordinated = entry.typesubordinated
                      } in
        let store =   
          try Hashtbl.find store (!Modules.current)
          with _ -> begin 
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x 
          end in
        let (_,_, n) = cid_tp in
        (DynArray.set store n new_entry;
         cid_tp)


    let rec cid_of_typ : Int.LF.typ -> Id.cid_typ = function
      | Int.LF.Atom (_, a, _ ) -> a
      | Int.LF.PiTyp(_, tA) -> cid_of_typ tA
      | Int.LF.Sigma typRec -> cid_of_typRec typRec
      | Int.LF.TClo (tA, s) -> cid_of_typ tA

    and cid_of_typRec = function
    | Int.LF.SigmaLast (n, tA) -> cid_of_typ tA
    | Int.LF.SigmaElem(_, _, rest) -> cid_of_typRec rest
    
    let var_gen cid_tp =  (get cid_tp).var_generator
    let mvar_gen cid_tp =  (get cid_tp).mvar_generator

    let rec gen_var_name tA = match tA with
      | Int.LF.Atom (_, a, _ ) -> var_gen a
      | Int.LF.PiTyp(_, tA) -> gen_var_name tA
      | Int.LF.Sigma typRec -> gen_var_name_typRec typRec
      | Int.LF.TClo (tA, s) -> gen_var_name tA

    and gen_var_name_typRec = function
      | Int.LF.SigmaLast (_, tA) -> gen_var_name tA
      | Int.LF.SigmaElem(_, _, rest) -> gen_var_name_typRec rest

    let rec gen_mvar_name tA = match tA with
      | Int.LF.Atom (_, a, _ ) -> mvar_gen a
      | Int.LF.PiTyp(_, tA)    -> gen_mvar_name tA
      | Int.LF.TClo(tA, _)     -> gen_mvar_name tA
      | Int.LF.Sigma typRec    -> gen_mvar_name_typRec typRec

    and gen_mvar_name_typRec = function
      | Int.LF.SigmaLast (n, tA) -> gen_mvar_name tA
      | Int.LF.SigmaElem(_, _, rest) -> gen_mvar_name_typRec rest


    (* Subordination array:

       Subordination information is stored in a bit array.
       if cid is a subordinate of this entry, then the cid-th bit is set

       We store subordination information as a adjacency matrix, i.e.
       the row corresponding to one type familly contains *all* cids
       it can depend on.

    *)
    (* subord_iter f arr = ()

       if f: int -> ()    and
          arr is a  bit array describing a subordination relation
       then
          f is applied to each cid which is in the subordination relation
    *)
    let subord_iter f arr =
      Enum.iter f (BitSet.enum arr)

    (* add the subordination:  b-terms can contain a-terms *)
    (* addSubord a b = ()

       Let a,b be cid for type constructors.
       Terms of type family b can contain terms of type family a.
     *)
    let rec addSubord a b =
      let (_, _, a_n) = a in
      let (_, _, _b_n) = b in
      let a_e = get a in
      let b_e = get b in
        if BitSet.is_set b_e.subordinates a_n then
          (* a is already in the subordinate relation for b, i.e. b depends on a *)
          ()
        else
          (* a is not yet in the subordinate relation for b, i.e. b depends on a *)
          (BitSet.set b_e.subordinates a_n;
           (* Take transitive closure:
              If b-terms can contain a-terms, then b-terms can contain everything a-terms can contain. *)
           (* Call below could be replaced by
              subord_iter (fun aa -> BitSet.set b_e subordinates aa) a_e.subordinates *)
           subord_iter (fun aa -> addSubord ([], [], aa) b) a_e.subordinates;
          )

(*
(* At the moment not relevant: may or may not be correct / unused code *)
    (* add the type-level subordination:  b-types can contain a-terms *)
     and addTypesubord a b =
      let a_e = get a in
      let b_e = get b in
(*      let _ = print_string ("addTypesubord " ^ a_e.name.Id.string_of_name ^ " " ^ b_e.name.Id.string_of_name ^ "\n") in *)
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
*)

    let rec inspect acc = function
      | Int.LF.Atom(_, b, spine) ->
          List.iter (fun a -> addSubord a b) acc ; [b]

      | Int.LF.PiTyp((Int.LF.TypDecl(_name, tA1), _depend), tA2) ->
          inspect (acc @ (inspect [] tA1)) tA2
    (*  | Sigma _ -> *)


    let rec inspectKind cid_tp acc = function
      | Int.LF.Typ ->
          List.iter (fun a -> addSubord a cid_tp) acc
      | Int.LF.PiKind((Int.LF.TypDecl(_name, tA1), _depend), tK2) ->
          inspectKind cid_tp (acc @ (inspect [] tA1)) tK2

    let add entry = match entry.name.Id.modules with
    | [] -> begin
      let cid_tp = 
        let store =   
          try Hashtbl.find store (!Modules.current)
          with _ -> begin 
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x
          end in
        DynArray.add store entry;
        ([], !Modules.current, (DynArray.length store) - 1) in

        let directory =   
          try Hashtbl.find directory (!Modules.current)
          with _ -> begin 
            let x = Hashtbl.create 0 in
            Hashtbl.add directory (!Modules.current) x; 
            x
          end in
        Hashtbl.replace directory entry.name cid_tp;

        let entry_list =   
          try Hashtbl.find entry_list (!Modules.current)
          with _ -> begin 
            let x = ref [] in
            Hashtbl.add entry_list (!Modules.current) x;
            x
          end in
        entry_list := cid_tp :: !entry_list;

        inspectKind cid_tp [] entry.kind;
        cid_tp end
    | l ->
      let n' = Id.mk_name (Id.SomeString entry.name.Id.string_of_name) in
      try Hashtbl.find (Hashtbl.find directory (!Modules.current @ l)) n'
      with Not_found -> Hashtbl.find (Hashtbl.find directory l) n'

    let addConstructor loc typ c tA =
      let entry = get typ in
        if entry.frozen then
          raise (Error (loc, FrozenType typ))
        else
          let _ = entry.constructors <- c :: entry.constructors in
          let _ = inspect [] tA in
          (* type families occuring tA are added to the subordination relation
             BP: This insepction should be done once for each type family - not
                 when adding a constructor; some type families do not have
                 constructors, and it is redundant to compute it multiple times.
          *)
            ()

    let clear () =
      (Hashtbl.find entry_list (!Modules.current)) := [];
      DynArray.clear (Hashtbl.find store (!Modules.current));
      Hashtbl.clear (Hashtbl.find directory (!Modules.current))

    let is_subordinate_to (a : Id.cid_typ) (b : Id.cid_typ) : bool =
      let a_e = get a in
      let (_, _, b_n) = b in
        (*subord_read*)BitSet.is_set a_e.subordinates b_n

    let is_typesubordinate_to (a : Id.cid_typ) (b : Id.cid_typ) : bool =
      let b_e = get b in
      let (_, _, a_n) = a in
        (*subord_read*)BitSet.is_set b_e.typesubordinated a_n
  end

  module Term = struct

    type entry = {
      name               : Id.name;
      implicit_arguments : int;
      typ                : Int.LF.typ
    }

    let mk_entry n t i = 
      let modules = n.Id.modules in
      {
      name               = n;
      implicit_arguments = i;
      typ                = Modules.forceTyp modules t
    }

    let store : (string list, entry DynArray.t) Hashtbl.t = Hashtbl.create 0

    let directory : (string list, (Id.name, Id.cid_term) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

    let index_of_name : Id.name -> Id.cid_typ = function
    | n when n.Id.modules = [] -> 
        Modules.find directory (fun x -> Hashtbl.find x n)
    | n -> 
      if Modules.is_signature n.Id.modules then raise Not_found else
      let m = n.Id.modules in
      let n' = Id.mk_name (Id.SomeString n.Id.string_of_name) in
      let (_,l,i) = 
        try Hashtbl.find (Hashtbl.find directory n.Id.modules) n'
        with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ n.Id.modules)) n' in
      (m,l,i)

    let add loc e_typ entry = match entry.name.Id.modules with
    | [] -> begin 
      let cid_tm = 
        let store = 
          try Hashtbl.find store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x
          end in
          DynArray.add store entry;
          ([], !Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try Hashtbl.find directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            Hashtbl.add directory (!Modules.current) x;
            x
          end in
        Hashtbl.replace directory entry.name cid_tm;
        Typ.addConstructor loc e_typ cid_tm entry.typ;
        cid_tm end
    | l ->
      let n' = Id.mk_name (Id.SomeString entry.name.Id.string_of_name) in
      try Hashtbl.find (Hashtbl.find directory l) n'
      with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ l)) n'

    let get = function
    | (m, [], n) -> 
        let e = Modules.find store (fun x -> DynArray.get x n) in
        {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceTyp m e.typ}
    | (m, l, n) -> 
      let e = try DynArray.get (Hashtbl.find store l) n
      with Not_found -> DynArray.get (Hashtbl.find store (!Modules.current @ l)) n in
      {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceTyp m e.typ }

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear (Hashtbl.find store (!Modules.current));
      Hashtbl.clear (Hashtbl.find directory  (!Modules.current))

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

    (*  store : entry DynArray.t *)
    let store : (string list, entry DynArray.t) Hashtbl.t = Hashtbl.create 0


    (*  directory : (Id.name, Id.cid_term) Hashtbl.t *)
    let directory : (string list, (Id.name, Id.cid_schema) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

    let index_of_name : Id.name -> Id.cid_typ = function
    | n when n.Id.modules = [] -> 
      Modules.find directory (fun x -> Hashtbl.find x n)
    | n -> 
      if Modules.is_signature n.Id.modules then raise Not_found else
      let m = n.Id.modules in
      let n' = Id.mk_name (Id.SomeString n.Id.string_of_name) in
      let (_,l,i) = 
        try Hashtbl.find (Hashtbl.find directory n.Id.modules) n'
        with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ n.Id.modules)) n' in
      (m,l,i)

    let add entry = match entry.name.Id.modules with
    | [] -> begin
      let cid_schema = 
        let store = 
          try Hashtbl.find store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x
          end in
          DynArray.add store entry;
          ([], !Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try Hashtbl.find directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            Hashtbl.add directory (!Modules.current) x;
            x
          end in
        Hashtbl.replace directory entry.name cid_schema;
        cid_schema end
    | l ->
      let n' = Id.mk_name (Id.SomeString entry.name.Id.string_of_name) in
      try Hashtbl.find (Hashtbl.find directory l) n'
      with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ l)) n'

    let get = function
    | (m, [], n) -> 
        let e = Modules.find store (fun x -> DynArray.get x n) in
        {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name))}
    | (m, l, n) -> 
      let e = try DynArray.get (Hashtbl.find store l) n
      with Not_found -> DynArray.get (Hashtbl.find store (!Modules.current @ l)) n in
      {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name))}

    let get_schema name = (get name).schema

    let get_name_from_schema s =
      let f a b = if (b.schema = s) then Some(b.name) else a in
      let n = DynArray.fold_left f None (Hashtbl.find store (!Modules.current)) in match n with
      | Some(n) -> n
      | _ -> raise Not_found

    let clear () =
      DynArray.clear (Hashtbl.find store (!Modules.current));
      Hashtbl.clear (Hashtbl.find directory (!Modules.current))

  end

  module CompTyp = struct
    type entry = {
      name                : Id.name;
      implicit_arguments  : int; (* bp : this is misgleding with the current design where explicitly declared context variables
                                    are factored into implicit arguments *)
      kind                : Int.Comp.kind;
      mutable frozen       : bool;
      mutable constructors: Id.cid_comp_const list
    }

    let mk_entry name kind implicit_arguments  =  {
      name               = name;
      implicit_arguments = implicit_arguments;
      kind               = kind;
      frozen             = false;
      constructors       = []
    }

    (*  store : entry DynArray.t *)
    let store : (string list, entry DynArray.t) Hashtbl.t = Hashtbl.create 0


    (*  directory : (Id.name, Id.cid_comp_typ) Hashtbl.t *)
    let directory : (string list, (Id.name, Id.cid_comp_typ) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

    let index_of_name : Id.name -> Id.cid_typ = function
    | n when n.Id.modules = [] -> 
      Modules.find directory (fun x -> Hashtbl.find x n)
    | n -> 
      if Modules.is_signature n.Id.modules then raise Not_found else
      let m = n.Id.modules in
      let n' = Id.mk_name (Id.SomeString n.Id.string_of_name) in
      let (_,l,i) = 
        try Hashtbl.find (Hashtbl.find directory n.Id.modules) n'
        with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ n.Id.modules)) n' in
      (m,l,i)

    let add entry = match entry.name.Id.modules with
    | [] -> begin
      let cid_comp_typ = 
        let store = 
          try Hashtbl.find store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x
          end in
          DynArray.add store entry;
          ([], !Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try Hashtbl.find directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            Hashtbl.add directory (!Modules.current) x;
            x
          end in
        Hashtbl.replace directory entry.name cid_comp_typ;
        cid_comp_typ end
    | l ->
      let n' = Id.mk_name (Id.SomeString entry.name.Id.string_of_name) in
      try Hashtbl.find (Hashtbl.find directory l) n'
      with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ l)) n'

    let get = function
    | (m, [], n) -> 
        let e = Modules.find store (fun x -> DynArray.get x n) in
        {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); kind = Modules.forceCompKind m e.kind}
    | (m, l, n) -> 
      let e = try DynArray.get (Hashtbl.find store l) n
      with Not_found -> DynArray.get (Hashtbl.find store (!Modules.current @ l)) n in
      {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); kind = Modules.forceCompKind m e.kind}

    let freeze a =
          (get a).frozen <- true

    let addConstructor c typ =
      let entry = get typ in
        entry.constructors <- c :: entry.constructors

    let clear () =
      DynArray.clear (Hashtbl.find store (!Modules.current));
      Hashtbl.clear (Hashtbl.find directory (!Modules.current))
  end

 module CompCotyp = struct
    type entry = {
      name                : Id.name;
      implicit_arguments  : int; (* bp : this is misgleding with the current design where explicitly declared context variables
                                    are factored into implicit arguments *)
      kind                : Int.Comp.kind;
      mutable frozen       : bool;
      mutable destructors: Id.cid_comp_dest list
    }

    let mk_entry name kind implicit_arguments  =  {
      name               = name;
      implicit_arguments = implicit_arguments;
      kind               = kind;
      frozen             = false;
      destructors        = []
    }


    let store : (string list, entry DynArray.t) Hashtbl.t = Hashtbl.create 0


    let directory : (string list, (Id.name, Id.cid_comp_const) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

    let index_of_name : Id.name -> Id.cid_typ = function
    | n when n.Id.modules = [] -> Modules.find directory (fun x -> Hashtbl.find x n)
    | n -> 
      if Modules.is_signature n.Id.modules then raise Not_found else
      let m = n.Id.modules in
      let n' = Id.mk_name (Id.SomeString n.Id.string_of_name) in
      let (_,l,i) = 
        try Hashtbl.find (Hashtbl.find directory n.Id.modules) n'
        with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ n.Id.modules)) n' in
      (m,l,i)

    let add entry = match entry.name.Id.modules with
    | [] -> begin
      let cid_comp_const = 
        let store = 
          try Hashtbl.find store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x
          end in
          DynArray.add store entry;
          ([], !Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try Hashtbl.find directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            Hashtbl.add directory (!Modules.current) x;
            x
          end in
        Hashtbl.replace directory entry.name cid_comp_const;
        cid_comp_const end
    | l ->
      let n' = Id.mk_name (Id.SomeString entry.name.Id.string_of_name) in
      try Hashtbl.find (Hashtbl.find directory l) n'
      with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ l)) n'

    let get = function
    | (m, [], n) -> 
        let e = Modules.find store (fun x -> DynArray.get x n) in
        {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); kind = Modules.forceCompKind m e.kind}
    | (m, l, n) -> 
      let e = try DynArray.get (Hashtbl.find store l) n
      with Not_found -> DynArray.get (Hashtbl.find store (!Modules.current @ l)) n in
      {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); kind = Modules.forceCompKind m e.kind}

    let freeze a =
          (get a).frozen <- true

    let addDestructor c typ =
      let entry = get typ in
        entry.destructors <- c :: entry.destructors

    let clear () =
      DynArray.clear (Hashtbl.find store (!Modules.current));
      Hashtbl.clear (Hashtbl.find directory (!Modules.current))
  end



  module CompConst = struct
    type entry = {
      name                : Id.name;
      implicit_arguments  : int;
      typ                : Int.Comp.typ
    }

    let mk_entry name tau implicit_arguments  =  {
      name               = name;
      implicit_arguments = implicit_arguments;
      typ               = Modules.forceCompTyp name.Id.modules tau
    }

    (*  store : entry DynArray.t *)
    let store : (string list, entry DynArray.t) Hashtbl.t = Hashtbl.create 0


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory : (string list, (Id.name, Id.cid_comp_const) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

    let index_of_name : Id.name -> Id.cid_typ = function
    | n when n.Id.modules = [] -> Modules.find directory (fun x -> Hashtbl.find x n)
    | n -> 
      if Modules.is_signature n.Id.modules then raise Not_found else
      let m = n.Id.modules in
      let n' = Id.mk_name (Id.SomeString n.Id.string_of_name) in
      let (_,l,i) = 
        try Hashtbl.find (Hashtbl.find directory n.Id.modules) n'
        with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ n.Id.modules)) n' in
      (m,l,i)

    let add cid_ctyp entry = match entry.name.Id.modules with
    | [] -> begin
      let cid_comp_const = 
        let store = 
          try Hashtbl.find store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x
          end in
          DynArray.add store entry;
          ([], !Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try Hashtbl.find directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            Hashtbl.add directory (!Modules.current) x;
            x
          end in
        Hashtbl.replace directory entry.name cid_comp_const;
        CompTyp.addConstructor cid_comp_const cid_ctyp;
        cid_comp_const end
    | l ->
      let n' = Id.mk_name (Id.SomeString entry.name.Id.string_of_name) in
      try Hashtbl.find (Hashtbl.find directory l) n'
      with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ l)) n'

    let get = function
    | (m, [], n) -> 
        let e = Modules.find store (fun x -> DynArray.get x n) in
        {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceCompTyp m e.typ }
    | (m, l, n) -> 
      let e = try DynArray.get (Hashtbl.find store l) n
      with Not_found -> DynArray.get (Hashtbl.find store (!Modules.current @ l)) n in
      {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceCompTyp m e.typ }

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear (Hashtbl.find store !(Modules.current));
      Hashtbl.clear (Hashtbl.find directory !(Modules.current))
  end

  module CompDest = struct
    type entry = {
      name                : Id.name;
      implicit_arguments  : int;
      typ                : Int.Comp.typ
    }


    let mk_entry name tau implicit_arguments  =  {
      name               = name;
      implicit_arguments = implicit_arguments;
      typ               = Modules.forceCompTyp name.Id.modules tau
    }
   (*  store : entry DynArray.t *)
    let store : (string list, entry DynArray.t) Hashtbl.t = Hashtbl.create 0


    (*  directory : (Id.name, Id.cid_comp_dest) Hashtbl.t *)
    let directory : (string list, (Id.name, Id.cid_comp_dest) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

    let index_of_name : Id.name -> Id.cid_typ = function
    | n when n.Id.modules = [] -> Modules.find directory (fun x -> Hashtbl.find x n)
    | n -> 
      if Modules.is_signature n.Id.modules then raise Not_found else
      let m = n.Id.modules in
      let n' = Id.mk_name (Id.SomeString n.Id.string_of_name) in
      let (_,l,i) = 
        try Hashtbl.find (Hashtbl.find directory n.Id.modules) n'
        with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ n.Id.modules)) n' in
      (m,l,i)

    let add cid_ctyp entry = match entry.name.Id.modules with
    | [] -> begin
      let cid_comp_dest = 
        let store = 
          try Hashtbl.find store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x
          end in
          DynArray.add store entry;
          ([], !Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try Hashtbl.find directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            Hashtbl.add directory (!Modules.current) x;
            x
          end in
        Hashtbl.replace directory entry.name cid_comp_dest;
        CompCotyp.addDestructor cid_comp_dest cid_ctyp;
        cid_comp_dest end
    | l ->
      let n' = Id.mk_name (Id.SomeString entry.name.Id.string_of_name) in
      try Hashtbl.find (Hashtbl.find directory l) n'
      with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ l)) n'

    let get = function
    | (m, [], n) -> 
        let e = Modules.find store (fun x -> DynArray.get x n) in
        {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceCompTyp m e.typ}
    | (m, l, n) -> 
      let e = try DynArray.get (Hashtbl.find store l) n
      with Not_found -> DynArray.get (Hashtbl.find store (!Modules.current @ l)) n in
      {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceCompTyp m e.typ}

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear (Hashtbl.find store !(Modules.current));
      Hashtbl.clear (Hashtbl.find directory !(Modules.current))
  end



  module CompTypDef = struct

    type entry = {
      name               : Id.name;
      implicit_arguments : int;
      kind               : Int.Comp.kind;
      mctx               : Int.LF.mctx;
      typ                : Int.Comp.typ
    }

    let mk_entry n i (cD,t) k = {
      name               = n;
      implicit_arguments = i;
      kind               = k;
      mctx               = cD;
      typ                = Modules.forceCompTyp n.Id.modules t
    }

    (*  store : entry DynArray.t *)
    let store : (string list, entry DynArray.t) Hashtbl.t = Hashtbl.create 0


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory : (string list, (Id.name, Id.cid_comp_typ) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

    let index_of_name : Id.name -> Id.cid_typ = function
    | n when n.Id.modules = [] -> Modules.find directory (fun x -> Hashtbl.find x n)
    | n -> 
      if Modules.is_signature n.Id.modules then raise Not_found else
      let m = n.Id.modules in
      let n' = Id.mk_name (Id.SomeString n.Id.string_of_name) in
      let (_,l,i) = 
        try Hashtbl.find (Hashtbl.find directory n.Id.modules) n'
        with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ n.Id.modules)) n' in
      (m,l,i)

    let add entry = match entry.name.Id.modules with
    | [] -> begin
      let cid_typdef = 
        let store = 
          try Hashtbl.find store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x
          end in
          DynArray.add store entry;
          ([], !Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try Hashtbl.find directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            Hashtbl.add directory (!Modules.current) x;
            x
          end in
        Hashtbl.replace directory entry.name cid_typdef;
        cid_typdef end
    | l ->
      let n' = Id.mk_name (Id.SomeString entry.name.Id.string_of_name) in
      try Hashtbl.find (Hashtbl.find directory l) n'
      with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ l)) n'

    let get = function
    | (m, [], n) -> 
        let e = Modules.find store (fun x -> DynArray.get x n) in
        {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceCompTyp m e.typ; kind = Modules.forceCompKind m e.kind}
    | (m, l, n) -> 
      let e = try DynArray.get (Hashtbl.find store l) n
      with Not_found -> DynArray.get (Hashtbl.find store (!Modules.current @ l)) n in
      {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceCompTyp m e.typ; kind = Modules.forceCompKind m e.kind}

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear (Hashtbl.find store !(Modules.current));
      Hashtbl.clear (Hashtbl.find directory !(Modules.current))

  end


  module Comp = struct

    type entry = {
      name               : Id.name;
      implicit_arguments : int;
      typ                : Int.Comp.typ;
      prog               : Int.Comp.value;
      mut_rec            : Id.name list
    }

    let mk_entry name typ implicit_arguments v name_list = {
      name               = name;
      implicit_arguments = implicit_arguments;
      typ                = Modules.forceCompTyp name.Id.modules typ;
      prog               = v;
      mut_rec            = name_list  (* names of functions with which n is mutually recursive *)
    }

    (*  store : entry DynArray.t *)
    let store : (string list, entry DynArray.t) Hashtbl.t = Hashtbl.create 0

    (*  directory : (Id.name, Id.cid_prog) Hashtbl.t *)
    let directory : (string list, (Id.name, Id.cid_prog) Hashtbl.t) Hashtbl.t = Hashtbl.create 0

    let index_of_name : Id.name -> Id.cid_typ = function
    | n when n.Id.modules = [] -> Modules.find directory (fun x -> Hashtbl.find x n)
    | n -> 
      if Modules.is_signature n.Id.modules then raise Not_found else
      let m = n.Id.modules in
      let n' = Id.mk_name (Id.SomeString n.Id.string_of_name) in
      let (_,l,i) = 
        try Hashtbl.find (Hashtbl.find directory n.Id.modules) n'
        with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ n.Id.modules)) n' in
      (m,l,i)

    let add f =
    let name = (f ([], [], 0)).name in
    match name.Id.modules with
    | [] -> begin
      let (cid_prog, e) = 
        let store = 
          try Hashtbl.find store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            Hashtbl.add store (!Modules.current) x;
            x
          end in
          let l = DynArray.length store in
          let e = f ([], [], l) in
          DynArray.add store e;
          (([], !Modules.current, l), e) in
      
        let directory = 
          try Hashtbl.find directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            Hashtbl.add directory (!Modules.current) x;
            x
          end in
        Hashtbl.replace directory e.name cid_prog;
        cid_prog end
    | l ->
      let n' = Id.mk_name (Id.SomeString name.Id.string_of_name) in
      try Hashtbl.find (Hashtbl.find directory l) n'
      with Not_found -> Hashtbl.find (Hashtbl.find directory (!Modules.current @ l)) n'

    let get = function
    | (m, [], n) -> 
        let e = Modules.find store (fun x -> DynArray.get x n) in
        {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceCompTyp m e.typ}
    | (m, l, n) -> 
      let e = try DynArray.get (Hashtbl.find store l) n
      with Not_found -> DynArray.get (Hashtbl.find store (!Modules.current @ l)) n in
      {e with name = (Id.mk_name ~modules:m (Id.SomeString e.name.Id.string_of_name)); typ = Modules.forceCompTyp m e.typ}

    let clear () =
      DynArray.clear (Hashtbl.find store !(Modules.current));
      Hashtbl.clear (Hashtbl.find directory !(Modules.current))

  end


  module NamedHoles = struct

    let printingHoles = ref false

    let usingRealNames = ref false

    let newNames = ref []

    let conventions = ref []

    let explicitNames = ref []

    let addExplicitName s = explicitNames := (s :: !explicitNames) 

    let addNameConvention cid mvar var =
      let vgen = match var with None -> None | Some x -> Some(Gensym.create_symbols [|x|]) in
      conventions := (cid, (mvar, Gensym.create_symbols [|mvar|], var, vgen))::!conventions

    let rec first_unique gen = 
      let s = Stream.next gen in
      if List.exists (fun (_, new_name) -> new_name = s) !newNames then first_unique gen else s

    let haveNameFor n = try
      Some(List.assoc n.Id.string_of_name !newNames)
    with
    | _ -> None

    let getName ?(tA=None) n = 
      let is_uppercase (n : Id.name) : bool = 
        let c = n.Id.string_of_name.[0] in
        0 = (Char.compare c (Char.uppercase c)) in

      if n.Id.was_generated && (not !usingRealNames) then
        let s = n.Id.string_of_name in
        try
          List.assoc s !newNames
        with
        | Not_found -> 
          let newName = match tA with
          | None -> 
            if (is_uppercase n) then 
              Gensym.MVarData.gensym () 
            else Gensym.VarData.gensym ()
          | Some(tA) -> 
            let cid = Typ.cid_of_typ tA in 
            try 
              let (_, mvar_gen, _, var_gen) = List.assoc cid !conventions in
              if is_uppercase n then
                first_unique mvar_gen 
              else match var_gen with
              | None -> Gensym.VarData.gensym ()
              | Some x -> first_unique x
            with _ -> 
              if (is_uppercase n) then 
                Gensym.MVarData.gensym () 
              else Gensym.VarData.gensym ()
          in
            (newNames := (s,newName) :: (!newNames)) ; newName        
      else 
        let s = n.Id.string_of_name in (newNames := (s,s) :: (!newNames)); s
        
      let reset () = 
        Gensym.MVarData.reset () ; 
        Gensym.VarData.reset (); 
        newNames := []; 
        conventions := List.map (fun (cid, (mvar, _, var, _)) -> 
                        let vargen = match var with None -> None | Some x -> Some(Gensym.create_symbols [|x|]) in
                        (cid, (mvar, Gensym.create_symbols [|mvar|], var, vargen)))
                       !conventions
  end


  module type RENDERER = sig

    open Id
    open Syntax.Int

    val render_name         : name         -> string
    val render_cid_comp_typ : cid_comp_typ -> string
    val render_cid_comp_cotyp : cid_comp_cotyp  -> string
    val render_cid_comp_const : cid_comp_const -> string
    val render_cid_comp_dest : cid_comp_dest -> string
    val render_cid_typ      : cid_typ      -> string
    val render_cid_term     : cid_term     -> string
    val render_cid_schema   : cid_schema   -> string
    val render_cid_prog     : cid_prog     -> string
    val render_offset       : offset       -> string

    val render_ctx_var      : LF.mctx    -> offset   -> string
    val render_cvar         : LF.mctx    -> offset   -> string
    val render_bvar         : LF.dctx    -> offset   -> string
    val render_var          : Comp.gctx  -> var      -> string

  end

  (* Default RENDERER for Internal Syntax using de Bruijn indices *)
  module DefaultRenderer : RENDERER = struct

    open Id

    let render_name n = 
      let name = if !NamedHoles.printingHoles then 
        match NamedHoles.haveNameFor n with Some x -> (Id.mk_name (Id.SomeString x)) | _ ->  n
      else n in
      match name.modules with
      | [] -> n.string_of_name
      | l -> (String.concat "." l) ^ "." ^ (n.string_of_name)

    let render_cid_comp_typ c  = render_name (CompTyp.get c).CompTyp.name
    let render_cid_comp_cotyp c = render_name (CompCotyp.get c).CompCotyp.name
    let render_cid_comp_const c = render_name (CompConst.get c).CompConst.name
    let render_cid_comp_dest c = render_name (CompDest.get c).CompDest.name
    let render_cid_typ    a    = render_name (Typ.get a).Typ.name
    let render_cid_term   c    = render_name (Term.get c).Term.name
    let render_cid_schema w    = render_name (Schema.get w).Schema.name
    let render_cid_prog   f    = render_name (Comp.get f).Comp.name
    let render_ctx_var _cO g   =  string_of_int g
    let render_cvar    _cD u   = "mvar " ^ string_of_int u
    let render_bvar  _cPsi i   = string_of_int i
    let render_offset      i   = string_of_int i
    let render_var   _cG   x   = string_of_int x

  end (* Int.DefaultRenderer *)


  (* RENDERER for Internal Syntax using names *)  (****)
  module NamedRenderer : RENDERER = struct

    open Id

    let render_name n = 
      let name = if !NamedHoles.printingHoles then 
        match NamedHoles.haveNameFor n with Some x -> (Id.mk_name (Id.SomeString x)) | _ ->  n
      else n in
      match name.modules with
      | [] -> n.string_of_name
      | l -> (String.concat "." l) ^ "." ^ (n.string_of_name)

    let render_cid_comp_typ c  = render_name (CompTyp.get c).CompTyp.name
    let render_cid_comp_cotyp c = render_name (CompCotyp.get c).CompCotyp.name
    let render_cid_comp_const c = render_name (CompConst.get c).CompConst.name
    let render_cid_comp_dest c = render_name (CompDest.get c).CompDest.name
    let render_cid_typ     a   = render_name (Typ.get a).Typ.name
    let render_cid_term    c   = render_name (Term.get c).Term.name
    let render_cid_schema  w   = render_name (Schema.get w).Schema.name
    let render_cid_prog    f   = render_name (Comp.get f).Comp.name
    let render_ctx_var cO g    =
      begin try
        render_name (Context.getNameMCtx cO g)
      with
          _ -> "FREE CtxVar " ^ string_of_int g
      end

    let render_cvar    cD u    =
      begin try
        render_name (Context.getNameMCtx cD u)
      with
          _ -> "FREE MVar " ^ (string_of_int u)
      end
    let render_bvar  cPsi i    =
      begin try
        render_name (Context.getNameDCtx cPsi i)
      with
          _ -> "FREE BVar " ^ (string_of_int i)
      end

    let render_offset     i   = string_of_int i

    let render_var   cG   x   =
      begin try
        render_name (Context.getNameCtx cG x)
      with
          _ -> "FREE Var " ^ (string_of_int x)
      end

  end (* Int.NamedRenderer *)

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


module FPatVar = struct

  let store    = ref Syntax.Int.LF.Empty

  let add x tau =
      store := Syntax.Int.LF.Dec (!store, Syntax.Int.Comp.CTypDecl (x,tau))

  let get x    =
    let rec lookup str = match str with
      | Syntax.Int.LF.Dec (str', Syntax.Int.Comp.CTypDecl ((y, tau))) ->
          if x = y then tau else lookup str'
      | _ -> raise Not_found
    in
      lookup (!store)


  let clear () = (store := Syntax.Int.LF.Empty)

  let fvar_ctx () = !store

end


(*
(* Free meta-variables *)
module FMVar = struct

  let store    = Hashtbl.create 0
  let add      = Hashtbl.add store
  let get      = Hashtbl.find store
  let clear () = Hashtbl.clear store

end
*)

(* Free contextual variables *)
module FCVar = struct

  let store    = Hashtbl.create 0
  let add      = Hashtbl.add store
  let get      = Hashtbl.find store
  let clear () = Hashtbl.clear store

end

(*
(* Free parameter variables *)
module FPVar = struct

  let store    = Hashtbl.create 0
  let add      = Hashtbl.add store
  let get      = Hashtbl.find store
  let clear () = Hashtbl.clear store

end
*)
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
  let append vars vars' = vars @ vars'
  let get          = List.nth
  let size  = List.length

end



(* Contextual variables *)
module CVar = struct

  type cvar = MV of Id.name | PV of Id.name | CV of Id.name | SV of Id.name

  type entry = { name : cvar }

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


  let nearest_cvar store =
    let rec ncvar store k = match store with
      | [] -> raise Not_found
      | e::store' ->
          match e.name with CV _  ->  k
            | _ -> ncvar store' (k+1)
    in
      ncvar store 1


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
  Cid.CompTyp.clear ();
  Cid.CompCotyp.clear();
  Cid.CompConst.clear ();
  Cid.CompDest.clear ();
  Cid.CompTypDef.clear ();
  Cid.Comp.clear ()

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | FrozenType n ->
            Format.fprintf ppf
              "Type %s is frozen. A new constructor cannot be defined."
              (Cid.DefaultRenderer.render_cid_typ n)))
