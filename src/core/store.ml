open Syntax

type error =
  | FrozenType of Id.cid_typ

exception Error of Syntax.Loc.t * error

(* Register error printer at the end of this module. *)
module OpPragmas = struct
  type fixPragma = {
    name : Id.name;
    fix : Ext.Sgn.fix;
    precedence : int;
    assoc : Ext.Sgn.assoc option;
  }

  let default = ref Syntax.Ext.Sgn.None
  
  let pragmaCount = ref 0

  let pragmas = ref []
  
  let clear () = pragmas := []
  
  let default_precedence = -1

  let addPragma n f p_option a = 
  let p = match p_option with Some x -> x | None -> default_precedence in
    if (List.exists (fun x -> x.name = n) !pragmas) then
      pragmas := List.map
        (fun x -> if x.name = n then {name = n; fix = f; precedence = p; assoc = a} else x)
        !pragmas
    else
      let new_entry = {name = n; fix = f; precedence = p; assoc = a} in
      pragmas := new_entry :: !pragmas ; incr pragmaCount

  let getPragma name = 
    begin
      try
        Some(List.find ((fun p -> name = p.name)) (!pragmas))
      with
      | _ -> None
    end

  let pragmaExists name = List.exists (fun x -> x.name = name) !pragmas

end

module Modules = struct
  type state = Id.module_id * string list * Id.module_id list

  let current : Id.module_id ref = ref 0

  let currentName : string list ref = ref []

  let opened : Id.module_id list ref = ref []

  let getState () = (!current, !currentName, !opened)

  let setState (a, b, c) = current := a; currentName := b; opened := c

  let directory : (string list, Id.module_id) Hashtbl.t = 
    let x = Hashtbl.create 1 in Hashtbl.add x [] 0; x

  let rev_directory : (string list) DynArray.t =
    let x = DynArray.create () in DynArray.add x []; x

  let modules : (Int.Sgn.decl list ref) DynArray.t = 
    let x = DynArray.create () in DynArray.add x (ref []); x

  let id_of_name (n : string list) : Id.module_id = Hashtbl.find directory n

  let name_of_id (id : Id.module_id) : string list = DynArray.get rev_directory id

  let open_module (m : string list) : Id.module_id =
    let x = try Hashtbl.find directory m 
    with _ -> Hashtbl.find directory (!currentName @ m) in 
    let l = x::
      (List.map (fun (Int.Sgn.Pragma(Int.LF.OpenPrag x)) -> x) 
        (List.filter (function (Int.Sgn.Pragma(Int.LF.OpenPrag _)) -> true | _ -> false) !(DynArray.get modules x))) in
    opened := l@ !opened; x

  (* Precondition: the name check in f is using a name with Id.modules = [] *)
  let find (n : Id.name) (x : 'a DynArray.t) (f : 'a -> 'b) : 'b =
    let m = n.Id.modules in
    let rec iter_find : Id.module_id list -> 'b = function
      | [] -> raise Not_found
      | h::t -> try f (DynArray.get x h) with _ -> iter_find t in
    begin match m with
    | [] -> begin try
              f (DynArray.get x !current)
            with | _ -> iter_find !opened end
    | l -> begin try
              f (DynArray.get x (id_of_name l))
            with | _ -> try f (DynArray.get x (id_of_name (!currentName @ l)))
            with | _ -> iter_find (List.map (fun h -> (id_of_name ((name_of_id h)@m))) !opened) end end

  let addSgnToCurrent (decl : Int.Sgn.decl) : unit = 
    let l = (DynArray.get modules !current) in l := decl :: !l 
  
  let instantiateModule (name : string) : Id.module_id =
    let l = !currentName@[name] in
    let module_id = DynArray.length modules in
    current := module_id; currentName := l; 
    DynArray.insert modules module_id (ref []); 
    Hashtbl.replace directory l module_id; 
    DynArray.insert rev_directory module_id l;
    module_id

  let reset () : unit = 
    current := 0;
    opened := [];
    currentName := []

  let correct (l : string list ) : string list = 
    let rec aux m l = match (m, l) with
      | _ when m = l -> m
      | ([], _) -> l
      | (h::t, h'::t') when h=h' -> aux t t'
      | _ -> m in
    aux (List.fold_left aux l (List.map name_of_id !opened)) !currentName
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

    let entry_list : (Id.cid_typ list ref) DynArray.t = DynArray.create ()


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
    let store : (entry DynArray.t) DynArray.t = DynArray.create ()


    (*  directory keeps track of which cid a name is associated with
        and provides a way to quickly look up this information. *)
    let directory : ((Id.name, Id.cid_typ) Hashtbl.t) DynArray.t = DynArray.create ()

    let index_of_name : Id.name -> Id.cid_typ = fun (n : Id.name) ->
      let n' = match n.Id.modules with 
        | [] -> n 
        | _ -> Id.mk_name (Id.SomeString n.Id.string_of_name) in 
      let cid = Modules.find n directory (fun x -> Hashtbl.find x n') in
       cid


    let rec args = function
    | Int.LF.Typ -> 0
    | Int.LF.PiKind(_, k) -> 1 + (args k)

    let get ?(fixName=false) (l, n) =
      let l' = Modules.name_of_id l in
      let m' =  if fixName && (l <> !Modules.current) &&
                   not (List.exists (fun x -> x = l) !Modules.opened)
                then Modules.correct l' else [] in
      let e = DynArray.get (DynArray.get store l) n in
      {e with name = (Id.mk_name ~modules:m' (Id.SomeString e.name.Id.string_of_name))}

    let args_of_name n = 
      let entry = get (index_of_name n) in
      (args (entry.kind)) - entry.implicit_arguments

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
          try DynArray.get store (!Modules.current)
          with _ -> begin 
            let x = DynArray.create () in
            DynArray.add store x;
            x 
          end in
        let (_, n) = cid_tp in
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
      let (a_l, a_n) = a in
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
           subord_iter (fun aa -> addSubord (a_l, aa) b) a_e.subordinates;
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

    let add entry = begin
      OpPragmas.addPragma entry.name Ext.Sgn.Prefix None (Some Ext.Sgn.Left) ;
      let cid_tp = 
        let store =   
          try DynArray.get store (!Modules.current)
          with _ -> begin 
            let x = DynArray.create () in
            while DynArray.length store < (!Modules.current ) do DynArray.add store (DynArray.create ()) done;
            DynArray.add store x;
            x
          end in
        DynArray.add store entry;
        (!Modules.current, (DynArray.length store) - 1) in

        let directory =   
          try DynArray.get directory (!Modules.current)
          with _ -> begin 
            let x = Hashtbl.create 0 in
            while DynArray.length directory < (!Modules.current ) do DynArray.add directory (Hashtbl.create 0) done;
            DynArray.add directory x; 
            x
          end in
        Hashtbl.replace directory entry.name cid_tp;

        let entry_list =   
          try DynArray.get entry_list (!Modules.current)
          with _ -> begin 
            let x = ref [] in
            while DynArray.length entry_list < (!Modules.current ) do DynArray.add entry_list (ref []) done;
            DynArray.add entry_list x;
            x
          end in
        entry_list := cid_tp :: !entry_list;

        inspectKind cid_tp [] entry.kind;
        cid_tp end

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
      (DynArray.get entry_list (!Modules.current)) := [];
      DynArray.clear (DynArray.get store (!Modules.current));
      Hashtbl.clear (DynArray.get directory (!Modules.current))

    let is_subordinate_to (a : Id.cid_typ) (b : Id.cid_typ) : bool =
      let a_e = get a in
      let (_, b_n) = b in
        (*subord_read*)BitSet.is_set a_e.subordinates b_n

    let is_typesubordinate_to (a : Id.cid_typ) (b : Id.cid_typ) : bool =
      let b_e = get b in
      let (_, a_n) = a in
        (*subord_read*)BitSet.is_set b_e.typesubordinated a_n
  end

  module Term = struct

    type entry = {
      name               : Id.name;
      implicit_arguments : int;
      typ                : Int.LF.typ
    }

    let mk_entry n t i = 
      {
      name               = n;
      implicit_arguments = i;
      typ                = t
    }

    let store : (entry DynArray.t) DynArray.t = DynArray.create ()

    let directory : ((Id.name, Id.cid_term) Hashtbl.t) DynArray.t = DynArray.create ()

    let index_of_name : Id.name -> Id.cid_typ = fun (n : Id.name) ->
      let n' = match n.Id.modules with 
        | [] -> n 
        | _ -> Id.mk_name (Id.SomeString n.Id.string_of_name) in 
      let cid = Modules.find n directory (fun x -> Hashtbl.find x n') in
       cid

    let rec args = function
    | Int.LF.PiTyp(_, tA) -> 1 + args tA
    | _ -> 0

    let add loc e_typ entry = begin 
      OpPragmas.addPragma entry.name Ext.Sgn.Prefix None (Some Ext.Sgn.Left) ;
      let cid_tm = 
        let store = 
          try DynArray.get store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            while DynArray.length store < (!Modules.current ) do DynArray.add store (DynArray.create ()) done;
            DynArray.add store x;
            x
          end in
          DynArray.add store entry;
          (!Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try DynArray.get directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            while DynArray.length directory < (!Modules.current ) do DynArray.add directory (Hashtbl.create 0) done;
            DynArray.add directory x;
            x
          end in
        Hashtbl.replace directory entry.name cid_tm;
        Typ.addConstructor loc e_typ cid_tm entry.typ;
        cid_tm end

    let get ?(fixName=false) (l, n) =
      let l' = Modules.name_of_id l in
      let m' =  if fixName && (l <> !Modules.current) &&
                   not (List.exists (fun x -> x = l) !Modules.opened)
                then Modules.correct l' else [] in
      let e = DynArray.get (DynArray.get store l) n in
      {e with name = (Id.mk_name ~modules:m' (Id.SomeString e.name.Id.string_of_name))}

    let args_of_name n = 
      let e = (get (index_of_name n)) in
      (args e.typ) - e.implicit_arguments

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear (DynArray.get store (!Modules.current));
      Hashtbl.clear (DynArray.get directory  (!Modules.current))

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
    let store : (entry DynArray.t) DynArray.t = DynArray.create ()


    (*  directory : (Id.name, Id.cid_term) Hashtbl.t *)
    let directory : ((Id.name, Id.cid_schema) Hashtbl.t) DynArray.t = DynArray.create ()

    let index_of_name : Id.name -> Id.cid_typ = fun (n : Id.name) ->
      let n' = match n.Id.modules with 
        | [] -> n 
        | _ -> Id.mk_name (Id.SomeString n.Id.string_of_name) in 
      let cid = Modules.find n directory (fun x -> Hashtbl.find x n') in
       cid

    let add entry = begin
      let cid_schema = 
        let store = 
          try DynArray.get store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            while DynArray.length store < (!Modules.current ) do DynArray.add store (DynArray.create ()) done;
            DynArray.add store x;
            x
          end in
          DynArray.add store entry;
          (!Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try DynArray.get directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            while DynArray.length directory < (!Modules.current ) do DynArray.add directory (Hashtbl.create 0) done;
            DynArray.add directory x;
            x
          end in
        Hashtbl.replace directory entry.name cid_schema;
        cid_schema end

    let get ?(fixName=false) (l, n) =
      let l' = Modules.name_of_id l in
      let m' =  if fixName && (l <> !Modules.current) &&
                   not (List.exists (fun x -> x = l) !Modules.opened)
                then Modules.correct l' else [] in
      let e = DynArray.get (DynArray.get store l) n in
      {e with name = (Id.mk_name ~modules:m' (Id.SomeString e.name.Id.string_of_name))}

    let get_schema name = (get name).schema

    let get_name_from_schema s =
      let f a b = if (b.schema = s) then Some(b.name) else a in
      let n = DynArray.fold_left f None (DynArray.get store (!Modules.current)) in match n with
      | Some(n) -> n
      | _ -> raise Not_found

    let clear () =
      DynArray.clear (DynArray.get store (!Modules.current));
      Hashtbl.clear (DynArray.get directory (!Modules.current))

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
    let store : (entry DynArray.t) DynArray.t = DynArray.create ()


    (*  directory : (Id.name, Id.cid_comp_typ) Hashtbl.t *)
    let directory : ((Id.name, Id.cid_comp_typ) Hashtbl.t) DynArray.t = DynArray.create ()

    let index_of_name : Id.name -> Id.cid_comp_typ = fun (n : Id.name) ->
      let n' = match n.Id.modules with 
        | [] -> n 
        | _ -> Id.mk_name (Id.SomeString n.Id.string_of_name) in 
      let cid = Modules.find n directory (fun x -> Hashtbl.find x n') in
       cid

    let add entry = begin
      let cid_comp_typ = 
        let store = 
          try DynArray.get store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            while DynArray.length store < (!Modules.current ) do DynArray.add store (DynArray.create ()) done;
            DynArray.add store x;
            x
          end in
          DynArray.add store entry;
          (!Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try DynArray.get directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            while DynArray.length directory < (!Modules.current ) do DynArray.add directory (Hashtbl.create 0) done;
            DynArray.add directory x;
            x
          end in
        Hashtbl.replace directory entry.name cid_comp_typ;
        cid_comp_typ end

    let get ?(fixName=false) (l, n) =
      let l' = Modules.name_of_id l in
      let m' =  if fixName && (l <> !Modules.current) &&
                   not (List.exists (fun x -> x = l) !Modules.opened)
                then Modules.correct l' else [] in
      let e = DynArray.get (DynArray.get store l) n in
      {e with name = (Id.mk_name ~modules:m' (Id.SomeString e.name.Id.string_of_name))}

    let freeze a =
          (get a).frozen <- true

    let addConstructor c typ =
      let entry = get typ in
        entry.constructors <- c :: entry.constructors

    let clear () =
      DynArray.clear (DynArray.get store (!Modules.current));
      Hashtbl.clear (DynArray.get directory (!Modules.current))
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


    let store : (entry DynArray.t) DynArray.t = DynArray.create ()

    let directory : ((Id.name, Id.cid_comp_const) Hashtbl.t) DynArray.t = DynArray.create ()

    let index_of_name : Id.name -> Id.cid_typ = fun (n : Id.name) ->
      let n' = match n.Id.modules with 
        | [] -> n 
        | _ -> Id.mk_name (Id.SomeString n.Id.string_of_name) in 
      let cid = Modules.find n directory (fun x -> Hashtbl.find x n') in
       cid

    let add entry = begin
      let cid_comp_const = 
        let store = 
          try DynArray.get store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            while DynArray.length store < (!Modules.current ) do DynArray.add store (DynArray.create ()) done;
            DynArray.add store x;
            x
          end in
          DynArray.add store entry;
          (!Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try DynArray.get directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            while DynArray.length directory < (!Modules.current ) do DynArray.add directory (Hashtbl.create 0) done;
            DynArray.add directory x;
            x
          end in
        Hashtbl.replace directory entry.name cid_comp_const;
        cid_comp_const end

    let get ?(fixName=false) (l, n) =
      let l' = Modules.name_of_id l in
      let m' =  if fixName && (l <> !Modules.current) &&
                   not (List.exists (fun x -> x = l) !Modules.opened)
                then Modules.correct l' else [] in
      let e = DynArray.get (DynArray.get store l) n in
      {e with name = (Id.mk_name ~modules:m' (Id.SomeString e.name.Id.string_of_name))}

    let freeze a =
          (get a).frozen <- true

    let addDestructor c typ =
      let entry = get typ in
        entry.destructors <- c :: entry.destructors

    let clear () =
      DynArray.clear (DynArray.get store (!Modules.current));
      Hashtbl.clear (DynArray.get directory (!Modules.current))
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
      typ               = tau
    }

    (*  store : entry DynArray.t *)
    let store : (entry DynArray.t) DynArray.t = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory : ((Id.name, Id.cid_comp_const) Hashtbl.t) DynArray.t = DynArray.create ()

    let index_of_name : Id.name -> Id.cid_typ = fun (n : Id.name) ->
      let n' = match n.Id.modules with 
        | [] -> n 
        | _ -> Id.mk_name (Id.SomeString n.Id.string_of_name) in 
      let cid = Modules.find n directory (fun x -> Hashtbl.find x n') in
       cid

    let add cid_ctyp entry = begin
      let cid_comp_const = 
        let store = 
          try DynArray.get store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            while DynArray.length store < (!Modules.current ) do DynArray.add store (DynArray.create ()) done;
            DynArray.add store x;
            x
          end in
          DynArray.add store entry;
          (!Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try DynArray.get directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            while DynArray.length directory < (!Modules.current ) do DynArray.add directory (Hashtbl.create 0) done;
            DynArray.add directory x;
            x
          end in
        Hashtbl.replace directory entry.name cid_comp_const;
        CompTyp.addConstructor cid_comp_const cid_ctyp;
        cid_comp_const end

    let get ?(fixName=false) (l, n) =
      let l' = Modules.name_of_id l in
      let m' =  if fixName && (l <> !Modules.current) &&
                   not (List.exists (fun x -> x = l) !Modules.opened)
                then Modules.correct l' else [] in
      let e = DynArray.get (DynArray.get store l) n in
      {e with name = (Id.mk_name ~modules:m' (Id.SomeString e.name.Id.string_of_name))}

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear (DynArray.get store !(Modules.current));
      Hashtbl.clear (DynArray.get directory !(Modules.current))
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
      typ               = tau
    }
   (*  store : entry DynArray.t *)
    let store : (entry DynArray.t) DynArray.t = DynArray.create ()


    (*  directory : (Id.name, Id.cid_comp_dest) Hashtbl.t *)
    let directory : ((Id.name, Id.cid_comp_dest) Hashtbl.t) DynArray.t = DynArray.create ()

    let index_of_name : Id.name -> Id.cid_typ = fun (n : Id.name) ->
      let n' = match n.Id.modules with 
        | [] -> n 
        | _ -> Id.mk_name (Id.SomeString n.Id.string_of_name) in 
      let cid = Modules.find n directory (fun x -> Hashtbl.find x n') in
       cid

    let add cid_ctyp entry = begin
      let cid_comp_dest = 
        let store = 
          try DynArray.get store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            while DynArray.length store < (!Modules.current ) do DynArray.add store (DynArray.create ()) done;
            DynArray.add store x;
            x
          end in
          DynArray.add store entry;
          (!Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try DynArray.get directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            while DynArray.length directory < (!Modules.current ) do DynArray.add directory (Hashtbl.create 0) done;
            DynArray.add directory x;
            x
          end in
        Hashtbl.replace directory entry.name cid_comp_dest;
        CompCotyp.addDestructor cid_comp_dest cid_ctyp;
        cid_comp_dest end

    let get ?(fixName=false) (l, n) =
      let l' = Modules.name_of_id l in
      let m' =  if fixName && (l <> !Modules.current) &&
                   not (List.exists (fun x -> x = l) !Modules.opened)
                then Modules.correct l' else [] in
      let e = DynArray.get (DynArray.get store l) n in
      {e with name = (Id.mk_name ~modules:m' (Id.SomeString e.name.Id.string_of_name))}

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear (DynArray.get store !(Modules.current));
      Hashtbl.clear (DynArray.get directory !(Modules.current))
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
      typ                = t
    }

    (*  store : entry DynArray.t *)
    let store : (entry DynArray.t) DynArray.t = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory : ((Id.name, Id.cid_comp_typ) Hashtbl.t) DynArray.t = DynArray.create ()

    let index_of_name : Id.name -> Id.cid_typ = fun (n : Id.name) ->
      let n' = match n.Id.modules with 
        | [] -> n 
        | _ -> Id.mk_name (Id.SomeString n.Id.string_of_name) in 
      let cid = Modules.find n directory (fun x -> Hashtbl.find x n') in
       cid

    let add entry = begin
      let cid_typdef = 
        let store = 
          try DynArray.get store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            while DynArray.length store < (!Modules.current ) do DynArray.add store (DynArray.create ()) done;
            DynArray.add store x;
            x
          end in
          DynArray.add store entry;
          (!Modules.current, (DynArray.length store) - 1) in
      
        let directory = 
          try DynArray.get directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            while DynArray.length directory < (!Modules.current ) do DynArray.add directory (Hashtbl.create 0) done;
            DynArray.add directory x;
            x
          end in
        Hashtbl.replace directory entry.name cid_typdef;
        cid_typdef end

    let get ?(fixName=false) (l, n) =
      let l' = Modules.name_of_id l in
      let m' =  if fixName && (l <> !Modules.current) &&
                   not (List.exists (fun x -> x = l) !Modules.opened)
                then Modules.correct l' else [] in
      let e = DynArray.get (DynArray.get store l) n in
      {e with name = (Id.mk_name ~modules:m' (Id.SomeString e.name.Id.string_of_name))}

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear (DynArray.get store !(Modules.current));
      Hashtbl.clear (DynArray.get directory !(Modules.current))

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
      typ                = typ;
      prog               = v;
      mut_rec            = name_list  (* names of functions with which n is mutually recursive *)
    }

    (*  store : entry DynArray.t *)
    let store : (entry DynArray.t) DynArray.t = DynArray.create ()

    (*  directory : (Id.name, Id.cid_prog) Hashtbl.t *)
    let directory : ((Id.name, Id.cid_prog) Hashtbl.t) DynArray.t = DynArray.create ()

    let index_of_name : Id.name -> Id.cid_prog = fun (n : Id.name) ->
      let n' = match n.Id.modules with 
        | [] -> n 
        | _ -> Id.mk_name (Id.SomeString n.Id.string_of_name) in 
      let cid = Modules.find n directory (fun x -> Hashtbl.find x n') in
       cid

    let add f = begin
      let (cid_prog, e) = 
        let store = 
          try DynArray.get store (!Modules.current)
          with _ -> begin
            let x = DynArray.create () in
            while DynArray.length store < (!Modules.current ) do DynArray.add store (DynArray.create ()) done;
            DynArray.add store x;
            x
          end in
          let l = DynArray.length store in
          let e = f (!Modules.current, l) in
          DynArray.add store e;
          ((!Modules.current, l), e) in
      
        let directory = 
          try DynArray.get directory (!Modules.current) 
          with _ -> begin
            let x = Hashtbl.create 0 in
            while DynArray.length directory < (!Modules.current) do DynArray.add directory (Hashtbl.create 0) done;
            DynArray.add directory x;
            x
          end in
        Hashtbl.replace directory e.name cid_prog;
        cid_prog end

    let get ?(fixName=false) (l, n) =
      let l' = Modules.name_of_id l in
      let m' =  if fixName && (l <> !Modules.current) &&
                   not (List.exists (fun x -> x = l) !Modules.opened)
                then Modules.correct l' else [] in
      let e = DynArray.get (DynArray.get store l) n in
      {e with name = (Id.mk_name ~modules:m' (Id.SomeString e.name.Id.string_of_name))}

    let clear () =
      DynArray.clear (DynArray.get store !(Modules.current));
      Hashtbl.clear (DynArray.get directory !(Modules.current))

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

    let render_cid_comp_typ c  = render_name (CompTyp.get ~fixName:true c).CompTyp.name
    let render_cid_comp_cotyp c = render_name (CompCotyp.get ~fixName:true c).CompCotyp.name
    let render_cid_comp_const c = render_name (CompConst.get ~fixName:true c).CompConst.name
    let render_cid_comp_dest c = render_name (CompDest.get ~fixName:true c).CompDest.name
    let render_cid_typ    a    = render_name (Typ.get ~fixName:true a).Typ.name
    let render_cid_term   c    = render_name (Term.get ~fixName:true c).Term.name
    let render_cid_schema w    = render_name (Schema.get ~fixName:true w).Schema.name
    let render_cid_prog   f    = render_name (Comp.get ~fixName:true f).Comp.name
    let render_ctx_var _cO g   =  string_of_int g
    let render_cvar    _cD u   = "mvar " ^ string_of_int u
    let render_bvar  _cPsi i   = string_of_int i
    let render_offset      i   = string_of_int i
    let render_var   _cG   x   = string_of_int x

  end (* Int.DefaultRenderer *)


  (* RENDERER for Internal Syntax using names *) 
  module NamedRenderer : RENDERER = struct

    open Id

    let render_name n = 
      let name = if !NamedHoles.printingHoles then 
        match NamedHoles.haveNameFor n with Some x -> (Id.mk_name (Id.SomeString x)) | _ ->  n
      else n in
      match name.modules with
      | [] -> n.string_of_name
      | l -> (String.concat "." l) ^ "." ^ (n.string_of_name)

    let render_cid_comp_typ c  = render_name (CompTyp.get ~fixName:true c).CompTyp.name
    let render_cid_comp_cotyp c = render_name (CompCotyp.get ~fixName:true c).CompCotyp.name
    let render_cid_comp_const c = render_name (CompConst.get ~fixName:true c).CompConst.name
    let render_cid_comp_dest c = render_name (CompDest.get ~fixName:true c).CompDest.name
    let render_cid_typ     a   = render_name (Typ.get ~fixName:true a).Typ.name
    let render_cid_term    c   = render_name (Term.get ~fixName:true c).Term.name
    let render_cid_schema  w   = render_name (Schema.get ~fixName:true w).Schema.name
    let render_cid_prog    f   = render_name (Comp.get ~fixName:true f).Comp.name
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
  Cid.Comp.clear ();
  OpPragmas.clear ()

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | FrozenType n ->
            Format.fprintf ppf
              "Type %s is frozen. A new constructor cannot be defined."
              (Cid.DefaultRenderer.render_cid_typ n)))
