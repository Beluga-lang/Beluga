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
    assoc : Ext.Sgn.assoc;
  }

  let pragmaCount = ref 0

  let pragmas = ref []
  
  let clear () = pragmas := []
  
  let addPragma n f p a = 
(*     let _ = print_string (n.Id.string_of_name ^ "; ")in *)
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

    let entry_list  = ref []

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

    (*  store : {!entry DynArray.t} *)
    (*  store is used for storing the information associated with a cid *)
    let store = DynArray.create ()

    (*  directory : {!(Id.name, Id.cid_type) Hashtbl.t} *)
    (*  directory keeps track of which cid a name is associated with
        and provides a way to quickly look up this information. *)
    let directory = Hashtbl.create 0

    let index_of_name n = Hashtbl.find directory n

    let rec args = function
    | Int.LF.Typ -> 0
    | Int.LF.PiKind(_, k) -> 1 + (args k)

    let args_of_name n = 
      let entry = DynArray.get store (index_of_name n) in
      (args (entry.kind)) - entry.implicit_arguments

    let get = DynArray.get store

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
        (DynArray.set store cid_tp new_entry;
         cid_tp)


    let var_gen cid_tp =  (get cid_tp).var_generator
    let mvar_gen cid_tp =  (get cid_tp).mvar_generator

    let rec gen_var_name tA = match tA with
      | Int.LF.Atom (_, a, _ ) -> var_gen a
      | Int.LF.PiTyp(_, tA) -> gen_var_name tA
      | Int.LF.Sigma typRec -> gen_var_name_typRec typRec
      | Int.LF.TClo (tA, s) -> gen_var_name tA

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
      let a_e = get a in
      let b_e = get b in
        if BitSet.is_set b_e.subordinates a then
          (* a is already in the subordinate relation for b, i.e. b depends on a *)
          ()
        else
          (* a is not yet in the subordinate relation for b, i.e. b depends on a *)
          (BitSet.set b_e.subordinates a;
           (* Take transitive closure:
              If b-terms can contain a-terms, then b-terms can contain everything a-terms can contain. *)
           (* Call below could be replaced by
              subord_iter (fun aa -> BitSet.set b_e subordinates aa) a_e.subordinates *)
           subord_iter (fun aa -> addSubord aa b) a_e.subordinates;
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

    let add entry =
(*       let a = args entry.kind in
      print_string ("Name: " ^ (entry.name.Id.string_of_name) ^ " Args: " ^ (string_of_int a) ^ " Implicit: " ^ (string_of_int entry.implicit_arguments) ^ "\n");
 *) 
      OpPragmas.addPragma entry.name Ext.Sgn.Prefix (-1) Ext.Sgn.Left ;
      let cid_tp = DynArray.length store in
        DynArray.add store entry;
        Hashtbl.replace directory entry.name cid_tp;
        entry_list := cid_tp :: !entry_list;
        inspectKind cid_tp [] entry.kind;
        cid_tp

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

    let mk_entry n t i = 
      {
      name               = n;
      implicit_arguments = i;
      typ                = t
    }

    (*  store : entry DynArray.t *)
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name name = Hashtbl.find directory name

    let rec args = function
    | Int.LF.PiTyp(_, tA) -> 1 + args tA
    | _ -> 0

    let args_of_name n = 
      let e = (DynArray.get store (index_of_name n)) in
      (args e.typ) - e.implicit_arguments


    let add loc e_typ entry =
      OpPragmas.addPragma entry.name Ext.Sgn.Prefix (-1) Ext.Sgn.Left ;
      let cid_tm = DynArray.length store in
        DynArray.add store entry;
        Hashtbl.replace directory entry.name cid_tm;
        Typ.addConstructor loc e_typ cid_tm entry.typ;
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
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name n = Hashtbl.find directory n

    let add e =
      let cid_comp_typ = DynArray.length store in
        DynArray.add store e;
        Hashtbl.replace directory e.name cid_comp_typ;
        cid_comp_typ

    let get = DynArray.get store

    let freeze a =
          (get a).frozen <- true

    let addConstructor c typ =
      let entry = get typ in
        entry.constructors <- c :: entry.constructors

    let clear () =
      DynArray.clear store;
      Hashtbl.clear directory
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

    (*  store : entry DynArray.t *)
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name n = Hashtbl.find directory n

    let add e =
      let cid_comp_typ = DynArray.length store in
        DynArray.add store e;
        Hashtbl.replace directory e.name cid_comp_typ;
        cid_comp_typ

    let get = DynArray.get store

    let freeze a =
          (get a).frozen <- true

    let addDestructor c typ =
      let entry = get typ in
        entry.destructors <- c :: entry.destructors

    let clear () =
      DynArray.clear store;
      Hashtbl.clear directory
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
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name n = Hashtbl.find directory n


    let add cid_ctyp entry =
      let cid_comp_const = DynArray.length store in
        DynArray.add store entry;
        Hashtbl.replace directory entry.name cid_comp_const;
        CompTyp.addConstructor cid_comp_const cid_ctyp;
        cid_comp_const

    let get = DynArray.get store

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear store;
      Hashtbl.clear directory
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
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name n = Hashtbl.find directory n

    let add cid_ctyp entry =
      let cid_comp_dest = DynArray.length store in
        DynArray.add store entry;
        Hashtbl.replace directory entry.name cid_comp_dest;
        CompCotyp.addDestructor cid_comp_dest cid_ctyp;
        cid_comp_dest

    let get = DynArray.get store

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear store;
      Hashtbl.clear directory
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
    let store = DynArray.create ()


    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name name = Hashtbl.find directory name

    let add entry =
      let cid_typdef = DynArray.length store in
        DynArray.add store entry;
        Hashtbl.replace directory entry.name cid_typdef;
        cid_typdef

    let get = DynArray.get store

    let get_implicit_arguments c = (get c).implicit_arguments

    let clear () =
      DynArray.clear store;
      Hashtbl.clear directory

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
    let store = DynArray.create ()

    (*  directory : (Id.name, Id.cid_type) Hashtbl.t *)
    let directory = Hashtbl.create 0

    let index_of_name n = Hashtbl.find directory n

    let add f =
      let cid_prog = DynArray.length store in
      let e = f cid_prog in
      DynArray.add store e;
      Hashtbl.replace directory e.name cid_prog;
      cid_prog

    let get = DynArray.get store

    let clear () =
      DynArray.clear store;
      Hashtbl.clear directory

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

    let render_name       n    = n.string_of_name
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


  (* RENDERER for Internal Syntax using names *)
  module NamedRenderer : RENDERER = struct

    open Id

    let render_name        n   = n.string_of_name
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
  Cid.CompConst.clear ();
  Cid.Comp.clear ();
  OpPragmas.clear()

let _ = Error.register_printer
  (fun (Error (loc, err)) ->
    Error.print_with_location loc (fun ppf ->
      match err with
        | FrozenType n ->
            Format.fprintf ppf
              "Type %s is frozen. A new constructor cannot be defined."
              (Cid.DefaultRenderer.render_cid_typ n)))
