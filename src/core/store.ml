open Support
open Beluga_syntax
open Syntax

module NameTable = Hashtbl.Make (Name)

type error =
  | FrozenType of Id.cid_typ

exception Error of Location.t * error

(* Register error printer at the end of this module. *)
module OpPragmas = struct
  type fixPragma =
    { name : Name.t
    ; fix : Fixity.t
    ; precedence : int
    ; assoc : Associativity.t
    }

  let default = ref Associativity.non_associative

  let pragmaCount = ref 0

  let pragmas = ref []

  let clear () = pragmas := []

  let getPragma name =
    !pragmas
    |> List.find_opt (fun { name = pragma_name; _ } -> Name.(pragma_name = name))

  let pragmaExists name =
    !pragmas
    |> List.exists (fun { name = pragma_name; _ } -> Name.(pragma_name = name))

  let addPragma name fix precedence assoc =
    if pragmaExists name
    then
      pragmas :=
        !pragmas
        |> List.map (fun ({ name = pragma_name; _ } as x) ->
          if Name.(pragma_name = name)
          then { name; fix; precedence; assoc }
          else x)
    else
      let new_entry = { name; fix; precedence; assoc } in
      pragmas := new_entry :: !pragmas;
      incr pragmaCount
end

module type ENTRY = sig
  type t
  val name_of_entry : t -> Name.t

  type cid = int
end

module type CIDSTORE = sig
  type entry
  type cid

  val index_of_name : Name.t -> cid
  val index_of_name_opt : Name.t -> cid option
  val replace_entry : cid -> entry -> unit
  val fixed_name_of : cid -> Name.t
  val get : cid -> entry
  val add : (cid -> entry) -> cid
  val clear : unit -> unit
  val current_entries : unit -> (cid * entry) list
end

module CidStore (M : ENTRY) : CIDSTORE
       with type entry = M.t
       with type cid = M.cid = struct
  include M
  type entry = M.t

  (** The entries in the store mapped by {!cid}. This is an arraylist, where
      the index of an entry is its {!cid}. *)
  let store : entry DynArray.t = DynArray.create ()

  (* FIXME: This needs to be phased out in favour of a persistent data
     structure for the names in scope. *)
  (** The entries in the store mapped by name. Only the latest binding is kept,
      so shadowed entries may only be retrived from {!store}. This does not
      take into account shadowing by entries in other stores, meaning that
      lookups from this hash table do not fully respect lexical scoping of
      signature entries. *)
  let directory : cid NameTable.t = NameTable.create 0

  let current_entries () =
    List.index (DynArray.to_list store)

  let clear () =
    DynArray.clear store

  let replace_entry n e =
    DynArray.set store n e

  let index_of_name (n : Name.t) : cid =
    NameTable.find directory n

  let index_of_name_opt (n : Name.t) : cid option =
    try
      Some (index_of_name n)
    with
    | Not_found -> None

  let get n =
    DynArray.get store n

  let fixed_name_of n = M.name_of_entry (get n)

  let add f =
    let cid = DynArray.length store in
    let e = f cid in
    DynArray.add store e;
    NameTable.add directory (name_of_entry e) cid;
    cid
end

module Cid = struct
  module Typ = struct
    (* type entry = *)
    module Entry = struct
      type t =
        { name : Name.t
        ; implicit_arguments : int
        ; kind : Int.LF.kind
        ; var_generator : (unit -> string) option
        ; mvar_generator : (unit -> string) option
        ; frozen : bool ref
        ; constructors : Id.cid_term list ref
        ; subordinates : BitSet.t ref
        (* bit array: if cid is a subordinate of this entry, then the cid-th bit is set *)
        ; typesubordinated : BitSet.t ref (* unused at the moment *)
        ; decl : Decl.t
        }
      let name_of_entry e = e.name
      type cid = Id.cid_typ
    end
    open Entry

    include CidStore (Entry)

    let mk_entry name kind implicit_arguments =
      { name
      ; implicit_arguments
      ; kind
      ; var_generator = None
      ; mvar_generator = None
      ; frozen = ref false
      ; constructors = ref []
      ; subordinates = ref (BitSet.empty ())
      ; typesubordinated = ref (BitSet.empty ())
      ; decl = Decl.next ()
      }

    let rec args =
      function
      | Int.LF.Typ -> 0
      | Int.LF.PiKind (_, k) -> 1 + args k

    let args_of_name n =
      let entry = get (index_of_name n) in
      args entry.kind - entry.implicit_arguments

    let args_of_name_opt n =
      try
        Option.some (args_of_name n)
      with
      | Not_found -> Option.none

    let freeze a =
      (get a).frozen := true

    let set_name_convention cid_tp mvar_name_generator var_name_generator =
      let entry = get cid_tp in
      let new_entry =
        { entry with
          var_generator = var_name_generator;
          mvar_generator = mvar_name_generator
        }
      in
      replace_entry cid_tp new_entry

    let var_gen cid_tp = (get cid_tp).var_generator
    let mvar_gen cid_tp = (get cid_tp).mvar_generator

    let rec get_atom_typ =
      function
      | Int.LF.Atom (_, a, _) -> a
      | Int.LF.PiTyp(_, tA) -> get_atom_typ tA
      | Int.LF.Sigma typRec -> get_atom_typ_rec typRec
      | Int.LF.TClo (tA, _) -> get_atom_typ tA
    and get_atom_typ_rec =
      function
      | Int.LF.SigmaLast (_, tA) -> get_atom_typ tA
      | Int.LF.SigmaElem(_, _, rest) -> get_atom_typ_rec rest

    let gen_var_name tA = var_gen (get_atom_typ tA)
    let gen_mvar_name tA = mvar_gen (get_atom_typ tA)

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
      if Bool.not (BitSet.is_set !(b_e.subordinates) a)
      then
        begin
          (* a is not yet in the subordinate relation for b, i.e. b depends on a *)
          BitSet.set !(b_e.subordinates) a;
          (* Take transitive closure:
             If b-terms can contain a-terms, then b-terms can contain everything a-terms can contain. *)
          (* Call below could be replaced by
             subord_iter (fun aa -> BitSet.set b_e subordinates aa) a_e.subordinates *)
          subord_iter (fun aa -> addSubord aa b) !(a_e.subordinates);
        end
      (* in else case, a is already in the subordinate relation for b, i.e. b depends on a *)

    let rec inspect acc =
      function
      | Int.LF.Atom(_, b, _) ->
         List.iter (fun a -> addSubord a b) acc ; [b]

      | Int.LF.PiTyp((Int.LF.TypDecl(_, tA1), _), tA2) ->
         inspect (acc @ (inspect [] tA1)) tA2
    (*  | Sigma _ -> *)


    let rec inspectKind cid_tp acc =
      function
      | Int.LF.Typ ->
         List.iter (fun a -> addSubord a cid_tp) acc
      | Int.LF.PiKind((Int.LF.TypDecl(_, tA1), _), tK2) ->
         inspectKind cid_tp (acc @ (inspect [] tA1)) tK2


    (* (\* At the moment not relevant: may or may not be correct / unused code *\)
     * (\* add the type-level subordination:  b-types can contain a-terms *\)
     * and addTypesubord a b =
     *   let a_e = get a in
     *   let b_e = get b in
     *   (\*      let _ = print_string ("addTypesubord " ^ a_(Id.string_of_name e.name) ^ " " ^ b_(Id.string_of_name e.name) ^ "\n") in *\)
     *   if BitSet.is_set a_e.typesubordinated b then
     *     ()
     *   else
     *     (BitSet.set a_e.typesubordinated b;
     *      (\* If b-types can contain a-terms, then b-types can contain everything a-terms can contain. *\)
     *      subord_iter (fun bb -> addTypesubord bb a) b_e.subordinates)
     *
     * let updateTypesubord cid entry =
     *   let rec doTypDecl = function
     *       Int.LF.TypDecl(_name, typ) -> doTyp typ
     *   and doTyp = function
     *     | Int.LF.Atom (_loc, a, _spine) ->
     *        addTypesubord a cid
     *     | Int.LF.PiTyp ((typdecl, _depend), typ) ->
     *        doTypDecl typdecl;
     *        doTyp typ
     *
     *   and update = function
     *     | Int.LF.Typ -> ()
     *     | Int.LF.PiKind ((typdecl, _depend), kind) ->
     *        doTypDecl typdecl;
     *        update kind
     *   (\*          List.iter (fun dependentArgType -> addTypesubord dependentArgType cid_tp) typesubords;
     *    *\)
     *   in
     *   update entry.kind *)


    (* let add entry = begin
     *     let cid_tp =
     *       let store =
     *         try DynArray.get store (!Modules.current)
     *         with _ -> begin
     *             let x = DynArray.create () in
     *             while DynArray.length store < (!Modules.current) do DynArray.add store (DynArray.create ()) done;
     *             DynArray.add store x;
     *             x
     *           end in
     *       DynArray.add store entry;
     *       (!Modules.current, (DynArray.length store) - 1) in
     *
     *     let directory =
     *       try DynArray.get directory (!Modules.current)
     *       with _ -> begin
     *           let x = NameTable.create 0 in
     *           while DynArray.length directory < (!Modules.current) do
     *             DynArray.add directory (NameTable.create 0)
     *           done;
     *           DynArray.add directory x;
     *           x
     *         end in
     *     NameTable.replace directory entry.name cid_tp;
     *
     *     let entry_list =
     *       try DynArray.get entry_list (!Modules.current)
     *       with _ -> begin
     *           let x = ref [] in
     *           while DynArray.length entry_list < (!Modules.current) do DynArray.add entry_list (ref []) done;
     *           DynArray.add entry_list x;
     *           x
     *         end in
     *     entry_list := cid_tp :: !entry_list;
     *
     *     inspectKind cid_tp [] entry.kind;
     *     cid_tp end *)

    (* Wrap the default add function so we call inspectKind after. *)
    let add f =
      let cid = add f in
      let e = get cid in
      inspectKind cid [] e.kind;
      cid

    let addConstructor loc typ c tA =
      let entry = get typ in
      if !(entry.frozen)
      then raise (Error (loc, FrozenType typ))
      else
        begin
          entry.constructors := c :: !(entry.constructors);
          ignore (inspect [] tA)
          (* type families occuring tA are added to the subordination relation
             BP: This insepction should be done once for each type family - not
             when adding a constructor; some type families do not have
             constructors, and it is redundant to compute it multiple times.
           *)
        end

    let is_subordinate_to (a : Id.cid_typ) (b : Id.cid_typ) : bool =
      let a_e = get a in
      (* subord_read *)BitSet.is_set !(a_e.subordinates) b

    let is_typesubordinate_to (a : Id.cid_typ) (b : Id.cid_typ) : bool =
      let b_e = get b in
      (* subord_read *)BitSet.is_set !(b_e.typesubordinated) a
  end

  module Term = struct
    module Entry = struct
      type t =
        { name : Name.t
        ; implicit_arguments : int
        ; typ : Int.LF.typ
        ; decl : Decl.t
        }
      type cid = Id.cid_term
      let name_of_entry e = e.name
    end
    include CidStore (Entry)
    open Entry

    let mk_entry name typ implicit_arguments =
      { name
      ; implicit_arguments
      ; typ
      ; decl = Decl.next ()
      }

    let rec args =
      function
      | Int.LF.PiTyp(_, tA) -> 1 + args tA
      | _ -> 0

    let add' loc e_typ f =
      let cid = add f in
      let e = get cid in
      Typ.addConstructor loc e_typ cid e.typ;
      cid

    let args_of_name n =
      let e = get (index_of_name n) in
      args e.typ - e.implicit_arguments

    let args_of_name_opt n =
      try
        Option.some (args_of_name n)
      with
      | Not_found -> Option.none

    let get_implicit_arguments c = (get c).implicit_arguments
  end

  module Schema = struct
    module Entry = struct
      type t =
        { name : Name.t
        ; schema : Int.LF.schema
        ; decl : Decl.t
        }
      type cid = Id.cid_schema
      let name_of_entry e = e.name
    end
    include CidStore (Entry)
    open Entry

    let mk_entry name schema =
      { name
      ; schema
      ; decl = Decl.next ()
      }

    let get_schema cid = (get cid).schema
    let get_name cid = (get cid).name


  (* (* Getting the schema name by finding a schema with the same
     elements can produce incorrect results, so we don't do it. -je *)
    let get_name_from_schema by s =
      match
        current_entries ()
        |> List.find_opt (fun (_, e) -> by e.schema s)
      with
      | Some (_, e) -> e.name
      | _ -> raise Not_found
   *)
  end

  module CompTyp = struct
    module Entry = struct
      type t =
        { name: Name.t
        (* bp : this is misgleding with the current design where
           explicitly declared context variables are factored into
           implicit arguments

           "explicitly declared" here is referring to variables declared
           by (g : ctx). These parameters are implicitly passed
           (instantiated via unification) but their type must be
           explicitly given, otherwise we don't know the schema of the
           context variable.
           Such explicitly declared implicit parameters are counted as
           implicit_arguments in this field. -je
         *)
        ; implicit_arguments : int

        ; kind : Int.Comp.kind
        ; positivity : Int.Sgn.positivity_flag
        (* flag for positivity and stratification checking *)

        ; mutable frozen : bool
        ; constructors : Id.cid_comp_const list ref
        ; decl : Decl.t
        }
      let name_of_entry e = e.name
      type cid = Id.cid_comp_typ
    end
    include CidStore (Entry)
    open Entry

    let mk_entry name kind implicit_arguments positivity =
      { name
      ; implicit_arguments
      ; kind
      ; positivity
      ; frozen = false
      ; constructors = ref []
      ; decl = Decl.next ()
      }

    let get_implicit_arguments c = (get c).implicit_arguments

    let freeze a = (get a).frozen <- true

    let addConstructor c typ =
      let entry = get typ in
      entry.constructors := c :: !(entry.constructors)
  end

  module CompCotyp = struct
    module Entry = struct
      type t =
        { name : Name.t
        (* bp : this is misleading with the current design where explicitly declared context variables
          are factored into implicit arguments *)
        ; implicit_arguments : int
        ; kind : Int.Comp.kind
        ; frozen : bool ref
        ; destructors: Id.cid_comp_dest list ref
        ; decl : Decl.t
        }
      type cid = Id.cid_comp_cotyp
      let name_of_entry e = e.name
    end

    include CidStore (Entry)
    open Entry

    let mk_entry name kind implicit_arguments =
      { name
      ; implicit_arguments
      ; kind
      ; frozen = ref false
      ; destructors = ref []
      ; decl = Decl.next ()
      }

    let freeze a = (get a).frozen := true

    let addDestructor c typ =
      let entry = get typ in
      entry.destructors := c :: !(entry.destructors)
  end

  module CompConst = struct
    module Entry = struct
      type t =
        { name : Name.t
        ; implicit_arguments : int
        ; typ : Int.Comp.typ
        ; decl : Decl.t
        }
      let name_of_entry e = e.name
      type cid = Id.cid_comp_const
    end
    include CidStore (Entry)
    open Entry

    let mk_entry name typ implicit_arguments =
      { name
      ; implicit_arguments
      ; typ
      ; decl = Decl.next ()
      }

    let add cid_ctyp f =
      let cid = add f in (* from CidStore *)
      CompTyp.addConstructor cid cid_ctyp;
      cid

    let get_implicit_arguments c = (get c).implicit_arguments
  end

  module CompDest = struct
    module Entry = struct
      type t =
        { name : Name.t
        ; implicit_arguments : int
        ; mctx : Int.LF.mctx
        ; obs_type : Int.Comp.typ
        ; return_type : Int.Comp.typ
        ; decl : Decl.t
        }
      let name_of_entry e = e.name
      type cid = Id.cid_comp_dest
    end
    include CidStore (Entry)
    open Entry

    let mk_entry name mctx obs_type return_type implicit_arguments =
      { name
      ; implicit_arguments
      ; mctx
      ; obs_type
      ; return_type
      ; decl = Decl.next ()
      }

    let add cid_ctyp f =
      let cid = add f in
      CompCotyp.addDestructor cid cid_ctyp;
      cid

    let get_implicit_arguments c = (get c).implicit_arguments
  end

  module CompTypDef = struct
    module Entry = struct
      type t =
        { name : Name.t
        ; implicit_arguments : int
        ; kind : Int.Comp.kind
        ; mctx : Int.LF.mctx
        ; typ : Int.Comp.typ
        ; decl : Decl.t
        }
      let name_of_entry e = e.name
      type cid = Id.cid_comp_typdef
    end
    include CidStore (Entry)
    open Entry

    let mk_entry name implicit_arguments (mctx, typ) kind =
      { name
      ; implicit_arguments
      ; kind
      ; mctx
      ; typ
      ; decl = Decl.next ()
      }

    let get_implicit_arguments c = (get c).implicit_arguments
  end

  module Comp = struct
    module Entry = struct
      type t =
        { name : Name.t
        ; implicit_arguments : int
        ; typ : Int.Comp.typ
        ; prog : Int.Comp.value option
        ; mutual_group : Id.cid_mutual_group
        ; decl : Decl.t option
          (* theorems without an associated
             declaration number have not yet been reflected into the
             signature. *)
        }
      let name_of_entry e = e.name
      type cid = Id.cid_comp_const
    end
    include CidStore (Entry)
    open Entry

    let mk_entry decl name typ implicit_arguments mutual_group prog =
      { name
      ; implicit_arguments
      ; typ
      ; prog
      ; mutual_group
      ; decl
      }

    let mutual_groups = DynArray.make 32

    let add_mutual_group decs =
      DynArray.add mutual_groups decs;
      DynArray.length mutual_groups - 1

    let lookup_mutual_group = DynArray.get mutual_groups

    let get_total_decl cid =
      let e = get cid in
      let name = e.Entry.name in
      let mg = lookup_mutual_group e.Entry.mutual_group in
      match
        List.find_opt
          (fun d -> Name.(d.Int.Comp.name = name))
          mg
      with
      | Some d -> d
      | None ->
         Error.raise_violation "theorem does not belong to its mutual group"

    let mutual_group cid = (get cid).mutual_group

    let name cid = (get cid).name

    let total_decs =
      Fun.(lookup_mutual_group ++ mutual_group)

    let set cid f =
      get cid
      |> f
      |> replace_entry cid

    let set_prog cid f =
      set cid (fun e -> { e with prog = f e.prog })

    let set_decl cid f =
      set cid (fun e -> { e with decl = f e.decl })
  end

  module type RENDERER = sig
    open Id
    open Syntax.Int

    val render_cid_comp_typ : cid_comp_typ -> string
    val render_cid_comp_cotyp : cid_comp_cotyp -> string
    val render_cid_comp_const : cid_comp_const -> string
    val render_cid_comp_dest : cid_comp_dest -> string
    val render_cid_typ : cid_typ -> string
    val render_cid_term : cid_term -> string
    val render_cid_schema : cid_schema -> string
    val render_cid_prog : cid_prog -> string
    val render_cid_mutual_group : cid_mutual_group -> string
    val render_offset : offset -> string

    val render_ctx_var: LF.mctx -> offset -> string
    val render_cvar : LF.mctx -> offset -> string
    val render_bvar : LF.dctx -> offset -> string
    val render_var : Comp.gctx -> var -> string
  end

  (* RENDERER for Internal Syntax using names *)
  module NamedRenderer : RENDERER = struct
    let render_cid_comp_typ c = Name.show (CompTyp.fixed_name_of c)
    let render_cid_comp_cotyp c = Name.show (CompCotyp.fixed_name_of c)
    let render_cid_comp_const c = Name.show (CompConst.fixed_name_of c)
    let render_cid_comp_dest c = Name.show (CompDest.fixed_name_of c)
    let render_cid_typ a = Name.show (Typ.fixed_name_of a)
    let render_cid_term c = Name.show (Term.fixed_name_of c)
    let render_cid_schema w = Name.show (Schema.fixed_name_of w)
    let render_cid_prog f = Name.show (Comp.fixed_name_of f)
    let render_cid_mutual_group c = string_of_int c
    let render_ctx_var cO g =
      try
        Name.show (Context.getNameMCtx cO g)
      with
      | _ -> "FREE CtxVar " ^ string_of_int g

    let render_cvar cD u =
      try
        Name.show (Context.getNameMCtx cD u)
      with
      | _ -> "FREE MVar " ^ string_of_int u

    let render_bvar cPsi i =
      try
        Name.show (Context.getNameDCtx cPsi i)
      with
      | _ -> "FREE BVar " ^ string_of_int i

    let render_offset i = string_of_int i

    let render_var cG x =
      try
        Name.show (Context.getNameCtx cG x)
      with
      | _ -> "FREE Var " ^ string_of_int x

  end (* Int.NamedRenderer *)

  (* Default RENDERER for Internal Syntax using de Bruijn indices *)
  module DefaultRenderer : RENDERER = struct
    include NamedRenderer

    let render_ctx_var _ g = string_of_int g
    let render_cvar _ u = "mvar " ^ string_of_int u
    let render_bvar _ i = "bvar " ^ string_of_int i
    let render_offset i = string_of_int i
    let render_var _ x = string_of_int x
  end (* Int.DefaultRenderer *)
end



(* LF Bound variables *)
module BVar = struct

  type entry = { name : Name.t }

  let mk_entry n = { name = n }

  type t = entry list

  let index_of_name store n =
    let rec loop i =
      function
      | [] -> raise Not_found
      | { name; _ } :: es ->
         if Name.(name = n)
         then i
         else loop (i + 1) es
    in
    loop 1 store

  let empty = []
  let extend ctx e = e :: ctx
  let length = List.length
  let get = List.nth
end

(* Free Bound Variables *)
module FVar = struct
  let store = NameTable.create 0
  let add = NameTable.add store
  let get = NameTable.find store
  let clear () = NameTable.clear store
end


(* Free contextual variables *)
module FCVar = struct

  let store = NameTable.create 0
  let add = NameTable.add store
  let get = NameTable.find store
  let clear () = NameTable.clear store
end

(* Computation-level variables *)
module Var = struct

  type entry =
    { name : Name.t
    }

  let mk_entry name =
    { name
    }

  type t = entry list

  let index_of_name store n =
    let rec loop i =
      function
      | [] -> raise Not_found
      | (e :: es) ->
         if Name.(e.name = n)
         then i
         else loop (i + 1) es
    in
    loop 1 store

  let to_list = Fun.id
  let empty = []
  let extend ctx e = e :: ctx
  let append vars vars' = vars @ vars'
  let get = List.nth
  let size = List.length

  (**
   * Erases a context down to a mere list of variables.
   * This is useful for indexing a term in the external syntax when the
   * context it occurs in is know, e.g. as in Harpoon.
   *)
  let of_gctx (cG : Int.Comp.gctx) : t =
    let f d v = Int.Comp.name_of_ctyp_decl d |> mk_entry |> extend v in
    List.fold_right f (Context.to_list_rev cG) empty

  let of_list (l : Name.t list) : t =
    List.map mk_entry l
end



(* Contextual variables *)
module CVar = struct

  type cvar = Name.t

  type entry =
    { name : cvar
    ; plicity : Plicity.t
    }

  let mk_entry name plicity =
    { name; plicity }

  type t = entry list

  let lookup store x =
    let rec loop i = function
      | [] -> raise Not_found
      | (e :: es) ->
         if Name.(e.name = x) then
           (i, e)
         else
           loop (i + 1) es
    in
    loop 1 store

  let index_of_name store x =
    let (i, e) = lookup store x in
    (e.plicity, i)

  let empty = []
  let extend cvars e = e :: cvars
  let get = List.nth
  let append cvars cvars' = cvars @ cvars'
  let length cvars = List.length cvars

  let to_string (cvars : t) : string =
    let rec go s =
      function
      | [] -> s
      | x :: xs -> go (s ^ ", " ^ Name.string_of_name x.name) xs
    in
    go "" cvars

  let of_mctx f (cD : Int.LF.mctx) : t =
    let f d v =
      let open Int.LF in
      match d with
      | Decl (u, _, plicity, inductivity) ->
        let plicity' = f (plicity, inductivity) in
        mk_entry u plicity' |> extend v
      | DeclOpt _ ->
         Error.raise_violation "[of_mctx] DeclOpt impossible"
    in
    List.fold_right f (Context.to_list_rev cD) empty

  let of_list (l : (Name.t * Plicity.t) list) : t =
    List.map (fun (u, p) -> mk_entry u p) l
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

let () =
  Error.register_exception_printer (function
      | Error (location, FrozenType n) ->
      Error.located_exception_printer
        (Format.dprintf
           "Type %s is frozen. A new constructor cannot be defined."
           (Cid.DefaultRenderer.render_cid_typ n))
        (List1.singleton location)
      | exn -> Error.raise_unsupported_exception_printing exn)
