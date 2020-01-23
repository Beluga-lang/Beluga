open Id
open Syntax.Int

module OpPragmas : sig
  type fixPragma = {
    name : Id.name;
    fix : Syntax.Ext.Sgn.fix;
    precedence : int;
    assoc : Syntax.Ext.Sgn.assoc option;
  }

  val default : Syntax.Ext.Sgn.assoc ref

  val clear : unit -> unit

  val addPragma : Id.name -> Syntax.Ext.Sgn.fix -> int option -> Syntax.Ext.Sgn.assoc option-> unit

  val getPragma : Id.name -> fixPragma option

  val pragmaExists : Id.name -> bool

  val pragmaCount : int ref

end

module Modules : sig
  type state = Id.module_id * string list * Id.module_id list * (string * string list) list

  val abbrevs : (string * string list) list ref
  val addAbbrev : string list -> string -> unit

  val getState : unit -> state
  val setState : state -> unit

  val current : module_id ref
  val currentName : string list ref
  val opened  : module_id list ref

  val addSgnToCurrent : Sgn.decl -> unit

  val directory : (string list, module_id) Hashtbl.t
  val modules : Sgn.decl list ref DynArray.t

  val id_of_name : string list -> module_id
  val name_of_id : module_id -> string list

  val instantiateModule : string -> module_id
  val open_module : string list -> module_id

  val reset : unit -> unit

end

module Cid : sig

  module Typ : sig

    type entry = private {
      name                 : name;
      implicit_arguments   : int;
      kind                 : LF.kind;
      var_generator        : (unit -> string) option;
      mvar_generator       : (unit -> string) option;
      frozen       : bool ref;
      constructors : Id.cid_term list ref;
      subordinates : BitSet.t ref;
      typesubordinated : BitSet.t ref
    }

    val freeze : cid_typ -> unit

    val entry_list : (Id.cid_typ list ref) DynArray.t

    val mk_entry          : name -> LF.kind -> int -> entry
    val add               : entry -> cid_typ
    val addNameConvention : name -> (unit -> string) option  -> (unit -> string) option -> cid_typ
    val gen_var_name      : LF.typ -> (unit -> string) option
    val gen_mvar_name     : LF.typ -> (unit -> string) option
    val cid_of_typ        : LF.typ -> cid_typ
    val get               : ?fixName:bool -> cid_typ -> entry
    val index_of_name     : name -> cid_typ
    val addConstructor    : Syntax.Loc.t -> cid_typ -> cid_term -> LF.typ -> unit
    val clear             : unit -> unit
    val args_of_name      : name -> int

    (* see subord.ml for an explanation of term-level subordination
         and type-level subordination *)
    val is_subordinate_to  : cid_typ -> cid_typ -> bool       (* term-level *)
    val is_typesubordinate_to  : cid_typ -> cid_typ -> bool   (* type-level (dependent arguments) *)
  end


  module Term : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      typ                : LF.typ;
    }

    val mk_entry      : name -> LF.typ -> int -> entry
    val add           : Syntax.Loc.t -> cid_typ -> entry -> cid_term
    val get           : ?fixName:bool -> cid_term -> entry
    val get_implicit_arguments : cid_term -> int
    val index_of_name : name -> cid_term
    val args_of_name  : name -> int
    val clear         : unit -> unit
  end

  module CompTyp : sig

    type entry = private {
      name                 : name;
      implicit_arguments   : int;
      kind                 : Comp.kind;
      positivity           : Sgn.positivity_flag;
      mutable frozen       : bool;
      constructors : cid_comp_const list ref
    }

    val entry_list : (Id.cid_comp_typ list ref) DynArray.t
    val mk_entry  : name -> Comp.kind -> int ->  Sgn.positivity_flag -> entry

    val add           : entry -> cid_comp_typ
    val get           : ?fixName:bool -> cid_comp_typ -> entry
    val freeze        : cid_comp_typ -> unit
    val addConstructor: cid_comp_const -> cid_comp_typ -> unit
    val index_of_name : name -> cid_comp_typ
    val clear         : unit -> unit
    val get_implicit_arguments : cid_comp_typ -> int
  end

  module CompCotyp : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      kind               : Comp.kind;
      frozen             : bool ref;
      destructors : cid_comp_dest list ref
    }

    val mk_entry  : name -> Comp.kind -> int -> entry


    val add           : entry -> cid_comp_cotyp
    val get           : ?fixName:bool -> cid_comp_cotyp -> entry
    val freeze : cid_comp_cotyp -> unit
    val addDestructor : cid_comp_dest -> cid_comp_cotyp -> unit
    val index_of_name : name -> cid_comp_typ
    val clear         : unit -> unit
  end

  module CompConst : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      typ                : Comp.typ    }

    val mk_entry      : name -> Comp.typ -> int -> entry
    val add           : cid_comp_typ -> entry -> cid_comp_const
    val get           : ?fixName:bool -> cid_comp_const -> entry
    val get_implicit_arguments : cid_comp_const -> int
    val index_of_name : name -> cid_comp_const
    val clear         : unit -> unit
  end

  module CompDest : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      mctx               : LF.mctx;
      obs_type           : Comp.typ;
      return_type        : Comp.typ
    }


    val mk_entry      : name -> LF.mctx -> Comp.typ -> Comp.typ -> int -> entry
    val add           : cid_comp_cotyp -> entry -> cid_comp_dest
    val get           : ?fixName:bool -> cid_comp_dest -> entry
    val get_implicit_arguments : cid_comp_dest -> int
    val index_of_name : name -> cid_comp_dest
    val clear         : unit -> unit
  end

  module CompTypDef : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      kind               : Comp.kind;
      mctx               : LF.mctx;
      typ                : Comp.typ
    }

    val mk_entry      : name -> int -> (LF.mctx * Comp.typ) -> Comp.kind -> entry
    val add           : entry -> cid_comp_typ
    val get           : ?fixName:bool -> cid_comp_typ -> entry
    val get_implicit_arguments : cid_comp_typ -> int
    val index_of_name : name -> cid_comp_typ
    val clear         : unit -> unit
  end

  module Comp : sig
    type entry = {
      name               : name;
      implicit_arguments : int;
      typ                : Comp.typ;
      prog               : Comp.value option;
      mut_rec            : name list;
      total              : bool;
      hidden             : bool;
    }

    val mk_entry  : name -> Comp.typ -> int -> bool -> Comp.value option -> name list -> entry

    (** Selects all entries matching a given predicate. *)
    val filter : (entry -> bool) -> entry list

    (** If the value we store in the entry is a recursive value, it
        itself needs the cid_prog that we are creating to store this
        entry. Therefore, unlike 'add' functions in other modules,
        this 'add' function expects a function to which it will
        provide the cid_prog it generated to store the entry, thus
        tying the recursive knot. *)
    val add           : Loc.t -> (cid_prog -> entry) -> (Loc.t option * cid_prog)
    val get           : ?fixName:bool -> cid_prog -> entry

    val index_of_name : name -> cid_prog

    val entry_list    : ((Id.cid_prog * Loc.t) list ref) DynArray.t
    val clear         : unit -> unit

    val set_hidden    : Id.cid_prog -> (bool -> bool) -> unit
  end

  module Schema : sig

    type entry = private {
      name   : name;
      schema : LF.schema
    }


    val mk_entry        : name -> LF.schema -> entry
    val add             : entry -> cid_schema
    val get             : ?fixName:bool -> cid_schema -> entry
    val get_schema      : cid_schema -> LF.schema
    val index_of_name   : name -> cid_schema
    val get_name_from_schema : LF.schema -> name
    val clear           : unit -> unit
  end

  module NamedHoles : sig
    val printingHoles : bool ref
    val usingRealNames : bool ref
    val addExplicitName : string -> unit
    val haveNameFor : name -> string option
    val addNameConvention : cid_typ -> string -> string option -> unit
    val getName : ?tA:LF.typ option -> Id.name -> string
    val reset : unit -> unit
  end


  module type RENDERER = sig

    open Id
    open Syntax.Int
    val render_cid_comp_typ   : cid_comp_typ -> string
    val render_cid_comp_cotyp : cid_comp_cotyp  -> string
    val render_cid_comp_const : cid_comp_const -> string
    val render_cid_comp_dest  : cid_comp_dest -> string
    val render_cid_typ        : cid_typ      -> string
    val render_cid_term       : cid_term     -> string
    val render_cid_schema     : cid_schema   -> string
    val render_cid_prog       : cid_prog     -> string
    val render_offset         : offset       -> string

    val render_ctx_var        : LF.mctx    -> offset   -> string
    val render_cvar           : LF.mctx    -> offset   -> string
    val render_bvar           : LF.dctx    -> offset   -> string
    val render_var            : Comp.gctx  -> var      -> string

  end

  (* Default RENDERER for Internal Syntax *)
  module DefaultRenderer : RENDERER

  (* Named Renderer for Internal Syntax *)
  module NamedRenderer : RENDERER

end

val clear : unit -> unit

module BVar : sig

  type entry = private {
    name : name
  }

  val mk_entry      : name -> entry
  type t   (* NOTE: t is an ordered data structure *)
  val create        : unit -> t
  val extend        : t -> entry -> t
  val get           : t -> var  -> entry
  val length        : t -> int
  val index_of_name : t -> name -> offset
end


module FVar : sig
 (* NOTE: FVars are stored in an an ordered data structure *)
  val add   : name -> LF.typ_free_var -> unit
  val get   : name -> LF.typ_free_var
  val clear : unit -> unit
  val fvar_list : unit -> (Id.name * LF.typ_free_var) list
end

(*
module FMVar : sig
   (* NOTE: FMVars are stored in an an ordered data structure *)

  val add   : name -> (LF.typ * LF.dctx) -> unit
  val get   : name -> (LF.typ * LF.dctx)
  val clear : unit -> unit
end

  *)

module FPatVar : sig
  val add   : name -> Syntax.Int.Comp.typ -> unit
  val get   : name -> Syntax.Int.Comp.typ
  val clear : unit -> unit
  val fvar_ctx : unit -> Syntax.Int.Comp.gctx
end

module FCVar : sig

   (* NOTE: FCVars are stored in an an ordered data structure *)
  val add   : name -> (LF.mctx * LF.ctyp_decl)  -> unit
  val get   : name -> (LF.mctx * LF.ctyp_decl)
  val clear : unit -> unit
end

(*
module FPVar : sig
 (* NOTE: FPVars are stored in an an ordered data structure *)
  val add   : name -> (LF.typ * LF.dctx) -> unit
  val get   : name -> (LF.typ * LF.dctx)
  val clear : unit -> unit
end
*)

module Var : sig

  type entry = { name : name }

  val mk_entry      : name -> entry
  type t (* NOTE: t is an ordered data structure *)
  val to_list       : t -> entry list
  val create        : unit -> t
  val extend        : t -> entry -> t
  val get           : t -> var  -> entry
  val append        : t -> t -> t
  val index_of_name : t -> name -> offset
  val size          : t -> int

  (** Erases the context down to a list of names. *)
  val of_gctx       : Comp.gctx -> t
  val of_list       : Id.name list -> t
end


module CVar : sig

  type cvar = Id.name

  type entry = {
    name : cvar
  }

  val mk_entry      : cvar -> entry

  type t  (* NOTE: t is an ordered data structure *)

  val create        : unit -> t
  val extend        : t -> entry -> t
  val get           : t -> var  -> entry
  val index_of_name : t -> cvar -> offset
  val append        : t -> t -> t
  val length        : t -> int

  (** Erases the context down to a list of names. *)
  val of_mctx       : LF.mctx -> t

  val to_string     : t -> string
  val of_list       : Id.name list -> t
end
