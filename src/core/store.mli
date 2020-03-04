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

module type ENTRY = sig
  type t
  val name_of_entry : t -> Id.name

  type cid = Id.module_id * int
end

module Cid : sig

  module Typ : sig

    module Entry : sig
      type t =
        private {
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
    end
    open Entry
    type entry = t

    val freeze : cid_typ -> unit

    (* val entry_list : (Id.cid_typ list ref) DynArray.t *)

    val mk_entry : name -> LF.kind -> int -> entry
    val add : (cid_typ -> entry) -> cid_typ
    val set_name_convention : cid_typ ->
                              (unit -> string) option ->
                              (unit -> string) option ->
                              unit
    val gen_var_name : LF.typ -> (unit -> string) option
    val gen_mvar_name : LF.typ -> (unit -> string) option
    val cid_of_typ : LF.typ -> cid_typ
    val get : cid_typ -> entry
    val index_of_name : name -> cid_typ
    val addConstructor : Syntax.Loc.t -> cid_typ -> cid_term -> LF.typ -> unit
    val clear : unit -> unit
    val args_of_name : name -> int
    val current_entries : unit -> (cid_typ * entry) list

    (* see subord.ml for an explanation of term-level subordination
         and type-level subordination *)
    val is_subordinate_to  : cid_typ -> cid_typ -> bool       (* term-level *)
    val is_typesubordinate_to  : cid_typ -> cid_typ -> bool   (* type-level (dependent arguments) *)
  end


  module Term : sig

    module Entry : sig
      type t =
        private
          { name : name
          ; implicit_arguments : int
          ; typ : LF.typ
          }
      type cid = Id.cid_term
      val name_of_entry : t -> Id.name
    end
    type entry = Entry.t

    val mk_entry      : name -> LF.typ -> int -> entry
    val get           : cid_term -> entry
    val add'          : Loc.t -> cid_typ -> (cid_term -> entry) -> cid_term
    val get_implicit_arguments : cid_term -> int
    val index_of_name : name -> cid_term
    val args_of_name  : name -> int
    val clear         : unit -> unit
  end

  module CompTyp : sig

    module Entry : sig
      type t =
        private {
            name                 : name;
            implicit_arguments   : int;
            kind                 : Comp.kind;
            positivity           : Sgn.positivity_flag;
            mutable frozen       : bool;
            constructors : cid_comp_const list ref
          }
      val name_of_entry : t -> Id.name
      type cid = Id.cid_comp_typ
    end
    type entry = Entry.t

    (* val entry_list : (Id.cid_comp_typ list ref) DynArray.t *)
    val mk_entry  : name -> Comp.kind -> int ->  Sgn.positivity_flag -> entry

    val add           : (cid_comp_typ -> entry) -> cid_comp_typ
    val get           : cid_comp_typ -> entry
    val freeze        : cid_comp_typ -> unit
    val addConstructor: cid_comp_const -> cid_comp_typ -> unit
    val index_of_name : name -> cid_comp_typ
    val clear         : unit -> unit
    val get_implicit_arguments : cid_comp_typ -> int
  end

  module CompCotyp : sig

    module Entry : sig
      type t =
        private {
            name               : name;
            implicit_arguments : int;
            kind               : Comp.kind;
            frozen             : bool ref;
            destructors : cid_comp_dest list ref
          }
      type cid = Id.cid_comp_cotyp
      val name_of_entry : t -> Id.name
    end
    type entry = Entry.t

    val mk_entry  : name -> Comp.kind -> int -> entry

    val add           : (cid_comp_cotyp -> entry) -> cid_comp_cotyp
    val fixed_name_of : cid_comp_cotyp -> Id.name
    val get           : cid_comp_cotyp -> entry
    val freeze : cid_comp_cotyp -> unit
    val addDestructor : cid_comp_dest -> cid_comp_cotyp -> unit
    val index_of_name : name -> cid_comp_typ
    val clear         : unit -> unit
  end

  module CompConst : sig

    module Entry : sig
      type t =
        private {
            name               : name;
            implicit_arguments : int;
            typ                : Comp.typ
          }
      type cid = Id.cid_comp_const
      val name_of_entry : t -> Id.name
    end

    type entry = Entry.t

    val mk_entry      : name -> Comp.typ -> int -> entry
    val add           : cid_comp_typ -> (cid_comp_const -> entry) -> cid_comp_const
    val get           : cid_comp_const -> entry
    val get_implicit_arguments : cid_comp_const -> int
    val index_of_name : name -> cid_comp_const
    val clear         : unit -> unit
  end

  module CompDest : sig

    module Entry : sig
      type t =
        private {
            name               : name;
            implicit_arguments : int;
            mctx               : LF.mctx;
            obs_type           : Comp.typ;
            return_type        : Comp.typ
          }
      type cid = Id.cid_comp_dest
      val name_of_entry : t -> Id.name
    end
    type entry = Entry.t

    val mk_entry      : name -> LF.mctx -> Comp.typ -> Comp.typ -> int -> entry
    val add           : cid_comp_cotyp -> (cid_comp_dest -> entry) -> cid_comp_dest
    val get           : cid_comp_dest -> entry
    val fixed_name_of : cid_comp_dest -> Id.name
    val get_implicit_arguments : cid_comp_dest -> int
    val index_of_name : name -> cid_comp_dest
    val clear         : unit -> unit
  end

  module CompTypDef : sig

    module Entry : sig
      type t =
        private {
            name               : name;
            implicit_arguments : int;
            kind               : Comp.kind;
            mctx               : LF.mctx;
            typ                : Comp.typ
          }
      type cid = Id.cid_comp_typdef
      val name_of_entry : t -> Id.name
    end
    type entry = Entry.t

    val mk_entry      : name -> int -> (LF.mctx * Comp.typ) -> Comp.kind -> entry
    val add           : (cid_comp_typdef -> entry) -> cid_comp_typdef
    val get           : cid_comp_typdef -> entry
    val fixed_name_of : cid_comp_typdef -> Id.name
    val get_implicit_arguments : cid_comp_typdef -> int
    val index_of_name : name -> cid_comp_typdef
    val clear         : unit -> unit
  end

  module Comp : sig
    type mutual_group_id

    val fmt_ppr_mutual_group_id : Format.formatter -> mutual_group_id -> unit

    val add_mutual_group : Comp.total_dec list option -> mutual_group_id
    val unchecked_mutual_group : mutual_group_id
    val trust_mutual_group : mutual_group_id

      module Entry : sig
        type t =
          { name               : name
          ; implicit_arguments : int
          ; typ                : Comp.typ
          ; prog               : Comp.value option
          ; mutual_group       : mutual_group_id
          ; hidden             : bool
          }
        type cid = Id.cid_prog
        val name_of_entry : t -> Id.name
      end
      type entry = Entry.t

    (** Gets the name of the given theorem ID. *)
    val name : cid_comp_const -> name

    (** Looks up the total declarations for the given mutual group. *)
    val lookup_mutual_group : mutual_group_id -> Comp.total_dec list option

    (** Gets the mutual group ID for a given function reference. *)
    val mutual_group : cid_comp_const -> mutual_group_id

    (** Looks up the total declarations for the mutual group of the
        given function.
     *)
    val total_decs : cid_comp_const -> Comp.total_dec list option

    val mk_entry  : name -> Comp.typ -> int ->
                    mutual_group_id -> Comp.value option ->
                    entry

    (** If the value we store in the entry is a recursive value, it
        itself needs the cid_prog that we are creating to store this
        entry. Therefore, unlike 'add' functions in other modules,
        this 'add' function expects a function to which it will
        provide the cid_prog it generated to store the entry, thus
        tying the recursive knot.
     *)
    val add           : (cid_prog -> entry) -> cid_prog
    val get           : cid_prog -> entry

    val fixed_name_of : cid_prog -> Id.name
    val index_of_name : name -> cid_prog
    val index_of_name_opt : name -> cid_prog option

    (* val entry_list    : ((Id.cid_prog * Loc.t) list ref) DynArray.t *)
    val clear         : unit -> unit

    (** Update the associated program of an existing entry.
        This is notably used for two-step elaboration of functions:
        - a function is added to the store with its type *before* its
          bodies is elaborated
        - indexing can find the cid of the function immediately from
          the store.
        - when the function body is elaborated, the store entry is
          updated to hold the body as well.
     *)
    val set_prog      : Id.cid_prog -> (Comp.value option -> Comp.value option) -> unit

    (** Update the hidden flag of an existing entry. *)
    val set_hidden    : Id.cid_prog -> (bool -> bool) -> unit
  end

  module Schema : sig

    module Entry : sig
      type t =
        private {
            name   : name;
            schema : LF.schema
          }
      val name_of_entry : t -> name
      type cid = Id.cid_schema
    end
    type entry = Entry.t

    val mk_entry        : name -> LF.schema -> entry
    val add             : (cid_schema -> entry) -> cid_schema
    val get             : cid_schema -> entry
    val get_schema      : cid_schema -> LF.schema
    val index_of_name   : name -> cid_schema
    val get_name        : cid_schema -> name
    val clear           : unit -> unit
  end

  module NamedHoles : sig
    val printingHoles : bool ref
    val usingRealNames : bool ref
    val addExplicitName : string -> unit
    val addNameConvention : cid_typ -> string -> string option -> unit
    val getName : Id.name -> string
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

  type entry =
    { name : cvar
    ; plicity : Comp.plicity
    }

  val mk_entry      : cvar -> Comp.plicity -> entry

  type t  (* NOTE: t is an ordered data structure *)

  val create        : unit -> t
  val extend        : t -> entry -> t
  val get           : t -> var  -> entry

  (** Looks up the index of a given name in scope.
      Raises Not_found if no such variable is in scope.
      Returns the plicity of the variable together with its offset.
   *)
  val index_of_name : t -> cvar -> Comp.plicity * offset
  val append        : t -> t -> t
  val length        : t -> int

  (** Erases the context down to a list of names. *)
  val of_mctx       : LF.mctx -> t

  val to_string     : t -> string
  val of_list       : (Id.name * Comp.plicity) list -> t
end
