open Id
open Syntax.Int

module Cid : sig

  module Typ : sig

    type entry = private {
      name                 : name;
      implicit_arguments   : int;
      kind                 : LF.kind;
      var_generator        : (unit -> string) option;
      mvar_generator       : (unit -> string) option;
      mutable frozen       : bool;
      mutable constructors : Id.cid_term list;
      mutable subordinates : BitSet.t;
      mutable typesubordinated : BitSet.t
    }

    val freeze : cid_typ -> unit

    val entry_list : Id.cid_typ list ref

    val mk_entry          : name -> LF.kind -> int -> entry
    val add               : entry -> cid_typ
    val addNameConvention : name -> (unit -> string) option  -> (unit -> string) option -> cid_typ
    val gen_var_name      : LF.typ -> (unit -> string) option
    val gen_mvar_name     : LF.typ -> (unit -> string) option
    val get               : cid_typ -> entry
    val index_of_name     : name -> cid_typ
    val addConstructor    : Syntax.Loc.t -> cid_typ -> cid_term -> LF.typ -> unit
    val clear             : unit -> unit

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
    val get           : cid_term -> entry
    val get_implicit_arguments : cid_term -> int
    val index_of_name : name -> cid_term
    val clear         : unit -> unit
  end

  module CompTyp : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      kind               : Comp.kind;
      mutable frozen             : bool;
      mutable constructors : cid_comp_const list
    }

    val mk_entry  : name -> Comp.kind -> int -> entry

    val add           : entry -> cid_comp_typ
    val get           : cid_comp_typ -> entry
    val freeze : cid_comp_typ -> unit
    val addConstructor: cid_comp_const -> cid_comp_typ -> unit
    val index_of_name : name -> cid_comp_typ
    val clear         : unit -> unit
  end

  module CompCotyp : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      kind               : Comp.kind;
      mutable frozen             : bool;
      mutable destructors : cid_comp_dest list
    }

    val mk_entry  : name -> Comp.kind -> int -> entry

    val add           : entry -> cid_comp_cotyp
    val get           : cid_comp_cotyp -> entry
    val freeze : cid_comp_cotyp -> unit
    val addDestructor : cid_comp_dest -> cid_comp_cotyp -> unit
    val index_of_name : name -> cid_comp_typ
    val clear         : unit -> unit
  end

  module CompConst : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      typ                : Comp.typ
    }

    val mk_entry      : name -> Comp.typ -> int -> entry
    val add           : cid_comp_typ -> entry -> cid_comp_const
    val get           : cid_comp_const -> entry
    val get_implicit_arguments : cid_comp_const -> int
    val index_of_name : name -> cid_comp_const
    val clear         : unit -> unit
  end

  module CompDest : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      typ                : Comp.typ
    }

    val mk_entry      : name -> Comp.typ -> int -> entry
    val add           : cid_comp_cotyp -> entry -> cid_comp_dest
    val get           : cid_comp_dest -> entry
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
    val get           : cid_comp_typ -> entry
    val get_implicit_arguments : cid_comp_typ -> int
    val index_of_name : name -> cid_comp_typ
    val clear         : unit -> unit
  end


  module Comp : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      typ                : Comp.typ;
      prog               : Comp.value;
      mut_rec            : name list;
      order              : Order.dec option
    }

    val mk_entry  : name -> Comp.typ -> int -> Comp.value -> name list -> entry

    (** If the value we store in the entry is a recursive value, it
        itself needs the cid_prog that we are creating to store this
        entry. Therefore, unlike 'add' functions in other modules,
        this 'add' function expects a function to which it will
        provide the cid_prog it generated to store the entry, thus
        tying the recursive knot. *)
    val add           : (cid_prog -> entry) -> cid_prog
    val add_total     : name -> Order.dec -> unit
    val get           : cid_prog -> entry
    val index_of_name : name -> cid_prog

    val clear         : unit -> unit
  end


  module Schema : sig

    type entry = private {
      name   : name;
      schema : LF.schema
    }

    val mk_entry        : name -> LF.schema -> entry
    val add             : entry -> cid_schema
    val get             : cid_schema -> entry
    val get_schema      : cid_schema -> LF.schema
    val index_of_name   : name -> cid_schema
    val clear           : unit -> unit
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

  type entry = private {
    name : name
  }

  val mk_entry      : name -> entry
  type t  (* NOTE: t is an ordered data structure *)
  val create        : unit -> t
  val extend        : t -> entry -> t
  val get           : t -> var  -> entry
  val append        : t -> t -> t
  val index_of_name : t -> name -> offset
  val size          : t -> int

end


module CVar : sig

  type cvar = MV of Id.name | PV of Id.name | CV of Id.name | SV of Id.name

  type entry = {
    name : cvar
  }

  val mk_entry      : cvar -> entry

  type t  (* NOTE: t is an ordered data structure *)

  val nearest_cvar  : t -> offset
  val create        : unit -> t
  val extend        : t -> entry -> t
  val get           : t -> var  -> entry
  val index_of_name : t -> cvar -> offset
  val append        : t -> t -> t
  val length        : t -> int

end
