(** Contexts

    @author Brigitte Pientka *)

open Beluga_syntax
open Synint.LF
open Synint

exception NoTypAvailable

(** Function form of the LF.Dec constructor with the arguments reversed.
    Useful for extending contexts multiple times without the need for
    parentheses.

    {[
      cD |> Context.dec ... |> Context.dec ...
    ]} *)
val dec : 'a -> 'a ctx -> 'a ctx

(** Extends a context with multiple entries from left to right. That is,

    {[
      ctx |> decs [ d1; d2; d3 ]
    ]}

    is equivalent to

    {[
      ctx |> dec d1 |> dec d2 |> dec d3
    ]} *)
val decs : 'a list -> 'a ctx -> 'a ctx

val dctxToHat : dctx -> dctx_hat

val addToHat : dctx_hat -> dctx_hat (* Lengthen by one declaration *)

val hatToDCtx : dctx_hat -> dctx

val extend_hatctx : int -> dctx_hat -> dctx_hat

(* Declaration Contexts *)
val ctxDec : dctx -> int -> typ_decl

val ctxSigmaDec : dctx -> int -> typ_decl

val containsSigma : dctx -> bool

val ctxVar : dctx -> ctx_var option

val hasCtxVar : dctx -> bool (* true if ctxVar dctx = Some _ *)

val append : 'a ctx -> 'a ctx -> 'a ctx

(** General eliminator for contexts. *)
val fold : 'b -> ('b -> 'a -> 'b) -> 'a ctx -> 'b

(** Lift a function into contexts. *)
val map : ('a -> 'b) -> 'a ctx -> 'b ctx

val to_list_map_rev : 'a ctx -> ('a ctx -> 'a -> 'b) -> 'b list

val to_list_map : 'a ctx -> ('a ctx -> 'a -> 'b) -> 'b list

val to_list_rev : 'a ctx -> 'a list

val to_list : 'a ctx -> 'a list

val to_sublist : 'a ctx -> ('a ctx * 'a) list

val to_sublist_rev : 'a ctx -> ('a ctx * 'a) list

val of_list_map : 'a list -> ('a -> 'b) -> 'b ctx

val of_list_map_rev : 'a list -> ('a -> 'b) -> 'b ctx

val of_list : 'a list -> 'a ctx

val of_list_rev : 'a list -> 'a ctx

val iter : 'a ctx -> ('a ctx -> 'a -> unit) -> unit

val iter' : 'a ctx -> ('a -> unit) -> unit

val iter_rev : 'a ctx -> ('a ctx -> 'a -> unit) -> unit

val iter_rev' : 'a ctx -> ('a -> unit) -> unit

val length : 'a ctx -> int

val dctxLength : dctx -> int (* number of concrete variables *)

val find : 'a ctx -> ('a ctx -> 'a -> bool) -> 'a option

val find' : 'a ctx -> ('a -> bool) -> 'a option

val find_rev : 'a ctx -> ('a ctx -> 'a -> bool) -> 'a option

val find_rev' : 'a ctx -> ('a -> bool) -> 'a option

val find_index : 'a ctx -> ('a ctx -> 'a -> bool) -> int option

val find_index' : 'a ctx -> ('a -> bool) -> int option

val find_index_rev : 'a ctx -> ('a ctx -> 'a -> bool) -> int option

val find_index_rev' : 'a ctx -> ('a -> bool) -> int option

(** Finds the leftmost element of the context, together with its index,
    satisfying the given predicate *)
val find_with_index :
  'a ctx -> ('a ctx -> 'a * int -> bool) -> ('a * int) option

val find_with_index' : 'a ctx -> ('a * int -> bool) -> ('a * int) option

val find_with_index_rev :
  'a ctx -> ('a ctx -> 'a * int -> bool) -> ('a * int) option

val find_with_index_rev' : 'a ctx -> ('a * int -> bool) -> ('a * int) option

val getNameDCtx : dctx -> int -> Name.t

val getNameMCtx : mctx -> int -> Name.t

val getNameCtx : Comp.gctx -> int -> Name.t

val projectCtxIntoDctx : typ_decl ctx -> dctx

val splitContextVariable : dctx -> typ_decl -> dctx

val emptyContextVariable : dctx -> dctx

val lookup' : 'a LF.ctx -> int -> 'a option

(** Looks up an index in a meta-context, giving the type and `inductivity`
    field.

    - Warning: This function does not [MShift] the type it returns; typically
      you should do this so the type makes sense in the whole context Delta.
    - Warning: returns [None] if the index is out of bounds OR if the context
      declaration does not assign a type (i.e. it's a [DeclOpt]). If you need
      to distinguish these cases, then you should use {!lookup'} and match on
      the [ctyp_decl] yourself. *)
val lookup_inductivity : LF.mctx -> int -> (LF.ctyp * Inductivity.t) option

val lookup : Comp.gctx -> int -> Comp.typ option

val lookupSchema : mctx -> int -> Id.cid_schema

val lookupCtxVar : mctx -> ctx_var -> Name.t * Id.cid_schema

val lookupCtxVarSchema : mctx -> ctx_var -> Id.cid_schema

(** Renames a variable in a meta-context. Returns None if there is no such
    variable, and otherwise returns the adjusted context with the name
    changed. *)
val rename_mctx : Name.t -> Name.t -> LF.mctx -> LF.mctx option

(** Renames a variable in a computational context. Returns None if there is
    no such variable, and otherwise returns the adjusted context with the
    name changed. *)
val rename_gctx : Name.t -> Name.t -> Comp.gctx -> Comp.gctx option

val concat : 'a LF.ctx list -> 'a LF.ctx

(** Erases an LF context to a list of names. To be used in preparation for
    contextual name generation. See nameGen.ml. *)
val names_of_dctx : LF.dctx -> Name.t list

(** Erases a meta-context to a list of names. To be used in preparation for
    contextual name generation. See nameGen.ml. *)
val names_of_mctx : LF.mctx -> Name.t list

(** Erases a program context to a list of names. To be used in preparation
    for contextual name generation. See nameGen.ml. *)
val names_of_gctx : Comp.gctx -> Name.t list

(** Computes the names in a proof state. This is the names from the
    meta-context and the program context. To be used in preparation for
    contextual name generation. See nameGen.ml. *)
val names_of_proof_state : Comp.proof_state -> Name.t list

val is_null : LF.dctx -> bool

val is_empty : 'a LF.ctx -> bool

(** Given two convertible meta-contexts, rebuilds the first using the names
    in the second. *)
val steal_mctx_names : LF.mctx -> LF.mctx -> LF.mctx

(** Given two convertible computational contexts, rebuilds the first using
    the names in the second. *)
val steal_gctx_names : Comp.gctx -> Comp.gctx -> Comp.gctx
