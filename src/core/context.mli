(** Contexts

    @author Brigitte Pientka
*)

open Syntax.Int.LF
open Syntax.Int


exception NoTypAvailable

val dctxToHat   : dctx -> psi_hat
val addToHat   : psi_hat -> psi_hat   (* Lengthen by one declaration *)
val hatToDCtx   : psi_hat -> dctx
(* Declaration Contexts *)
val ctxDec      : dctx -> int -> typ_decl
val ctxSigmaDec : dctx -> int -> typ_decl
val ctxVar      : dctx -> ctx_var option
val hasCtxVar   : dctx -> bool         (* true if ctxVar dctx = Some _ *)

val append      : 'a ctx -> 'a ctx -> 'a ctx
val to_list_map_rev : 'a ctx -> ('a ctx -> 'a -> 'b) -> 'b list
val to_list_map     : 'a ctx -> ('a ctx -> 'a -> 'b) -> 'b list
val to_list_rev     : 'a ctx -> 'a list
val to_list         : 'a ctx -> 'a list
val to_sublist      : 'a ctx -> ('a ctx * 'a) list
val to_sublist_rev  : 'a ctx -> ('a ctx * 'a) list
val iter        : 'a ctx -> ('a ctx -> 'a -> unit) -> unit
val iter'       : 'a ctx -> ('a -> unit) -> unit
val iter_rev    : 'a ctx -> ('a ctx -> 'a -> unit) -> unit
val iter_rev'   : 'a ctx -> ('a -> unit) -> unit
val length      : 'a ctx -> int
val dctxLength  : dctx -> int    (* number of concrete variables *)

val getNameDCtx : dctx -> int -> Id.name
val getNameMCtx : mctx -> int -> Id.name
val getNameCtx  : Comp.gctx -> int -> Id.name

val projectCtxIntoDctx : typ_decl ctx -> dctx
val splitContextVariable : dctx -> typ_decl -> dctx
val emptyContextVariable : dctx -> dctx

val lookup' : 'a LF.ctx -> int -> 'a option

(** Looks up an index in a meta-context, giving the type and `depend` field.
    - Warning: This function does not MShift the type it returns;
      typically you should do this so the type makes sense in the
      whole context Delta.
    - Warning: returns None if the index is out of bounds OR if the
      context declaration does not assign a type (i.e. it's a
      DeclOpt).  If you need to distinguish these cases, then you
      should use `lookup'` and match on the `ctyp_decl` yourself.
 *)
val lookup_dep : LF.mctx -> int -> (LF.ctyp * LF.depend) option
val lookup : Comp.gctx -> int -> Comp.typ option

val lookupSchema : mctx -> int -> Id.cid_schema
val lookupCtxVar : mctx -> ctx_var -> Id.name * Id.cid_schema
val lookupCtxVarSchema : mctx -> ctx_var -> Id.cid_schema
