(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
   @author Darin Morrison
*)




(** Syntax for the LF and Computation languages *)


(*

(** External Syntax *)
module Ext = struct

end
*)



(** Internal Syntax *)
module Int = struct

  module rec Decl : sig
    type sign  =
      | Typ   of Id.cid_typ  * LF.kind
      | Const of Id.cid_term * LF.typ
    and  typ   = Id.name * LF.typ
    and  ctx   =
      | Meta  of Id.name * LF.typ   * Ctx.data
      | Param of Id.name * LF.typ   * Ctx.data
      | Subst of Id.name * Ctx.data * Ctx.data
    and  sigma =
      | Sigma of Id.name * typ Ctx.abs
  end = struct

    (** Declarations *)

    (** Signature Declatation *)
    type sign  =
      | Typ   of Id.cid_typ  * LF.kind
      | Const of Id.cid_term * LF.typ 

    (** Typing Declaration {i x:A } *)
    and  typ   = Id.name * LF.typ

    (** Contextual Declaration {i D } *)
    and  ctx   =
      | Meta  of Id.name * LF.typ   * Ctx.data  (** u::A\[Ψ\] *)
      | Param of Id.name * LF.typ   * Ctx.data  (** p::A\[Ψ\] *)
      | Subst of Id.name * Ctx.data * Ctx.data  (** s::Ψ\[Φ\] *)

    (** Sigma Declaration {i x:Σ x{_1}:A{_1} … x{_n}:A{_n} } *)
    and  sigma =
      | Sigma of Id.name * typ Ctx.abs

  end



  and Schema : sig
    type elem =
      | Elem of LF.typ Ctx.abs * Decl.sigma
    and  t    =
      | Nil
      | Cons of elem * t
  end = struct

    (** Schemas *)

    (** Schema Elements {i Π x{_1}:A{_1} … x{_n}:A{_n}. Σ y{_1}:B{_1} … y{_k}:B{_k}.B } **)
    type elem =
      | Elem of LF.typ Ctx.abs * Decl.sigma

    (** Schema {i W } *)
    and  t    =
      | Nil
      | Cons of elem * t

  end




  and Ctx : sig
    type 'a abs =
      | NilAbs
      | ConAbs of 'a * 'a abs
    and  hat    = Id.var option * Id.offset
    and  data   =
      | Nil
      | VarCtx    of Id.var
      | Decl      of data * Decl.typ
      | DeclSigma of data * Decl.sigma
    and modal   = Decl.ctx abs
  end = struct

    (** Contexts *)

    (** Abstract List-Like Structure *)
    type 'a abs =
      | NilAbs
      | ConAbs of 'a * 'a abs

    (** Hat Context {i Ψ^ } *)
    and  hat    = Id.var option * Id.offset  (** {i ψ | Ψ^, x } *)

    (** LF Context {i Ψ, Φ } *)
    and  data   =
      | Nil
      | VarCtx    of Id.var             (** {i ψ                                  } *)
      | Decl      of data * Decl.typ    (** {i Ψ, x:A                             } *)
      | DeclSigma of data * Decl.sigma  (** {i Ψ, x:Σ x{_1}:{A_1} … x{_n}:A{_n}.B } *)

    (** Modal Context *)
    and modal   = Decl.ctx abs

  end




  and LF : sig
    type sign  = Decl.sign list
    and  kind  =
      | PiKind of Decl.typ * kind
      | TypKind
    and  typ   =
      | Atom   of Id.cid_typ * spine
      | TypClo of typ * Subst.t
      | PiTyp  of Decl.typ * typ
    and  term  =
      | TermClo of term * Subst.t
      | Lam     of Id.name * term
      | Root    of head * spine
    and  head  =
      | Ann      of head * typ
      | Const    of Id.cid_term
      | Proj     of head * Id.offset
      | DataVar  of Id.offset
      | MetaVar  of Id.var * Subst.t
      | ParamVar of Id.var * Subst.t
    and  spine =
      | App      of term * spine
      | SpineClo of spine * Subst.t
      | Nil
  end = struct

    (** LF Syntax *)

    (** LF Signatures *)
    type sign  = Decl.sign list

    (** LF Kinds {i K } *)
    and  kind  =
      | PiKind of Decl.typ * kind     (** {i Πx:A.K } *)
      | TypKind                       (** type        *)

    (** LF Types {i A, B } *)
    and  typ   =
      | Atom   of Id.cid_typ * spine  (** {i a M{_1} … M{_n} } *)
      | TypClo of typ * Subst.t       (** {i TpClo(A,s)      } *)
      | PiTyp  of Decl.typ * typ      (** {i Πx:A.B{_n}      } *)

    (** LF Terms {i M, N } *)
    and  term  =
      | TermClo  of term * Subst.t    (** {i TmClo(M, s)     } *)
      | Lam      of Id.name * term    (** {i λx.M            } *)
      | Root     of head * spine      (** {i H M{_1} … M{_n} } *)

    (** LF Heads {i H } *)
    and  head  =
      | Ann      of head * typ        (** {i (H:A)            } *)
      | Const    of Id.cid_term       (** {i c                } *)
      | Proj     of head * Id.offset  (** {i #k(x)|#k(p\[s\]) } *)
      | DataVar  of Id.offset         (** {i x                } *)
      | MetaVar  of Id.var * Subst.t  (** {i u\[s\]           } *)
      | ParamVar of Id.var * Subst.t  (** {i p\[s\]           } *)

    (** LF Spines {i S } *)
    and  spine =
      | App      of term * spine      (** {i M N{_1} … N{_n} } *)
      | SpineClo of spine * Subst.t   (** {i SClo(S,s)       } *)
      | Nil

  end




  and Subst : sig
    type t     =
      | Dot   of head * t
      | Shift of Id.offset
      | Var   of Id.var * t
    and  head  =
      | Index of Id.offset
      | Term  of Id.var * t
    and  modal =
      | Meta  of LF.term
      | Param of Id.offset
      | Shift of Id.offset
  end = struct

    (** Substitutions *)

    (** Substitutions {i σ} *)
    type t     =
      | Dot   of head * t    (** {i HS . s } *)
      | Shift of Id.offset   (** {i ^n     } *)
      | Var   of Id.var * t  (** {i s\[σ\] } *)

    (** Substitution Heads *)
    and  head  =
      | Index of Id.offset   (** {i k } *)
      | Term  of Id.var * t  (** {i M } *)

    (** Modal Substitution *)
    and  modal =
      | Meta  of LF.term     (** {i Ψ^. M / u } *)
      | Param of Id.offset   (** {i Ψ^. x / p } *)
      | Shift of Id.offset   (** {i ^k        } *)

  end




  and Closure : sig
    type 'a abs = 'a * Subst.t
    type term   =  LF.term         abs
    type typ    =  LF.typ          abs
    type typs   = (LF.typ Ctx.abs) abs
  end                = struct

    (** Closures *)

    type 'a abs = 'a * Subst.t

    type term   =  LF.term         abs

    type typ    =  LF.typ          abs

    type typs   = (LF.typ Ctx.abs) abs

  end




  and Comp : sig
    type typ      =
      | Arr      of typ * typ
      | BoxTp    of LF.typ * Ctx.data
      | PiBox    of Decl.ctx * typ
      | PiCtx    of (Id.name * Schema.t) * typ
      | SigmaBox of Decl.ctx * typ
      | Subst    of Ctx.data * Ctx.data
    module Exp : sig
      type check  =
        | BoxExp  of Ctx.hat * LF.term
        | SBoxExp of Ctx.hat * Subst.t
        | Case    of synth * branch list
        | Fn      of Id.name * check
        | LamBox  of Id.name * check
        | LamCtx  of Id.name * check
        | Pack    of Ctx.hat * LF.term * check
        | Rec     of Id.name * check
        | Synth   of synth
      and  synth  =
        | Ann      of check * typ
        | App      of synth * check
        | AppCtx   of synth * Ctx.data
        | AppTerm  of synth * (Ctx.hat * LF.term)
        | Let      of check * (Id.name * check)
        | LetPack  of check * (Id.name * Id.name * check)
        | Var      of Id.var
      and  branch =
        | BoxBranch  of Decl.ctx * (Ctx.hat * LF.term  * typ) * check
        | SBoxBranch of Decl.ctx * (Ctx.hat * Subst.t * typ) * check
    end
  end             = struct

    (** Computation Syntax *)

    (** Computation Types {i τ } *)
    type typ =
      | Arr      of typ * typ                              (** τ → τ'         *)
      | BoxTp    of LF.typ * Ctx.data                      (** A\[Ψ\]         *)
      | PiBox    of Decl.ctx * typ                         (** Π□ u::A\[Ψ\].τ *)
      | PiCtx    of (Id.name * Schema.t) * typ             (** Π  g::W.τ      *)
      | SigmaBox of Decl.ctx * typ                         (** Σ□ u::A\[Ψ\].τ *)
      | Subst    of Ctx.data * Ctx.data                    (** Ψ\[Φ\]         *)

    module Exp = struct

      type check  =
        | BoxExp  of Ctx.hat * LF.term                     (** box  Ψ^.M    *)
        | SBoxExp of Ctx.hat * Subst.t                     (** sbox Ψ^.s    *)
        | Case    of synth * branch list                   (** case e of bs *)
        | Fn      of Id.name * check                       (** fn y. e      *)
        | LamBox  of Id.name * check                       (** λ□ u. e      *)
        | LamCtx  of Id.name * check                       (** Λ ψ. e       *)
        | Pack    of Ctx.hat * LF.term * check             (** <Ψ^. M, e>   *)
        | Rec     of Id.name * check                       (** rec f. e     *)
        | Synth   of synth                                 (** i            *)

      and  synth  =
        | Ann      of check * typ                          (** e : τ                     *)
        | App      of synth * check                        (** i e                       *)
        | AppCtx   of synth * Ctx.data                     (** i <Ψ>                     *)
        | AppTerm  of synth * (Ctx.hat * LF.term)          (** i <Ψ^. M>                 *)
        | Let      of check * (Id.name * check)            (** let x = e in e' end       *)
        | LetPack  of check * (Id.name * Id.name * check)  (** let pack <u, x> = e in e' *)
        | Var      of Id.var                               (** y                         *)

      and  branch =
          (** ΠΔ. box (Ψ^. M) : A\[Ψ\] ↦ e *)
        | BoxBranch  of Decl.ctx * (Ctx.hat * LF.term * typ) * check
          (** ΠΔ. sbox(Ψ^. s) : A\[Ψ\] ↦ e *)
        | SBoxBranch of Decl.ctx * (Ctx.hat * Subst.t * typ) * check
    end

  end

end
