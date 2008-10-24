(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
   @author Darin Morrison
*)

(** Syntax for the LF and Computation languages *)



open Id



(** External Syntax *)
module Ext = struct

  module Loc = Camlp4.PreCast.Loc

  type kind =
    | Typ     of Loc.t
    | ArrKind of Loc.t * typ * kind
    | PiKind  of Loc.t * typ_decl * kind

  and typ_decl =
    | TypDecl of name * typ

  and typ =
    | Atom   of Loc.t * name * spine
    | ArrTyp of Loc.t * typ * typ
    | PiTyp  of Loc.t * typ_decl * typ

  and normal =
    | Lam  of Loc.t * name * normal
    | Root of Loc.t * head * spine

  and head =
    | Name of Loc.t * name

  and spine =
    | Nil
    | App of normal * spine

  type sgn_decl =
    | SgnTyp   of Loc.t * name * kind
    | SgnConst of Loc.t * name * typ

end



(** Internal Syntax *)
module Int = struct

  type kind =
    | Typ
    | PiKind of typ_decl * kind

  and typ_decl =
    | TypDecl of name * typ

  and sigma_decl =
    | SigmaDecl of name * typ_rec

  and ctx_decl =
    | MDecl of name * typ  * dctx
    | PDecl of name * typ  * dctx
    | SDecl of name * dctx * dctx

  and typ =
    | Atom  of cid_typ * spine
    | PiTyp of typ_decl * typ
    | TClo  of typ * sub

  and normal =
    | Lam  of name * normal
    | Root of head * spine
    | Clo  of (normal * sub)

  and head =
    | BVar  of offset
    | Const of cid_term
    | MVar  of cvar * sub
    | PVar  of cvar * sub
    | AnnH  of head * typ
    | Proj  of head * int

  and spine =
    | Nil
    | App  of normal * spine
    | SClo of spine * sub

  and sub =
    | Shift of offset
    | SVar  of cvar * sub
    | Dot   of front * sub

  and front =
    | Head of head
    | Obj  of normal
    | Undef

  and cvar =
    | Offset of offset
    | Inst   of normal option ref * dctx * typ * cnstr list ref
    | PInst  of head   option ref * dctx * typ * cnstr list ref
    | CInst  of dctx   option ref * schema

  and constrnt =
    | Solved
    | Eqn of psi_hat * normal * normal
    | Eqh of psi_hat * head * head

  and cnstr = constrnt ref

  and dctx =
    | Null
    | CtxVar   of cvar
    | DDec     of dctx * typ_decl
    | SigmaDec of dctx * sigma_decl

  and 'a ctx =
    | Empty
    | Dec of 'a ctx * 'a

  and sch_elem =
    | SchElem of typ ctx * sigma_decl

  and schema =
    | Schema of sch_elem list

  and psi_hat = cvar option * offset

  and typ_rec = typ list

  type sgn_decl =
    | SgnTyp   of cid_typ  * kind
    | SgnConst of cid_term * typ



  (**********************)
  (* Type Abbreviations *)
  (**********************)

  type nclo     = normal  * sub
  type tclo     = typ     * sub
  type trec_clo = typ_rec * sub
  type mctx     = ctx_decl ctx



  (* Should consider moving the following stuff out into it's own
     module, e.g., Subst -dwm *)

  (* Which of thise functions are in the signature? -dwm *)

  (* Fix order wrt signature. -dwm *)

  (**************************)
  (* Explicit Substitutions *)
  (**************************)


  (* id = ^0 
     
     Invariant:

       Psi |- id : Psi      id is patsub

     Note: we do not take into account weakening here. 
  *)
  let id = Shift 0



  (* shift = ^1
  
     Invariant:

       Psi, x:A |- ^ : Psi     ^ is patsub
  *)
  let shift = Shift 1



  (* invShift = ^-1 = _.^0

     Invariant:

       G |- ^-1 : G, V    ^-1 is patsub
  *)
  let invShift = Dot (Undef, id)



  (* comp (s1, s2) = s'

     Invariant:

       If   G'  |- s1 : G 
       and  G'' |- s2 : G'
       then s'  =  s1 o s2
       and  G'' |- s1 o s2 : G

       If   s1, s2 patsub
       then s' patsub
   *)
  let rec comp s1 s2 = match (s1, s2) with
    | (Shift 0, s)             -> s
    (* next line is an optimization *)
    (* roughly 15% on standard suite for Twelf 1.1 *)
    (* Sat Feb 14 10:15:16 1998 -fp *)
    | (s, Shift 0)             -> s
    | (SVar(s,tau), s2)        -> SVar(s, comp tau s2)
      (* (s1, SVar(s,tau)) => undefined ? -bp *)
    | (Shift (n), Dot (ft, s)) -> comp (Shift (n-1)) s
    | (Shift (n), Shift (m))   -> Shift (n+m)
    | (Dot (ft, s), s')        -> Dot (frontSub ft s', comp s s')

    (* comp(s[tau], Shift(k)) = s[tau]
       where s :: Psi[Phi]  and |Psi| = k 

       comp(s[tau], Shift(k)) = Dot(Id(1), ... Dot(Id(k0), s[tau]))
       where s :: Psi[Phi]  and |Psi| = k'
       k = k' + k0  
     *)



  (* bvarSub n s = Ft'
     
     Invariant: 

       If    G |- s : G'    G' |- n : V
       then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
         or  Ft' = ^(n + k)    if  s = Ft1 .. Ftm ^k   and m < n
         and G |- Ft' : V [s]
     *)
  and bvarSub n s = match (n, s) with
    | (1, Dot (ft, s)) -> ft
    | (n, Dot (ft, s)) -> bvarSub (n-1) s
    | (n, Shift k)     -> Head (BVar (n+k))



  (* frontSub Ft s = Ft'

     Invariant:

       If   G |- s : G'     G' |- Ft : V
       then Ft' = Ft [s]
       and  G |- Ft' : V [s]
  *)
  and frontSub ft s = match ft with
    | Head (BVar n)       -> bvarSub n s
    | Head (MVar (u, s')) -> Head (MVar (u, comp s' s))
    | Head (PVar (u, s')) -> Head (PVar (u, comp s' s))

    | Head (Proj (h, k))  ->
        let Head h' = frontSub (Head h) s in
          Head (Proj (h', k))

    | Head (AnnH (h, a))  ->
        let Head h' = frontSub (Head h) s in
          Head (AnnH (h', a))

    | Head (Const c)      -> Head(Const c)
    | Obj u               -> Obj (Clo (u, s))
    | Undef               -> Undef



  (* dot1 (s) = s'

     Invariant:

       If   G |- s : G'
       then s' = 1. (s o ^)
       and  for all V s.t.  G' |- V : L
         G, V[s] |- s' : G', V 

         If s patsub then s' patsub
  *)
  (* first line is an optimization *)
  (* roughly 15% on standard suite for Twelf 1.1 *)
  (* Sat Feb 14 10:16:16 1998 -fp *)
  and dot1 s = match s with
    | Shift 0 -> s
    | s       -> Dot (Head (BVar 1), comp s shift)



  (* decSub (x:A) s = (x:A[s])

     Invariant:

       If   D ; Psi  |- s <= Psi'    D ; Psi' |- A <= type
       then D ; Psi  |- A[s] <= type
  *)

  (* First line is an optimization suggested by cs *)
  (* Dec[id] = Dec *)
  (* Sat Feb 14 18:37:44 1998 -fp *)
  (* seems to have no statistically significant effect *)
  (* undo for now Sat Feb 14 20:22:29 1998 -fp *)
  (*
    fun decSub (D, Shift(0)) = D
    | decSub (Dec (x, A), s) = Dec (x, Clo (A, s))
  *)
  let decSub (TypDecl (x, a)) s = TypDecl (x, TClo (a, s))



  (* invDot1 (s)         = s'
     invDot1 (1. s' o ^) = s'

     Invariant:

       s = 1 . s' o ^
       If G' |- s' : G
       (so G',V[s] |- s : G,V)
  *)
  let invDot1 s = comp (comp shift s) invShift



  (***************************)
  (* Inverting Substitutions *)
  (***************************)

  (* invert s = s'

     Invariant:

       If   D ; Psi  |- s  <= Psi'    (and s patsub)
       then D ; Psi' |- s' <= Psi
       s.t. s o s' = id  
  *)
  let invert s =
    let rec lookup n s p = match s with
      | Shift _                 -> None
      | Dot (Undef, s')         -> lookup (n+1) s' p
      | Dot (Head (BVar k), s') ->
          if k = p
          then Some n
          else lookup (n+1) s' p in

    let rec invert'' p si = match p with
      | 0 -> si
      | p ->
          let front = match lookup 1 s p with
            | Some k -> Head (BVar k)
            | None   -> Undef
          in
            invert'' (p-1) (Dot (front, si)) in

    let rec invert' n s = match s with
      | Shift p     -> invert'' p (Shift n)
      | Dot (_, s') -> invert' (n+1) s'

    in
      invert' 0 s



  (* strengthen t Psi = Psi'

     Invariant:

       If   D ; Psi'' |- t : Psi  (* and t is a pattern sub *)
       then D ; Psi'  |- t : Psi  and Psi' subcontext of Psi
  *)
  let rec strengthen s psi = match (s, psi) with
    | (Shift n (* = 0 *), Null) -> Null

    | (Dot (Head (BVar k) (* k = 1 *), t), DDec (psi, decl)) ->
        let t' = comp t invShift in
          (* Psi  |- decl dec     *)
          (* Psi' |- t' : Psi     *)
          (* Psi' |- decl[t'] dec *)
          DDec (strengthen t' psi, decSub decl t')

    | (Dot (Undef, t), DDec (psi, _)) ->
        strengthen t psi

    | (Shift n, psi) ->
        strengthen (Dot (Head(BVar (n+1)), Shift (n+1))) psi



  (* isId s = B
     
     Invariant:

       If   Psi |- s: Psi', s weakensub
       then B holds 
         iff s = id, Psi' = Psi
  *)
  let isId s =
    let rec isId' s k' = match s with
      | Shift k                 -> k = k'
      | Dot (Head (BVar n), s') -> n = k' && isId' s' (k' + 1)
      | _                       -> false
    in
      isId' s 0



  (* cloInv (U, w) = U[w^-1]

     Invariant:

       If Psi |- M <= A
          Psi |- w <= Psi'  w pattern subst
          M[w^-1] defined (without pruning or constraints)

       then Psi' |- M[w^-1] : A[w^-1]

     Effects: None
  *)
  let cloInv (m, w) = Clo (m, invert w)



  (* compInv s w = t

     Invariant:

       If  D ; Psi |- s <= Psi1 
           D ; Psi |- w <= Psi'
       then  t = s o (w^-1)
       and   D ; Psi' |- t <= Psi1
  *)
  let compInv s w = comp s (invert w)

    (* isPatSub s = B

       Invariant:
       If    Psi |- s : Psi' 
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)



  let isPatSub = assert false

  (*------------------------------------------------------------------------ *)

  let dctxToHat = assert false

  let ctxDec = assert false

  let ctxSigmaDec = assert false

  let ctxVar = assert false

  let mctxMDec = assert false

  let mctxPDec = assert false

  let constType = assert false

  let tconstKind = assert false

  let newMVar = assert false

  let newPVar = assert false

end
