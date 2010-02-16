(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Substitutions

    @author Brigitte Pientka
*)


open Syntax.Int.LF

module LF = struct

  let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [9])

  exception Error of string

  (**************************)
  (* Explicit Substitutions *)
  (**************************)

  (* id = ^0
   *
   * Invariant:
   *
   * cPsi |- id : cPsi      id is patsub
   *
   * Note: we do not take into account weakening here.
   *)
  let id =  Shift (NoCtxShift , 0)

  (* shift = ^1
   *
   * Invariant:
   *
   * cPsi, x:tA |- ^ : cPsi     ^ is patsub
   *)
  let shift =  Shift (NoCtxShift , 1)

  (* invShift = ^-1 = _.^0
   *
   * Invariant:
   *
   * Psi |- ^-1 : Psi, A    ^-1 is patsub
   *)
  let invShift = Dot (Undef, id)

  (* comp s1 s2 = s'
   *
   * Invariant:
   *
   * If   Psi'  |- s1 : Psi
   * and  Psi'' |- s2 : Psi'
   * then s'  =  s1 o s2
   * and  Psi'' |- s1 o s2 : Psi
   *
   * If   s1, s2 patsub
   * then s' patsub
   *)
  let rec comp s1 s2 = match (s1, s2) with
      
    | (Shift (NoCtxShift , 0), s2) -> 
        (*  Psi |- s1 : Psi   and Psi2 |- s2 : Psi
         *  therefore   Psi2 |- s2 : Psi  and s2 = s1 o s2
         *)
        s2

    | (s, Shift (NoCtxShift, 0)) ->
        (*  Psi1 |- s1 : Psi   and Psi1 |- s2 : Psi1
         *  therefore   Psi1 |- s1 : Psi  and s1 = s1 o s2
         *)
        s

    (* Case: Shift(CtxShift psi, m) o Shift(CtxShift psi', n) impossible *)

    | (Shift (NoCtxShift, n), Shift (NoCtxShift, m)) ->
        (* psi, Psi |- s1 : psi, Psi1   and psi, Psi2 |- s2: psi, Psi
         *  therefore  psi, Psi2 |- s : psi, Psi1  where s = s1 o s2
         *)
        Shift (NoCtxShift, n + m)

    | (Shift (CtxShift psi, n), Shift (NegCtxShift psi', k)) ->
        (* psi, Psi |- s1 : .   and     Psi,Psi' |- s2 : psi, Psi
         * therefore  Psi,Psi' |- s : .
         *)
        if psi = psi' then
          Shift (NoCtxShift, n+k)
        else
          raise (Error "Composition undefined - 1 ")

    | (Shift (CtxShift psi , m), s2) ->
        let rec ctx_shift n s2 = match s2 with
          | Dot(_ft, s) -> ctx_shift (n - 1) s
              (*  psi, Psi |- s1 : .   and Psi2 |- s2. ft : psi, Psi  *)

          | Shift (NoCtxShift, k) -> Shift (CtxShift psi, k + n)
              (*  psi, Psi |- s1 : .   and (psi, Psi), Psi2 |- s2 : psi, Psi
               *  psi |-  s : .
               *)

          | Shift (NegCtxShift _psi, k) -> Shift (NoCtxShift, k + n)
              (* psi, Psi |- s1 : .    and Psi, Psi' |- s2 : psi, Psi
               * Psi, Psi' |- s1 o s2 : .
               *)


          | _ -> (* (Printf.printf "Composing: s1 = %s \n and s2 = %s\n\n"
                    (P.subToString s1) (P.subToString s2) ; *)
              raise (Error "Composition undefined - 2 ")
        in
          ctx_shift m s2

    | (Shift (NegCtxShift psi, k), Shift (NoCtxShift, m)) ->
        (* Psi1 |- s1 : psi     and   Psi1, Psi |- s2 : Psi1
         *  therefore   Psi1, Psi |- s : psi      where s = s1 o s2
         *)
        Shift (NegCtxShift psi, k + m)

    | (Shift (NegCtxShift psi, 0), Shift (CtxShift psi', m)) ->
        (* . |- s1 : psi     and  psi,Psi' |- s2 : .
         *  therefore   psi, Psi' |- s : psi      where s = s1 o s2
         *)
        if psi = psi' then
          Shift (NoCtxShift, m)
        else
          raise (Error "Composition not defined - 3")


    (*    | (Shift (psi, n), SVar (s, tau)) -> Shift (|Psi''|) *)

    | (Shift (psi,n), Dot (_ft, s)) ->
        comp (Shift (psi, n - 1)) s

    | (SVar (s, tau), s2) ->
        SVar (s, comp tau s2)

    | (Dot (ft, s), s') ->
        (* comp(s[tau], Shift(k)) = s[tau]
         * where s :: Psi[Phi]  and |Psi| = k
         *
         * comp(s[tau], Shift(k)) = Dot(Id(1), ... Dot(Id(k0), s[tau]))
         * where s :: Psi[Phi]  and |Psi| = k'
         * k = k' + k0
         *)
        let h = frontSub ft s' in 
          Dot (h, comp s s')

(*    | (Shift (CtxShift _, _ ), _s2) -> 
       raise (Error "Composition not defined? - Shift CtxShift")
*)
    | (Shift (NoCtxShift , k ), Shift (NegCtxShift _, _ )) -> 
        raise (Error ("Composition not defined? - NoCtxShift " ^ string_of_int k ^ " o Shift NegCtx?"))


    | (Shift (NoCtxShift , k ), Shift (CtxShift _, _ )) -> 
    (*  psi, x:A |- s1 <= psi  
                 |-    <= psi, x:A
     *)
        raise (Error ("Composition not defined? - NoCtxShift " ^ string_of_int k ^ " o Shift CtxShift ?"))



    | (_s1, _s2) -> 
        raise (Error "Composition not defined?")


  (* bvarSub n s = Ft'
   *
   * Invariant:
   *
   * If    Psi |- s <= Psi'    Psi' |- n <= A
   * then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
   * or  Ft' = ^(n + k)      if  s = Ft1 .. Ftm ^k   and m < n
   * and Psi |- Ft' <= [s]A
   *)
  and bvarSub n s = match (n, s) with
    | (1, Dot (ft, _s))  -> ft
    | (n, Dot (_ft, s))  -> bvarSub (n - 1) s
    | (n, Shift (_ , k)) -> Head (BVar (n + k))


  (* frontSub Ft s = Ft'
   *
   * Invariant:
   *
   * If   Psi |- s : Psi'     Psi' |- Ft : A
   * then Ft' = Ft [s]
   * and  Psi |- Ft' : [s]A
   *)
  and frontSub ft s = match ft with
    | Head (BVar n)       ->  bvarSub n s
    | Head (FVar _)       -> ft
    | Head (MVar (u, s')) -> Head (MVar (u, comp s' s)) 
    | Head (PVar (u, s')) -> Head (PVar (u, comp s' s))

    | Head (Proj (BVar n, k))  ->
        begin match bvarSub n s with
          | Head (BVar x) ->
              Head (Proj (BVar x, k))

          | Head (PVar _ as h) ->
              Head (Proj (h, k))

          | Obj (Tuple (_, tuple)) ->
              let rec nth s = function
                | (Last u, 1) -> (u, s)
                | (Cons (u, _), 1) -> (u, s)
                | (Cons (u, tuple), n) -> nth (Dot(Obj u, s)) (tuple, n - 1)
              in
(*              Obj (Clo (nth s (tuple, k))) *)
                Obj (fst (nth s (tuple, k)))
        end

    | Head (Proj (h, k))  ->
        begin match frontSub (Head h) s with
          | Head h' ->
              Head (Proj (h', k))

          | Obj (Tuple (_, tuple)) ->
              let rec nth s = function
                | (Last u, 1) -> (u, s)
                | (Cons (u, _), 1) -> (u, s)
                | (Cons (u, tuple), n) -> nth (Dot(Obj u, s)) (tuple, n - 1)
              in
(*              Obj (Clo (nth s (tuple, k))) *)
                Obj (fst (nth s (tuple, k)))
        end

    | Head (AnnH (h, a))  ->
        let Head h' = frontSub (Head h) s in
          Head (AnnH (h', a))

    | Head (Const c)      -> Head (Const c)
    | Obj u               -> Obj (Clo (u, s))
    | Undef               -> Undef
    | Head (FPVar (_n, _ )) -> ft
    | Head (MMVar (_n, _ )) -> raise (Error "[frontSub] mmvar undefined ")

        
  (* dot1 (s) = s'
   *
   * Invariant:
   *
   * If   Psi |- s : Psi'
   * then s' = 1. (s o ^)
   * and  for all A s.t.  Psi' |- A : type
   * Psi, [s]A |- s' : Psi', A
   *
   * If s patsub then s' patsub
   *)
  (* first line is an optimization *)
  (* roughly 15% on standard suite for Twelf 1.1 *)
  (* Sat Feb 14 10:16:16 1998 -fp *)
  and dot1 s = match s with
    | Shift (_ , 0) -> s
    | s             -> Dot (Head (BVar 1), comp s shift)



  (* decSub (x:tA) s = (x:tA[s])
   *
   * Invariant:
   *
   * If   D ; Psi  |- s     <= Psi'    D ; Psi' |- A <= type
   * then D ; Psi  |- [s]A] <= type
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
  let decSub (TypDecl (x, tA)) s = TypDecl (x, TClo (tA, s))


  (* invDot1 (s)         = s'
   * invDot1 (1. s' o ^) = s'
   *
   * Invariant:
   *
   * s = 1 . s' o ^
   * If Psi' |- s' : Psi
   * (so Psi',A[s] |- s : Psi,A)
   *)
  (*  let invDot1 s = comp (comp shift s) invShift *)


  (***************************)
  (* Inverting Substitutions *)
  (***************************)

  (* invert s = s'
   *
   * Invariant:
   *
   * If   D ; Psi  |- s  <= Psi'    (and s patsub)
   * then D ; Psi' |- s' <= Psi
   * s.t. s o s' = id    (comp s' s = id)
   *)
  let invert s =
    let rec lookup n s p = match s with
      | Shift _                 -> None
      | Dot (Undef, s')         -> lookup (n + 1) s' p
      | Dot (Head (BVar k), s') ->
          if k = p then
            Some (Head (BVar n))
          else
            lookup (n + 1) s' p 
    in

    let rec invert'' p si = match p with
      | 0 -> si
      | p ->
          let front = match lookup 1 s p with
            | Some h -> h
            | None   -> Undef
          in
            invert'' (p - 1) (Dot (front, si)) in

    let rec invert' n s = match s with

      | Shift (NoCtxShift, p) ->
          invert'' p (Shift (NoCtxShift, n))

      | Shift (CtxShift(psi), p) ->
          invert'' p (Shift (NegCtxShift(psi), n))

      | Shift (NegCtxShift(psi), 0) ->
          (* . |- s : psi  Hence psi |- si : . *)
          Shift (CtxShift(psi), 0)

      | Shift (NegCtxShift(psi), p) ->
          (* Psi |- s : psi  Hence psi |- si : Psi *)
          invert'' p (Shift (CtxShift psi, n))

      | Dot (_, s') ->
          invert' (n + 1) s'

    in
      invert' 0 s


  (* strengthen t Psi = Psi'
   *
   * Invariant:
   *
   * If   D ; Psi'' |- t : Psi  (* and t is a pattern sub *)
   * then D ; Psi'  |- t : Psi  and cPsi' subcontext of cPsi
   *)
  let rec strengthen s cPsi = match (s, cPsi) with
    | (Shift (NoCtxShift, _ (* 0 *)), Null) ->
        Null

    | (Shift (CtxShift _psi, _ (* 0 *)), Null) ->
        Null

    | (Shift (NegCtxShift _psi, _ ), CtxVar _psi') ->
        Null

    | (Shift (NoCtxShift, _ ), CtxVar psi) ->
        CtxVar psi

    | (Dot (Head (BVar _k) (* k = 1 *), t), DDec (cPsi, decl)) ->
        let t' = comp t invShift in
          (* Psi  |- x:A dec where decl = x:A
           * Psi' |- t' : Psi
           * Psi' |- x:[t']A dec
           *)
          DDec (strengthen t' cPsi, decSub decl t')

    | (Dot (Undef, t), DDec (cPsi, _)) ->
        strengthen t cPsi

    | (Shift (psi, n), cPsi) ->
        strengthen (Dot (Head (BVar (n + 1)), Shift (psi, n + 1))) cPsi


  (* isId s = B
   *
   * Invariant:
   *
   * If   Psi |- s: Psi', s weakensub
   * then B holds
   * iff s = id, Psi' = Psi
   *)
  let isId s =
    let rec isId' s k' = match s with
      | Shift (NoCtxShift, k)   -> k = k'
      | Dot (Head (BVar n), s') -> n = (k' + 1) && isId' s' (k' + 1)
      | _                       -> false
    in
      isId' s 0 


(* cloInv (U, w) = U[w^-1]
 *
 * Invariant:
 *
 * If Psi |- M <= A
 * Psi |- w  <= Psi'  w pattern subst
 * [w^-1]M defined (without pruning or constraints)
 *
 * then Psi' |- [w^-1]M : [w^-1]A
 *
 * Effects: None
 *)
(*   let cloInv (tM, w) = Clo (tM, invert w) *)



(* compInv s w = t
 *
 * Invariant:
 *
 * If  D ; Psi |- s <= Psi1
 * D ; Psi |- w <= Psi'
 * then  t = s o (w^-1)
 * and   D ; Psi' |- t <= Psi1
 *)
(*  let compInv s w = comp s (invert w) *)

  (* isMId t = B
   *
   * Invariant:
   *
   * If   cD |- t: cD', t weaken_msub
   * then B holds
   * iff t = id, cD' = cD
   *)
  let isMId t =
    let rec isId' s k' = match s with
      | MShift k   -> k = k'
      | MDot (MV n, s') -> n = k' && isId' s' (k' + 1)
      | _                       -> false
    in
      isId' t 0


(* applyMSub n t = MFt'
     
   Invariant: 

     If    D |- t <= D'    n-th element in D' = A[Psi]
     then  Ft' = Ft_n      if  t = Ft_1 .. Ft_n .. ^0
     and D ; [|t|]Psi |- Ft' <= [|t|]A
  *)

let rec applyMSub n t = 
    begin match (n, t) with
  | (1, MDot (ft, _t)) -> ft
  | (n, MDot (_ft, t)) -> applyMSub (n - 1) t
  | (n, MShift k)       -> MV (k + n)
    end 


end
