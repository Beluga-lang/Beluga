(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   @author Darin Morrison
*)

(* There may be a better way of arranging the signatures ("module types") and
  structures across unify.ml, trail.ml, and notrail.ml; this is the only thing I stumbled
  across that actually seems to work.

  The functor itself is called Make (hence Unify.Make to other modules (?));
  the instantiations UnifyTrail and UnifyNoTrail (hence Unify.UnifyTrail and
  Unify.UnifyNoTrail to other modules (?)) are declared at the end of this file.
*)

module type TRAIL = sig
  type 'a trail

  val trail : unit -> 'a trail

  val suspend: 'a trail * ('a -> 'b) -> 'b trail
  val resume : 'b trail * 'a trail  * ('b -> 'a) -> unit

  val reset  : 'a trail -> unit
  val mark   : 'a trail -> unit
  val unwind : 'a trail * ('a -> unit) -> unit
  val log    : 'a trail * 'a -> unit
end

module type UNIFY = sig

  open Syntax.Int
  type unifTrail

  (* trailing of variable instantiation *)

  val reset       : unit -> unit
  val mark   : unit -> unit
  val unwind : unit -> unit

  val instantiateMVar : normal option ref * normal * constrnt list -> unit
  val instantiatePVar : head option ref * head * constrnt list -> unit

  val resetAwakenCnstrs : unit -> unit
  val nextCnstr : unit -> constrnt option
  val addConstraint : constrnt list ref * constrnt -> unit
  val solveConstraint : constrnt -> unit


  (* unification *)
  val intersection : psi_hat * (sub * sub) * dctx -> (sub * dctx)

  exception Unify of string

  val unify : psi_hat * nclo * nclo -> unit (* raises Unify *)

end

(* Unification *)
(* Author: Brigitte Pientka *)
(* Trailing is taken from Twelf 1.5 *)
module Make (Trail : TRAIL) =
struct
  
  exception Unify of string
  exception NotInvertible
  
  open Syntax.Int

  (*-------------------------------------------------------------------------- *)
  (* Trailing and Backtracking infrastructure *)

  type action =
      InstNormal of normal option ref
    | InstHead of head option ref
    | Add of cnstr list ref
    | Solve of cnstr * constrnt   (* FIXME: names *)

    type unifTrail = action Trail.trail

    let globalTrail : (action Trail.trail) = Trail.trail()

    let rec undo action = match action with
      | InstNormal refM ->
          refM := None
      | InstHead refH ->
          refH := None
      | Add ({contents= cnstr :: cnstrL} as cnstrs) ->
          cnstrs := cnstrL
      | Solve (cnstr, constrnt) ->
          cnstr := constrnt

    let rec reset () = Trail.reset globalTrail

    let rec mark () = Trail.mark globalTrail

    let rec unwind () = Trail.unwind (globalTrail, undo)

    let rec addConstraint (cnstrs, cnstr) =
          (
            cnstrs := cnstr :: (!cnstrs);
            Trail.log (globalTrail, Add cnstrs)
          )

    let rec solveConstraint ({contents=constrnt} as cnstr) =
          (
            cnstr := Solved;
            Trail.log (globalTrail, Solve (cnstr, constrnt))
          )

    (* trail the given function *)
    let rec trail f =
      let
        _ = mark ()
      and r = f()
      and _ = unwind ()
      in
        r

    (* initial success contination used in prune *)
    let idsc = fun () -> ()
   (* ---------------------------------------------------------------------- *)

    let awakenCnstrs : cnstr list ref = ref []

    let rec resetAwakenCnstrs () = (awakenCnstrs := [])

    let rec nextCnstr () = 
            match !awakenCnstrs
            with | [] -> None
               | cnstr :: cnstrL -> 
                   (awakenCnstrs := cnstrL; Some cnstr)

    let rec instantiatePVar(q, head, cnstrL) = 
        (q := Some head;
         Trail.log (globalTrail, InstHead q);
         awakenCnstrs := cnstrL @ !awakenCnstrs)


    let rec instantiateMVar(u, tM, cnstrL) = 
        (u := Some tM ;
         Trail.log (globalTrail, InstNormal u);
         awakenCnstrs := cnstrL @ !awakenCnstrs)

    (* ---------------------------------------------------------------------- *)
    (* Higher-order unification *)

    (* Preliminaries:

       cD: a context of contextual variables; this is modelled
          implicitly since contextual variables are implemented as
          references.  cD thus describes the current status of
          memory cells for contextual variables.  


       phat : a context of LF bound variables, without their typing
          annotations. While technically cPsi (or hat(cPsi) = phat) does
          not play a role in the unification algorithm itself, this
          will allow us to print normal terms and their types if
          they do not unify.

       tM : normal term that only contains MVar(MInst _, t) and 
           PVar(PInst _, t), that is, all meta-variables and parameter
           variables are subject to instantiation. There are no bound
           contextual variables present, i.e. MVar(Offset _, t),
           PVar(Offset _, t).

           Normal terms are in weak head normal form; the following is
           guaranteed by whnf:

          - all meta-variables are of atomic type, i.e.

              H = (MVar(MInst(r,cPsi, tP, _), t)) where tP = Atom _

          - Since meta-variables are of atomic type, their spine will
            always be Nil, i.e.

              Root(MVar(MInst(r,cPsi, tP, _), t), Nil).

          - Weak head normal forms are either
            (Lam (x,tM) ,s)   or   (Root(H, tS), id).        
     *)

    (* pruneCtx(phat, (t,Psi1), ss) = (cPsi2, s')

       If phat = hat(cPsi)  and  cD ; cPsi |- t  <= Psi1 
                                cD ; cPsi'|- ss <= cPsi   and (ss')^-1 = ss
       then   cD ; Psi1 |- s' <= cPsi2  
              where Psi2 <= Psi1 where s' is a weakened identity substitution,

              and there exists a t' s.t. [t]s' = t' and  cD ; cPsi  |- t'  <= Psi2 , 
              and moreover [ss']^-1 (t') = t'' exists and cD ; cPsi' |- t'' <= Psi2  
     
     *)
    let rec pruneCtx (phat, (t, cPsi1), ss) = match (t, cPsi1) with
         (Shift k, Null) ->  (id, Null)
      | (Shift k, DDec(_, TypDecl(x,tA))) ->  
          pruneCtx(phat, (Dot (Head(BVar (k+1)), Shift (k+1)), cPsi1), ss)
      | (Dot(Head(BVar k), s), DDec (cPsi1, TypDecl(x,tA))) -> 
          let (s', cPsi2) = pruneCtx(phat, (s, cPsi1), ss)
              (* sP1 |- s' <= cPsi2 *)
          in begin
          match bvarSub k ss with 
            | Undef ->  (comp s' shift, cPsi2) (* cPsi1, x:tA |- s' <= cPsi2 *)
            | Head(BVar n) ->                   (* cPsi1, x:tA |- s' <= cPsi2, x:([s']^-1 tA) 
                                                    since tA = [s']([s']^-1 tA) *)
                (dot1 s',  DDec(cPsi2, TypDecl(x, TClo(tA, invert s'))))
          end
      | (Dot(Undef, t), DDec(cPsi1, _)) -> 
          let (s', cPsi2) = pruneCtx (phat, (t, cPsi1), ss)  (* sP1 |- s' <= cPsi2 *)
          in 
          (comp s' shift, cPsi2)

    (* invNorm (cPsi, (tM, s), ss, rOccur) = [ss](tM[s])

       if cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- tM <= tA  (cD ; cPsi |- tM[s] <= tA[s])

          cD ; cPsi'' |- ss  <= cPsi  and ss = [ss']^-1
          cD ; cPsi   |- ss' <= cPsi''

       Effect: raises NotInvertible if [ss](tM[s]) does not exist
               or rOccurs occurs in tM[s]
               does NOT prune MVars in tM[s] according to ss; 
               fails instead
    *)
    let rec invNorm (phat, sM, ss, rOccur) =
          invNorm' (phat, Whnf.whnf sM, ss, rOccur)

    and invNorm' ((cvar, offset) as phat, sM, ss, rOccur) = match sM with
          (Lam (x, tM), s) ->
          Lam (x, invNorm ((cvar, offset +1), (tM, dot1 s), dot1 ss, rOccur))

      | (Root(MVar(Inst(r, cPsi1, tP, cnstrs) as u, t), Nil), s) ->
        (* by invariant tM is in whnf and meta-variables are lowered; 
           hence tS = Nil and s = id *)
          if (rOccur = r) then raise NotInvertible
          else 
            let t' = comp t s (* t' = t, since s = Id *)
            in 
              if isPatSub t' then
               let (s',cPsi2) = pruneCtx (phat, (t', cPsi1), ss)
                     (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                        t' =  t o s 
                        cD ; cPsi |-  t' <= cPsi1 and 
                        cD ; cPsi1 |- s' <= cPsi2 and 
                        cD ; cPsi  |- [t']s' <= cPsi2  *)
               in begin if isId s' then 
                   Root(MVar(u, comp t' ss), Nil) 
                 (* this is what happens in Twelf -- not sure I
                  understand entirely why this is correct *)
                 else 
                   raise NotInvertible
               end
              else (* t' not patsub *) 
                Root(MVar(u, invSub (phat, t', ss, rOccur)), Nil)
               (* this is what happens in Twelf -- not sure I
               understand entirely why this is correct *)

      | (Root(PVar (PInst(r, cPsi1, tA, cnstrs) as q, t), tS),  s) ->
        (* by invariant tM is in whnf and meta-variables are lowered and s = id *)
            let t' = comp t s (* t' = t, since s = Id *)
            in 
              if isPatSub t' then
                let (s',cPsi2) = pruneCtx (phat, (t', cPsi1), ss)
                     (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                        t' =  t o s 
                        cD ; cPsi |-  t' <= cPsi1 and 
                        cD ; cPsi1 |- s' <= cPsi2 and 
                        cD ; cPsi  |- [t']s' <= cPsi2  *)
                in begin
                 if isId s' then (* cPsi1 = cPsi2 *)
                   Root(PVar(q, comp t' ss), 
                        invSpine(phat, (tS,s), ss, rOccur)) 
                 (* this is what happens in Twelf -- not sure I
                  understand entirely why this is correct *)
                 else 
                   raise NotInvertible
               end
              else (* t' not patsub *) 
                Root(PVar(q, invSub (phat, t', ss, rOccur)), 
                     invSpine (phat, (tS,s), ss, rOccur))
               (* this is what happens in Twelf -- not sure I
               understand entirely why this is correct *)               

      | (Root(Proj (PVar(PInst(r, cPsi1, tA, cnstrs) as q,t), i), tS), s) ->
            let t' = comp t s   (* t' = t, since s = Id *)
            in begin
              if isPatSub t' then
               let (s',cPsi2) = pruneCtx (phat, (t', cPsi1), ss)
                     (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                        t' =  t o s r
                        cD ; cPsi |-  t' <= cPsi1 and 
                        cD ; cPsi1 |- s' <= cPsi2 and 
                        cD ; cPsi  |- [t']s' <= cPsi2  *)
               in begin
                 if isId s' then (* cPsi1 = cPsi2 *)
                   Root(Proj (PVar(q, comp t' ss), i),
                        invSpine(phat, (tS,s), ss, rOccur)) 
                 (* this is what happens in Twelf -- not sure I
                  understand entirely why this is correct *)
                 else 
                   raise NotInvertible
               end
              else (* t' not patsub *) 
                Root(Proj (PVar(q, invSub (phat, t', ss, rOccur)), i),
                     invSpine (phat, (tS,s), ss, rOccur))
               (* this is what happens in Twelf -- not sure I
               understand entirely why this is correct *)               
            end

      | (Root (head, tS), s (* = id *)) ->
          Root (invHead (phat, head, ss, rOccur), 
                invSpine (phat, (tS, s), ss, rOccur)) 

    and invSpine (phat, spine, ss, rOccur) = match spine with
         (Nil, s) -> Nil 
      | (App (tM, tS), s) ->
          App (invNorm (phat, (tM, s), ss, rOccur), 
               invSpine (phat, (tS, s), ss, rOccur)) 
      | (SClo (tS, s'), s) ->
          invSpine (phat, (tS, comp s' s), ss, rOccur) 

   (* invHead(phat, head, ss, rOccur) = h' 
       cases for parameter variable and meta-variables taken 
       care in invNorm' *) 
    and invHead (phat, head, ss, rOccur) = match head with
        BVar k ->
          begin match bvarSub k ss
           with Undef -> raise NotInvertible
            | Head(BVar k') -> BVar k'
          end
      | Const _ -> head
      | Proj (BVar k as tB, i) ->
        (match bvarSub k ss
           with Head(BVar k' as head) -> head
             | Undef -> raise NotInvertible)
  
    (* invSub (phat, s, ss, rOccur) = s' 
       
       if phat = hat(cPsi)  and 
          cD ; cPsi  |- s <= cPsi'
          cD ; cPsi''|- ss <= cPsi 
       then s' = [ss]s   if it exists, and 
            cD ; cPsi'' |- [ss]s <= cPsi'

     *)
    and invSub ((cvar, offset) as phat, s, ss, rOccur) =
        match s with
            Shift n ->
                if n < offset 
                  then invSub (phat, Dot (Head(BVar (n+1)), Shift (n+1)), ss, rOccur)
                else comp s ss          (* must be defined *)
      | Dot (Head(BVar(n)), s') ->
        (match bvarSub n ss
           with Undef -> raise NotInvertible
            | ft -> Dot (ft, invSub (phat, s', ss, rOccur)))
      | Dot (Obj (tM), s') ->
          (* below may raise NotInvertible *)
          Dot (Obj (invNorm (phat, (tM, id), ss, rOccur)),
               invSub (phat, s', ss, rOccur))


    (* intersection (phat, (s1, s2), cPsi') = (s', cPsi'')
       s' = s1 /\ s2 (see JICSLP'96 and Pientka's thesis)
       
       Invariant: 
       If   cD ; cPsi |- s1 : cPsi'    s1 patsub
       and  cD ; cPsi |- s2 : cPsi'    s2 patsub
       then cD ; cPsi |- s' : cPsi'' for some cPsi''  
       and  s' patsub
    *)
    let rec intersection (phat, (subst1, subst2), cPsi') = match (subst1, subst2, cPsi') with
         (Dot (Head(BVar k1), s1), Dot (Head(BVar k2), s2), 
                      DDec (cPsi', TypDecl(x,tA))) ->
          if k1 = k2 then 
            begin let (s', cPsi') = intersection (phat, (s1,s2), cPsi')
                (* cD ; cPsi |- s' : cPsi'' where cPsi'' =< cPsi' *)
            in let ss' = invert s'
                (* cD ; cPsi'' |- ss' <= cPsi *)
                (* by assumption:
                   [s1]tA = [s2]tA = tA'  and cD ; cPsi |- tA' <= type *)
                (* tA'' = [s']^-1(tA') = *)
            in let tA'' = TClo(tA, comp s1 ss')
                 (* cD ; cPsi |- s', x/x <= cPsi, x:[s']^-1(tA') *)
            in 
              (dot1 s', DDec (cPsi', TypDecl(x,tA'')))
            end
          else  (* k1 = k2 *)
            begin let (s', cPsi') = intersection (phat, (s1,s2), cPsi')
            in
                (comp s' shift, cPsi')
            end
      | ((Dot _ as s1), Shift n2, cPsi) ->
          intersection (phat, (s1, Dot (Head(BVar (n2+1)), Shift (n2+1))), cPsi)
      | (Shift n1, (Dot _ as s2), cPsi) ->
          intersection (phat, (Dot (Head(BVar (n1+1)), Shift (n1+1)), s2), cPsi)
      | (Shift _ , Shift _, Null) -> (id, Null)
        (* both substitutions are the same number of shifts by invariant *)
        (* all other cases impossible for pattern substitutions *)

    (* prune (phat, (tM, s), ss, rOccur) = tM' 

       If cD ; cPsi |- s <= cPsi'  and  cD ; cPsi' |- tM <= tA  and phat = hat(cPsi)
          ss = (ss')^-1 is a pattern substitution where 

          cD ; cPsi         |- ss' <= cPsi''
          cD ; cPsi'', cPsi* |- ss  <= cPsi    and cD ; cPsi'' |-

       then it returns tM' = [ss]([s]tM) where cD ; cPsi'', cPsi* |- tM' <= tA'
            if 
            - rOccur does not occur in tM
            - there exists a pruning substitution rho s.t. 
              cD' |- rho <= cD   and [ss']^-1([|rho|]([s]tM)) exists.
            - meta-variables u[t] where t is not a pattern substitution
              and [ss](t) does not exist are replaced by v[ss'] and
              a constraint between v[ss'] and u[t o s] is added to the 
              list of constraints

       Effect: - MVars and PVars in tM are pruned;
               - raises Unify if [ss]([|rho|][s]tM) does not exist, 
                 or rOccur occurs in tM
               - meta-variables u[t] where t is not a pattern substitution
                 and [ss] (t) does not exist are delayed and added to
                  the constraints.    


       Improvement: Instead of returning (), we could return 
                    ([ss]([|rho|]([s]tM)); this would possibly avoid
                    traversing [s]tM twice, once for pruning and once
                    for actually applying [ss]  to ([|rho|]([s]tM)).
    *)

    let rec prune  (phat, sM, ss, rOccur, sc) = 
      let qq : sub = ss in
          prune' (phat, Whnf.whnf sM, ss, rOccur, sc)

    and prune' ((cvar, offset) as phat, sM, ss, rOccur, sc) = match sM with
       (Lam (x, tM), s) ->
        let (tM',sc') = prune ((cvar, offset+1), (tM, dot1 s), dot1 ss, rOccur, sc)
        in 
          (Lam(x,tM'), sc')

      | (Root(MVar (Inst(r, cPsi1, tP, cnstrs) as u, t), Nil) as tM, s (* id *)) ->
        (* by invariant: MVars are lowered since tM is in whnf *)
        (if rOccur = r then raise (Unify "Variable occurrence")
          else 
            if isPatSub t then
              begin let (idsub, cPsi2) = pruneCtx (phat, (comp t s, cPsi1), ss)  
                (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= cPsi1
                 cD ; cPsi |-  t o s <= cPsi1 and 
                 cD ; cPsi1 |- idsub <= cPsi2 and 
                 cD ; cPsi |- t o s o idsub <= cPsi2 *)
              in let v = newMVar(cPsi2, tP) (* v::tP[cPsi2] -- may need to shift tP*)
                                          (* should be TClo(tP, invert idsub) *)
              in
                 (tM, fun () -> (instantiateMVar (r, Root(MVar(v, idsub), Nil), !cnstrs) ; sc ()))
                      (* [|v[idsub] / u|] *)
              end 
            else (* s not patsub *)
              (* cD ; cPsi' |- u[t] <= [t]tP, and u::tP[cPsi1]  and cD ; cPsi' |- t <= cPsi1
                 cD ; cPsi  |- s <= cPsi'     and cD ; cPsi''|- ss <= cPsi 

                 s' = [ss]([s]t) and  cD ; cPsi'' |- s' <= cPsi'  *)
              (let s' = invSub(phat, comp t s, ss, rOccur) 
               in 
                 (Root(MVar(u,s'), Nil), sc)
               ))
              (* may raise notInvertible *)
      | (Root(PVar(PInst(r, cPsi1, tA, cnstrs) as q, t) as h, tS), s (* id *)) ->
        (if isPatSub t then
           begin let (idsub, cPsi2) = pruneCtx(phat, (comp t s, cPsi1), ss)  
             (* cD ; cPsi1 |- idsub <= cPsi2 *)
           in let p = newPVar(cPsi2, tA) (* p::tA[cPsi2] *)
           in let sc1 = fun () -> (instantiatePVar (r, PVar(p, idsub), !cnstrs) ; sc())
             (* [|p[idsub] / q|] *)
           in let (tS', sc') = pruneSpine (phat, (tS,s), ss, rOccur, sc1)
           in
             (Root(h, tS'), sc') 
           end 
         else (* s not patsub *) 
           let s' = invSub(phat, comp t s, ss, rOccur) 
             and (tS', sc') = pruneSpine (phat, (tS,s), ss, rOccur, sc)
           in 
             (Root(PVar(q,s'), tS'), sc')
           )

      | (Root(Proj(PVar(PInst(r, cPsi1, tA, cnstrs) as q, t), i) as h, tS), s (* id *)) ->
           if isPatSub t then
              let (idsub, cPsi2) = pruneCtx(phat, (comp t s, cPsi1), ss)  
                (* cD ; cPsi1 |- idsub <= cPsi2 *)
              in let p = newPVar(cPsi2, tA) (* p::tA[cPsi2] *)
              in let sc0 = fun () -> (instantiatePVar (r, PVar(p, idsub), !cnstrs) ; sc())
                (* [|p[idsub] / q|] *)
              in let (tS',sc') = pruneSpine (phat, (tS,s), ss, rOccur, sc0)
              in
                (Root(h, tS'), sc')
            else (* s not patsub *) 
              let s' = invSub(phat, comp t s, ss, rOccur) 
              in let (tS', sc') = pruneSpine (phat, (tS,s), ss, rOccur, sc)
              in 
                (Root(Proj(PVar(q,s'), i), tS'), sc')
              
      | (Root ((*H as*) BVar k, tS), s (* = id *)) ->
          begin match bvarSub k ss
          with Undef -> raise (Unify "Parameter dependency")
            | Head(BVar k as h') -> 
             let (tS',sc') = pruneSpine (phat, (tS, s), ss, rOccur, sc)
             in 
               (Root(h',tS'), sc')
          end

      | (Root (Const _ as h, tS), s (* id *)) ->
          let (tS', sc') = pruneSpine(phat, (tS, s), ss, rOccur, sc)
          in (Root(h, tS'), sc')

      | (Root (Proj (BVar k, i), tS), s (* id *)) ->
          let (tS',sc') = pruneSpine (phat, (tS, s), ss, rOccur, sc) 
          in 
            match bvarSub k ss with 
              Head(BVar k' as h') -> (Root(Proj(h',i), tS') , sc')
            | _ -> raise (Unify "Parameter dependency")

    and pruneSpine (phat, spine, ss, rOccur, sc) = match spine with
        (Nil, s) -> (Nil , sc)

      | (App (tM, tS), s) ->
        let (tM', sc') = prune (phat, (tM, s), ss, rOccur, sc)
        in let (tS', sc'') = pruneSpine (phat, (tS, s), ss, rOccur, sc')
        in 
          (App(tM',tS') , sc'')

      | (SClo (tS, s'), s) ->
          pruneSpine (phat, (tS, comp s' s), ss, rOccur, sc)

  
    (* Unification: 
  
       Precondition: cD describes the current contextual variables

       Given cD ; cPsi1 |- tN <= tA1    and cD ; cPsi |- s1 <= cPsi1
             cD ; cPsi2 |- tM <= tA2    and cD ; cPsi |- s2 <= cPsi2
             cD ; cPsi  |- [s1]tA1 = [s2]tA2 <= type 
       
             hat(cPsi) = phat
      
        unify (phat, (tN,s), (tM,s')) succeeds if there exists a 
        contextual substitution theta s.t. 

        [|theta|]([s1]tN) = [|theta|]([s2]tM) where cD' |- theta <= cD.

        instantiation theta is applied as an effect and () is returned. 
        otherwise exception Unify is raised.
     
       Post-Condition: cD' describes the new and possibly updated
       contextual variables; 

       Other effects: MVars in cD may have been lowered and pruned; Constraints 
       may be added for non-patterns.  

          
     *)      


    let rec unify (phat, sN, sM) = unify' (phat, Whnf.whnf sN, Whnf.whnf sM) 
    
    and unify' (((psi, offset) as phat), sN, sM) = match (sN, sM) with
       ((Lam(x,tN), s1), (Lam(y,tM),s2)) ->
          unify ((psi, offset+1), (tN, dot1 s1), (tM, dot1 s2))

      (* MVar-MVar case *)
      | ((((Root(MVar(Inst(r1, cPsi1, tP1, cnstrs1), t1), Nil) as tM1), s1) as sM1), 
         ((((Root(MVar(Inst(r2, cPsi2, tP2, cnstrs2), t2), Nil) as tM2), s2)) as sM2)) -> 
        (* by invariant: meta-variables are lowered during whnf, s1 = s2 = id *)
          begin let t1' = comp t1 s1 (* cD ; cPsi |- t1' <= cPsi1 *)
          and t2' = comp t2 s2 (* cD ; cPsi |- t2' <= cPsi2 *)
        in
          if r1 = r2 then (* by invariant:  cPsi1 = cPsi2, tP1 = tP2, cnstr1 = cnstr2 *)
            if isPatSub t1' then 
              if isPatSub t2' then
                begin let (s', cPsi') = intersection (phat, (t1', t2'), cPsi1)
                      (* if cD ; cPsi |- t1' <= cPsi1 and cD ; cPsi |- t2' <= cPsi1 
                       then cD ; cPsi1 |- s' <= cPsi' *)
                in let ss' = invert s'
                      (* cD ; cPsi' |- [s']^-1(tP1) <= type *)
                in let w = newMVar (cPsi', TClo(tP1, ss')) 
                     (* w::[s']^-1(tP1)[cPsi1'] in cD'            *)
                     (* cD' ; cPsi1 |- w[s'] <= [s']([s']^-1 tP1) 
                        [|w[s']/u|](u[t]) = [t](w[s'])
                      *)
                in
                  instantiateMVar (r1, Root(MVar(w, s'),Nil), !cnstrs1)
                end
              else addConstraint (cnstrs2, ref (Eqn (phat, Clo sM, Clo sN))) (*XXX double-check *)
            else addConstraint (cnstrs1, ref (Eqn (phat, Clo sN, Clo sM)))  (*XXX double-check *)
          else
            if isPatSub t1' then (* cD ; cPsi' |- t1 <= cPsi1 and cD ; cPsi |- t1 o s1 <= cPsi1 *)
              begin try let ss1 = invert t1' (* cD ; cPsi1 |- ss1 <= cPsi *)
               in let (sM2',sc) = prune (phat, sM2, ss1, r1, idsc) (* sM2 = ([ss1][s2]tM2 *)
               in
                (sc(); instantiateMVar (r1, sM2', !cnstrs1))
              with NotInvertible -> 
                addConstraint (cnstrs1, ref (Eqn (phat, Clo sM1, Clo sM2)))
              end
            else 
              if isPatSub t2' then try begin
                let ss2 = invert t2'(* cD ; cPsi2 |- ss2 <= cPsi *)
                in let (sM1', sc') = prune(phat, sM1, ss2, r2, idsc)
                in
                  (sc'() ; instantiateMVar (r2, sM1', !cnstrs2))
              end with NotInvertible -> 
                addConstraint (cnstrs2, {contents= Eqn (phat, Clo sM2, Clo sM1)})
              else
                (* neither t1' nor t2' are pattern substitutions *)
                let cnstr = ref (Eqn (phat, Clo sM1, Clo sM2))
                in
                  addConstraint (cnstrs1, cnstr)
        end

      (* MVar-normal case *)
      | ((Root(MVar(Inst(r, cPsi, tP, cnstrs) as u, t), tS), s1) as sM1, ((tM2,s2) as sM2)) -> 
        let t' = comp t s1
        in 
          if isPatSub t' then
            try begin
            let ss = invert t'
            in let (sM2', sc) = prune (phat, sM2, ss, r, idsc)    
            in
              sc ();
              instantiateMVar (r, sM2', !cnstrs)
            end
            with NotInvertible -> 
                addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))
          else
            addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))

      (* normal-MVar case *)
      | ((tM1,s1) as sM1, ((Root(MVar (Inst(r, cPsi, tP, cnstrs), t), tS), s2) as sM2)) ->
        let t' = comp t s2
        in 
          if isPatSub t' then 
            try begin let ss = invert t'
            in let (sM1', sc) = prune (phat, sM1, ss, r, idsc)
            in
              sc ();
              instantiateMVar (r, Clo (tM1, ss), !cnstrs)
            end
            with NotInvertible -> 
                addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))
          else
            addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))

      | ((Root(h1,tS1), s1), (Root(h2, tS2), s2)) ->
        (* s1 = s2 = id by whnf *)
        (unifyHead(phat, h1, h2); unifySpine (phat, (tS1, s1), (tS2, s2)))
          
      | (sM1, sM2) -> 
          raise (Unify "Expression clash")

    and unifyHead (phat, head1, head2) = match (head1, head2) with
         (BVar k1, BVar k2) ->
          (if k1 = k2 then ()
           else raise (Unify "Bound variable clash"))
      | (Const c1, Const c2) ->
        if (c1 = c2) then ()
        else raise (Unify "Constant clash")
      | (PVar(PInst(q, _, _, cnstr),s1) as h1, BVar k2) ->
         if isPatSub s1 then 
           (match bvarSub k2 (invert s1) with 
              Head(BVar k2') -> instantiatePVar(q, BVar(k2'), !cnstr)
           | _ -> raise (Unify "Parameter violation"))
         else 
           addConstraint(cnstr, ref (Eqh (phat, h1, BVar k2)))

      | (BVar k1, (PVar(PInst(q, _, _, cnstr), s2) as h1)) ->
        if isPatSub s2 then 
          (match bvarSub k1 (invert s2) with 
             Head(BVar k1') -> instantiatePVar(q, BVar k1', !cnstr)
           | _ -> raise (Unify "Parameter violation"))
        else 
          addConstraint(cnstr, ref (Eqh (phat, BVar k1, h1)))

      | (PVar(PInst(q1, _, _, cnstr1), s1'), PVar(PInst(q2, _, _, cnstr2), s2')) ->
               (* check s1', and s2' are pattern substitutions; possibly generate constraints
                  check intersection(s1',s2'); possibly prune;
                  check q1 = q2 *)
               raise (Unify "Not Implemented")
                
    (* Not Implemented: Cases for projections 

            Proj(BVar k, i), Proj(BVar k', i)
            Proj(BVar k, i), Proj(PVar(q, _,_, cnstr), i)
            Proj(PVar(q, _,_, cnstr), i), Proj(BVar k, i)

            *)


 
    (* unifySpine (phat, (tS1, s1), (tS2, s2)) = ()
     
       Invariant: 
       If   hat(cPsi) = phat 
       and  cPsi |- s1 : cPsi1   cPsi1 |- tS1 : tA1 > tP1 
       and  cPsi |- s2 : cPsi2   cPsi2 |- tS2 : tA2 > tP2 
       and  cPsi |- tA1 [s1] = tA2 [s2]  <= type
       and  cPsi |- tP1 [s1] = tP2 [s2]  
       then if there is an instantiation t :
                 s.t. cPsi |- [|theta|] (tS1 [s1]) == [|theta|](tS2 [s2])
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: MVars may be lowered during whnf,
                      constraints may be added for non-patterns
    *)
    and unifySpine (phat, spine1, spine2) = match (spine1, spine2) with
        ((Nil,_), (Nil,_)) -> ()
      | ((SClo (tS1, s1'), s1), sS) ->
          unifySpine (phat, (tS1, comp s1' s1), sS)
      | (sS, (SClo (tS2, s2'), s2)) -> 
          unifySpine (phat, sS, (tS2, comp s2' s2))
      | ((App (tM1, tS1), s1), (App (tM2, tS2), s2)) ->
        (   unify (phat, (tM1, s1), (tM2, s2)) ; 
            unifySpine (phat, (tS1, s1), (tS2, s2))   )
      (* Nil/App or App/Nil cannot occur by typing invariants *)


    (* Unify pattern fragement, and awake constraints after pattern unification succeeded *)

    let rec unify1 (phat, sM1, sM2) =
          (unify (phat, sM1, sM2); awakeCnstr (nextCnstr ()))

    and unify1' (phat, sM1, sM2) =
          (unify' (phat, sM1, sM2); awakeCnstr (nextCnstr ()))


    and awakeCnstr constrnt = match constrnt with
       None -> ()
      | Some {contents= Solved} -> awakeCnstr (nextCnstr ())
      | Some ({contents= Eqn (phat, tM1, tM2)} as cnstr) ->
          (solveConstraint cnstr;
           unify1 (phat, (tM1, id), (tM2, id)))

      | Some ({contents= Eqh (phat, h1, h2)} as cnstr) ->
          (solveConstraint cnstr;
           unifyHead (phat, h1, h2))

    let unify (phat, sM1, sM2) =
      (resetAwakenCnstrs (); 
       unify1 (phat, sM1, sM2))

end

module UnifyNoTrail = Make (Notrail.Notrail)
module UnifyTrail = Make (Trail.Trail)
