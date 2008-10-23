(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   @author Darin Morrison
*)

(* Unification *)
(* Author: Brigitte Pientka *)
(* Trailing is taken from Twelf 1.5 *)
module Unify = functor (Trail   : TRAIL) ->
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

    in let rec undo action = match action with
      | InstNormal refM ->
          refM := None
      | InstHead refH ->
          refH := None
      | Add (cnstrs as ref(cnstr :: cnstrL)) ->
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

    let rec solveConstraint (cnstr as ref constrnt) =
          (
            cnstr := Solved;
            Trail.log (globalTrail, Solve (cnstr, constrnt))
          )

    (* trail the given function *)
    let rec trail f =
      let
        val _ = mark ()
        val r = f()
        val _ = unwind ()
      in
        r
      end

    (* initial success contination used in prune *)
    val idsc = fn () -> ()
   (* ---------------------------------------------------------------------- *)

    local
      val awakenCnstrs = ref nil : cnstr list ref
    in
      let rec resetAwakenCnstrs () = (awakenCnstrs := nil)

      let rec nextCnstr () = 
            case !awakenCnstrs
              of nil -> None
               | (cnstr :: cnstrL) -> 
                   (awakenCnstrs := cnstrL; Some cnstr)

      let rec instantiatePVar(q, H, cnstrL) = 
        (q := Some H;
         Trail.log (globalTrail, InstHead q);
         awakenCnstrs := cnstrL @ !awakenCnstrs)


      let rec instantiateMVar(u, tM, cnstrL) = 
        (u := Some tM ;
         Trail.log (globalTrail, InstNormal u);
         awakenCnstrs := cnstrL @ !awakenCnstrs)
    end

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
    


    (* pruneCtx(phat, (t,Psi1), ss) = (Psi2, s')

       If phat = hat(cPsi)  and  cD ; cPsi |- t  <= Psi1 
                                cD ; cPsi'|- ss <= cPsi   and (ss')^-1 = ss
       then   cD ; Psi1 |- s' <= Psi2  
              where Psi2 <= Psi1 where s' is a weakened identity substitution,

              and there exists a t' s.t. [t]s' = t' and  cD ; cPsi  |- t'  <= Psi2 , 
              and moreover [ss']^-1 (t') = t'' exists and cD ; cPsi' |- t'' <= Psi2  
     
     *)
    let rec pruneCtx (phat, (t, Psi1), ss) = match (t, Psi1) with
         (Shift k, Null) ->  (id, Null)
      | (Shift k, Psi1 as DDec(_, Decl(x,tA))) ->  
          pruneCtx(phat, (Dot (Head(BVar (k+1)), Shift (k+1)), Psi1), ss)
      | (Dot(Head(BVar k), s), DDec (Psi1, Decl(x,tA))) -> 
        let
          val (s', Psi2) = pruneCtx(phat, (s, Psi1), ss)
              (* sP1 |- s' <= Psi2 *)
        in 
          match bvarSub k ss with 
            Undef ->  (comp s' shift, Psi2) (* Psi1, x:tA |- s' <= Psi2 *)
          | Head(BVar n) ->                   (* Psi1, x:tA |- s' <= Psi2, x:([s']^-1 tA) 
                                                 since tA = [s']([s']^-1 tA) *)
              (dot1 s',  DDec(Psi2, Decl(x, TClo(tA, invert s'))))
        end
      | (Dot(Undef, t), DDec(Psi1, _)) -> 
        let
          val (s', Psi2) = pruneCtx (phat, (t, Psi1), ss)  (* sP1 |- s' <= Psi2 *)
        in 
          (comp s' shift, Psi2)
        end

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

    and invNorm' (phat as (cvar, offset), sM, ss, rOccur) = match sM with
          (Lam (x, tM), s) ->
          Lam (x, invNorm ((cvar, offset +1), (tM, dot1 s), dot1 ss, rOccur))

      | (Root(MVar(u as Inst(r, Psi1, tP, cnstrs), t), Nil), s) ->
        (* by invariant tM is in whnf and meta-variables are lowered; 
           hence tS = Nil and s = id *)
          if (rOccur = r) then raise NotInvertible
          else 
            let
              val t' = comp t s (* t' = t, since s = Id *)
            in 
              if isPatSub (t') then
               let
                 val (s',Psi2) = pruneCtx (phat, (t', Psi1), ss)
                     (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= Psi1
                        t' =  t o s 
                        cD ; cPsi |-  t' <= Psi1 and 
                        cD ; Psi1 |- s' <= Psi2 and 
                        cD ; cPsi  |- [t']s' <= Psi2  *)
               in
                 if isId s' then 
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
                
            end
      | (Root(PVar (q as PInst(r, Psi1, tA, cnstrs),t), tS),  s) ->
        (* by invariant tM is in whnf and meta-variables are lowered and s = id *)
            let
              val t' = comp t s (* t' = t, since s = Id *)
            in 
              if isPatSub (t') then
               let
                 val (s',Psi2) = pruneCtx (phat, (t', Psi1), ss)
                     (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= Psi1
                        t' =  t o s 
                        cD ; cPsi |-  t' <= Psi1 and 
                        cD ; Psi1 |- s' <= Psi2 and 
                        cD ; cPsi  |- [t']s' <= Psi2  *)
               in
                 if isId s' then (* Psi1 = Psi2 *)
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
            end

      | (Root(Proj (PVar(q as PInst(r, Psi1, tA, cnstrs),t), i), tS), s) ->
            let
              val t' = comp t s   (* t' = t, since s = Id *)
            in 
              if isPatSub (t') then
               let
                 val (s',Psi2) = pruneCtx (phat, (t', Psi1), ss)
                     (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= Psi1
                        t' =  t o s r
                        cD ; cPsi |-  t' <= Psi1 and 
                        cD ; Psi1 |- s' <= Psi2 and 
                        cD ; cPsi  |- [t']s' <= Psi2  *)
               in
                 if isId s' then (* Psi1 = Psi2 *)
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

      | (Root (H, tS), s (* = id *)) ->
          Root (invHead (phat, H, ss, rOccur), 
                invSpine (phat, (tS, s), ss, rOccur)) 

    and invSpine (phat, spine, ss, rOccur) = match spine with
         (Nil, s) -> Nil 
      | (App (tM, tS), s) ->
          App (invNorm (phat, (tM, s), ss, rOccur), 
               invSpine (phat, (tS, s), ss, rOccur)) 
      | (SClo (tS, s'), s) ->
          invSpine (phat, (tS, comp s' s), ss, rOccur) 

   (* invHead(phat, H, ss, rOccur) = H' 
       cases for parameter variable and meta-variables taken 
       care in invNorm' *) 
    and invHead (phat, head, ss, rOccur) = match head with
        BVar k ->
        (case bvarSub k ss
           of Undef -> raise NotInvertible
            | Head(BVar k') -> BVar k')
      | Const _ -> head
      | Proj (tB as BVar k, i) ->
        (case bvarSub k ss
           of Head(H as BVar k') -> H
             | Undef -> raise NotInvertible)
  
    (* invSub (phat, s, ss, rOccur) = s' 
       
       if phat = hat(cPsi)  and 
          cD ; cPsi  |- s <= cPsi'
          cD ; cPsi''|- ss <= cPsi 
       then s' = [ss]s   if it exists, and 
            cD ; cPsi'' |- [ss]s <= cPsi'

     *)
    and invSub (phat as (cvar, offset), s, ss, rOccur) =
        match s with
            Shift n ->
                if n < offset 
                  then invSub (phat, Dot (Head(BVar (n+1)), Shift (n+1)), ss, rOccur)
                else comp s ss          (* must be defined *)
      | Dot (Head(BVar(n)), s') ->
        (case bvarSub n ss
           of Undef -> raise NotInvertible
            | Ft -> Dot (Ft, invSub (phat, s', ss, rOccur)))
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
                      DDec (cPsi', Decl(x,tA))) ->
          if k1 = k2 then 
            let val (s', cPsi') = intersection (phat, (s1,s2), cPsi')
                (* cD ; cPsi |- s' : cPsi'' where cPsi'' =< cPsi' *)
                val ss' = invert s'
                (* cD ; cPsi'' |- ss' <= cPsi *)
                (* by assumption:
                   [s1]tA = [s2]tA = tA'  and cD ; cPsi |- tA' <= type *)
                (* tA'' = [s']^-1(tA') = *)
                val tA'' = TClo(tA, comp s1 ss')
                 (* cD ; cPsi |- s', x/x <= cPsi, x:[s']^-1(tA') *)
            in 
              (dot1 s', DDec (cPsi', Decl(x,tA'')))
            end
          else  (* k1 = k2 *)
            let
               val (s', cPsi') = intersection (phat, (s1,s2), cPsi')
            in
                (comp s' shift, cPsi')
            end
      | (s1 as Dot _, Shift n2, cPsi) ->
          intersection (phat, (s1, Dot (Head(BVar (n2+1)), Shift (n2+1))), cPsi)
      | (Shift n1, s2 as Dot _, cPsi) ->
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
          prune' (phat, Whnf.whnf sM, ss, rOccur, sc)
    
    and prune' (phat as (cvar, offset), sM, ss, rOccur, sc) = match sM with
       (Lam (x, tM), s) ->
        let 
          val (tM',sc') = prune ((cvar, offset+1), (tM, dot1 s), dot1 ss, rOccur, sc)
        in 
          (Lam(x,tM'), sc')
        end
      | (tM as Root(MVar (u as Inst(r, Psi1, tP, cnstrs), t), Nil), s (* id *)) ->
        (* by invariant: MVars are lowered since tM is in whnf *)
        (if rOccur = r then raise Unify "Variable occurrence"
          else 
            if isPatSub t then
              let
                val (idsub, Psi2) = pruneCtx (phat, (comp t s, Psi1), ss)  
                (* cD ; cPsi |- s <= cPsi'   cD ; cPsi' |- t <= Psi1
                 cD ; cPsi |-  t o s <= Psi1 and 
                 cD ; Psi1 |- idsub <= Psi2 and 
                 cD ; cPsi |- t o s o idsub <= Psi2 *)
                 val v = newMVar(Psi2, tP) (* v::tP[Psi2] -- may need to shift tP*)
                                          (* should be TClo(tP, invert idsub) *)
               in
                 (tM, fn () -> (instantiateMVar (r, Root(MVar(v, idsub), Nil), !cnstrs) ; sc ()))
                      (* [|v[idsub] / u|] *)
              end 
            else (* s not patsub *)
              (* cD ; cPsi' |- u[t] <= [t]tP, and u::tP[Psi1]  and cD ; cPsi' |- t <= Psi1
                 cD ; cPsi  |- s <= cPsi'     and cD ; cPsi''|- ss <= cPsi 

                 s' = [ss]([s]t) and  cD ; cPsi'' |- s' <= cPsi'  *)
              (let
                 val s' = invSub(phat, comp t s, ss, rOccur) 
               in 
                 (Root(MVar(u,s'), Nil), sc)
               end))
              (* may raise notInvertible *)
      | (Root(H as PVar(q as PInst(r, Psi1, tA, cnstrs), t), tS), s (* id *)) ->
        (if isPatSub t then
           let
             val (idsub, Psi2) = pruneCtx(phat, (comp t s, Psi1), ss)  
             (* cD ; Psi1 |- idsub <= Psi2 *)
             val p = newPVar(Psi2, tA) (* p::tA[Psi2] *)
             val sc1 = fn () ->  (instantiatePVar (r, PVar(p, idsub), !cnstrs) ; sc())
             (* [|p[idsub] / q|] *)
             val (tS', sc') = pruneSpine (phat, (tS,s), ss, rOccur, sc1)
           in
             (Root(H, tS'), sc') 
           end 
         else (* s not patsub *) 
           let
             val s' = invSub(phat, comp t s, ss, rOccur) 
             val (tS', sc') = pruneSpine (phat, (tS,s), ss, rOccur, sc)
           in 
             (Root(PVar(q,s'), tS'), sc')
           end)

      | (Root(H as Proj(PVar(q as PInst(r, Psi1, tA, cnstrs), t), i), tS), s (* id *)) ->
       (if isPatSub t then
          let
            val (idsub, Psi2) = pruneCtx(phat, (comp t s, Psi1), ss)  
            (* cD ; Psi1 |- idsub <= Psi2 *)
            val p = newPVar(Psi2, tA) (* p::tA[Psi2] *)
            val sc0 = fn () -> (instantiatePVar (r, PVar(p, idsub), !cnstrs) ; sc())
            (* [|p[idsub] / q|] *)
            val (tS',sc') = pruneSpine (phat, (tS,s), ss, rOccur, sc0)
          in
            (Root(H, tS'), sc')
          end 
        else (* s not patsub *) 
          let
            val s' = invSub(phat, comp t s, ss, rOccur) 
            val (tS', sc') = pruneSpine (phat, (tS,s), ss, rOccur, sc)
          in 
            (Root(Proj(PVar(q,s'), i), tS'), sc')
          end)
              
      | (Root (H as BVar k, tS), s (* = id *)) ->
        (case bvarSub k ss
           of Undef -> raise Unify "Parameter dependency"
            | Head(H' as BVar k) -> 
             let
               val (tS',sc') = pruneSpine (phat, (tS, s), ss, rOccur, sc)
             in 
               (Root(H',tS'), sc')
             end)

      | (Root (H as Const _, tS), s (* id *)) ->
        let
           val (tS', sc') = pruneSpine(phat, (tS, s), ss, rOccur, sc)
        in 
           (Root(H, tS'), sc')
        end

      | (Root (Proj (BVar(k), i), tS), s (* id *)) ->
        let 
          val (tS',sc') = pruneSpine (phat, (tS, s), ss, rOccur, sc) 
        in 
          match bvarSub k ss with 
            Head(H' as (BVar k')) -> (Root(Proj(H',i), tS') , sc')
          | _ -> raise Unify "Parameter dependency"
        end

    and pruneSpine (phat, spine, ss, rOccur, sc) = match spine with
        (Nil, s) -> (Nil , sc)
      | (App (tM, tS), s) ->
        let
           val (tM', sc') = prune (phat, (tM, s), ss, rOccur, sc)
           val (tS', sc'') = pruneSpine (phat, (tS, s), ss, rOccur, sc')
        in 
          (App(tM',tS') , sc'')
        end
      | (SClo (tS, s'), s) ->
          pruneSpine (phat, (tS, comp s' s), ss, rOccur, sc)

  
    (* Unification: 
  
       Precondition: cD describes the current contextual variables

       Given cD ; Psi1 |- tN <= tA1    and cD ; cPsi |- s1 <= Psi1
             cD ; Psi2 |- tM <= tA2    and cD ; cPsi |- s2 <= Psi2
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
    
    and unify' (phat as (psi, offset), sN, sM) = match (sN, sM) with
       ((Lam(x,tN), s1), (Lam(y,tM),s2)) ->
          unify ((psi, offset+1), (tN, dot1 s1), (tM, dot1 s2))

      (* MVar-MVar case *)
      | (sM1 as (tM1 as Root(MVar(u as Inst(r1, Psi1, tP1, cnstrs1), t1), Nil) ,s1), 
                      sM2 as (tM2 as Root(MVar(v as Inst(r2, Psi2, tP2, cnstrs2), t2), Nil), s2)) -> 
        (* by invariant: meta-variables are lowered during whnf, s1 = s2 = id *)
        let
          val t1' = comp t1 s1 (* cD ; cPsi |- t1' <= Psi1 *)
          val t2' = comp t2 s2 (* cD ; cPsi |- t2' <= Psi2 *)
        in
          if r1 = r2 then (* by invariant:  Psi1 = Psi2, tP1 = tP2, cnstr1 = cnstr2 *)
            if isPatSub(t1') then 
              if isPatSub(t2') then
                let
                  val (s', cPsi') = intersection (phat, (t1', t2'), Psi1)
                      (* if cD ; cPsi |- t1' <= Psi1 and cD ; cPsi |- t2' <= Psi1 
                       then cD ; Psi1 |- s' <= cPsi' *)
                  val ss' = invert(s')
                      (* cD ; cPsi' |- [s']^-1(tP1) <= type *)
                  val w = newMVar (cPsi', TClo(tP1, ss')) 
                     (* w::[s']^-1(tP1)[Psi1'] in cD'            *)
                     (* cD' ; Psi1 |- w[s'] <= [s']([s']^-1 tP1) 
                        [|w[s']/u|](u[t]) = [t](w[s'])
                      *)
                in
                  instantiateMVar (r1, Root(MVar(w, s'),Nil), !cnstrs1)
                end
              else addConstraint (cnstrs2, ref (Eqn (phat, Clo sM2, Clo sM1)))
            else addConstraint (cnstrs1, ref (Eqn (phat, Clo sM1, Clo sM2)))
          else
            if isPatSub(t1') then (* cD ; cPsi' |- t1 <= Psi1 and cD ; cPsi |- t1 o s1 <= Psi1 *)
               let
                val ss1 = invert (t1') (* cD ; Psi1 |- ss1 <= cPsi *)
                val (sM2',sc) = prune (phat, sM2, ss1, r1, idsc) (* sM2 = ([ss1][s2]tM2 *)
              in
                (sc(); instantiateMVar (r1, sM2', !cnstrs1))
              end
              handle NotInvertible -> 
                addConstraint (cnstrs1, ref (Eqn (phat, Clo sM1, Clo sM2)))
            else 
              if isPatSub(t2') then 
                let
                  val ss2 = invert t2'(* cD ; Psi2 |- ss2 <= cPsi *)
                  val (sM1', sc') = prune(phat, sM1, ss2, r2, idsc)
                in
                  (sc'() ; instantiateMVar (r2, sM1', !cnstrs2))
                end
              handle NotInvertible -> 
                addConstraint (cnstrs2, ref (Eqn (phat, Clo sM2, Clo sM1)))
              else
                (* neither t1' nor t2' are pattern substitutions *)
                let
                  val cnstr = ref (Eqn (phat, Clo sM1, Clo sM2))
                in
                  addConstraint (cnstrs1, cnstr)
                end
        end

      (* MVar-normal case *)
      | (sM1 as (Root(MVar(u as Inst(r, cPsi, tP, cnstrs), t), tS), s1), sM2 as (tM2,s2)) -> 
        let
          val t' = comp t s1
        in 
          if isPatSub t' then 
            let 
              val ss = invert t'
              val (sM2', sc) = prune (phat, sM2, ss, r, idsc)    
            in
              sc ();
              instantiateMVar (r, sM2', !cnstrs)
            end
              handle NotInvertible -> 
                addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))
          else
            addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))
        end

      (* normal-MVar case *)
      | (sM1 as (tM1,s1), sM2 as (Root(MVar (u as Inst(r, cPsi, tP, cnstrs), t), tS), s2)) ->
        let
          val t' = comp t s2
        in 
          if isPatSub t' then 
            let
              val ss = invert t'
              val (sM1', sc) = prune (phat, sM1, ss, r, idsc)
            in
              sc ();
              instantiateMVar (r, Clo (tM1, ss), !cnstrs)
            end
              handle NotInvertible -> 
                addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))
          else
            addConstraint (cnstrs, ref (Eqn (phat, Clo sM1, Clo sM2)))
        end

      | ((Root(H1,tS1), s1), (Root(H2, tS2), s2)) ->
        (* s1 = s2 = id by whnf *)
        (unifyHead(phat, H1, H2); unifySpine (phat, (tS1, s1), (tS2, s2)))
          
      | (sM1, sM2) -> 
          raise Unify ("Expression clash")

    and unifyHead (phat, head1, head2) = match (head1, head2) with
         (BVar k1, BVar k2) ->
          (if k1 = k2 then ()
           else raise Unify "Bound variable clash")
      | (Const c1, Const c2) ->
        if (c1 = c2) then ()
        else raise Unify "Constant clash"
      | (H1 as PVar(PInst(q, _, _, cnstr),s1), BVar k2) ->
         if isPatSub s1 then 
           (match bvarSub k2 (invert s1) with 
              Head(H' as (BVar k2')) -> instantiatePVar(q, BVar(k2'), !cnstr)
           | _ -> raise Unify "Parameter violation")
         else 
           addConstraint(cnstr, ref (Eqh (phat, H1, BVar k2)))

      | ((BVar k1), (H1 as PVar(PInst(q, _, _, cnstr), s2))) ->
        if isPatSub s2 then 
          (match bvarSub k1 (invert s2) with 
             Head(H' as BVar k1') -> instantiatePVar(q, BVar k1', !cnstr)
           | _ -> raise Unify "Parameter violation")
        else 
          addConstraint(cnstr, ref (Eqh (phat, BVar k1, H1)))

      | (PVar(PInst(q1, _, _, cnstr1), s1'), PVar(PInst(q2, _, _, cnstr2), s2')) ->
               (* check s1', and s2' are pattern substitutions; possibly generate constraints
                  check intersection(s1',s2'); possibly prune;
                  check q1 = q2 *)
               raise Unify "Not Implemented"
                
    (* Not Implemented: Cases for projections 

            Proj(BVar k, i), Proj(BVar k', i)
            Proj(BVar k, i), Proj(PVar(q, _,_, cnstr), i)
            Proj(PVar(q, _,_, cnstr), i), Proj(BVar k, i)

            *)


 
    (* unifySpine (phat, (tS1, s1), (tS2, s2)) = ()
     
       Invariant: 
       If   hat(cPsi) = phat 
       and  cPsi |- s1 : Psi1   Psi1 |- tS1 : tA1 > tP1 
       and  cPsi |- s2 : Psi2   Psi2 |- tS2 : tA2 > tP2 
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
      | Some(ref Solved) -> awakeCnstr (nextCnstr ())
      | Some(cnstr as ref (Eqn (phat, tM1, tM2))) ->
          (solveConstraint cnstr;
           unify1 (phat, (tM1, id), (tM2, id)))

      | Some(cnstr as ref (Eqh (phat, H1, H2))) ->
          (solveConstraint cnstr;
           unifyHead (phat, H1, H2))

    let unify (phat, sM1, sM2) =
      (resetAwakenCnstrs (); 
       unify1 (phat, sM1, sM2))

end

module UnifyNoTrail = Unify (NoTrail)

module UnifyTrail = Unify(Trail)
