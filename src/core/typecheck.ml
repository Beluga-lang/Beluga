(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
   @author Darin Morrison
*)



    (* check (Δ, Ψ, (M, s₁), (A, s₂)) = ()

       Invariant:

       If   Δ ; Ψ ⊢ s₁ ⇐ Ψ₁   
       and  Δ ; Ψ ⊢ s₂ ⇐ Ψ₂    Ψ₂ ⊢ A ⇐ type

       returns () if there exists an A' s.t.    

  	    Δ ; Ψ₁ ⊢ M ⇐ A' 
       and  Δ ; Ψ  ⊢ A'[s₁] = A[s₂] : type
       and  Δ ; Ψ  ⊢ M[s₁] ⇐ A'[s₁]

       otherwise exception Error is raised
    *)

    (* checkSpine (Δ, Ψ, (S, s1), (A, s2), Ps) = ()

       Invariant:

       If   Δ ; Ψ  ⊢ s₁ ⇐ Ψ1  
       and  Δ ; Ψ  ⊢ s₂ ⇐ Ψ2
       and  Δ ; Ψ₂ ⊢ A  ⇐ type
       and (A, s₂) in whnf  

       then succeeds if there exists A', P' s.t.

            Δ ; Ψ₁ ⊢ S  : A' > P'
       and  Δ ; Ψ  ⊢ s' : Ψ'
       and  Δ ; Ψ' ⊢ A'             ⇐ type
       and  Δ ; Ψ  ⊢ A'[s'] = A[s₂] ⇐ type
       and  Δ ; Ψ  ⊢ P'[s'] = Ps    ⇐ type

    *)
