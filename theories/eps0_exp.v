(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.
From Hydra Require Import utils ordinal ordered eps0 eps0_mult.

Import ListNotations.

Set Implicit Arguments.

#[local] Notation π₁ := proj1_sig.
#[local] Notation π₂ := proj2_sig.

#[local] Hint Resolve eps0_le_refl eps0_lt_succ
                      eps0_zero_least
                      eps0_lt_add_incr
                      eps0_lt_add_right
                      eps0_lt_zero_exp 
                      eps0_zero_lt_omega 
                      eps0_lt_le_weak 
                      eps0_le_add_left 
                      eps0_le_add
                      eps0_le_add_incr_left
                      eps0_le_add_incr_right
: core.

(** Section expo *)

Check eps0_omega_zero.

(** Define exponentiation in CNF 

    α * 0     = 0
    α * (β+1) = α*β + α
    α * γ     = sup { α*x | x < γ }
 
    and 

    α^0 = 1
    α^(β+1) = α^β.α
    α^γ = sup { α^x | x < γ }
    
    are isomorphic

    α^(x+y) = α^x.α^y
    (α^x)^y = α^(x.y)
    
    for the multiplication    
    start with the operation (θ : ε₀) (j : ord) => θ * (1+j)   (struct on θ)
   
         0 * (1+j) = 0
         (ω^⟨α,i⟩+β)) * (1+j) = ω^⟨α,i.j⟩+β  (if 1+j is succ)
         (ω^⟨α,i⟩+β)) * (1+j) = ω^⟨α,i.j⟩      (if j is limit)
   
         then the operation (θ α : ε₀)         => θ * ω^α     (struct on θ)
         
         0 * ω^α = 0
         (ω^⟨γ,n⟩+β) * ω^α = ω^(γ+α)
         
         and finally        (γ α : ε₀)         => γ * α       (struct on α)
   
         γ * 0           = 0
         γ * ω^⟨0,n⟩     = γ * (1+n⟩
         γ * (ω^⟨α,n⟩+β) = (γ*ω^α)*(1+n) + γ*β
         
    for the exponentiation
    start with the operation (θ : ε₀) (j : ord) => θ ^ (1+j)   (struct on θ)
   
         0 ^ (1+j) = 0
         (ω^⟨α,i⟩+β)) ^ (1+j) = ω^⟨α*(1+j),i⟩ + ω^⟨α*k,i⟩*β         (if 1+j = k+1, what if 1+j = 1 ie k = 0 ?) 
         (ω^⟨α,i⟩+β)) ^ (1+j) = ω^⟨α*j⟩      (if j is limit)
   
         then the operation (θ α : ε₀)         => θ ^ ω^α     (struct on θ)
         
         0 ^ ω^α = 0
         (ω^⟨γ,n⟩+β) ^ ω^α = ω^(γ*ω^α)
         
         and finally        (γ α : ε₀)         => γ ^ α       (struct on α)
   
         γ ^ 0           = 1
         γ ^ ω^⟨0,n⟩     = γ ^ (1+n⟩
         γ ^ (ω^⟨α,n⟩+β) = (γ ^ ω^α) ^ (1+n) * γ^β
         
      The formula here: 

         https://proofwiki.org/wiki/Ordinal_Exponentiation_via_Cantor_Normal_Form/Limit_Exponents

      (α^a₁.n₁+...+α^aₚ.nₚ)^β = α^(a₁.β) when a₁ > ... > aₚ > 0 are ordinals 
                                              0 < n₁,...,nₚ < α are ordinals
          and α, β are limit ordinals !!
          
          
      (ω^⟨α,i⟩+β)) ^ (l+n) = (ω^⟨α,i⟩+β)) ^ l * (ω^⟨α,i⟩+β)) ^ n
      
      if 0 < α
      (ω^⟨α,i⟩+β)) ^ 0 = 1
      (ω^⟨α,i⟩+β)) ^ (n+1) = (ω^⟨α,i⟩+β))^n * (ω^⟨α,i⟩+β))
      can we compute a general formula for successor ordinals ?  
      
         (ω^⟨a,i⟩+b) * (ω^⟨e,j⟩+f) = ω^⟨a+e,j⟩ + (ω^⟨a,i⟩+b)*f.
      
      (ω^⟨α,i⟩+β) * (ω^⟨α,i⟩+β) = ω^⟨α.2,i⟩ + ω^⟨α,i⟩*β.
      (ω^⟨α,i⟩+β) * (ω^⟨α,i⟩+β)² = (ω^⟨α,i⟩+β) * (ω^⟨α.2,i⟩ + ω^⟨α,i⟩*β) 
                                 = ω^⟨α.3,i⟩ + (ω^⟨α,i⟩+β)*ω^⟨α,i⟩*β
                                 = ω^⟨α.3,i⟩ + ω^⟨α.2,i⟩*β
      
      try to prove this:
          if k = n+1    then (ω^⟨α,i⟩+β)^(n+1) = ω^⟨α.(n+1),i⟩ + ω^⟨α.n,i⟩*β
          if k is limit then (ω^⟨α,i⟩+β)^k = ω^⟨α.k⟩

      The spec above is probably wrong for α or β successor

    α^a₁ <= α^a₁.n₁+...+α^aₚ.nₚ <= α^a₁.n₁ + α^a₁ = α^a₁.(n₁+1)
    (α^a₁)^β <= (α^a₁.n₁+...+α^aₚ.nₚ)^β
             <= (α^a₁.(n₁+1))^β
             <= (α^a₁)^β = α^(a₁.β)

   we only need (α^a.n)^β = (α^a)^β for 0 < n < α and 0 < a and α, β limit
   PROOF.
   ADMITTED.

   Then there is the case n^β = (α^0.n)^β where β is limit ordinal and 0 < n < α.
   I would say n^β < α:
   Proof.
     by induction on β:
      n^(β+1) = n^β.n is product of two ords < α (α is closure) so < α
      n^γ < α for all γ < β so n^β <= α
   
   ω^(ε₀+1) = ω^ε₀.ω = ε₀.ω > ε₀

   Compute n^β for n < α and β < ε where ε is lfp of ε = α^ε
   assuming n^a already exists for n,a < α

     n^(α^a₁.u + v) with v < α^a₁
   = n^(α^a₁.u).n^v
   = (n^(α^a₁))^u.n^v

     n^(α^a) = 
     n^α = sup { n^i | i < α } <= α
      but >= sup { i | i < α } = α

     if a is limit then n^(α^a) = n^(α^(1+a)) = n^(α^1.α^a) = n^(α.α^a) = (n^α)^(α^a) = α^(α^a) (if 1 < n < α)
        a is succ then  n^(α^(b+1)) = n^(α^b.α) = (n^(α^b))^α =? (α^(α^b))^α = α^(α^b.α) = α^(α^(b+1))

     Can we show than, for 1 < n < α, we have n^(α^a) = α^(α^a) ??

     n^ω = ω  for 2 < n < ω
     n^ω² = sup n^(ω.i) = sup (n^ω)^i = sup ω^i = ω^ω
     n^ω² = ω^ω < ω^ω² so the answer above is NO !!
   


*)


(*

Section eps0_exponentiation.


  Inductive eps0_expo_gr α : ε₀ → ε₀ → Prop :=
    | eps0_expr_gr_0 : eps0_expo_gr α 0₀ 0₀
    | eps0_expr_gr_1 γ n β : β <ε₀ ω^γ → eps0_expo_gr α (ω^⟨γ,n⟩ +₀ β) ω^(γ*₀α).

  Fact eps0_expo_fun α e1 f1 e2 f2 :
    eps0_expo_gr α e1 f1 → eps0_expo_gr α e2 f2 → e1 = e2 → f1 = f2.
  Proof.
    intros [] []; auto.
    + now intros ?%eps0_zero_neq_hnf.
    + symm; now intros ?%eps0_zero_neq_hnf.
    + intros (<- & <- & <-)%eps0_eq_hnf_inv; auto.
  Qed. 

  Definition eps0_expo_pwc e α : sig (eps0_expo_gr α e).
  Proof.
    destruct e as [ | e ] using eps0_hnf_rect.
    + exists 0₀; constructor.
    + exists ω^(e*₀α); constructor; auto.
  Qed.

  Definition eps0_expo e α := proj1_sig (eps0_expo_pwc e α).

  Fact eps0_expo_spec e α : eps0_expo_gr α e (eps0_expo e α).
  Proof. apply (proj2_sig _). Qed.

  Hint Constructors eps0_expo_gr : core.
  Hint Resolve eps0_expo_spec : core.

  Tactic Notation "functionality" :=
    apply eps0_expo_fun with (1 := eps0_expo_spec _ _) (3 := eq_refl); auto.

  Fact eps0_expo_zero e : eps0_expo 0₀ e = 0₀.
  Proof. functionality; constructor. Qed.

  Fact eps0_expo_head a n b e : b <ε₀ ω^a → eps0_expo (ω^⟨a,n⟩ +₀ b) e = ω^(a*₀e).
  Proof. intros; functionality; constructor; auto. Qed.

  Fact eps0_expo_exp_S a n e : eps0_expo ω^⟨a,n⟩ e = ω^(a*₀e).
  Proof. rewrite <- (eps0_add_zero_right ω^⟨_,n⟩), eps0_expo_head; auto. Qed.

  Fact eps0_expo_omega_pos n e : eps0_expo ω^⟨1₀,n⟩ e = ω^e.
  Proof. now rewrite eps0_expo_exp_S, eps0_mult_one_left. Qed.

  Fact eps0_expo_omega a e : eps0_expo ω^a e = ω^(a*₀e).
  Proof. apply eps0_expo_exp_S. Qed.

  (** Need to check more equations *)

End eps0_exponentiation.

*)


