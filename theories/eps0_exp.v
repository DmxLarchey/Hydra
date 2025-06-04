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
   
      The formula here: 

         https://proofwiki.org/wiki/Ordinal_Exponentiation_via_Cantor_Normal_Form/Limit_Exponents

      (w^a₁.n₁+...+w^aₚ.nₚ)^e = w^(a₁.e) when a₁ > ... > aₚ

      The spec here is probably wrong for α successor
      
    α^0 = 1
    α^(β+1) = α^β.α
    α^γ = sup { α^x | x < γ }
    
    α^(x+y) = α^x.α^y
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


