(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils pos eps0 eps0_least_split eps0_fseq.

Set Implicit Arguments.

Section upper_bound.

  Variables (X : Type) (R : X → X → Prop).
  
  Implicit Type (P : X → Prop).

  Definition ub P u := ∀x, P x → R x u.
  Definition lub P u := ub P u ∧ ∀v, ub P v → R u v.
  
  Fact ub_mono P Q : (∀x, P x → Q x) → ∀u, ub Q u → ub P u.
  Proof. intros H ? ? ? ?%H; auto. Qed.
  
  Fact lub_uniq P u v : lub P u → lub P v → R u v ∧ R v u.
  Proof.
    intros H1 H2; split.
    + apply H1, H2.
    + apply H2, H1.
  Qed.

  Hypothesis (R_refl : reflexive _ R)
             (R_trans : transitive R).

  Fact lub_iff P u : lub P u ↔ ∀v, ub P v ↔ R u v.
  Proof.
    split.
    + intros Hu v; split.
      * apply Hu.
      * intros Huv x Hx.
        now apply R_trans with (2 := Huv), Hu.
    + intros Hu; split.
      * apply Hu, R_refl.
      * intro; apply Hu.
  Qed.
  
End upper_bound.

Theorem eps0_lub_simpler P e :
    ub eps0_le P e
  → (∀ u : ε₀, u <ε₀ e → ∃ v : ε₀, P v ∧ u <ε₀ v)
  → lub eps0_le P e. 
Proof.
  intros H1 H2; split; auto.
  intros v Hv.
  destruct (eps0_le_lt_dec e v) as [ | (w & ? & Hw)%H2 ]; auto.
  destruct (@eps0_lt_irrefl v).
  apply eps0_lt_le_trans with (1 := Hw), Hv; auto.
Qed.

(* for a limit ordinal e, it is the ≤ε₀-lub of its fundemental sequence *) 
Theorem eps0_fseq_lub e l : lub eps0_le (λ x, ∃n, x = @eps0_fseq e l n) e.
Proof.
  apply eps0_lub_simpler.
  + intros x (n & ->); left; apply eps0_fseq_lt.
  + intros u Hu.
    apply eps0_lt_fseq_inv with (l := l) in Hu as (n & Hn); auto.
    exists (eps0_fseq l n); eauto.
Qed.

#[local] Hint Resolve eps0_fseq_lt : core.

(* A limit ordinal is the ≤ε₀-lub of <ε₀-smaller ordinals.
   This is also the case of 0₀. But of course, this is not
   the case for successor ordinals *)
Theorem eps0_is_limit_lub e : eps0_is_limit e → lub eps0_le (λ x, x <ε₀ e) e.
Proof.
  intros l; apply eps0_lub_simpler.
  + now left.
  + intros ? []%(eps0_lt_fseq_inv l); eauto.
Qed.

(* For a successor ordinal S₀ e, the lub of its <ε₀-smaller ordinals
   is e (and not S₀ e). *)
Theorem eps0_is_succ_lub e : lub eps0_le (λ x, x <ε₀ S₀ e) e.
Proof.
  split.
  + now intros ? ?%eps0_succ_next_inv.
  + intros v Hv; apply Hv, eps0_lt_succ.
Qed.

Hint Resolve eps0_add_mono eps0_add_mono_right eps0_lt_le_weak : core.

(** We need the fundemental sequence to work with lubs 
    constructivelly !!! *)

(** Addition respects the limit *)
Theorem eps0_add_lub a e :
    eps0_is_limit e
  → lub eps0_le (λ x, ∃u, x = a +₀ u ∧ u <ε₀ e) (a +₀ e).
Proof.
  intros l; apply eps0_lub_simpler.
  + intros ? (? & -> & ?); auto.
  + intros v [ H1 | (g & -> & Hg) ]%eps0_lt_add_inv_add.
    * exists a; split; auto.
      exists 0₀; rewrite eps0_add_zero_right; auto.
    * apply eps0_lt_fseq_inv with (l := l) in Hg as (n & Hn).
      exists (a+₀eps0_fseq l n); split; auto.
      exists (eps0_fseq l n); split; auto.
Qed.

(* #[local] Hint Resolve eps0_fseq_lt : core. *)
#[local] Hint Resolve eps0_mult_mono eps0_le_refl : core.

(** Maybe we can factor out these two proofs !! *)

Corollary eps0_add_limit a e :
    eps0_is_limit e
  → lub eps0_le (λ x, ∃u, x = a +₀ u ∧ u <ε₀ e) (a +₀ e).
Proof.
  intros l; apply eps0_lub_simpler.
  + intros ? (? & -> & ?); auto.
  + intros v Hv.
    generalize (eps0_add_is_limit a l); intros l'.
    apply eps0_lt_fseq_inv with (l := l') in Hv.
    destruct Hv as (n & Hn).
    exists (a+₀eps0_fseq l n); split.
    * exists (eps0_fseq l n); auto.
    * apply eps0_lt_le_trans with (2 := eps0_fseq_add _ l l' _); auto.
Qed.

Corollary eps0_mult_limit a e :
    eps0_is_limit e
  → lub eps0_le (λ x, ∃u, x = a *₀ u ∧ u <ε₀ e) (a *₀ e).
Proof.
  intros l; apply eps0_lub_simpler.
  + intros ? (? & -> & ?); auto.
  + intros v Hv.
    destruct (eps0_zero_or_pos a) as [ -> | Ha ].
    1: rewrite eps0_mult_zero_left in Hv; now apply eps0_zero_not_gt in Hv.
    generalize (eps0_mult_is_limit Ha l); intros l'.
    apply eps0_lt_fseq_inv with (l := l') in Hv.
    destruct Hv as (n & Hn).
    exists (a*₀eps0_fseq l n); split.
    * exists (eps0_fseq l n); auto.
    * apply eps0_lt_le_trans with (2 := eps0_fseq_mult _ l l' _); auto.
Qed.

Check eps0_add_zero_right.
Check eps0_add_succ_right.
Check eps0_add_limit.

Check eps0_mult_zero_right.
Check eps0_mult_succ_right.
Check eps0_mult_limit.

Definition is_lub {X} (R : X → X → Prop) (P : X → Prop) u := ∀v, (∀x, P x → R x v) ↔ R u v.

#[local] Hint Resolve eps0_lt_le_trans eps0_le_refl eps0_le_trans : core.

(* for a limit ordinal e, it is the ≤ε₀-lub of its fundemental sequence *) 
Theorem eps0_fseq_is_lub e l : is_lub eps0_le (λ x, ∃n, x = @eps0_fseq e l n) e.
Proof.
  red; apply lub_iff; auto.
  1,2: red; eauto.
  apply eps0_fseq_lub.
Qed.



