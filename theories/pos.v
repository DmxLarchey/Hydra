(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Utf8.

From Hydra Require Import ordered.
(* pos is the same type as nat but viewed as {1,2,...}
   and not {0,1,...} *)
Definition pos := nat.

Definition pos_add (i j : pos) := S (i+j).
Definition pos_mul (i j : pos) := i*j+i+j.
Definition pos_one := 0.

#[global] Notation "x '+ₚ' y" := (pos_add x y) (at level 31, left associativity).
#[global] Notation "x '*ₚ' y" := (pos_mul x y) (at level 29, left associativity).
#[global] Notation "1ₚ" := pos_one.

Section pos.

  Tactic Notation "solve" "pos" :=
    unfold pos_add, pos_mul, pos_one; lia || ring || auto.

  Implicit Type (i j k pn : pos).

  Local Fact pos_rect (P : pos → Type) :
      P 1ₚ
    → (∀n, P n → P (n +ₚ 1ₚ))
    → ∀n, P n.
  Proof.
    intros H1 H2; apply nat_rect; auto.
    intros; replace (S n) with (n +ₚ 1ₚ); auto.
  Qed.

  Fact pos_le_lt_iff i j : i ≤ j ↔ i = j ∨ i < j.
  Proof. solve pos. Qed.

  Fact pos_lt_sdec i j : sdec lt i j.
  Proof. apply lt_sdec. Qed.

  Fact pos_one_or_succ i : (i = 1ₚ) + { j | i = j +ₚ 1ₚ }.
  Proof. induction i using pos_rect; eauto. Qed.

  Fact pos_add_is_succ i j : { k | i +ₚ j = k +ₚ 1ₚ }.
  Proof. exists (i+j); solve pos. Qed.

  Fact pos_succ_neq_one i : i +ₚ 1ₚ ≠ 1ₚ.
  Proof. solve pos. Qed.

  Fact pos_succ_inj i j : i +ₚ 1ₚ = j +ₚ 1ₚ → i = j.
  Proof. solve pos. Qed.

  Fact pos_add_comm i j : i +ₚ j = j +ₚ i.
  Proof. solve pos. Qed.

  Fact pos_add_assoc i j k : (i +ₚ j) +ₚ k = i +ₚ (j +ₚ k).
  Proof. solve pos. Qed.

  Fact pos_mul_comm i j : i *ₚ j = j *ₚ i.
  Proof. solve pos. Qed.

  Fact pos_mul_assoc i j k : (i *ₚ j) *ₚ k = i *ₚ (j *ₚ k).
  Proof. solve pos. Qed.

  Fact pos_mul_one_left i : 1ₚ *ₚ i = i.
  Proof. solve pos. Qed.

  Fact pos_mul_one_right i : i *ₚ 1ₚ = i.
  Proof. solve pos. Qed.

  Fact pos_mul_distr_left i j k : (i +ₚ j) *ₚ k = i *ₚ k +ₚ j *ₚ k.
  Proof. solve pos. Qed.

  Fact pos_mul_distr_right i j k : k *ₚ (i +ₚ j)  = k *ₚ i +ₚ k *ₚ j.
  Proof. solve pos. Qed.

  Fact pos_one_lt_S i : 1ₚ < S i.
  Proof. solve pos. Qed.

  Fact pos_add_sincr_left i j : j < i +ₚ j.
  Proof. solve pos. Qed.

  Fact pos_add_sincr_right i j : i < i +ₚ j.
  Proof. solve pos. Qed.

  Fact pos_add_incr_left i j : j ≤ i +ₚ j.
  Proof. solve pos. Qed.

  Fact pos_add_mono_lt_left i j k : i < j → i +ₚ k < j +ₚ k.
  Proof. solve pos. Qed.

  Fact pos_one_least i : 1ₚ ≤ i.
  Proof. solve pos. Qed.

  Fact pos_not_lt_one i : ¬ i < 1ₚ.
  Proof. solve pos. Qed.

  Fact pos_lt_iff_le_succ i j : i < j ↔ i +ₚ 1ₚ ≤ j.
  Proof. solve pos. Qed.

  Fact pos_lt_sub i j : i < j → { k | j = i +ₚ k }.
  Proof. exists (j-i-1); solve pos. Qed.

  Fact pos_mul_mono_left i j p k : i < j → p ≤ k → i *ₚ p < j *ₚ k.
  Proof. 
    solve pos; intros H1 H2.
    assert (i*p <= j*k).
    + apply Nat.mul_le_mono; lia.
    + lia.
  Qed.

  Fact pos_mul_mono_right i j p k : i ≤ j → p < k → i *ₚ p < j *ₚ k.
  Proof.
    intros; rewrite (pos_mul_comm i), (pos_mul_comm j); now apply pos_mul_mono_left.
  Qed.

  Fact pos_mul_mono i j p k : i ≤ j → p ≤ k → i *ₚ p ≤ j *ₚ k.
  Proof. 
    solve pos; intros H1 H2.
     assert (i*p <= j*k).
    + apply Nat.mul_le_mono; lia.
    + lia.
  Qed.

End pos.

#[global] Hint Resolve
    pos_one_least
    pos_one_lt_S
    pos_add_sincr_left
    pos_add_sincr_right
    pos_add_incr_left 
    pos_add_mono_lt_left : core. 

