(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Utf8.

(* pos is the same type as nat but viewed as {1,2,...}
   and not {0,1,...} *)
Definition pos := nat.

Definition pos_add (i j : pos) := S (i+j).
Definition pos_mul (i j : pos) := i*j+i+j.
Definition pos_one := 0.

#[global] Notation "x '+ₚ' y" := (pos_add x y) (at level 31, left associativity).
#[global] Notation "x '*ₚ' y" := (pos_mul x y) (at level 29, left associativity).
#[global] Notation "1ₚ" := pos_one.

Tactic Notation "solve" "pos" :=
  unfold pos_add, pos_mul, pos_one; lia || ring || auto.

Fact pos_one_or_succ i : (i = 1ₚ) + { j | i = j +ₚ 1ₚ }.
Proof. destruct i as [ | i ]; auto; right; exists i; solve pos. Qed.

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

Fact pos_not_lt_one i : ¬ i < 1ₚ.
Proof. solve pos. Qed.

Fact pos_lt_sub i j : i < j → { k | j = i +ₚ k }.
Proof. exists (j-i-1); solve pos. Qed.

#[global] Hint Resolve
    pos_one_lt_S
    pos_add_sincr_left
    pos_add_sincr_right
    pos_add_incr_left 
    pos_add_mono_lt_left : core. 

