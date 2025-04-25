(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Euclid Lia Utf8.

From Hydra Require Import ordered.

Definition ord := nat.

Definition ord_zero : ord := 0.
Definition ord_one : ord := 1.
Definition ord_lt (i j : ord) := (lt i j).
Definition ord_le (i j : ord) := (le i j).

#[global] Notation "x '<ₒ' y" := (ord_lt x y) (at level 70, no associativity, format "x  <ₒ  y").
#[global] Notation "x '≤ₒ' y" := (ord_le x y) (at level 70, no associativity, format "x  ≤ₒ  y").
#[global] Notation "0ₒ" := ord_zero.
#[global] Notation "1ₒ" := ord_one.

Definition ord_add (i j : ord) := i+j.
Definition ord_mul (i j : ord) := i*j.

#[global] Notation "x '+ₒ' y" := (ord_add x y) (at level 31, left associativity).
#[global] Notation "x '*ₒ' y" := (ord_mul x y) (at level 29, left associativity).


(*
(* When i encodes 1ₒ +ₒ i
    and j encodes 1ₒ +ₒ j
    then i +ₚ j encodes (1 +ₒ i) +ₒ (1 +ₒ j) *) 
Definition pos_add i j := i +ₒ 1ₒ +ₒ j.
Definition pos_mul i j := i *ₒ j +ₒ i +ₒ j.

#[global] Notation "x '+ₚ' y" := (pos_add x y) (at level 31, left associativity).
#[global] Notation "x '*ₚ' y" := (pos_mul x y) (at level 29, left associativity).

*)

Section ord.

  Tactic Notation "solve" "ord" :=
    unfold (* pos_add, pos_mul, *) ord_one, ord_zero, ord_add, ord_mul, ord_lt, ord_le; lia || ring || auto.

  Implicit Type (i j k p n : ord).

  Local Fact ord_rect (P : ord → Type) :
      P 0ₒ
    → (∀n, P n → P (1ₒ + n ))
    → ∀n, P n.
  Proof. apply nat_rect. Qed.
  
  Fact ord_lt_wf : well_founded ord_lt.
  Proof. apply lt_wf. Qed.
  
  Fact ord_lt_irrefl i : ¬ i <ₒ i.
  Proof. solve ord. Qed.
  
  Fact ord_lt_trans i j k : i <ₒ j → j <ₒ k → i <ₒ k.
  Proof. solve ord. Qed.

  Fact ord_le_lt_iff i j : i ≤ₒ j ↔ i = j ∨ i <ₒ j.
  Proof. solve ord. Qed.

  Fact ord_lt_sdec i j : sdec ord_lt i j.
  Proof. apply lt_sdec. Qed.
  
  Fact ord_zero_or_1add i : (i = 0ₒ) + { j | i = 1ₒ +ₒ j }.
  Proof. induction i using ord_rect; eauto. Qed.
  
  Fact ord_sub i j : i ≤ₒ j → { k | j = i +ₒ k }.
  Proof. intros H; exists (j-i); revert H; solve ord. Qed.
  

(*
  Fact pos_add_is_1add i j : { k | i +ₚ j = 1ₒ +ₒ k }.
  Proof. exists (i +ₒ j); solve ord. Qed.
  *)

(*
  Fact pos_succ_neq_one i : i +ₚ 1ₚ ≠ 1ₚ.
  Proof. solve pos. Qed.
  *)
  
  Fact ord_add_zero_left i : 0ₒ +ₒ i = i.
  Proof. solve ord. Qed.
  
  Fact ord_add_zero_right i : i +ₒ 0ₒ = i.
  Proof. solve ord. Qed.
  
  Fact ord_le_zero_least i : 0ₒ ≤ₒ i.
  Proof. solve ord. Qed.

  Fact ord_zero_lt_one i : 0ₒ <ₒ 1ₒ.
  Proof. solve ord. Qed.
  
  Fact ord_lt_one_is_zero i : i <ₒ 1ₒ → i = 0ₒ.
  Proof. solve ord. Qed.
  
  Fact ord_add_mono_le_left i j k : i ≤ₒ j → i +ₒ k ≤ₒ j +ₒ k.
  Proof. solve ord. Qed.
  
  Fact ord_add_mono_lt_right i j k : i <ₒ j → k +ₒ i <ₒ k +ₒ j.
  Proof. solve ord. Qed.
  
  Fact ord_add_assoc i j k : (i +ₒ j) +ₒ k = i +ₒ (j +ₒ k).
  Proof. solve ord. Qed.
  
  Fact ord_mul_assoc i j k : (i *ₒ j) *ₒ k = i *ₒ (j *ₒ k).
  Proof. solve ord. Qed.
  
  Fact ord_mul_zero_left i : 0ₒ *ₒ i = 0ₒ.
  Proof. solve ord. Qed.
  
  Fact ord_mul_zero_right i : i *ₒ 0ₒ = 0ₒ.
  Proof. solve ord. Qed.
  
  Fact ord_mul_one_left i : 1ₒ *ₒ i = i.
  Proof. solve ord. Qed.
  
  Fact ord_mul_one_right i : i *ₒ 1ₒ = i.
  Proof. solve ord. Qed.
  
  Fact ord_mul_distr i j k : k *ₒ (i +ₒ j) = k *ₒ i +ₒ k *ₒ j.
  Proof. solve ord. Qed.
  
  Fact ord_euclid a d : 0ₒ <ₒ d → { q : ord & { r | a = d *ₒ q +ₒ r ∧ r <ₒ d } }.
  Proof.
    intro Hd.
    destruct (eucl_dev d Hd a) as [ q r ].
    exists q, r; split; subst; solve ord.
  Qed. 
 
  (************)
  
  Hint Resolve ord_le_zero_least ord_lt_trans ord_add_mono_le_left ord_add_mono_lt_right 
               ord_zero_lt_one : core.
  
  Fact ord_lt_le_weak i j : i <ₒ j → i ≤ₒ j.
  Proof. rewrite ord_le_lt_iff; auto. Qed.
  
  Fact ord_le_refl i j : i ≤ₒ i.
  Proof. rewrite ord_le_lt_iff; auto. Qed.
  
  Fact ord_le_antisym i j : i ≤ₒ j → j ≤ₒ i → i = j.
  Proof.
    rewrite !ord_le_lt_iff; intros [] []; subst; auto.
    destruct ord_lt_irrefl with (i := i); eauto.
  Qed.
  
  Hint Resolve ord_le_refl ord_lt_le_weak : core.
  
  Fact ord_le_lt_dec i j : { i ≤ₒ j } + { j <ₒ i }.
  Proof. destruct (ord_lt_sdec i j); eauto. Qed.
 
  Fact ord_lt_succ i : i <ₒ i +ₒ 1ₒ.
  Proof. rewrite <- (ord_add_zero_right i) at 1; auto. Qed.
  
  Fact ord_le_trans i j k : i ≤ₒ j → j ≤ₒ k → i ≤ₒ k.
  Proof. rewrite !ord_le_lt_iff; intros [] []; subst; eauto. Qed.
  
  Fact ord_le_lt_trans i j k : i ≤ₒ j → j <ₒ k → i <ₒ k.
  Proof. intros []%ord_le_lt_iff; subst; eauto. Qed.
  
  Fact ord_lt_le_trans i j k : i <ₒ j → j ≤ₒ k → i <ₒ k.
  Proof. intros ? []%ord_le_lt_iff; subst; eauto. Qed.
  
  Hint Resolve ord_lt_le_weak ord_le_refl ord_le_trans
               ord_le_lt_trans ord_lt_le_trans : core.

  Fact ord_not_lt_zero i : ¬ i <ₒ 0.
  Proof. intro; apply (@ord_lt_irrefl 0); eauto. Qed.
  
  Fact ord_add_mono_le i j k l : i ≤ₒ j → k ≤ₒ l → i +ₒ k ≤ₒ j +ₒ l.
  Proof.
    intros []%ord_le_lt_iff []%ord_le_lt_iff; subst; eauto.
    apply ord_le_lt_iff; right. 
    apply ord_le_lt_trans with (j +ₒ k); eauto.
  Qed.

  Fact ord_add_cancel_right i j k : k +ₒ i = k +ₒ j → i = j.
  Proof.
    intros H.
    destruct (ord_lt_sdec i j); auto.
    + destruct ord_lt_irrefl with (i := k +ₒ x).
      rewrite H at 2; now apply ord_add_mono_lt_right.
    + destruct ord_lt_irrefl with (i := k +ₒ x).
      rewrite H at 1; now apply ord_add_mono_lt_right.
  Qed.
  
  Fact ord_succ_not_zero i : i +ₒ 1ₒ ≠ 0ₒ.
  Proof.
    intros H.
    generalize (ord_lt_succ i).
    rewrite H; apply ord_not_lt_zero.
  Qed.
  
  Fact ord_add_mono_lt_inv i j k : k +ₒ i <ₒ k +ₒ j → i <ₒ j.
  Proof.
    intros H.
    destruct (ord_lt_sdec i j); auto.
    + now apply ord_lt_irrefl in H.
    + destruct ord_lt_irrefl with (i := k +ₒ x); eauto.
  Qed.
  
  Fact ord_add_mono_le_inv i j k : k +ₒ i ≤ₒ k +ₒ j → i ≤ₒ j.
  Proof.
    intros [ <-%ord_add_cancel_right | ?%ord_add_mono_lt_inv ]%ord_le_lt_iff; auto.
  Qed.
  
  Fact ord_lt_add_one_is_succ i j : i <ₒ j → j <ₒ i +ₒ 1 → False.
  Proof.
    intros H1 H2.
    destruct (ord_sub i j) as (k & ->); auto.
    apply ord_add_mono_lt_inv, ord_lt_one_is_zero in H2 as ->.
    rewrite ord_add_zero_right in H1.
    now apply ord_lt_irrefl in H1.
  Qed.
  
  Hint Resolve ord_lt_succ : core.
  
  Fact ord_lt__succ_le_iff i j : i <ₒ j ↔ i +ₒ 1 ≤ₒ j.
  Proof.
    split; eauto.
    intros H.
    destruct (ord_le_lt_dec (i +ₒ 1) j); auto.
    now destruct (ord_lt_add_one_is_succ i j).
  Qed.
  
  Fact ord_lt_succ__le_iff i j : i <ₒ j +ₒ 1 ↔ i ≤ₒ j.
  Proof.
    split; eauto.
    intros H.
    destruct (ord_le_lt_dec i j) as [ | C%ord_lt__succ_le_iff ]; auto.
    destruct (ord_lt_irrefl (j +ₒ 1)); eauto.
  Qed.
  
  Hint Resolve ord_add_mono_lt_right ord_zero_lt_one ord_add_mono_le ord_le_zero_least ord_le_refl : core.

  Fact ord_zero_lt_succ i : 0 <ₒ i +ₒ 1ₒ.
  Proof. apply ord_le_lt_trans with (i +ₒ 0ₒ); eauto. Qed.
  
  Fact ord_zero_lt_1add i : 0 <ₒ 1ₒ +ₒ i.
  Proof. apply ord_lt_le_trans with (1ₒ +ₒ 0ₒ); eauto. Qed.
  
  Hint Resolve ord_zero_lt_1add : core.
  
  Fact ord_add_incr_left i j : i ≤ₒ i +ₒ j.
  Proof. rewrite <- (ord_add_zero_right i) at 1; auto. Qed.

  Fact pos_add_incr_left i j : j ≤ₒ i +ₒ 1ₒ +ₒ j.
  Proof. rewrite <- (ord_add_zero_left j) at 1; eauto. Qed.
  
  Fact pos_add_sincr_right i j : i <ₒ i +ₒ 1ₒ +ₒ j.
  Proof.
    rewrite <- (ord_add_zero_right i) at 1.
    rewrite ord_add_assoc; eauto.
  Qed.
  
  Fact pos_lt_sub i j : i <ₒ j → { k | j = i +ₒ 1ₒ +ₒ k }.
  Proof. now intros H%ord_lt__succ_le_iff%ord_sub. Qed.
  
  Fact ord_lt_succ_mono_iff i j : i +ₒ 1ₒ <ₒ j +ₒ 1ₒ ↔ i <ₒ j. 
  Proof.
    split.
    + now rewrite ord_lt_succ__le_iff, ord_lt__succ_le_iff.
    + intros H%ord_lt__succ_le_iff; eauto.
  Qed.
  
  Fact ord_eq_succ_iff i j : i +ₒ 1ₒ = j +ₒ 1ₒ ↔ i = j. 
  Proof.
    split; auto.
    intros H.
    destruct (ord_lt_sdec i j) as [ i j C | | i j C ]; auto.
    all: exfalso; apply ord_lt_succ_mono_iff in C; revert C; rewrite H; apply ord_lt_irrefl.
  Qed.

  Fact ord_le_succ_mono_iff i j : i +ₒ 1ₒ ≤ₒ j +ₒ 1ₒ ↔ i ≤ₒ j.
  Proof.
    split.
    + intros H.
      destruct (ord_le_lt_dec i j) as [ | C%ord_lt_succ_mono_iff ]; auto.
      destruct (ord_lt_irrefl (j +ₒ 1ₒ)); eauto.
    + intros [ -> | ]%ord_le_lt_iff; auto.
  Qed.
  
  Definition ord_is_succ n := (∃j, n = j +ₒ 1ₒ).
  
  Fact ord_is_succ_succ n : ord_is_succ (n +ₒ 1ₒ).
  Proof. now exists n. Qed.
  
  Fact ord_add_is_succ_inv a i : ord_is_succ (a +ₒ i) → ord_is_succ i ∨ i = 0ₒ ∧ ord_is_succ a.
  Proof.
    unfold ord_is_succ.
    intros (j & Hj).
    destruct (ord_zero_or_1add i) as [ -> | (p & ->) ].
    + rewrite ord_add_zero_right in Hj; eauto.
    + left.
      destruct (ord_sub a j) as (q & ->).
      * apply ord_le_succ_mono_iff.
        rewrite <- Hj, <- (ord_add_zero_right 1ₒ) at 1; auto.
      * rewrite ord_add_assoc in Hj.
        apply ord_add_cancel_right in Hj; eauto.
  Qed.
  
  Fact ord_is_succ_1 : ord_is_succ 1ₒ.
  Proof. exists 0ₒ; now rewrite ord_add_zero_left. Qed.
  
  Hint Resolve ord_is_succ_1 : core. 
  
  Fact ord_is_succ_10 : ord_is_succ (1ₒ +ₒ 0ₒ).
  Proof. now rewrite ord_add_zero_right. Qed.
  
  Fact ord_is_succ_1add n : ord_is_succ n → ord_is_succ (1ₒ +ₒ n).
  Proof. intros (j & ->); exists (1ₒ +ₒ j); now rewrite ord_add_assoc. Qed.
  
  Hint Resolve ord_is_succ_1add : core.
  
  Fact ord_is_succ_1add_inv n : ord_is_succ (1ₒ +ₒ n) → n = 0ₒ ∨ ord_is_succ n.
  Proof. intros [ | [] ]%ord_add_is_succ_inv; auto. Qed.

  Fact ord_add_zero_inv i j : i +ₒ j = 0ₒ → i = 0ₒ ∧ j = 0ₒ.
  Proof.
    intros H.
    generalize (ord_le_zero_least i).
    intros [<- | C ]%ord_le_lt_iff.
    + now rewrite ord_add_zero_left in H.
    + destruct (ord_lt_irrefl 0ₒ).
      rewrite <- H at 2.
      apply ord_lt_le_trans with (1 := C); auto.
      apply ord_add_incr_left.
  Qed.
       
(*
  Fact pos_add_comm i j : i +ₚ j = j +ₚ i.
  Proof. solve pos. Qed.
  
 *=

  Fact pos_add_assoc i j k : (i +ₚ j) +ₚ k = i +ₚ (j +ₚ k).
  Proof. solve pos. Qed.

(*
  Fact pos_mul_comm i j : i *ₚ j = j *ₚ i.
  Proof. solve pos. Qed.
  
  *)

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
  
*)

End ord.

#[global] Opaque ord_add ord_mul ord ord_one ord_zero ord_lt ord_le.

#[global] Hint Resolve
    ord_le_refl : core.
    
    (*
    pos_one_least
    pos_one_lt_S
    pos_add_sincr_left
    pos_add_sincr_right
    pos_add_incr_left 
    pos_add_mono_lt_left : core. 
    *)

