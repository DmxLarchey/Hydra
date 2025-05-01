(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Relations Utf8.

From Hydra Require Import utils ordered.

Set Implicit Arguments.

Record ord : Type := {
  ord_type :> Type;
  ord_lt : ord_type → ord_type → Prop;
  ord_le : ord_type → ord_type → Prop;
  ord_zero : ord_type;
  ord_one  : ord_type;
  ord_add : ord_type → ord_type → ord_type;
  ord_mul : ord_type → ord_type → ord_type;

  ord_lt_wf : well_founded ord_lt;
  ord_lt_irrefl : ∀i, ¬ ord_lt i i;
  ord_lt_trans : ∀ i j k, ord_lt i j → ord_lt j k → ord_lt i k;
  ord_le_lt_iff : ∀ i j, ord_le i j ↔ i = j ∨ ord_lt i j;
  ord_lt_sdec : ∀ i j, sdec ord_lt i j;
  ord_le_zero_least : ∀i, ord_le ord_zero i;
  ord_zero_lt_one : ord_lt ord_zero ord_one;
  ord_zero_ge_one : ∀i, i = ord_zero ∨ ord_le ord_one i;

  ord_sub : ∀ i j, ord_le i j → { k | j = ord_add i k };
  ord_add_zero_left : ∀i, ord_add ord_zero i = i;
  ord_add_zero_right : ∀i, ord_add i ord_zero = i;
  ord_1add_le_succ_comm : ∀i, ord_le (ord_add ord_one i) (ord_add i ord_one);
  ord_lt_add_right : ∀ i j k, ord_lt i j → ord_lt (ord_add k i) (ord_add k j);
  ord_le_add_left  : ∀ i j k, ord_le i j → ord_le (ord_add i k) (ord_add j k);
  ord_add_assoc : ∀ i j k, ord_add (ord_add i j) k = ord_add i (ord_add j k);

  ord_mul_assoc : ∀ i j k, ord_mul (ord_mul i j) k = ord_mul i (ord_mul j k);
  ord_mul_zero_left : ∀i, ord_mul ord_zero i = ord_zero;
  ord_mul_zero_right : ∀i, ord_mul i ord_zero = ord_zero;
  ord_mul_one_left : ∀i, ord_mul ord_one i = i;
  ord_mul_one_right : ∀i,ord_mul i ord_one = i;
  ord_mul_distr : ∀ i j k, ord_mul k (ord_add i j) = ord_add (ord_mul k i) (ord_mul k j);
  ord_le_mul : ∀ i j k l, ord_le i j → ord_le k l → ord_le (ord_mul i k) (ord_mul j l);

  ord_is_succ_dec : ∀i, { j | i = ord_add j ord_one } + { ¬ ∃j, i = ord_add j ord_one  };
  (* if _.i is a successor then i must be a successor *)
  ord_mul_is_succ_inv : ∀ a i, (∃j, ord_mul a i = ord_add j ord_one) 
                             → (∃j, i = ord_add j ord_one);

  ord_fseq : ∀ i, (i ≠ ord_zero ∧ ¬ ∃j, i = ord_add j ord_one) → nat → ord_type;
  ord_fseq_pirr : ∀ i l₁ l₂ n, @ord_fseq i l₁ n = @ord_fseq i l₂ n;
  ord_fseq_incr : ∀ i l n, ord_lt (@ord_fseq i l n) (ord_fseq l (S n));
  ord_fseq_lt : ∀ i l n, ord_lt (@ord_fseq i l n) i;
  ord_fseq_limit : ∀ i l j, ord_lt j i → ∃n, ord_lt j (@ord_fseq i l n);
  ord_fseq_add : ∀ i j lj lij n, ord_le (@ord_fseq (ord_add i j) lij n) (ord_add i (@ord_fseq j lj n));
  ord_fseq_mul : ∀ i j lj lij n, ord_le (@ord_fseq (ord_mul i j) lij n) (ord_mul i (@ord_fseq j lj n));

  ord_mseq : nat → ord_type;
  ord_mseq_incr : ∀n, ord_lt (ord_mseq n) (ord_mseq (S n));
  ord_mseq_limit : ∀j, ∃n, ord_lt j (ord_mseq n);
}.

Arguments ord_lt {_}.
Arguments ord_le {_}.
Arguments ord_add {_}.
Arguments ord_mul {_}.
Arguments ord_sub {_}.
Arguments ord_fseq {_ _}.
Arguments ord_zero_ge_one {_}.
Arguments ord_lt_sdec {_}.
Arguments ord_add_zero_left {_}.
Arguments ord_add_zero_right {_}.
Arguments ord_lt_irrefl [_].
Arguments ord_zero_lt_one {_}.

#[global] Notation "x '<ₒ' y" := (ord_lt x y) (at level 70, no associativity, format "x  <ₒ  y").
#[global] Notation "x '≤ₒ' y" := (ord_le x y) (at level 70, no associativity, format "x  ≤ₒ  y").

#[global] Notation "0ₒ" := (@ord_zero _).
#[global] Notation "1ₒ" := (@ord_one _).
#[global] Notation "x '+ₒ' y" := (ord_add x y) (at level 31, left associativity).
#[global] Notation "x '*ₒ' y" := (ord_mul x y) (at level 29, left associativity).

Section ord_extra.

  Variable (o : ord).

  Implicit Types (i j k : o).

  Definition ord_is_succ i := (∃j, i = j +ₒ 1ₒ).
  Definition ord_is_limit i := i ≠ 0ₒ ∧ ¬ ord_is_succ i.

  Fact ord_lt_le_weak i j : i <ₒ j → i ≤ₒ j.
  Proof. rewrite ord_le_lt_iff; auto. Qed.
  
  Fact ord_le_refl i j : i ≤ₒ i.
  Proof. rewrite ord_le_lt_iff; auto. Qed.

  Hint Resolve ord_lt_trans : core.

  Fact ord_le_antisym i j : i ≤ₒ j → j ≤ₒ i → i = j.
  Proof.
    rewrite !ord_le_lt_iff; intros [] []; subst; auto.
    destruct ord_lt_irrefl with (i := i); eauto.
  Qed.
  
  Hint Resolve ord_le_refl ord_lt_le_weak : core.

  Fact ord_le_trans i j k : i ≤ₒ j → j ≤ₒ k → i ≤ₒ k.
  Proof. rewrite !ord_le_lt_iff; intros [] []; subst; eauto. Qed.
  
  Fact ord_le_lt_trans i j k : i ≤ₒ j → j <ₒ k → i <ₒ k.
  Proof. intros []%ord_le_lt_iff; subst; eauto. Qed.
  
  Fact ord_lt_le_trans i j k : i <ₒ j → j ≤ₒ k → i <ₒ k.
  Proof. intros ? []%ord_le_lt_iff; subst; eauto. Qed.

  Hint Resolve ord_le_trans ord_le_lt_trans ord_lt_le_trans : core.

  Fact ord_lt_one_is_zero i : i <ₒ 1ₒ → i = 0ₒ.
  Proof.
    intros Hi.
    destruct (ord_zero_ge_one i); auto.
    destruct ord_lt_irrefl with (i := i); eauto.
  Qed.

  Fact ord_le_lt_dec i j : { i ≤ₒ j } + { j <ₒ i }.
  Proof. destruct (ord_lt_sdec i j); eauto. Qed.

  Fact ord_zero_or_1add i : (i = 0ₒ) + { j | i = 1ₒ +ₒ j }.
  Proof. 
    destruct (ord_le_lt_dec 1ₒ i) as [ ?%ord_sub | H ]; auto.
    left; revert H; apply ord_lt_one_is_zero.
  Qed.

  Fact ord_eq_dec i j : { i = j } + { i ≠ j }.
  Proof.
    destruct (ord_lt_sdec i j) as [ i j H | | i j H ]; auto;
      right; intros ->; revert H; apply ord_lt_irrefl.
  Qed.

  Hint Resolve ord_lt_add_right ord_le_add_left ord_zero_lt_one : core.

  Fact ord_le_add i j k l : i ≤ₒ j → k ≤ₒ l → i +ₒ k ≤ₒ j +ₒ l.
  Proof. intros ? [ -> |]%ord_le_lt_iff; eauto. Qed.

  Hint Resolve ord_le_add ord_le_zero_least : core.

  Fact ord_lt_succ i : i <ₒ i +ₒ 1ₒ.
  Proof. rewrite <- (ord_add_zero_right i) at 1; auto. Qed.

  Fact ord_lt_zero_1add i : 0ₒ <ₒ 1ₒ +ₒ i.
  Proof.
    apply ord_lt_le_trans with (1 := ord_zero_lt_one).
    rewrite <- (ord_add_zero_right 1ₒ) at 1; auto.
  Qed.

  Hint Resolve ord_le_mul ord_lt_zero_1add : core.

  Fact ord_lt_zero_succ i : 0ₒ <ₒ i +ₒ 1ₒ.
  Proof. eauto. Qed.

  Fact ord_mul_is_zero_inv i j : i *ₒ j = 0ₒ → i = 0ₒ ∨ j = 0ₒ.
  Proof.
    intros E.
    destruct (ord_zero_or_1add i) as [ | (a & ->) ]; auto.
    destruct (ord_zero_or_1add j) as [ | (b & ->) ]; auto.
    destruct (@ord_lt_irrefl o 0ₒ).
    rewrite <- E at 2.
    rewrite ord_mul_distr, ord_mul_one_right, ord_add_assoc.
    auto.
  Qed.

  Hint Resolve ord_zero_lt_one : core.

  Fact ord_not_lt_zero i : ¬ i <ₒ 0ₒ.
  Proof. intro; apply (@ord_lt_irrefl o 0ₒ); eauto. Qed.

  Fact ord_zero_or_above i : { i = 0ₒ } + { 0ₒ <ₒ i }.
  Proof.
    destruct (ord_le_lt_dec i 0ₒ) as [ H%ord_le_lt_iff | ]; auto.
    left; destruct H; auto.
    now apply ord_not_lt_zero in H.
  Qed.

  Fact ord_add_cancel_right i j k : k +ₒ i = k +ₒ j → i = j.
  Proof.
    intros H.
    destruct (ord_lt_sdec i j); auto.
    + destruct ord_lt_irrefl with (i := k +ₒ x).
      rewrite H at 2; auto.
    + destruct ord_lt_irrefl with (i := k +ₒ x).
      rewrite H at 1; auto.
  Qed.

  Fact ord_add_is_zero_inv i j : i +ₒ j = 0ₒ → i = 0ₒ ∧ j = 0ₒ.
  Proof.
    destruct (ord_zero_or_above i) as [ -> | Hi ].
    + rewrite ord_add_zero_left; auto.
    + intros E.
      destruct (ord_lt_irrefl (i +ₒ j)).
      rewrite E at 1.
      apply ord_lt_le_trans with (1 := Hi).
      rewrite <- (ord_add_zero_right i) at 1; auto.
  Qed.

  Fact ord_lt_neq i j : i <ₒ j → i ≠ j.
  Proof. intros H <-; revert H; apply ord_lt_irrefl. Qed. 

  Fact ord_one_not_zero : 1ₒ ≠ ord_zero o.
  Proof. symmetry; apply ord_lt_neq; auto. Qed.

  Fact ord_1add_not_zero i : 1ₒ +ₒ i ≠ 0ₒ.
  Proof. symmetry; apply ord_lt_neq; auto. Qed.

  Hint Resolve ord_lt_zero_succ : core.

  Fact ord_zero_not_succ i : 0ₒ ≠ i +ₒ 1ₒ .
  Proof. apply ord_lt_neq; auto. Qed.

  Fact ord_succ_not_zero i : i +ₒ 1ₒ ≠ 0ₒ.
  Proof. symmetry; apply ord_zero_not_succ. Qed.

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

  (* False: 2 + ω <= 1 + ω but not 2 <= 1 *)
  (* Fact ord_add_mono_le_inv_left i j k : i +ₒ k ≤ₒ j +ₒ k → i ≤ₒ j. *)
  
  Fact ord_lt_add_one_is_succ i j : i <ₒ j → j <ₒ i +ₒ 1ₒ → False.
  Proof.
    intros H1 H2.
    destruct (ord_sub i j) as (k & ->); auto.
    apply ord_add_mono_lt_inv, ord_lt_one_is_zero in H2 as ->.
    rewrite ord_add_zero_right in H1.
    now apply ord_lt_irrefl in H1.
  Qed.
  
  Hint Resolve ord_lt_succ : core.
  
  Fact ord_lt__succ_le_iff i j : i <ₒ j ↔ i +ₒ 1ₒ ≤ₒ j.
  Proof.
    split; eauto.
    intros H.
    destruct (ord_le_lt_dec (i +ₒ 1ₒ) j); auto.
    now destruct (ord_lt_add_one_is_succ i j).
  Qed.
  
  Fact ord_lt_succ__le_iff i j : i <ₒ j +ₒ 1ₒ ↔ i ≤ₒ j.
  Proof.
    split; eauto.
    intros H.
    destruct (ord_le_lt_dec i j) as [ | ?%ord_lt__succ_le_iff ]; auto.
    destruct (ord_lt_irrefl (j +ₒ 1ₒ)); eauto.
  Qed.

(*
  Hint Resolve ord_add_mono_lt_right ord_zero_lt_one
               ord_add_mono_le ord_le_zero_least
               ord_le_refl : core. *)

  Fact ord_zero_lt_succ i : 0ₒ <ₒ i +ₒ 1ₒ.
  Proof. apply ord_le_lt_trans with (i +ₒ 0ₒ); eauto. Qed.
  
  Fact ord_zero_lt_1add i : 0ₒ <ₒ 1ₒ +ₒ i.
  Proof. apply ord_lt_le_trans with (1ₒ +ₒ 0ₒ); eauto. Qed.
  
  Hint Resolve ord_zero_lt_1add : core.
  
  Fact ord_add_incr_left i j : i ≤ₒ i +ₒ j.
  Proof. rewrite <- (ord_add_zero_right i) at 1; auto. Qed.
  
  Fact ord_add_incr_right i j : j ≤ₒ i +ₒ j.
  Proof. rewrite <- (ord_add_zero_left j) at 1; auto. Qed.

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
    split; intros H; subst; auto.
    destruct (ord_lt_sdec i j) as [ i j C | | i j C ]; auto.
    all: exfalso; apply ord_lt_succ_mono_iff in C; revert C; rewrite H; apply ord_lt_irrefl.
  Qed.

  Fact ord_succ_inj i j:  i +ₒ 1ₒ = j +ₒ 1ₒ → i = j.
  Proof. apply ord_eq_succ_iff. Qed.

  Fact ord_le_succ_mono_iff i j : i +ₒ 1ₒ ≤ₒ j +ₒ 1ₒ ↔ i ≤ₒ j.
  Proof. now rewrite !ord_le_lt_iff, ord_eq_succ_iff, ord_lt_succ_mono_iff. Qed.

  Fact ord_zero_succ_limit_dec n : (n = 0ₒ) + { p | n = p +ₒ 1ₒ } + (ord_is_limit n).
  Proof.
    destruct (ord_eq_dec n 0ₒ) as [ -> | H1 ]; auto.
    destruct (ord_is_succ_dec _ n) as [ | H2 ]; auto.
    right; now split.
  Qed.

  Fact ord_is_succ_succ n : ord_is_succ (n +ₒ 1ₒ).
  Proof. now exists n. Qed.
  
  Hint Resolve ord_is_succ_succ : core.
  
  Fact ord_is_limit_dec n : { ord_is_limit n } + { ¬ ord_is_limit n }.
  Proof.
    destruct (ord_zero_succ_limit_dec n) as [ [ | (? & ->)] | ]; auto; right; intros []; auto.
  Qed.

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
    generalize (ord_le_zero_least _ i).
    intros [<- | C ]%ord_le_lt_iff.
    + now rewrite ord_add_zero_left in H.
    + destruct (@ord_lt_irrefl o 0ₒ).
      rewrite <- H at 2.
      apply ord_lt_le_trans with (1 := C); auto.
      apply ord_add_incr_left.
  Qed.

  Hint Resolve ord_is_succ_10 ord_is_succ_succ : core.

  Fact ord_is_succ_add i j : ord_is_succ (i +ₒ j) ↔ ord_is_succ j ∨ j = 0ₒ ∧ ord_is_succ i.
  Proof.
    split.
    + destruct (ord_eq_dec j 0ₒ) as [ -> | ].
      1: rewrite ord_add_zero_right; auto.
      intros (k & Hk); left.
      destruct (ord_sub i k) as (p & ->).
      * apply ord_le_succ_mono_iff.
        rewrite <- Hk.
        apply ord_le_add; auto.
        rewrite <- (ord_add_zero_left 1ₒ),
                <- ord_lt__succ_le_iff.
        now destruct (ord_zero_or_above j).
      * rewrite ord_add_assoc in Hk.
        apply ord_add_cancel_right in Hk as ->; auto.
    + intros [ (k & ->) | (-> & ?) ].
      * rewrite <- ord_add_assoc; auto.
      * now rewrite ord_add_zero_right.
  Qed.

  Fact ord_is_limit_add i j : ord_is_limit (i +ₒ j) ↔ ord_is_limit j ∨ j = 0ₒ ∧ ord_is_limit i.
  Proof.
    destruct (ord_eq_dec j 0ₒ) as [ -> | D ].
    1: { rewrite ord_add_zero_right; split; auto.
         intros [ [ [] ] | [] ]; auto. }
    unfold ord_is_limit; rewrite ord_is_succ_add; split.
    + intros (H1 & H2); left; split; auto.
    + intros [ (H1 & H2) | [] ]; try easy; split.
      * now intros []%ord_add_is_zero_inv.
      * now intros [ | [] ].
  Qed.
  
  Fact ord_is_limit_succ_iff i : ord_is_limit (i +ₒ 1ₒ) ↔ False.
  Proof. split; [ | easy ]; intros [ _ H]; apply H; auto. Qed.
  
  Fact ord_is_limit_add_succ i j : ord_is_limit (i +ₒ 1ₒ +ₒ j) ↔ ord_is_limit j.
  Proof. rewrite ord_is_limit_add, ord_is_limit_succ_iff; tauto. Qed.

  Fact ord_is_limit_1add i : ord_is_limit (1ₒ +ₒ i) ↔ ord_is_limit i.
  Proof.
    split; intros (H1 & H2); split.
    + intros ->; apply H2; auto.
    + contradict H2; auto.
    + now intros []%ord_add_is_zero_inv.
    + now intros [ | [] ]%ord_add_is_succ_inv.
  Qed.

  Fact ord_mul_is_succ i j : ord_is_succ i → ord_is_succ j → ord_is_succ (i *ₒ j).
  Proof.
    intros (a & ->) (b & ->).
    rewrite ord_mul_distr, ord_mul_one_right, <- ord_add_assoc; auto.
  Qed.

  Fact ord_mul_is_limit_right a i : a ≠ 0ₒ → ord_is_limit i → ord_is_limit (a *ₒ i).
  Proof.
    intros H1 (H2 & H3); split.
    + now intros [-> | ->]%ord_mul_is_zero_inv.
    + contradict H3; revert H3. apply ord_mul_is_succ_inv.
  Qed.

  Fact ord_mul_is_limit_left a i : i ≠ 0ₒ → ord_is_limit a → ord_is_limit (a *ₒ i).
  Proof.
    intros Hi H.
    destruct (ord_zero_succ_limit_dec i) as [ [ -> | (k & ->) ] | ].
    + easy.
    + rewrite ord_mul_distr, ord_mul_one_right.
      apply ord_is_limit_add; auto.
    + apply ord_mul_is_limit_right; auto.
      apply H.
  Qed.

  Fact ord_lt_mul i j k l : 0ₒ <ₒ i → k <ₒ l → i *ₒ k <ₒ i *ₒ l.
  Proof. 
    intros H ?%ord_lt__succ_le_iff.
    apply ord_lt_le_trans with (i *ₒ (k +ₒ 1ₒ)).
    + rewrite ord_mul_distr, ord_mul_one_right.
      rewrite <- (ord_add_zero_right (i *ₒ k)) at 1; auto.
    + apply ord_le_mul; auto.
  Qed.

  Hint Resolve ord_fseq_incr ord_mseq_incr : core.

  Fact ord_fseq_mono i l n m : n < m → @ord_fseq _ i l n <ₒ ord_fseq l m.
  Proof. induction 1; eauto. Qed.

  Fact ord_mseq_mono n m : n < m → @ord_mseq o n <ₒ @ord_mseq o m.
  Proof. induction 1; eauto. Qed.

  (* i = ω.α hence 1 + i <= 1 + ω.α .??? *)
  Fact ord_is_limit_1add_eq i : ord_is_limit i → 1ₒ +ₒ i = i.
  Proof.
    intros H.
    apply ord_le_antisym; auto.
    + apply ord_lt_succ__le_iff.
      admit.
    + rewrite <- (ord_add_zero_left i) at 1; auto.
  Admitted.

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

End ord_extra.

Arguments ord_zero_or_1add {_}.
Arguments ord_is_succ {_}.
Arguments ord_is_limit {_}.
Arguments ord_le_lt_dec {_}.
Arguments ord_fseq {_ _}.
Arguments ord_mseq {_}.

Check ord_fseq.

(*
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

*)