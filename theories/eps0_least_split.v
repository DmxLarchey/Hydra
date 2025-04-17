(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils pos eps0.

Import ListNotations.

(* (a,e) is a least split for the value a + ω^e if
   a is the least possible for this decomposition *)
Definition eps0_least_split a e := ∀b, a +₀ ω^e = b +₀ ω^e → a ≤ε₀ b.

#[local] Hint Resolve eps0_zero_least : core.

#[local] Hint Resolve eps0_le_antisym : core.

#[local] Hint Resolve eps0_le_refl eps0_le_trans eps0_lt_trans 
                      eps0_lt_le_weak : core.

#[local] Hint Resolve eps0_add_mono eps0_add_incr 
                      eps0_add_incr_left eps0_add_incr_right : core.

Fact eps0_least_split_zero e : eps0_least_split 0₀ e.
Proof. red; auto. Qed.

Fact eps0_split_least_uniq :
  ∀ a b e f,
      eps0_least_split a e
    → eps0_least_split b f
    → a +₀ ω^e = b +₀ ω^f
    → a = b ∧ e = f.
Proof.
  intros a b e f H1 H2 E.
  assert (e = f) as <-; auto.
  1: now apply eps0_add_omega_fun_right in E.
Qed.

#[local] Hint Resolve eps0_least_split_zero : core. 

Fact eps0_one_eq_least_split a e :
    eps0_least_split a e
  → 1₀ = a +₀ ω^e
  → a = 0₀ ∧ e = 0₀.
Proof.
  intros H1.
  replace 1₀ with (0₀ +₀ ω^0₀).
  + intros (<- & <-)%eps0_split_least_uniq; eauto.
  + now rewrite eps0_add_zero_left, eps0_omega_zero.
Qed.

Fact eps0_omega_eq_least_split a b e :
    eps0_least_split b e
  → ω^a = b +₀ ω^e
  → b = 0₀ ∧ a = e.
Proof.
  intros H.
  rewrite <- (eps0_add_zero_left ω^a).
  intros (<- & <-)%eps0_split_least_uniq; auto.
Qed.

Fact eps0_least_split_exp_S e n : eps0_least_split ω^⟨e,n⟩ e.
Proof.
  intros b Hb.
  rewrite eps0_add_exp_S_omega in Hb.
  destruct b as [ | g i f Hf _ ] using eps0_head_rect.  
  + rewrite eps0_add_zero_left in Hb.
    now apply eps0_exp_S_inj, proj2, pos_succ_neq_one in Hb.
  + rewrite <- (eps0_add_zero_right ω^e) in Hb; unfold eps0_omega in Hb.
    destruct (eps0_lt_sdec g e) as [ g e C | e | g e C ].
    * rewrite eps0_add_head_lt, eps0_add_zero_right in Hb; auto.
      now apply eps0_exp_S_inj, proj2, pos_succ_neq_one in Hb.
    * rewrite eps0_add_head_eq, eps0_add_zero_right in Hb; auto.
      apply eps0_exp_S_inj, proj2,pos_succ_inj in Hb as <-; auto.
    * apply eps0_le_trans with ω^⟨g,i⟩; auto.
      left; now apply eps0_exp_S_mono_left.
Qed.

Fact eps0_least_split_add_exp_S e n g h : 
    g +₀ ω^(h) <ε₀ ω^(e)
  → eps0_least_split g h
  → eps0_least_split (ω^⟨e,n⟩ +₀ g) h.
Proof.
  intros Hg Hgh b Hb.
  destruct (eps0_le_lt_dec (ω^⟨e,n⟩ +₀ g) b) as [ | [C | (b' & -> & Hb2)]%eps0_lt_add_inv_add ]; auto.
  + assert (ω^h <ε₀ ω^e) as Hh. 
    1:{ apply eps0_le_lt_trans with (2 := Hg); auto. }
    destruct (@eps0_lt_irrefl ω^⟨e,n⟩).
    apply eps0_le_lt_trans with (2 := eps0_add_below_exp_S _ _ C Hh).
    rewrite <- Hb, eps0_add_assoc; auto.
  + apply eps0_add_mono; auto.
    apply Hgh.
    rewrite !eps0_add_assoc in Hb.
    apply eps0_head_split_uniq in Hb as (_ & _ & Hb); auto.
    apply eps0_le_lt_trans with (2 := Hg); auto.
Qed.

#[local] Hint Resolve eps0_least_split_exp_S 
                      eps0_least_split_add_exp_S : core.

Inductive eps0_least_split_decomp : ε₀ → Type :=
  | eps0_ls_zero :      eps0_least_split_decomp 0₀
  | eps0_ls_split g e : eps0_least_split g e
                      → eps0_least_split_decomp (g +₀ ω^e).

Lemma eps0_least_split_build e : eps0_least_split_decomp e.
Proof.
  induction e as [ | e n f H _ IH ] using eps0_head_rect.
  1: constructor.
  destruct IH as [ | g h IH ].
  + rewrite eps0_add_zero_right.
    destruct (pos_one_or_succ n) as [ -> | (m & ->) ].
    * rewrite <- eps0_add_zero_left; constructor 2; auto.
    * rewrite <- eps0_add_exp_S_omega; constructor 2; auto.
  + rewrite <- eps0_add_assoc; constructor 2; auto.
Qed.

Section eps0_least_split_rect.

  (** Induction principle corresponding to the following building rules 
      for ordinals below ε₀:

                   g  e  eps0_least_split g e
        ------   ------------------------------
          0₀             g +₀ ω^e
   *)

  Variables (P : ε₀ → Type)
            (HP0 : P 0₀)
            (HP2 : ∀ g e, eps0_least_split g e → P g → P e → P (g +₀ ω^e)).

  Theorem eps0_least_split_rect e : P e.
  Proof.
    induction e as [ e IH ] using eps0_rect.
    destruct (eps0_least_split_build e); auto.
    apply HP2; auto.
    apply IH, eps0_lt_le_trans with (1 := eps0_lt_omega _); auto.
  Qed.

End eps0_least_split_rect.
