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

Set Implicit Arguments.

(** The least tail form (ltf) of an ordinal is a decomposition
    of the form a + ω^e for with a is the least possible 
 
    Hence for instance:
     - 0 + ω is a ltf
     - ω³ + ω is a ltf
     - but (ω³+ω) + ω² is not a ltf  *)

Definition eps0_ltf a e := ∀b, a +₀ ω^e = b +₀ ω^e → a ≤ε₀ b.

#[local] Hint Resolve eps0_zero_least : core.

#[local] Hint Resolve eps0_le_antisym : core.

#[local] Hint Resolve eps0_le_refl eps0_le_trans eps0_lt_trans 
                      eps0_lt_le_weak : core.

#[local] Hint Resolve eps0_add_mono eps0_add_incr 
                      eps0_add_incr_left eps0_add_incr_right : core.

Fact eps0_ltf_zero e : eps0_ltf 0₀ e.
Proof. red; auto. Qed.

Fact eps0_eq_ltf_inv :
  ∀ a b e f,
      eps0_ltf a e
    → eps0_ltf b f
    → a +₀ ω^e = b +₀ ω^f
    → a = b ∧ e = f.
Proof.
  intros a b e f H1 H2 E.
  assert (e = f) as <-; auto.
  1: now apply eps0_tf_fun_right in E.
Qed.

#[local] Hint Resolve eps0_ltf_zero : core. 

Fact eps0_one_eq_ltf a e :
    eps0_ltf a e
  → 1₀ = a +₀ ω^e
  → a = 0₀ ∧ e = 0₀.
Proof.
  intros H1.
  replace 1₀ with (0₀ +₀ ω^0₀).
  + intros (<- & <-)%eps0_eq_ltf_inv; eauto.
  + now rewrite eps0_add_zero_left, eps0_omega_zero.
Qed.

Fact eps0_eq_omega_ltf_inv a b e :
    eps0_ltf b e
  → ω^a = b +₀ ω^e
  → b = 0₀ ∧ a = e.
Proof.
  intros H.
  rewrite <- (eps0_add_zero_left ω^a).
  intros (<- & <-)%eps0_eq_ltf_inv; auto.
Qed.

Fact eps0_ltf_exp e n : eps0_ltf ω^⟨e,n⟩ e.
Proof.
  intros b Hb.
  rewrite eps0_add_exp_omega in Hb.
  destruct b as [ | g i f Hf _ ] using eps0_hnf_rect.
  + rewrite eps0_add_zero_left in Hb.
    now apply eps0_exp_inj, proj2, pos_succ_neq_one in Hb.
  + rewrite <- (eps0_add_zero_right ω^e) in Hb; unfold eps0_omega in Hb.
    destruct (eps0_lt_sdec g e) as [ g e C | e | g e C ].
    * rewrite eps0_add_hnf_lt, eps0_add_zero_right in Hb; auto.
      now apply eps0_exp_inj, proj2, pos_succ_neq_one in Hb.
    * rewrite eps0_add_hnf_eq, eps0_add_zero_right in Hb; auto.
      apply eps0_exp_inj, proj2, pos_succ_inj in Hb as <-; auto.
    * apply eps0_le_trans with ω^⟨g,i⟩; auto.
      apply eps0_le_iff_lt.
      left; now apply eps0_exp_mono_left.
Qed.

Fact eps0_ltf_hnf e n g h : 
    g +₀ ω^(h) <ε₀ ω^(e)
  → eps0_ltf g h
  → eps0_ltf (ω^⟨e,n⟩ +₀ g) h.
Proof.
  intros Hg Hgh b Hb.
  destruct (eps0_le_lt_dec (ω^⟨e,n⟩ +₀ g) b) as [ | [C | (b' & -> & Hb2)]%eps0_lt_add_inv_add ]; auto.
  + assert (ω^h <ε₀ ω^e) as Hh. 
    1:{ apply eps0_le_lt_trans with (2 := Hg); auto. }
    destruct (@eps0_lt_irrefl ω^⟨e,n⟩).
    apply eps0_le_lt_trans with (2 := eps0_add_below_exp _ _ _ _ C Hh).
    rewrite <- Hb, eps0_add_assoc; auto.
  + apply eps0_add_mono; auto.
    apply Hgh.
    rewrite !eps0_add_assoc in Hb.
    apply eps0_eq_hnf_inv in Hb as (_ & _ & Hb); auto.
    apply eps0_le_lt_trans with (2 := Hg); auto.
Qed.

Fact eps0_ltf_hnf' e g i f :
      g <ε₀ ω^e
    → ω^f <ε₀ ω^e
    → eps0_ltf g f
    → eps0_ltf (ω^⟨e,i⟩ +₀ g) f.
Proof. intros ? ?; apply eps0_ltf_hnf, eps0_add_below_omega; auto. Qed.

Section eps0_ltf_rect.

  Inductive eps0_ltf_decomp : ε₀ → Type :=
    | eps0_ld_zero :    eps0_ltf_decomp 0₀
    | eps0_ld_ltf g e : eps0_ltf g e
                      → eps0_ltf_decomp (g +₀ ω^e).

  Hint Constructors eps0_ltf_decomp : core.
  Hint Resolve eps0_ltf_exp eps0_ltf_hnf : core.

  Local Fact eps0_ld_exp e n : eps0_ltf_decomp ω^⟨e,n⟩.
  Proof.
    destruct (pos_one_or_succ n) as [ -> | (m & ->) ].
    + rewrite <- eps0_add_zero_left; constructor 2; auto.
    + rewrite <- eps0_add_exp_omega; eauto.
  Qed.

  Hint Resolve eps0_ld_exp : core.

  Lemma eps0_ld_build e : eps0_ltf_decomp e.
  Proof.
    induction e as [ | e n f H _ IH ] using eps0_hnf_rect; auto.
    destruct IH as [ | g h IH ].
    + rewrite eps0_add_zero_right; auto.
    + rewrite <- eps0_add_assoc; auto.
  Qed.

  Section eps0_ltf_rect.

    (** Induction principle corresponding to the following building rules 
        for ordinals below ε₀:

                       g  e  eps0_ltf g e
            ------   ----------------------
              0₀          g +₀ ω^e
     *)

    Variables (P : ε₀ → Type)
            (HP0 : P 0₀)
            (HP2 : ∀ g e, eps0_ltf g e → P g → P e → P (g +₀ ω^e)).

    Hint Resolve eps0_lt_le_trans eps0_lt_omega : core.

    Theorem eps0_ltf_rect e : P e.
    Proof.
      induction e as [ e IH ] using eps0_rect.
      destruct (eps0_ld_build e); auto.
      apply HP2; eauto.
    Qed.

  End eps0_ltf_rect.

End eps0_ltf_rect.
