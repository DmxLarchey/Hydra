(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Relations Utf8.

From Hydra Require Import utils.

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

  Hypothesis (R_refl : reflexive R)
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