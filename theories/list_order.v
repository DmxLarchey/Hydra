(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils.

Import ListNotations.

(** The list order is a weak variant of the multiset order on list 

   The proof displayed here is largely inspired from 
   the short outline of Tobias Nipkow and Wilfried Buchholz 

     http://www4.in.tum.de/~nipkow/misc/multiset.ps *)

(** Notations for the construction of the list order *)
#[local] Reserved Notation "x '≺' y" (at level 70, no associativity, format "x  ≺  y").
#[local] Reserved Notation "x '≺ₗ' y" (at level 70, no associativity, format "x  ≺ₗ  y").
#[local] Reserved Notation "x '⊏' y" (at level 70, no associativity, format "x  ⊏  y").
#[local] Reserved Notation "x '⊏⁺' y" (at level 70, no associativity, format "x  ⊏⁺  y").

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.

Section list_order.

  Variables (X : Type) (R : X → X → Prop).

  Infix "≺" := R.
  Notation "l ≺ₗ y" := (∀x, x ∈ l → x ≺ y).

  Local Fact lt_fall_sg x y : x ≺ y → [x] ≺ₗ y.
  Proof. now intros ? ? [ <- | [] ]. Qed.

  Hint Resolve lt_fall_sg : core.

  (* Inductive definition of the list relation ⊏ 
     of which the transitive closure ⊏⁺ is the list order. *)

  Inductive lo_step : list X → list X → Prop :=
    | lo_step_intro l m x r : m ≺ₗ x → l++m++r ⊏ l++[x]++r
  where "l ⊏ m" := (lo_step l m).

  Hint Constructors lo_step : core.

  Fact lo_step_ctx l r u v : u ⊏ v → l++u++r ⊏ l++v++r.
  Proof.
    induction 1 in l, r |- *; eauto.
    rewrite <- !app_assoc, !(app_assoc l); eauto.
  Qed.

  Fact lo_step_cons x l : l ⊏ x::l.
  Proof. now apply @lo_step_intro with (l := []) (m := []); simpl. Qed.

  (* The inversion lemma gives an alternate characterization,
     used below for more specific inversion lemmas below *)
  Local Fact lo_step_inv k p :
         k ⊏ p ↔ ∃ l m x r, k = l++m++r ∧ p = l++[x]++r ∧ m ≺ₗ x.
  Proof.
    split.
    + intros [ l m x r ]; now exists l, m, x, r.
    + intros (? & ? & ? & ? & -> & -> & ?); eauto.
  Qed.

  (** These two are key lemmas in the proof of (Acc lo_step) below *)

  Local Fact lo_step_nil_inv l : ~ l ⊏ [].
  Proof. now intros ([] & ? & ? & ? & ? & ? & ?)%lo_step_inv. Qed.

  Local Lemma lo_step_cons_right_inv k y m : 
          k ⊏ y::m 
        → (∃ u, k = u++m ∧ u ≺ₗ y)
        ∨ (∃ l u x r, m = l++[x]++r ∧ k = y::l++u++r ∧ u ≺ₗ x).
  Proof.
    intros ([ | z l] & u & x & r & hk & e & hu)%lo_step_inv; simpl in *;
    apply cons_inj in e as [-> ->]; [ left | right ]; eauto.
    exists l, u, x, r; eauto.
  Qed.

  Section Acc_lo_step.

    Notation W := (Acc lo_step).

    Local Fact Acc_lo_step_nil : W [].
    Proof. constructor 1; intros _ []%lo_step_nil_inv. Qed.

    Local Fact W_app_bound y r :
        (∀x, x ≺ y → ∀l, W l → W (x::l))
       → W r 
       → ∀l, l ≺ₗ y → W (l++r).
    Proof.
      intros hy ? l. 
      induction l; simpl; eauto.
      intros; apply hy; eauto.
    Qed.

    Hint Resolve W_app_bound : core.

    Local Fact W_cons_rec y m :
           (∀x, x ≺ y → ∀l, W l → W (x::l))
         → W m
         → (∀l, l ⊏ m → W (y::l))
         → W (y::m).
    Proof. constructor; intros ? [ (? & -> & ?) | (? & ? & ? & ? & -> & -> & ?) ]%lo_step_cons_right_inv; eauto. Qed.

    Hint Resolve W_cons_rec : core.

    Local Fact W_cons y : (∀x, x ≺ y → ∀l, W l → W (x::l)) → ∀l, W l → W (y::l).
    Proof. induction 2; eauto. Qed.

    Hint Resolve W_cons : core.

    Local Lemma Acc_lo_step_cons x : Acc R x → ∀l, W l → W (x::l).
    Proof. induction 1; eauto. Qed.

  End Acc_lo_step.

  Hint Resolve Acc_lo_step_nil
               Acc_lo_step_cons : core.

  (* W is closed under [] and x::_ for any accessible x
     so it contains any list composed of accessibles *) 
  Local Lemma forall_Acc_lo_step l : (∀x, x ∈ l → Acc R x) → Acc lo_step l.
  Proof.
    rewrite <- Forall_forall.
    induction 1; eauto.
  Qed.

  Definition lo := clos_trans lo_step.

  Infix "⊏⁺" := lo.

  Hint Resolve lo_step_cons lo_step_ctx : core.

  (** Closure properties of lo/⊏⁺ *)

  (* The constructor for the basic reduction *)
  Fact lo_intro x l : l ≺ₗ x → l ⊏⁺ [x].
  Proof.
    constructor 1.
    rewrite <- (app_nil_r l).
    now constructor 1 with (l := []) (r := []).
  Qed.

  (* Contextual closure *)
  Fact lo_ctx l r u v : u ⊏⁺ v → l++u++r ⊏⁺ l++v++r.
  Proof. unfold lo; induction 1 in l, r |- *; eauto. Qed.

  (* Transitivity *)
  Fact lo_trans l m p : l ⊏⁺ m → m ⊏⁺ p → l ⊏⁺ p.
  Proof. econstructor 2; eassumption. Qed.

  Fact lo_erase l x r : l++r ⊏⁺ l++[x]++r.
  Proof. apply lo_ctx with (u := []), lo_intro; now simpl. Qed.

  (* Closure under right head/tail append *)
  Fact lo_app_head l m r : m ⊏⁺ r → m ⊏⁺ l++r.
  Proof.
    intros H.
    induction l as [ | x l IH ]; simpl; auto. 
    apply lo_trans with (1 := IH), lo_erase with (l := []).
  Qed.

  Fact lo_app_tail l m r : m ⊏⁺ l → m ⊏⁺ l++r.
  Proof.
    intros H.
    induction r as [ | x r IH ]; simpl; auto.
    + now rewrite app_nil_r.
    + apply lo_trans with (1 := IH), lo_erase.
  Qed.

  Fact lo_app_head_tail m m' l r : m ⊏⁺ m' → m ⊏⁺ l++m'++r.
  Proof. now intro; apply lo_app_head, lo_app_tail. Qed.

  Fact lo_cons x l m : l ⊏⁺ m → x::l ⊏⁺ x::m.
  Proof. 
    intros; rewrite <- (app_nil_r l), <- (app_nil_r m).
    now apply lo_ctx with (l := [_]).
  Qed.

  Lemma Acc_lo_forall l : Acc lo l → ∀x, x ∈ l → Acc R x.
  Proof.
    induction 1 as [ l _ IHl ]; intros x Hx.
    constructor; intros y Hy.
    apply IHl with (y := [y]); auto.
    apply in_split in Hx as (l' & r' & ->).
    apply lo_app_head_tail with (m' := [_]),
          lo_intro; eauto.
  Qed.

  Hint Resolve Acc_lo_forall forall_Acc_lo_step Acc_clos_trans : core.

  (* This is the main theorem characterizing mso Acc(essibility) *)
  Theorem Acc_lo_iff l : Acc lo l ↔ ∀x, x ∈ l → Acc R x.
  Proof. unfold lo; split; eauto. Qed.

  Corollary wf_lo : well_founded R → well_founded lo.
  Proof. intros ? ?; apply Acc_lo_iff; auto. Qed.

End list_order.

Arguments lo_step {_}.
Arguments lo {_}.

Section mono.

  Variables (X : Type) (R T : X → X → Prop).

  Fact lo_step_mono : R ⊆₂ T → lo_step R ⊆₂ lo_step T.
  Proof. induction 2; constructor; eauto. Qed.

  Hint Resolve lo_step_mono : core.

  Fact lo_mono : R ⊆₂ T → lo R ⊆₂ lo T.
  Proof. intro; apply clos_trans_mono; eauto. Qed.

End mono.

