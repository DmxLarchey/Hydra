(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia List Relations Wellfounded Eqdep_dec Utf8.
From Hydra Require Import utils.

Import ListNotations.

Set Implicit Arguments.

#[local] Hint Constructors clos_trans clos_refl_trans : core.
#[local] Hint Resolve in_cons in_eq in_elt in_or_app 
                      clos_trans_rev transitive_rev : core.

Definition dec (P : Prop) := {P} + {~P}. 

Section sdec.

  Variables (X : Type)
            (R : X → X → Prop).

  Inductive sdec : X → X → Type :=
    | sdec_lt x y : R x y → sdec x y
    | sdec_eq x   :         sdec x x
    | sdec_gt x y : R y x → sdec x y.

  Inductive sdec_lt_inv_t {x y} : sdec x y → Prop := 
    | sdec_lt_inv_intro h : sdec_lt_inv_t (sdec_lt h).

  Inductive sdec_eq_inv_t {x} : sdec x x → Prop :=
    | sdec_eq_inv_intro : sdec_eq_inv_t (sdec_eq x).

  Inductive sdec_gt_inv_t {x y} : sdec x y → Prop := 
    | sdec_gt_inv_intro h : sdec_gt_inv_t (sdec_gt h).

  Hint Constructors sdec_lt_inv_t sdec_eq_inv_t sdec_gt_inv_t : core.

  Fact sdec_inv x y (s : sdec x y) :
    match s with
    | sdec_lt _ as s => sdec_lt_inv_t s
    | sdec_eq _ as s => sdec_eq_inv_t s
    | sdec_gt _ as s => sdec_gt_inv_t s
    end.
  Proof. destruct s; auto. Qed.

  Hypothesis (R_sdec : ∀ x y, sdec x y)
             (R_irrefl : ∀x, ¬ R x x).

  Fact sdec_eq_dec (x y : X) : { x = y } + { x ≠ y }.
  Proof.
    destruct (R_sdec x y); auto; right; intro; subst; eapply R_irrefl; eassumption.
  Qed.

  Fact sdec_uip (x : X) (h : x = x) : eq_refl = h. 
  Proof. apply UIP_dec, sdec_eq_dec. Qed.

  Section sdec_eq_inv.

    Let sdec_eq_inv_dep x y (s : sdec x y) : ∀e, sdec_eq_inv_t (eq_rect y (sdec x) s x e).
    Proof.
      destruct s as [ ? ? H | | ? ? H ].
      1,3: intros <-; destruct (R_irrefl H).
      intros e; destruct (sdec_uip e); constructor.
    Defined.

    Theorem sdec_eq_inv x (s : sdec x x) : sdec_eq_inv_t s.
    Proof. exact (sdec_eq_inv_dep s eq_refl). Qed.

  End sdec_eq_inv.

  Hypothesis (R_trans : transitive R).

  Theorem sdec_lt_inv x y (s : sdec x y) : R x y → sdec_lt_inv_t s.
  Proof.
    intros H; destruct s; eauto.
    + now apply R_irrefl in H.
    + destruct (@R_irrefl x); eauto.
  Qed.

  Theorem sdec_gt_inv x y (s : sdec x y) : R y x → sdec_gt_inv_t s.
  Proof.
    intros H; destruct s; eauto.
    + destruct (@R_irrefl x); eauto.
    + now apply R_irrefl in H.
  Qed.

End sdec.

Check sdec_lt_inv.
Check sdec_eq_inv.
Check sdec_gt_inv.

#[local] Hint Constructors sdec : core.

Lemma lt_sdec i j : sdec lt i j.
Proof. destruct (lt_eq_lt_dec i j) as [ [ | []] | ]; eauto. Qed.

Section ordered.

  Variables (X : Type).

  Implicit Type (R : X → X → Prop).

  Inductive ordered_from R : X → list X → Prop :=
    | ordered_from_nil x : ordered_from R x []
    | ordered_from_cons x y l : R x y → ordered_from R y l → ordered_from R x (y::l).

  Inductive ordered R : list X → Prop :=
    | ordered_nil : ordered R []
    | ordered_cons x l : ordered_from R x l → ordered R (x::l).

  Hint Constructors ordered_from ordered : core.

  Fact ordered_from_inv R x y l : ordered_from R x (y::l) → R x y ∧ ordered_from R y l.
  Proof. inversion 1; auto. Qed.

  Fact ordered_from_inv_iff R x y l : ordered_from R x (y::l) ↔ R x y ∧ ordered_from R y l.
  Proof. split; [ inversion 1 | intros []; constructor ]; auto. Qed.

  Fact ordered_inv_iff R x l : ordered R (x::l) ↔ ordered_from R x l.
  Proof. split; [ now inversion 1 | now constructor ]. Qed.

  Fact ordered_inv R x l : ordered R (x::l) → ordered_from R x l.
  Proof. now inversion 1. Qed.

  Fact ordered_from_ordered R x : ordered_from R x ⊆₁ ordered R.
  Proof. induction 1; eauto. Qed.

  Hint Resolve ordered_inv ordered_from_ordered : core.

  Fact ordered_cons_inv R x l : ordered R (x::l) → ordered R l.
  Proof. eauto. Qed.

  Fact ordered_from_app_head R x l m : ordered_from R x (l++m) → ordered_from R x l.
  Proof. induction l in x |- *; simpl; eauto; intros []%ordered_from_inv; eauto. Qed.

  Fact ordered_from_app_tail R x l m : ordered_from R x (l++m) → ordered R m.
  Proof. induction l in x |- *; simpl; eauto. Qed.

  Hint Resolve ordered_from_app_head ordered_from_app_tail : core.

  Fact ordered_app_head R l m : ordered R (l++m) → ordered R l.
  Proof. destruct l; auto; simpl; intros ?%ordered_inv; eauto. Qed.

  Fact ordered_app_tail R l m : ordered R (l++m) → ordered R m.
  Proof. destruct l; simpl; auto; intros ?%ordered_inv; eauto. Qed.

  Fact ordered_from_comp R x l y m : ordered_from R x (l++[y]) → ordered_from R y m → ordered_from R x (l++[y]++m).
  Proof. induction l in x |- *; simpl; intros []%ordered_from_inv; eauto. Qed.

  Fact ordered_from_trans R x y l : transitive R → ordered_from R x l → R y x → ordered_from R y l.
  Proof. induction 2 in y |- *; eauto. Qed.

  Fact ordered_from_app_middle R l x m : 
       transitive R
     → ordered R l 
     → (∀y, y ∈ l → R y x ∨ y = x)
     → ordered_from R x m
     → ordered R (l++m).
  Proof.
    intros HR.
    induction 1 as [ | a l Hl ]; simpl; eauto.
    revert Hl x; induction 1 as [ a | a b l H1 H2 IH2 ]; intros x Hx H; simpl.
    + constructor.
      destruct (Hx a) as [ Ha | ]; subst; auto.
      revert Ha; apply ordered_from_trans; auto.
    + constructor.
      apply IH2 in H; eauto.
  Qed.

  Fact ordered_comp R l x m : ordered R (l++[x]) → ordered R (x::m) → ordered R (l++[x]++m).
  Proof.
    destruct l; simpl; auto; intros ?%ordered_inv ?%ordered_inv.
    now constructor; apply ordered_from_comp.
  Qed.

  Fact ordered_from_tail R x l y z : ordered_from R x (l++[y]) → (∀u, R u y → R u z) → ordered_from R x (l++[z]).
  Proof. induction l in x |- *; simpl; intros []%ordered_from_inv; constructor; eauto. Qed.

  Hint Resolve ordered_from_tail : core.

  Fact ordered_tail R l x y : ordered R (l++[x]) → (∀u, R u x → R u y) → ordered R (l++[y]).
  Proof. destruct l; simpl; eauto. Qed.

  Fact ordered_from_rev R x l : ordered_from R x l → ordered R⁻¹ (rev l++[x]).
  Proof.
    induction 1 as [ | x y l H _ IH ]; simpl; auto.
    rewrite <- app_assoc.
    apply ordered_comp with (m := [_]); auto.
  Qed.

  Hint Resolve ordered_from_rev : core.

  Fact ordered_rev R l : ordered R l → ordered R⁻¹ (rev l).
  Proof. induction 1; simpl; auto. Qed.

  Fact ordered_rev_iff R l : ordered R l ↔ ordered R⁻¹ (rev l).
  Proof.
    split.
    + apply ordered_rev.
    + intros ?%ordered_rev.
      now rewrite <- rev_involutive.
  Qed.

  Hint Constructors clos_trans : core.

  Fact ordered_from_clos_trans R x l : ordered_from R x l → ∀ y, y ∈ l → clos_trans R x y.
  Proof.
    induction 1 as [ | x y l H1 H2 IH2 ]; [ easy | ].
    intros ? [ <- | ? ]; eauto.
  Qed.

  Fact ordered_app_clos_trans R l m : ordered R (l++m) → ∀ x y, x ∈ l → y ∈ m → clos_trans R x y.
  Proof.
    destruct l as [ | x l ]; simpl.
    1: easy.
    intros H%ordered_inv; revert H.
    induction l in x |- *; simpl.
    + intros ? ? ? [ <- | [] ]; now apply ordered_from_clos_trans.
    + intros []%ordered_from_inv ? ? [ <- | ] ?; eauto.
  Qed.

  Fact ordered_from_dec R x l : 
        (∀ u v, u ∈ x::l → v ∈ x::l → { R u v } + { ~ R u v })
      → { ordered_from R x l } + { ~ ordered_from R x l }.
  Proof.
    revert x.
    induction l as [ | y l IHl ]; intros x H.
    + left; eauto.
    + destruct (H x y) as [ G | G ]; eauto.
      * destruct (IHl y) as [ F | F ]; eauto.
        right; contradict F; now inversion F.
      * right; contradict G; now inversion G.
  Qed.

  Fact ordered_dec R l : 
        (∀ u v, u ∈ l → v ∈ l → { R u v } + { ~ R u v })
      → { ordered R l } + { ~ ordered R l }.
  Proof.
    destruct l as [ | x ].
    + left; eauto.
    + intros []%ordered_from_dec; [ left | right ]; eauto.
  Qed.

  Fact ordered_from_Forall R x l : ordered_from R x l → Forall (clos_trans R x) l.
  Proof.
    induction 1 as [ | ? ? ? ? _ IH ]; eauto; constructor; auto.
    revert IH; apply Forall_impl; eauto.
  Qed.

  Hint Resolve Acc_inv_crt clos_refl_trans_rev transitive_clos_rt : core.

  Fact ordered_from_crt_Acc R x l :
     ordered_from (clos_refl_trans R⁻¹) x l → Acc R x → ∀y, y ∈ l → Acc R y.
  Proof.
    intros H%ordered_from_Forall.
    rewrite Forall_forall in H.
    intros A y Hy.
    apply Acc_inv_crt with (2 := A), clos_refl_trans_rev.
    generalize (H _ Hy); apply transitive__clos_trans; auto.
  Qed.

  Hint Constructors ordered_from ordered : core.

  Fact ordered_from_mono R T a l : 
      (∀ x y, x ∈ a::l → y ∈ a::l → R x y → T x y)
    → ordered_from R a l → ordered_from T a l.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1; intro; eauto.
    constructor 2; eauto.
  Qed.

  Hint Resolve ordered_from_mono : core.

  Fact ordered_mono R T l : 
      (∀ x y, x ∈ l → y ∈ l → R x y → T x y)
    → ordered R l → ordered T l.
  Proof. induction 2; eauto. Qed.

  Section transitive.

    Variables (R : _ ) (HR : transitive R).

    Local Fact transitive_clos_trans : clos_trans R ⊆₂ R.
    Proof. now apply transitive__clos_trans. Qed.

    Hint Resolve transitive_clos_trans (* transitive__clos_trans cannot be used as hint *)
                 ordered_from_ordered
                 ordered_from_clos_trans : core.

    Fact ordered_cons_iff x l : ordered R (x::l) ↔ ordered R l ∧ ∀y, y ∈ l → R x y.
    Proof.
      split.
      + intros ?%ordered_inv; split; eauto.
      + intros (H1 & H2); constructor.
        induction H1; constructor; eauto.
    Qed.

    Fact ordered_app_iff l m : ordered R (l++m) ↔ ordered R l ∧ ordered R m ∧ ∀ x y, x ∈ l → y ∈ m → R x y.
    Proof.
      induction l as [ | x l IH ]; simpl; split; try tauto.
      + repeat split; tauto || constructor.
      + rewrite !ordered_cons_iff, IH; firstorder; subst; auto.
      + rewrite !ordered_cons_iff, IH; intros ([] & ? & ?); repeat split; auto.
        intros ? []%in_app_iff; eauto.
    Qed.

    Fact ordered_snoc_iff x l : ordered R (l++[x]) ↔ ordered R l ∧ ∀y, y ∈ l → R y x.
    Proof.
      rewrite ordered_app_iff; split.
      + intros (? & _ & ?); eauto.
      + intros []; repeat split; eauto.
    Qed.

  End transitive.

End ordered.

Section ordered_morphism.

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (f : X → Y → Prop).

  Fact ordered_from_morphism x l y m : 
      (∀ x₁ x₂ y₁ y₂, x₁ ∈ x::l → x₂ ∈ x::l → f x₁ y₁ → f x₂ y₂ → R x₁ x₂ → T y₁ y₂)
    → f x y 
    → Forall2 f l m
    → ordered_from R x l
    → ordered_from T y m. 
  Proof.
    intros f_morph H1 H2 H3; revert H3 y m H1 H2.
    induction 1.
    + inversion 2; constructor.
    + inversion 2; subst; constructor 2; eauto.
  Qed.

  Hint Resolve ordered_from_morphism : core.
 
  Fact ordered_morphism l m :
      (∀ x₁ x₂ y₁ y₂, x₁ ∈ l → x₂ ∈ l → f x₁ y₁ → f x₂ y₂ → R x₁ x₂ → T y₁ y₂)
    → Forall2 f l m
    → ordered R l
    → ordered T m.
  Proof. intros ? H; induction 1; inversion H; subst; constructor; eauto. Qed.

End ordered_morphism.
