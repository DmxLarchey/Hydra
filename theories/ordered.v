(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.

Import ListNotations.

Set Implicit Arguments.

#[local] Infix "∈" := In (at level 70, no associativity).
#[local] Arguments clos_trans {_}.

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro in_cons in_eq in_elt in_or_app : core.

#[global] Notation ge R := (λ x y, x = y ∨ R y x).

Inductive sdec {X} (R : X → X → Prop) : X → X → Type :=
  | sdec_lt x y : R x y → sdec R x y
  | sdec_eq x : sdec R x x
  | sdec_gt x y : R y x → sdec R x y.

Definition dec (P : Prop) := {P} + {~P}. 

Section ordered.

  Variables (X : Type) (R : X → X → Prop).

  Inductive ordered_from : X → list X → Prop :=
    | ordered_from_nil x : ordered_from x []
    | ordered_from_cons x y l : R x y → ordered_from y l → ordered_from x (y::l).

  Inductive ordered : list X → Prop :=
    | ordered_nil : ordered []
    | ordered_cons x l : ordered_from x l → ordered (x::l).

  Hint Constructors ordered_from ordered : core.

  Fact ordered_from_inv x y l : ordered_from x (y::l) → R x y ∧ ordered_from y l.
  Proof. inversion 1; auto. Qed.

  Fact ordered_from_inv_iff x y l : ordered_from x (y::l) ↔ R x y ∧ ordered_from y l.
  Proof. split; [ inversion 1 | intros []; constructor ]; auto. Qed.

  Fact ordered_inv_iff x l : ordered (x::l) ↔ ordered_from x l.
  Proof. split; [ now inversion 1 | now constructor ]. Qed.

  Fact ordered_inv x l : ordered (x::l) → ordered_from x l.
  Proof. now inversion 1. Qed.

  Fact ordered_from_ordered x l : ordered_from x l → ordered l.
  Proof. induction 1; eauto. Qed.

  Hint Resolve ordered_inv ordered_from_ordered : core.

  Fact ordered_cons_inv x l : ordered (x::l) → ordered l.
  Proof. eauto. Qed.

  Fact ordered_from_app_head x l m : ordered_from x (l++m) → ordered_from x l.
  Proof. induction l in x |- *; simpl; eauto; intros []%ordered_from_inv; eauto. Qed.

  Fact ordered_from_app_tail x l m : ordered_from x (l++m) → ordered m.
  Proof. induction l in x |- *; simpl; eauto. Qed.

  Hint Resolve ordered_from_app_head ordered_from_app_tail : core.

  Fact ordered_app_head l m : ordered (l++m) → ordered l.
  Proof. destruct l; auto; simpl; intros ?%ordered_inv; eauto. Qed.

  Fact ordered_app_tail l m : ordered (l++m) → ordered m.
  Proof. destruct l; simpl; auto; intros ?%ordered_inv; eauto. Qed.

  Fact ordered_from_comp x l y m : ordered_from x (l++[y]) → ordered_from y m → ordered_from x (l++[y]++m).
  Proof. induction l in x |- *; simpl; intros []%ordered_from_inv; eauto. Qed.

  Fact ordered_comp l x m : ordered (l++[x]) → ordered (x::m) → ordered (l++[x]++m).
  Proof.
    destruct l; simpl; auto; intros ?%ordered_inv ?%ordered_inv.
    now constructor; apply ordered_from_comp.
  Qed.

  Fact ordered_from_tail x l y z : ordered_from x (l++[y]) → (∀u, R u y → R u z) → ordered_from x (l++[z]).
  Proof. induction l in x |- *; simpl; intros []%ordered_from_inv; constructor; eauto. Qed.

  Hint Resolve ordered_from_tail : core.

  Fact ordered_tail l x y : ordered (l++[x]) → (∀u, R u x → R u y) → ordered (l++[y]).
  Proof. destruct l; simpl; eauto. Qed.

  Hint Constructors clos_trans : core.

  Fact ordered_from_clos_trans x l : ordered_from x l → ∀ y, y ∈ l → clos_trans R x y.
  Proof.
    induction 1 as [ | x y l H1 H2 IH2 ]; [ easy | ].
    intros ? [ <- | ? ]; eauto.
  Qed.

  Fact ordered_from_dec x l : 
        (∀ u v, u ∈ x::l → v ∈ x::l → { R u v } + { ~ R u v })
      → { ordered_from x l } + { ~ ordered_from x l }.
  Proof.
    revert x.
    induction l as [ | y l IHl ]; intros x H.
    + left; eauto.
    + destruct (H x y) as [ G | G ]; eauto.
      * destruct (IHl y) as [ F | F ]; eauto.
        right; contradict F; now inversion F.
      * right; contradict G; now inversion G.
  Qed.

  Fact ordered_dec l : 
        (∀ u v, u ∈ l → v ∈ l → { R u v } + { ~ R u v })
      → { ordered l } + { ~ ordered l }.
  Proof.
    destruct l as [ | x ].
    + left; eauto.
    + intros []%ordered_from_dec; [ left | right ]; eauto.
  Qed.

End ordered.

Fact ordered_from_ge_Acc X R (x : X) l : ordered_from (ge R) x l → Acc R x → ∀y, y ∈ l → Acc R y.
Proof. induction 1 as [ | ? ? ? [ <- | ] ]; intros ? ? []; subst; eauto. Qed.

Fact ordered_map X Y (f : X -> Y) R T :
         (∀ a b, R a b ↔ T (f a) (f b))
        → ∀l, ordered R l ↔ ordered T (map f l).
Proof.
  intros E l.
  destruct l as [ | x l ]; simpl.
  1: split; constructor.
  rewrite !ordered_inv_iff.
  induction l as [ | y l IHl ] in x |- *; simpl.
  1: split; constructor.
  now rewrite !ordered_from_inv_iff, E, IHl.
Qed.

Section mono.

  Hint Constructors ordered_from ordered : core.

  Variables (X : Type) (R T : X → X → Prop).

  Fact ordered_from_mono a l : 
          (∀ x y, x ∈ a::l → y ∈ a::l → R x y → T x y)
        → ordered_from R a l → ordered_from T a l.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1; intro; eauto.
    constructor 2; eauto.
  Qed.

  Hint Resolve ordered_from_mono : core.

  Fact ordered_mono l : 
          (∀ x y, x ∈ l → y ∈ l → R x y → T x y)
        → ordered R l → ordered T l.
  Proof. induction 2; eauto. Qed.

  Fact clos_trans_mono : 
          (∀ x y, R x y → T x y)
        → (∀ l m, clos_trans R l m → clos_trans T l m).
  Proof. induction 2; eauto. Qed.

End mono.

