(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.

Import ListNotations.

Set Implicit Arguments.

(** Notations with global scope *)

#[global] Notation "x ∈ l" := (In x l) (at level 70, no associativity, format "x  ∈  l").
#[global] Notation ge R := (λ x y, x = y ∨ R y x).
#[global] Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.
Arguments transitive {_}.

(** Tactics *)

Tactic Notation "symm" :=
  let H := fresh in
  match goal with
    |- _ = _ -> _ => intro H; symmetry in H; revert H
  end.

(** nat utils *)

Fact lt_irrefl n : ¬ n < n.
Proof. lia. Qed.

Fact lt_trans a b c : a < b → b < c → a < c.
Proof. lia. Qed.

Section iter.

  Variable (X : Type).

  Implicit Type (f : X → X).

  Definition iter f :=
    fix loop n x := 
      match n with
      | 0   => x
      | S n => loop n (f x)
      end.

  Fact iter_ext f g : (∀x, f x = g x) → ∀ n x, iter f n x = iter g n x.
  Proof.
    intros E n.
    induction n as [ | n IHn ]; intro; simpl; auto. 
    now rewrite E, IHn.
  Qed.

End iter.

Arguments iter {_}.

(** rel utils *)

#[local] Hint Constructors clos_refl_trans clos_trans : core.

Section clos_trans.

  Variables (X : Type).

  Implicit Type (R T : X → X → Prop).

  Fact clos_trans_rev R x y : @clos_trans X R x y → clos_trans R⁻¹ y x. 
  Proof. induction 1; eauto. Qed.
  Fact clos_t_rt R x y z :
       clos_trans R x y → clos_refl_trans R y z → clos_trans R x z.
  Proof. induction 2; eauto. Qed.

  Fact clos_trans_ge R : transitive R → ∀ x y, clos_trans (ge R) x y → ge R x y.
  Proof. 
    intros HR; red in HR.
    induction 1 as [ ? ? [] | ? ? ? _ [] _ [] ]; subst; eauto.
  Qed.

  Fact clos_t_ge_rt R x y : clos_trans (ge R) x y → clos_refl_trans R y x.
  Proof. induction 1 as [ ? ? [ <- | ] | ]; eauto. Qed.

  Fact clos_trans_mono R T : 
          (∀ x y, R x y → T x y)
        → (∀ l m, clos_trans R l m → clos_trans T l m).
  Proof. induction 2; eauto. Qed.

  Hint Resolve clos_trans_rev : core.

  Fact clos_trans_rev_iff R x y : clos_trans R⁻¹ x y ↔ (clos_trans R)⁻¹ x y.
  Proof. split; auto. Qed.

  Fact transitive_rev R : transitive R → transitive R⁻¹.
  Proof. unfold transitive; eauto. Qed.

End clos_trans.

(** list utils *)

#[local] Hint Resolve in_cons in_eq in_elt in_or_app : core.

Fact rev_rect X (P : list X → Type) :
      P [] → (∀ l x, P l → P (l++[x])) → ∀l, P l.
Proof.
  intros H1 H2 l; revert l P H1 H2.
  induction l as [ | x l IH ]; intros P H1 H2; auto.
  apply IH.
  + apply (H2 []); auto.
  + intros ? ? ?; now apply (H2 (_::_)).
Qed.

Inductive list_snoc_inv_shape X : list X → Type :=
  | in_list_snoc_inv_shape l x : list_snoc_inv_shape (l++[x]).

Fact list_snoc_inv X (l : list X) : l ≠ [] → list_snoc_inv_shape l.
Proof.
  destruct l as [ | l x ] using rev_rect.
  + now intros [].
  + constructor.
Qed.

Fact in_snoc_iff X (l : list X) x y : y ∈ l++[x] ↔ x = y ∨ y ∈ l.
Proof. rewrite in_app_iff; simpl; tauto. Qed.

Fact snoc_assoc X l (x y : X) : l++[x;y] = (l++[x])++[y].
Proof. now rewrite <- app_assoc. Qed.

Fact cons_inj {X} (x y : X) l m : x::l = y::m → x = y ∧ l = m.
Proof. now inversion 1. Qed.

Fact app_nil_inv {X} (l m : list X) : l++m = [] → l = [] ∧ m = [].
Proof. revert l m; now intros [] []. Qed.

Fact sg_eq_insert {X} (x y : X) l r : [x] = l++y::r → x = y ∧ l = [] ∧ r = [].
Proof. destruct l as [ | ? [] ]; inversion 1; auto. Qed.

Fact list_split {X} (l₁ l₂ r₁ r₂ : list X) :
    l₁++r₁ = l₂++r₂
  → ∃m, l₁++m = l₂ ∧ r₁ = m++r₂
     ∨  l₁ = l₂++m ∧ m++r₁ = r₂.
Proof.
  revert l₂; induction l₁ as [ | x l1 IH ]; intros [ | y l2 ]; simpl.
  + exists []; auto.
  + intros ->; eauto.
  + intros <-; eauto.
  + injection 1; intros (m & [ [] | [] ])%IH <-; subst; eauto.
Qed.

Fact list_split_cons {X} (l₁ l₂ r₁ r₂ : list X) x :
    l₁++r₁ = l₂++[x]++r₂
  → ∃m, l₁++m = l₂ ∧ r₁ = m++[x]++r₂
     ∨  l₁ = l₂++[x]++m ∧ m++r₁ = r₂.
Proof.
  intros (m & [ [H1 H2] | [H1 H2] ])%list_split; subst; eauto.
  destruct m as [ | y m ]; simpl in H2.
  + subst; exists []; rewrite !app_nil_r; auto.
  + inversion H2; subst; exists m; auto.
Qed. 

Fact list_split_cons2 {X} (l₁ l₂ r₁ r₂ : list X) x y :
    l₁++[x]++r₁ = l₂++[y]++r₂
  → l₁ = l₂ ∧ x = y ∧ r₁ = r₂
  ∨ ∃m, l₁++[x]++m = l₂ ∧ r₁ = m++[y]++r₂
     ∨  l₁ = l₂++[y]++m ∧ m++[x]++r₁ = r₂.
Proof.
  intros (m & [ [H1 H2] | [H1 H2] ])%list_split; subst.
  + destruct m as [ | z m ]; simpl in H2.
    * inversion H2; subst y r₂.
      rewrite app_nil_r; auto.
    * inversion H2; subst z r₁.
      right; exists m; auto.
  + destruct m as [ | z m ]; simpl in H2.
    * inversion H2; subst y r₂.
      rewrite app_nil_r; auto.
    * inversion H2; subst z r₂.
      right; exists m; auto.
Qed.

Fact list_nil_choose X (l : list X) : {l = []} + {l ≠ []}.
Proof. destruct l; eauto; now right. Qed.

Fact list_fall_choose X (P Q : X → Prop) l :
        (∀x, x ∈ l → {P x} + {Q x})
      → { x | x ∈ l ∧ P x } + { ∀x, x ∈ l → Q x }.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + now right.
  + destruct (Hl x); eauto.
    destruct IHl as [ (? & []) | ]; eauto.
    right; intros ? [<- |]; eauto.
Qed.

Fact fold_right_conj X (P : X → Prop) l :
         fold_right (λ x, and (P x)) True l ↔ ∀x, x ∈ l → P x.
Proof.
  rewrite <- Forall_forall.
  induction l; simpl.
  + split; constructor.
  + now rewrite Forall_cons_iff, IHl.
Qed.

(** Squashing a decidable predidate into an equivalent
    one that has unique proofs *)

Section squash.

  (* Squashing map a (strongly) decidable predicate into
     an equivalent proof irrelevant one *)

  Variables (P : Prop) (d : {P}+{¬P}).

  Definition squash := if d then True else False.

  Fact squash_iff : squash ↔ P.
  Proof. unfold squash; destruct d; tauto. Qed.

  Fact squash_pirr : ∀ p1 p2 : squash, p1 = p2.
  Proof. unfold squash; destruct d; now intros [] []. Qed.

End squash.

(** Acc utils, morphims *)

#[local] Hint Resolve Acc_inv Acc_intro : core.

Fact Acc_irrefl X (R : X → X → Prop) x : Acc R x → ~ R x x.
Proof. induction 1 as [ x _ IH ]; intros H; exact (IH _ H H). Qed.

Section wf_rel_morph.

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (f : X → Y → Prop)
            (f_surj : ∀y, ∃x, f x y)
            (f_morph : ∀ x₁ x₂ y₁ y₂, f x₁ y₁ → f x₂ y₂ → T y₁ y₂ → R x₁ x₂).

  Theorem Acc_rel_morph x y : f x y → Acc R x → Acc T y.
  Proof.
    intros H1 H2; revert H2 y H1.
    induction 1 as [ x _ IH ]; intros y ?.
    constructor; intros z ?.
    destruct (f_surj z); eauto.
  Qed.

  Hint Resolve Acc_rel_morph : core.

  Corollary wf_rel_morph : well_founded R → well_founded T.
  Proof. intros ? y; destruct (f_surj y); eauto. Qed.

End wf_rel_morph.
