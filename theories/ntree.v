(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Arith Lia Relations Wellfounded Utf8.
From Hydra Require Import utils list_order.

Import ListNotations.

Set Implicit Arguments.

#[local] Hint Constructors clos_refl_trans : core.

Fact crt_mono X (R T : X → X → Prop) : R ⊆₂ T → clos_refl_trans R ⊆₂ clos_refl_trans T.
Proof. induction 2; eauto. Qed. 

Section Acc_sum_prod.

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop).

  Definition rel_prod p q := R (fst p) (fst q) ∧ T (snd p) (snd q).

  Fact Acc_prod x y : Acc R x → Acc T y → Acc rel_prod (x,y).
  Proof.
    induction 1 in y |- *; induction 1; constructor.
    intros [] []; auto.
  Qed.

  Definition rel_sum (p q : X + Y) :=
    match p, q with
    | inl x1, inl x2 => R x1 x2
    | inr y1, inr y2 => T y1 y2
    | _, _ => False
    end.

  Fact Acc_sum_left x : Acc R x → Acc rel_sum (inl x).
  Proof. induction 1; constructor; intros [] ?; now auto. Qed.

  Fact Acc_sum_right y : Acc T y → Acc rel_sum (inr y).
  Proof. induction 1; constructor; intros [] ?; now auto. Qed.

End Acc_sum_prod.

Section tree.

  Variables (X : Type).

  Unset Elimination Schemes.

  Inductive tree := tree_node : X → list tree → tree.

  Set Elimination Schemes.

  Definition tree_root t := match t with tree_node x _ => x end.
  Definition tree_sons t := match t with tree_node _ l => l end.

  Section tree_ind.
  
    Variables (P : tree → Prop)
              (HP : ∀ x l, (∀s, s ∈ l → P s) → P (tree_node x l)).

    Fixpoint tree_ind t : P t.
    Proof.
      destruct t as [ x l ].
      apply HP.
      induction l as [ | s l IHl ].
      + intros ? [].
      + intros t [ Ht | ]; [ | now apply IHl ].
        specialize (tree_ind s); now subst.
    Qed.

  End tree_ind.

  Definition sub_tree_struct s t := s ∈ tree_sons t.

  Local Fact sub_tree_struct_wf : well_founded sub_tree_struct.
  Proof. intros t; induction t; constructor; simpl; auto. Qed.

  Section tree_rect.

    Variables (P : tree → Type)
              (HP : ∀ x l, (∀s, s ∈ l → P s) → P (tree_node x l)).

    Theorem tree_rect : ∀e, P e.
    Proof. 
      apply Fix with (1 := sub_tree_struct_wf).
      intros []; simpl; auto.
    Qed.

  End tree_rect.

  Definition tree_fall P : tree → Prop :=
    fix loop e :=
      match e with
      | tree_node x l => P x l ∧ fold_right (λ p, and (loop p)) True l
      end.

  Lemma tree_fall_fix P x l : tree_fall P (tree_node x l) ↔ P x l ∧ ∀r, r ∈ l → tree_fall P r.
  Proof. simpl; rewrite fold_right_conj; easy. Qed.

  Section tree_fall_rect.

    Variables (P : X → list tree → Prop)
              (Q : tree → Type)
              (HQ : ∀ x l, P x l 
                         → (∀ r, r ∈ l → tree_fall P r)
                         → (∀ r, r ∈ l → Q r)
                      → Q (tree_node x l)).

    Theorem tree_fall_rect e : tree_fall P e → Q e.
    Proof. induction e; intros []%tree_fall_fix; eauto. Qed.

  End tree_fall_rect.

  Fact tree_fall_impl P Q e :
      tree_fall P e
    → tree_fall (λ x l, P x l → Q x l) e
    → tree_fall Q e.
  Proof. induction 1 using tree_fall_rect; rewrite !tree_fall_fix; intros []; auto. Qed.

  Fact tree_fall_True P : (∀ x l, P x l) → ∀e, tree_fall P e.
  Proof. induction e; apply tree_fall_fix; split; eauto. Qed.

  Fact tree_fall_mono P Q : P ⊆₂ Q → tree_fall P ⊆₁ tree_fall Q.
  Proof. intros H1 e H2; apply tree_fall_impl with (1 := H2), tree_fall_True, H1. Qed.

  Inductive tree_sub r : tree → Prop :=
    | tree_sub_refl : tree_sub r r
    | tree_sub_sons x t l : t ∈ l → tree_sub r t → tree_sub r (tree_node x l).

  Hint Constructors tree_sub : core.

  Notation "r ≤t t" := (tree_sub r t) (at level 70).

  Fact tree_sub_inv r t :
    r ≤t t → r = t ∨ ∃s, r ≤t s ∧ s ∈ tree_sons t.
  Proof. intros []; eauto. Qed.

  Fact tree_sub_trans r s t : r ≤t s → s ≤t t → r ≤t t.
  Proof. induction 2; eauto. Qed.

  Hint Resolve tree_sub_trans : core.
  Hint Constructors clos_refl_trans : core. 

  Fact crt_sub_tree_struct_iff_tree_sub s t :
    clos_refl_trans sub_tree_struct s t ↔ tree_sub s t.
  Proof. 
    split.
    + induction 1 as [ ? [] | | ]; eauto. 
    + induction 1; eauto.
  Qed.

  Fact tree_fall_sub_iff P t : tree_fall P t ↔ ∀s, s ≤t t → P (tree_root s) (tree_sons s).
  Proof.
    split.
    + intros H s H1; revert H1 H.
      induction 1; [ destruct s | ]; rewrite tree_fall_fix; intros []; auto.
    + induction t as [ x l IH ]; intros H; apply tree_fall_fix; split; eauto.
      apply (H (tree_node x l)); auto.
  Qed.

(*
  Definition lmax := fold_right max 0.

  Fixpoint tree_ht t :=
    match t with tree_node _ l => S (lmax (map tree_ht l)) end.

  Fact lmax_in n l : n ∈ l → n ≤ lmax l.
  Proof.
    induction l as [ | x l IH ].
    + intros [].
    + intros [ <- | ?%IH ]; simpl; lia.
  Qed.

  Fact tree_ssub_ht r x l : r ∈ l → tree_ht r < tree_ht (tree_node x l).
  Proof.
    intros H.
    apply in_map with (f := tree_ht), lmax_in in H.
    simpl; lia.
  Qed.

  Fact tree_sub_ht r t : r ≤t t → tree_ht r ≤ tree_ht t.
  Proof.
    induction 1 as [ | x t l H _ IH ]; auto.
    generalize (tree_ssub_ht _ x _ H); lia.
  Qed.

  Fact tree_sub_lt_inv r t : r ≤t t → tree_ht r < tree_ht t → ∃s, r ≤t s ∧ s ∈ tree_sons t.
  Proof. intros [ <- | ]%tree_sub_inv; auto; lia. Qed.

  Fact tree_sub_eq_inv r t : r ≤t t → tree_ht t ≤ tree_ht r → r = t.
  Proof.
    intros [ <- | (s & H1%tree_sub_ht & H2) ]%tree_sub_inv C; auto.
    destruct t as [ x l ]; simpl in H2.
    generalize (tree_ssub_ht _ x _ H2); lia.
  Qed.

  Fact tree_sub_inv_dec r t : r ≤t t → { r = t } + { ∃s, r ≤t s ∧ s ∈ tree_sons t }.
  Proof.
    intros H.
    destruct (le_lt_dec (tree_ht t) (tree_ht r)) as [ H1 | H1 ].
    + left; revert H H1; apply tree_sub_eq_inv.
    + right; revert H H1; apply tree_sub_lt_inv.
  Qed.

  Fact tree_sub_fall_fix P t : P t → (∀r, (∃s, r ≤t s ∧ s ∈ tree_sons t) → P r) → (∀s, s ≤t t → P s).
  Proof. intros H1 H2 s [-> | ]%tree_sub_inv_dec; auto. Qed.

*)

  Variables  (R : X → X → Prop).

  Inductive tpo : tree → tree → Prop :=
    | tpo_node x l y m : R x y
                       → lo tpo l m
                       → tpo (tree_node x l) (tree_node y m).

  Fact tpo_inv s t :
      tpo s t
    → match s, t with
      | tree_node x l, tree_node y m  => R x y ∧ lo tpo l m
      end.
  Proof. now destruct 1. Qed.

  (** If every label in every node is accessible then so is the tree *)
  Theorem Acc_tpo e : tree_fall (λ x _, Acc R x) e → Acc tpo e.
  Proof.
    induction 1 as [ x l Hx _ IH%Acc_lo_iff ] using tree_fall_rect.
    revert IH.
    apply Acc_rel_morph with (f := λ l m, l = tree_sons m); auto.
    + intros []; simpl; eauto.
    + intros ? ? [] []; simpl; intros -> -> ?%tpo_inv; tauto.
  Qed.

  Corollary wf_tpo : well_founded R → well_founded tpo.
  Proof. intros ? ?; apply Acc_tpo, tree_fall_True; auto. Qed.

End tree.

Arguments tree_root {_}.
Arguments tree_sons {_}.
Arguments tree_sub {_}.
Arguments sub_tree_struct {_}.

Notation "r ≤t t" := (tree_sub r t) (at level 70).

Section ntree.

  Variables (X : Type).

  (** We strudy the case of a deeper nesting

      list X = 1 + X * list X     (lo : list ordering))
      tree X = X * list (tree X)  (tpo : tree path ordering)
     ntree X = X + tree (ntree X) (ntpo : nested tree path ordering)

     mtree X = 1 + X * tree (mtree X)  ?? *)

  Unset Elimination Schemes.

  Inductive ntree : Type :=
    | ntree_leaf : X → ntree
    | ntree_node : tree ntree → ntree.

  Set Elimination Schemes.

  Section ntree_rect.

    Local Definition sub_ntree_struct r s :=
      match s with
      | ntree_leaf _ => False
      | ntree_node t => r = tree_root t
                      ∨ ∃p, p ∈ tree_sons t
                      ∧ r = ntree_node p
      end.

    Local Fact sub_ntree_struct_1 t : sub_ntree_struct (tree_root t) (ntree_node t).
    Proof. now left. Qed.

    Local Fact sub_ntree_struct_2 s t : s ∈ tree_sons t → sub_ntree_struct (ntree_node s) (ntree_node t).
    Proof. right; eauto. Qed.

    Local Fixpoint wf_sub_ntree_struct s : Acc sub_ntree_struct s.
    Proof.
      destruct s as [ | t ].
      1: constructor; intros _ [].
      revert t; refine (fix loop t := _).
      destruct t as [ s l ].
      constructor.
      intros z [H | (p & ? & ->)]; simpl in H.
      + specialize (wf_sub_ntree_struct s); now subst.
      + clear s wf_sub_ntree_struct; revert H.
        induction l as [ | t l IHl ].
        * intros [].
        * intros [ | H ].
          - specialize (loop t); now subst.
          - apply IHl, H.
    Qed.

    Hint Constructors clos_trans : core.
    Hint Resolve sub_ntree_struct_1 sub_ntree_struct_2 : core.

    Local Fact tree_sub__sub_ntree_struct s t : s ≤t t → clos_trans sub_ntree_struct (tree_root s) (ntree_node t).
    Proof. induction 1; eauto. Qed.

    Variables (P : ntree → Type)
              (HP0 : ∀x, P (ntree_leaf x))  
              (HP1 : ∀t, (∀s, s ≤t t → P (tree_root s)) → P (ntree_node t)).

    Definition ntree_rect : ∀s, P s.
    Proof.
      apply Fix with (1 := wf_clos_trans _ _ wf_sub_ntree_struct).
      intros [] IH.
      + apply HP0.
      + apply HP1; intros ? ?%tree_sub__sub_ntree_struct; auto.
    Qed.

  End ntree_rect.

  Section ntree_ind.
  
    Variables (P : ntree → Prop)
              (HP0 : ∀x, P (ntree_leaf x))  
              (HP1 : ∀t, tree_fall (λ x _, P x) t → P (ntree_node t)).

    Definition ntree_ind : ∀s, P s.
    Proof.
      apply ntree_rect; trivial.
      intros; now apply HP1, tree_fall_sub_iff.
    Qed.

  End ntree_ind.

  Definition ntree_fall (P : X → Prop) : ntree → Prop :=
    fix loop s :=
      match s with
      | ntree_leaf x => P x
      | ntree_node t => loop (tree_root t) ∧ tree_fall (λ x _, loop x) t
      end.

  Fact ntree_fall_fix_0 P x :
      ntree_fall P (ntree_leaf x) ↔ P x. 
  Proof. simpl; tauto. Qed.

  Fact ntree_fall_fix_1 P t :
      ntree_fall P (ntree_node t)
    ↔ ntree_fall P (tree_root t)
    ∧ tree_fall (λ x _, ntree_fall P x) t.
  Proof. simpl; easy. Qed.

  Fact ntree_fall_True P : (∀x, P x) → ∀s, ntree_fall P s.
  Proof.
    intros HP s.
    induction s as [ x | t ].
    + now rewrite ntree_fall_fix_0.
    + rewrite ntree_fall_fix_1; split; auto.
      rewrite tree_fall_sub_iff in H.
      apply H; constructor 1.
  Qed.

  Section ntree_fall_ind.

    Variables (P : X → Prop)
              (Q : ntree → Prop)
              (HQ0 : ∀x, P x → Q (ntree_leaf x))
              (HQ1 : ∀t, tree_fall (λ x _, ntree_fall P x) t
                       → tree_fall (λ x _, Q x) t
                       → Q (ntree_node t)).

    Hint Resolve tree_fall_impl : core.

    Theorem ntree_fall_ind e : ntree_fall P e → Q e.
    Proof. 
      induction e.
      + intros ?%ntree_fall_fix_0; eauto.
      + rewrite ntree_fall_fix_1; intros []; eauto.
    Qed.

  End ntree_fall_ind.

  Section ntree_fall_rect.

    Variables (P : X → Prop)
              (Q : ntree → Type)
              (HQ0 : ∀x, P x → Q (ntree_leaf x))
              (HQ1 : ∀t, tree_fall (λ x _, ntree_fall P x) t
                       → (∀ s, s ≤t t → Q (tree_root s))
                       → Q (ntree_node t)).

    Hint Resolve tree_fall_impl : core.

    Theorem ntree_fall_rect e : ntree_fall P e → Q e.
    Proof. 
      induction e as [ | t IH ].
      + intros ?%ntree_fall_fix_0; eauto.
      + intros H; rewrite ntree_fall_fix_1 in H.
        destruct H as (H1 & H2).
        apply HQ1; auto.
        rewrite tree_fall_sub_iff in H2; eauto. 
    Qed.

  End ntree_fall_rect.

  Variables (R : X → X → Prop).

  Inductive ntpo : ntree → ntree → Prop :=
    | ntpo_leaf x y : R x y → ntpo (ntree_leaf x) (ntree_leaf y)
    | ntpo_node s t : tpo ntpo s t → ntpo (ntree_node s) (ntree_node t).

  Fact ntpo_inv s t :
      ntpo s t 
    → match s, t with
      | ntree_leaf x, ntree_leaf y => R x y
      | ntree_node s, ntree_node t => tpo ntpo s t
      | _, _ => False
      end.
  Proof. now destruct 1. Qed.

  Let f (p : X + tree ntree) : ntree :=
    match p with
    | inl x => ntree_leaf x
    | inr s => ntree_node s
    end.

  Local Fact f_surj : ∀q, ∃p, f p = q.
  Proof.
    intros [x | s].
    + now exists (inl x).
    + now exists (inr s).
  Qed.

  Local Fact f_morph : ∀ x₁ x₂ y₁ y₂,
      f x₁ = y₁
    → f x₂ = y₂
    → ntpo y₁ y₂
    → rel_sum R (tpo ntpo) x₁ x₂.
  Proof. unfold f; intros [|[]] [|[]] ? ? <- <- ?%ntpo_inv; auto. Qed.

  Hint Resolve f_surj f_morph : core.

  Theorem Acc_ntpo t : ntree_fall (Acc R) t → Acc ntpo t.
  Proof.
    induction 1 as [ x Hx | r H1 H2 ] using ntree_fall_ind.
    + generalize (Acc_sum_left (tpo ntpo) Hx).
      apply Acc_rel_morph with (f := fun p q => f p = q); eauto.
    + assert (Acc (tpo ntpo) r) as H3 by (apply Acc_tpo; auto).
      generalize (Acc_sum_right R H3).
      apply Acc_rel_morph with (f := fun p q => f p = q); eauto.
  Qed.

  Corollary wf_ntpo : well_founded R → well_founded ntpo.
  Proof. intros ? ?; apply Acc_ntpo, ntree_fall_True; auto. Qed.

End ntree.

Fixpoint listn n :=
  match n with
  | 0   => []
  | S n => n::listn n
  end.

Fixpoint mytree {X} n (x : X) :=
  match n with
  | 0 => tree_node x []
  | S n => tree_node x (map (fun _ => mytree n x) (listn n))
  end.

Fixpoint myntree n : ntree unit :=
  match n with
  | 0   => ntree_leaf tt
  | S n => ntree_node (mytree n (myntree n))
  end.

Eval compute in myntree 5.


