(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.
From Hydra Require Import utils ordered list_order.

Import ListNotations.

Set Implicit Arguments.

Section Acc_sum_prod.

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop).
  
  Definition rel_prod p q := R (fst p) (fst q) ∧ T (snd p) (snd q).
  
  Theorem Acc_prod x y : Acc R x → Acc T y → Acc rel_prod (x,y).
  Proof.
    induction 1 in y |- *.
    induction 1.
    constructor.
    intros [] []; simpl in *; auto.
  Qed.

  Definition rel_sum (p q : X + Y) :=
    match p, q with
    | inl x1, inl x2 => R x1 x2
    | inr y1, inr y2 => T y1 y2
    | _, _ => False
    end.
    
  Theorem Acc_sum_left x : Acc R x → Acc rel_sum (inl x).
  Proof. induction 1; constructor; intros [] ?; now auto. Qed.
  
  Theorem Acc_sum_right y : Acc T y → Acc rel_sum (inr y).
  Proof. induction 1; constructor; intros [] ?;now auto. Qed.
  
End Acc_sum_prod.

Unset Elimination Schemes.

Section tree.

  Variables (X : Type) (R : X → X → Prop).
    
  Inductive tree := tree_node : X → list tree → tree.
  
  Definition tree_root t := match t with tree_node x _ => x end.
  Definition tree_sons t := match t with tree_node _ l => l end.
  
  Section tree_ind.
  
    Variables (P : tree → Prop) (HP : ∀ x l, (∀s, s ∈ l → P s) → P (tree_node x l)).
    
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
  
  Let tree_sub s t := match t with tree_node _ l => In s l end.
  
  Local Fact tree_sub_wf : well_founded tree_sub.
  Proof. intros t; induction t; constructor; simpl; auto. Qed.
  
  Section tree_rect.

    Variables (P : tree → Type) (HP : ∀ x l, (∀s, s ∈ l → P s) → P (tree_node x l)).

    Theorem tree_rect : forall e, P e.
    Proof. 
      apply Fix with (1 := tree_sub_wf).
      intros []; simpl; auto.
    Qed.

  End tree_rect.
  
  Definition tree_fall P : tree → Prop :=
    fix loop e :=
      match e with
      | tree_node x l => P x l ∧ fold_right (λ p, and (loop p)) True l
      end.

  Lemma tree_fall_fix P x l : tree_fall P (tree_node x l) ↔ P x l ∧ ∀ r, r ∈ l → tree_fall P r.
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
  
  Fact tree_fall_impl P Q e : tree_fall P e → tree_fall (λ x l, P x l → Q x l) e → tree_fall Q e.
  Proof. induction 1 using tree_fall_rect; rewrite !tree_fall_fix; intros []; auto. Qed.

  Inductive tpo : tree → tree → Prop :=
    | tpo_node x l y m : R x y → lo tpo l m → tpo (tree_node x l) (tree_node y m).
    
  Fact tpo_inv s t :
      tpo s t
    → match s, t with
      | tree_node x l, tree_node y m  => R x y ∧ lo tpo l m
      end.
  Proof. now destruct 1. Qed.
  
  (** If every label in every node is accessible then so is the tree *)
  Theorem tpo_Acc e : tree_fall (λ x _, Acc R x) e → Acc tpo e.
  Proof.
    induction 1 as [ x l Hx _ IH%Acc_lo_iff ] using tree_fall_rect.
    revert IH.
    apply Acc_rel_morph with (f := fun l m => l = tree_sons m); auto.
    + intros []; simpl; eauto.
    + intros ? ? [] []; simpl; intros -> -> ?%tpo_inv; tauto.
  Qed.
  
  Hypothesis R_wf : well_founded R.
 
  Theorem tpo_wf : well_founded tpo.
  Proof.
    intros e; apply tpo_Acc.
    induction e; rewrite tree_fall_fix; auto.
  Qed.

End tree.

Section ntree.

  Variables (X : Type) (R : X → X → Prop).
  
  (* A ntree is either
     - a leaf of type X
     - or a node decorated with tree of ntrees 
          and a list of ntrees as sub-trees *)
          
  Inductive ntree : Type :=
    | ntree_leaf : X → ntree
    | ntree_node : tree ntree → list ntree → ntree.
    
  Section ntree_ind.
  
    Variables (P : ntree → Prop)
              (HP0 : ∀x,    P (ntree_leaf x))  
              (HP1 : ∀ r l, tree_fall (λ x _, P x) r
                          → (∀s, s ∈ l → P s)
                          → P (ntree_node r l)).
    
    Fixpoint ntree_ind t : P t.
    Proof.
      destruct t as [ x | r l ].
      + apply HP0.
      + apply HP1.
        * clear l; revert r.
          refine (fix loop r := _).
          destruct r as [ x l ].
          rewrite tree_fall_fix; split.
          - apply ntree_ind.
          - clear x ntree_ind.
            induction l as [ | s l IHl ].
            ++ intros ? [].
            ++ intros t [ Ht | ]; [ | now apply IHl ].
               specialize (loop s); now subst.
        * clear r.
          induction l as [ | s l IHl ].
          - intros ? [].
          - intros t [ Ht | ]; [ | now apply IHl ].
            specialize (ntree_ind s); now subst.
    Qed.

  End ntree_ind.
  
  Definition ntree_fall (P : X → Prop) : ntree → Prop :=
    fix loop e :=
      match e with
      | ntree_leaf x   => P x
      | ntree_node s l => tree_fall (λ x _, loop x) s ∧ fold_right (λ p, and (loop p)) True l
      end.

  Lemma ntree_fall_fix_0 P x : ntree_fall P (ntree_leaf x) ↔ P x. 
  Proof. simpl; tauto. Qed.
  
  Lemma ntree_fall_fix_1 P r l : ntree_fall P (ntree_node r l) ↔ tree_fall (λ x _, ntree_fall P x) r ∧ ∀s, s ∈ l → ntree_fall P s.
  Proof. simpl; rewrite fold_right_conj; easy. Qed.

  Section ntree_fall_ind.

    Variables (P : X → Prop)
              (Q : ntree → Prop)
              (HQ0 : ∀ x, P x → Q (ntree_leaf x))
              (HQ1 : ∀ r l, tree_fall (λ x _, ntree_fall P x) r
                         → tree_fall (λ x _, Q x) r 
                         → (∀ s, s ∈ l → ntree_fall P s)
                         → (∀ s, s ∈ l → Q s)
                      → Q (ntree_node r l)).
                      
    Hint Resolve tree_fall_impl : core.

    Theorem ntree_fall_ind e : ntree_fall P e → Q e.
    Proof. 
      induction e.
      + intros ?%ntree_fall_fix_0; eauto.
      + intros []%ntree_fall_fix_1; eauto.
    Qed.

  End ntree_fall_ind.
    
  Inductive ntpo : ntree → ntree → Prop :=
    | ntpo_leaf x y : R x y → ntpo (ntree_leaf x) (ntree_leaf y)
    | ntpo_node s l t m : tpo ntpo s t → lo ntpo l m → ntpo (ntree_node s l) (ntree_node t m).
    
  Fact ntpo_inv s t :
      ntpo s t 
    → match s, t with
      | ntree_leaf x, ntree_leaf y => R x y
      | ntree_node s l, ntree_node t m => tpo ntpo s t ∧ lo ntpo l m
      | _, _ => False
      end.
  Proof. now destruct 1. Qed.
  
  Let f (p : X + tree ntree * list ntree) : ntree :=
    match p with inl x => ntree_leaf x | inr (r,l) => ntree_node r l end.
    
  Local Fact f_surj : ∀q, ∃p, f p = q.
  Proof.
    intros [x | s m].
    + now exists (inl x).
    + now exists (inr (s,m)).
  Qed.

  Local Fact f_morph : ∀ x₁ x₂ y₁ y₂, f x₁ = y₁ → f x₂ = y₂ → ntpo y₁ y₂ → rel_sum R (rel_prod (tpo ntpo) (lo ntpo)) x₁ x₂.
  Proof. unfold f; intros [|[]] [|[]] ? ? <- <- ?%ntpo_inv; auto. Qed.

  Hint Resolve f_surj f_morph : core.

  Theorem ntpo_Acc t : ntree_fall (Acc R) t → Acc ntpo t.
  Proof.
    induction 1 as [ x Hx | r l H1 H2 H3 H4 ] using ntree_fall_ind.
    + generalize (Acc_sum_left (rel_prod (tpo ntpo) (lo ntpo)) Hx).
      apply Acc_rel_morph with (f := fun p q => f p = q); eauto.
    + rewrite <- Acc_lo_iff in H4.
      assert (Acc (tpo ntpo) r) as H5 by (apply tpo_Acc; auto).
      generalize (Acc_sum_right R (Acc_prod H5 H4)).
      apply Acc_rel_morph with (f := fun p q => f p = q); eauto.
  Qed.
  
  Hypothesis R_wf : well_founded R.
  
  Theorem ntpo_wf : well_founded ntpo.
  Proof.
    intro e; apply ntpo_Acc.
    induction e as [ x | r l IH1 IH2 ].
    + rewrite ntree_fall_fix_0; auto.
    + rewrite ntree_fall_fix_1; auto.
  Qed.

End ntree.

Check ntpo_wf.

