(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import hydra ordered lex_list.

Import ListNotations hydra_notations.

Set Implicit Arguments.

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.
Arguments transitive {_}.

Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

Notation π₁ := proj1_sig.
Notation π₂ := proj2_sig.

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.

Fact lt_irrefl n : ¬ n < n.
Proof. lia. Qed.

Fact lt_trans a b c : a < b → b < c → a < c.
Proof. lia. Qed.

Fact clos_trans_rev X R x y : @clos_trans X R x y → clos_trans R⁻¹ y x. 
Proof. induction 1; eauto. Qed.

#[local] Hint Resolve clos_trans_rev : core.

Fact clos_trans_rev_iff X R x y : @clos_trans X R⁻¹ x y ↔ (clos_trans R)⁻¹ x y.
Proof. split; auto. Qed.

Fact transitive_rev X R : @transitive X R → transitive R⁻¹.
Proof. unfold transitive; eauto. Qed.

#[local] Hint Resolve transitive_rev : core.

Fact rev_rect X (P : list X → Type) :
      P [] → (∀ l x, P l → P (l++[x])) → ∀l, P l.
Proof.
  intros H1 H2 l; revert l P H1 H2.
  induction l as [ | x l IH ]; intros P H1 H2; auto.
  apply IH.
  + apply (H2 []); auto.
  + intros ? ? ?; now apply (H2 (_::_)).
Qed.

Fact in_snoc_iff X (l : list X) x y : y ∈ l++[x] ↔ x = y ∨ y ∈ l.
Proof. rewrite in_app_iff; simpl; tauto. Qed.

Fact snoc_assoc X l (x y : X) : l++[x;y] = (l++[x])++[y].
Proof. now rewrite <- app_assoc. Qed.

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

Unset Elimination Schemes.

Inductive E0 : Set :=
  | E0_cons : list (E0*nat) → E0.

Set Elimination Schemes.

Notation "'ω[' l ]" := (E0_cons l) (at level 1, no associativity, format "ω[ l ]").

Fact E0_eq_inv l m : ω[l] = ω[m] → l = m.
Proof. now inversion 1. Qed.

Section E0_rect.

  Let E0_sub e f := match f with ω[l] => ∃n, (e,n) ∈ l end.

  Local Lemma E0_sub_wf : well_founded E0_sub.
  Proof.
    refine (fix loop f := _).
    destruct f as [ l ].
    constructor; intros e (n & Hn).
    induction l as [ | y l IHl ].
    + destruct Hn.
    + destruct Hn as [ Hn | Hn ]; [ | apply IHl; assumption ].
      generalize (loop (fst y)). (* be careful here on what loop is applied *)
      clear loop; now subst.
  Qed.

  Variables (P : E0 → Type)
            (HP : ∀l, (∀ e n, (e,n) ∈ l → P e) → P ω[l]).

  Theorem E0_rect e : P e.
  Proof.
    apply Fix_F with (2 := E0_sub_wf e).
    intros [l] Hl.
    apply HP.
    intros f n Hfn; apply Hl; simpl; eauto.
  Defined.

End E0_rect.

Definition E0_ind (P : _ → Prop) := E0_rect P.
Definition E0_rec (P : _ → Set) := E0_rect P.

Fixpoint E0_ht e :=
  match e with
  | ω[l] => lmax (map (λ x, 1+E0_ht (fst x)) l)
  end.

Fact E0_ht_fix l : E0_ht ω[l] = lmax (map (λ x, 1+E0_ht (fst x)) l).
Proof. trivial. Qed.

Fact lmax_cons x l : lmax (x::l) = max x (lmax l).
Proof. induction l; simpl; lia. Qed.

Fact lmax_bounded n l : (∀ x : nat, x ∈ l → x ≤ n) → lmax l ≤ n.
Proof. rewrite <- Forall_forall; induction 1; simpl; lia. Qed.

Fact E0_ht_in e i l : (e,i) ∈ l → E0_ht e < E0_ht ω[l].
Proof.
  intros H; rewrite E0_ht_fix.
  apply lmax_in, in_map_iff.
  now exists (e,i).
Qed.

Definition E0_fall (P : list (E0*nat) → Prop) : E0 → Prop :=
  fix loop e :=
    match e with
    | ω[l] => P l ∧ fold_right (λ p, and (loop (fst p))) True l
    end.

Lemma E0_fall_fix P l : E0_fall P ω[l] ↔ P l ∧ ∀ x i, (x,i) ∈ l → E0_fall P x.
Proof.
  simpl; rewrite fold_right_conj.
  apply and_iff_compat_l.
  split.
  + intros H ? ?; apply (H (_,_)).
  + intros ? []; eauto.
Qed.

Section E0_fall_rect.

  Variables (P : list (E0*nat) → Prop)
            (Q : E0 → Type)
            (HQ : ∀l, P l 
                    → (∀ e i, (e,i) ∈ l → E0_fall P e)
                    → (∀ e i, (e,i) ∈ l → Q e)
                    → Q ω[l]).

  Theorem E0_fall_rect e : E0_fall P e → Q e.
  Proof. induction e; intros []%E0_fall_fix; eauto. Qed.

End E0_fall_rect.

Section lex2.

  Variables (X I : Type) (RX : X → X → Prop) (RI : I → I → Prop).

  Inductive lex2 : X*I → X*I → Prop :=
    | lex2_left x i y j : RX x y → lex2 (x,i) (y,j)
    | lex2_right x i j  : RI i j → lex2 (x,i) (x,j).

  Hint Constructors lex2 : core.

  Fact lex2_inv xi yj :
      lex2 xi yj
    → match xi, yj with
      | (x,i), (y,j) => RX x y ∨ x = y ∧ RI i j
      end.
  Proof. destruct 1; eauto. Qed.

  Lemma lex2_irrefl xi : lex2 xi xi → RX (fst xi) (fst xi) ∨ RI (snd xi) (snd xi).
  Proof. revert xi; intros []?%lex2_inv; simpl; tauto. Qed.

  Section lex2_trans.

    Variables (l m p : list (X*I))
              (RXtrans : ∀ x i y j z u, (x,i) ∈ l → (y,j) ∈ m → (z,u) ∈ p → RX x y → RX y z → RX x z)
              (RItrans : ∀ x i y j z u, (x,i) ∈ l → (y,j) ∈ m → (z,u) ∈ p → RI i j → RI j u → RI i u).

    Lemma lex2_trans xi yj zk : xi ∈ l → yj ∈ m → zk ∈ p → lex2 xi yj → lex2 yj zk → lex2 xi zk.
    Proof.
      revert xi yj zk.
      intros [] [] [] ? ? ? [ | (<- & ?) ]%lex2_inv [ | (<- & ?) ]%lex2_inv; eauto.
    Qed.

  End lex2_trans.

  Hint Constructors sdec : core.

  Section lex2_sdec.

    Variables (l m : list (X*I))
              (RX_sdec : ∀ x i y j, (x,i) ∈ l → (y,j) ∈ m → sdec RX x y)
              (RI_sdec : ∀ x i y j, (x,i) ∈ l → (y,j) ∈ m → sdec RI i j).

    Lemma lex2_sdec xi yj : xi ∈ l → yj ∈ m → sdec lex2 xi yj.
    Proof.
      revert xi yj; intros (x,i) (y,j) ? ?.
      destruct (RX_sdec x i y j) as [| x |]; eauto.
      destruct (RI_sdec x i x j); eauto.
    Qed.

  End lex2_sdec.

  Section Acc.

    Hypothesis RI_wf : well_founded RI.

    Fact Acc_lex2 x : Acc RX x → ∀i, Acc lex2 (x,i).
    Proof.
      induction 1 as [ x _ IHx ].
      intros i; induction i using (well_founded_induction RI_wf).
      constructor.
      intros [] [ | (<- & ?) ]%lex2_inv; eauto.
    Qed.

  End Acc.

End lex2.

Arguments lex2 {_ _}.

#[local] Hint Constructors lex2 : core.

Section wlist_combine.

  Variables (X : Type) (R : X → X → Prop) (R_sdec : ∀ x y, sdec R x y).

  Implicit Type (l m : list (X*nat)).

  Fixpoint wlist_cut m y j :=
    match m with
    | []       => [(y,j)]
    | (x,i)::m =>
      match R_sdec x y with
      | sdec_lt _ _ _ _ => [(y,j)]
      | sdec_eq _ _     => [(x,i+j)]
      | sdec_gt _ _ _ _ => (x,i)::wlist_cut m y j
      end
    end.

  Fact wlist_cut_spec m y j :
      Forall (λ x, R y (fst x)) m ∧ wlist_cut m y j = m++[(y,j)]
    ∨ (∃ i l r, m   = l++[(y,i)]++r ∧ Forall (λ x, R y (fst x)) l ∧ wlist_cut m y j = l++[(y,i+j)])
    ∨ (∃ x i l r, m = l++[(x,i)]++r ∧ Forall (λ x, R y (fst x)) l ∧ R x y ∧ wlist_cut m y j = l++[(y,j)]).
  Proof.
    induction m as [ | (x,i) m IH ]; simpl.
    + left; simpl; auto.
    + destruct (R_sdec x y) as [ x y H | y | x y H ].
      * do 2 right; exists x, i, [], m; simpl; auto.
      * right; left; exists i, [], m; simpl; auto.
      * destruct IH 
          as [ (H1 & ->) 
           | [ (k & l & r & E & ? & ->) 
             | (z & k & l & r & E & ? & ? & ->) ] ].
        - left; auto.
        - subst m; right; left; exists k, ((x,i)::l), r; simpl; auto.
        - subst m; do 2 right.
          exists z, k, ((x,i)::l), r; auto.
  Qed.

  Fact wlist_cut_choice m y : 
      Forall (λ x, R y (fst x)) m
    ∨ (∃ i l r,   m = l++[(y,i)]++r ∧ Forall (λ x, R y (fst x)) l)
    ∨ (∃ x i l r, m = l++[(x,i)]++r ∧ Forall (λ x, R y (fst x)) l ∧ R x y).
  Proof.
    induction m as [ | (x,i) m IH ]; simpl.
    + left; simpl; auto.
    + destruct (R_sdec x y) as [ x y H | y | x y H ].
      * do 2 right; exists x, i, [], m; simpl; auto.
      * right; left; exists i, [], m; simpl; auto.
      * destruct IH 
          as [ H1 
           | [ (k & l & r & E & ?) 
             | (z & k & l & r & E & ? & ?) ] ].
        - left; auto.
        - subst m; right; left; exists k, ((x,i)::l), r; simpl; auto.
        - subst m; do 2 right.
          exists z, k, ((x,i)::l), r; auto.
  Qed.

  Hypothesis (R_irrefl : ∀x, ~ R x x) (R_trans : transitive R).

  Fact wlist_cut_spec1 m y j :
      Forall (λ x, R y (fst x)) m
    → wlist_cut m y j = m++[(y,j)].
  Proof.
    induction 1 as [ | (x,i) m H1 H2 IH2 ]; simpl; auto.
    destruct (R_sdec x y) as [ x y H | y | x y H ].
    + destruct (@R_irrefl x); eauto.
    + destruct (R_irrefl H1).
    + f_equal; auto.
  Qed.

  Fact wlist_cut_gt_list l r y j :
      Forall (λ x, R y (fst x)) l
    → wlist_cut (l++r) y j = l++wlist_cut r y j.
  Proof.
    induction 1 as [ | (x,k) m H1 H2 IH2 ]; simpl; auto.
    + destruct (R_sdec x y) as [ x y H | x | x y H ].
      * destruct (@R_irrefl x); eauto.
      * destruct (R_irrefl H1).
      * f_equal; auto.
  Qed.

  Fact wlist_cut_gt x i r y j :
      R y x
    → wlist_cut ((x,i)::r) y j = (x,i)::wlist_cut r y j.
  Proof.
    intro; apply wlist_cut_gt_list with (l := [_]).
    constructor; auto.
  Qed.

  Local Fact R_sdec_refl x y : 
      x = y
    → match R_sdec x y with
      | sdec_lt _ _ _ _ => False
      | sdec_eq _ _     => True
      | sdec_gt _ _ _ _ => False
      end.
  Proof. intros; destruct (R_sdec x y); auto; subst; eapply R_irrefl; eauto. Qed.

  Fact wlist_cut_eq i r y j : wlist_cut ((y,i)::r) y j = [(y,i+j)].
  Proof.
    simpl.
    generalize (@R_sdec_refl y y eq_refl).
    destruct (R_sdec y y); tauto.
  Qed.

  Fact wlist_cut_lt x i r y j : R x y → wlist_cut ((x,i)::r) y j = [(y,j)].
  Proof.
    simpl; intro H.
    destruct (R_sdec x y); auto.
    + destruct (R_irrefl H).
    + destruct (@R_irrefl x); eauto.
  Qed.

  Fact wlist_cut_spec2 l y i r j :
      Forall (λ x, R y (fst x)) l
    → wlist_cut (l++[(y,i)]++r) y j = l++[(y,i+j)].
  Proof.
    induction 1 as [ | (x,k) m H1 H2 IH2 ]; simpl; auto.
    + generalize (@R_sdec_refl y y eq_refl).
      now destruct (R_sdec y y) as [ | y | ].
    + destruct (R_sdec x y) as [ x y H | x | x y H ].
      * destruct (@R_irrefl x); eauto.
      * destruct (R_irrefl H1).
      * simpl in IH2; rewrite IH2; auto.
  Qed.

  Fact wlist_cut_spec3 l x y i r j :
      Forall (λ x, R y (fst x)) l
    → R x y 
    → wlist_cut (l++[(x,i)]++r) y j = l++[(y,j)].
  Proof.
    intros H1 Hxy; revert H1.
    induction 1 as [ | (u,k) m H1 H2 IH2 ]; simpl; auto.
    + destruct (R_sdec x y) as [ | y | ]; auto.
      * destruct (R_irrefl Hxy).
      * destruct (@R_irrefl y); eauto.
    + destruct (R_sdec u y) as [ u y H | y | u y H ].
      * destruct (@R_irrefl u); eauto.
      * destruct (R_irrefl H1).
      * simpl in IH2; rewrite IH2; auto.
  Qed.

  Fact wlist_cut_last l y j : ∃m k, j ≤ k ∧ wlist_cut l y j = m++[(y,k)].
  Proof.
    induction l as [ | (x,i) l (m & k & Hk & Hw) ]; simpl.
    + exists [], j; auto.
    + destruct (R_sdec x y) as [ x y H | x | x y H ].
      * exists [], j; auto.
      * exists [], (i+j); split; auto; lia.
      * exists ((x,i)::m), k; split; simpl; auto.
        now f_equal.
  Qed. 

  Local Fact wlist_cut_ordered_from a l y j : R y a → ordered_from R⁻¹ a (map fst l) → ordered_from R⁻¹ a (map fst (wlist_cut l y j)).
  Proof.
    induction l as [ | (x,i) l IHl ] in a |- *; simpl; intros Ha.
    + constructor; auto; constructor.
    + intros (H1 & H2)%ordered_from_inv.
      destruct (R_sdec x y) as [ x y Hxy | x | x y Hxy ].
      * repeat constructor; auto.
      * repeat constructor; auto.
      * simpl; constructor; auto.
  Qed.

  Local Fact wlist_cut_ub l y j : ∀ a u, (a,u) ∈ wlist_cut l y j → R y a ∨ y = a.
  Proof.
    induction l as [ | (x,i) l IHl ]; simpl; intros a u.
    + intros [ [=] | [] ]; auto.
    + destruct (R_sdec x y).
      * intros [ [=] | [] ]; auto.
      * intros [ [=] | [] ]; auto.
      * intros [ [=] | ? ]; subst; eauto.
  Qed.

  Hint Resolve wlist_cut_ordered_from : core.

  Local Fact wlist_cut_ordered l y j : ordered R⁻¹ (map fst l) → ordered R⁻¹ (map fst (wlist_cut l y j)).
  Proof.
    destruct l as [ | (x,i) l ]; simpl.
    + repeat constructor.
    + intros ?%ordered_inv.
      destruct (R_sdec x y).
      * repeat constructor.
      * repeat constructor.
      * simpl; constructor; eauto.
  Qed.

  Definition wlist_combine l m :=
    match m with
    | []       => l
    | (y,j)::m => wlist_cut l y j ++ m
    end.

  Fact wlist_combine_spec_nil l : wlist_combine l [] = l.
  Proof. trivial. Qed.

  Fact wlist_combine_spec_cons l y j m :
      Forall (fun x => R y (fst x)) l ∧ wlist_combine l ((y,j)::m) = l++[(y,j)]++m
    ∨ (∃ i a b,   l = a++[(y,i)]++b ∧ Forall (fun x => R y (fst x)) a ∧ wlist_combine l ((y,j)::m) = a++[(y,i+j)]++m)
    ∨ (∃ x i a b, l = a++[(x,i)]++b ∧ Forall (fun x => R y (fst x)) a ∧ R x y ∧ wlist_combine l ((y,j)::m) = a++[(y,j)]++m).
  Proof.
    simpl.
    destruct (wlist_cut_spec l y j)
      as [ (H1 & ->) 
       | [ (k & a & b & E & H1 & ->) 
         | (z & k & a & b & E & H1 & H2 & ->) ] ]; subst; rewrite <- !app_assoc; auto.
    + right; left; exists k, a, b; auto. 
    + do 2 right; exists z, k, a, b; auto.
  Qed.

  Fact wlist_combine_gt_list l r y j m :
      Forall (λ x, R y (fst x)) l
    → wlist_combine (l++r) ((y,j)::m) = l++wlist_combine r ((y,j)::m).
  Proof.
    simpl; intros.
    rewrite wlist_cut_gt_list; auto.
    now rewrite app_assoc.
  Qed.

  Fact wlist_combine_gt x i r y j m :
      R y x
    → wlist_combine ((x,i)::r) ((y,j)::m) = (x,i)::wlist_combine r ((y,j)::m).
  Proof.
    intros.
    apply wlist_combine_gt_list with (l := [_]).
    constructor; auto.
  Qed.

  Fact wlist_combine_eq i r y j m :
      wlist_combine ((y,i)::r) ((y,j)::m) = (y,i+j)::m.
  Proof.
    unfold wlist_combine.
    now rewrite wlist_cut_eq.
  Qed.

  Fact wlist_combine_lt x i r y j m :
      R x y -> wlist_combine ((x,i)::r) ((y,j)::m) = (y,j)::m.
  Proof.
    unfold wlist_combine; intro.
    now rewrite wlist_cut_lt.
  Qed.

  Fact wlist_combine_choice x i l y j m :
    ∃ z k r, wlist_combine ((x,i)::l) ((y,j)::m) = (z,k)::r
           ∧ ( R x y ∧ z = y ∧ k = j ∧ r = m
             ∨ x = y ∧ z = x ∧ k = i+j ∧ r = m
             ∨ R y x ∧ z = x ∧ k = i ∧ r = wlist_combine l ((y,j)::m) ).
  Proof.
    destruct (R_sdec x y) as [ x y H | x | x y H ].
    + rewrite wlist_combine_lt; auto.
      exists y, j, m; split; auto.
    + rewrite wlist_combine_eq.
      exists x, (i+j), m; split; auto; right; auto.
    + rewrite wlist_combine_gt; auto.
      exists x, i, (wlist_combine l ((y,j)::m)); split; auto; do 2 right; auto.
  Qed. 

  Fact wlist_combine_in l m x i : (x,i) ∈ wlist_combine l m → ∃j, j ≤ i ∧ ((x,j) ∈ l ∨ (x,j) ∈ m).
  Proof.
    destruct m as [ | (y,j) m ].
    + rewrite wlist_combine_spec_nil.
      exists i; auto.
    + destruct (wlist_combine_spec_cons l y j m)
        as [ (H1 & ->) 
         | [ (k & a & b & E & H1 & ->) 
           | (z & k & a & b & E & H1 & H2 & ->) ] ]; subst.
      * intros []%in_app_iff; eauto.
      * intros [H|[[=]|H]]%in_app_iff; subst; eauto.
        - exists i; rewrite in_app_iff; auto.
        - exists j; simpl; split; eauto; lia.
      * intros []%in_app_iff; eauto.
        exists i; rewrite in_app_iff; eauto.
  Qed.

  Fact wlist_combine_spec1 l y j m :
      Forall (λ x, R y (fst x)) l
    → wlist_combine l ((y,j)::m) = l++[(y,j)]++m.
  Proof.
    intros H.
    unfold wlist_combine.
    rewrite wlist_cut_spec1, <- app_assoc; auto.
  Qed.

  Fact wlist_combine_spec2 l y i r j m :
      Forall (λ x, R y (fst x)) l
    → wlist_combine (l++[(y,i)]++r) ((y,j)::m) = l++[(y,i+j)]++m.
  Proof.
    intros H.
    unfold wlist_combine.
    rewrite wlist_cut_spec2, <- app_assoc; auto.
  Qed.

  Fact wlist_combine_spec3 l x i r y j m :
      Forall (λ x, R y (fst x)) l
    → R x y
    → wlist_combine (l++[(x,i)]++r) ((y,j)::m) = l++[(y,j)]++m.
  Proof.
    intros H1 H2.
    unfold wlist_combine.
    rewrite wlist_cut_spec3, <- app_assoc; auto.
  Qed.

  Fact wlist_combine_last l m y j :
    ∃ r k, j ≤ k ∧ wlist_combine l (m++[(y,j)]) = r++[(y,k)].
  Proof.
    destruct m as [ | (z,p) m ]; simpl.
    + destruct (wlist_cut_last l y j) as (r & k & ? & E).
      exists r, k; split; auto; now rewrite app_nil_r.
    + exists (wlist_cut l z p ++ m), j; split; auto.
      now rewrite app_assoc.
  Qed.

  Fact wlist_combine_ordered l m : ordered R⁻¹ (map fst l) → ordered R⁻¹ (map fst m) → ordered R⁻¹ (map fst (wlist_combine l m)).
  Proof.
    destruct m as [ | (y,j) m ]; simpl; auto.
    intros Hl Hm%ordered_inv.
    rewrite map_app.
    apply wlist_cut_ordered with (y := y) (j := j) in Hl.
    generalize (wlist_cut_ub l y j); intros H.
    apply ordered_from_app_middle with y; eauto.
    intros ? ((x,i) & <- & ?)%in_map_iff; simpl; eauto.
    destruct (H x i) as [ | <- ]; eauto.
  Qed. 

End wlist_combine.

Arguments wlist_cut {_ _}.
Arguments wlist_combine {_ _}.

Unset Elimination Schemes.

Inductive E0_lt : E0 → E0 → Prop :=
  | E0_lt_intro l m : lex_list (lex2 E0_lt lt) l m → E0_lt ω[l] ω[m].

Set Elimination Schemes.

#[local] Hint Constructors E0_lt : core.

Notation "e '<E₀' f" := (E0_lt e f) (at level 70, format "e  <E₀  f").

(* This inversion principle is enough to reason about <ε₀, 
   proceeding by induction on arguments *)
Fact E0_lt_inv l m : ω[l] <E₀ ω[m] ↔ lex_list (lex2 E0_lt lt) l m.
Proof. split; auto; now inversion 1. Qed.

(** We show that <E₀ is a strict order (irreflexive and transitive)
    and computably total, ie either e <E₀ f or e = f or f <E₀ e *)

(* irreflexive *)
Lemma E0_lt_irrefl e : ¬ e <E₀ e.
Proof.
  induction e as [ l IH ].
  intros ((?,i) & ? & [ ?%(IH _ i) | ?%lt_irrefl ]%lex2_irrefl)%E0_lt_inv%lex_list_irrefl; auto.
Qed.

#[local] Hint Resolve lt_trans lex2_trans : core.

(* transitive *)
Lemma E0_lt_trans : transitive E0_lt.
Proof.
  intros e.
  induction e as [ l IH ]. 
  intros [] [] H1%E0_lt_inv H2%E0_lt_inv; constructor.
  revert H1 H2; apply lex_list_trans; eauto.
Qed.

#[local] Hint Constructors sdec : core.

Lemma lt_sdec i j : sdec lt i j.
Proof. destruct (lt_eq_lt_dec i j) as [ [ | []] | ]; eauto. Qed.

#[local] Hint Resolve lt_sdec lex2_sdec : core.

(* computably total *)
Lemma E0_lt_sdec e f : sdec E0_lt e f.
Proof.
  revert f; induction e as [l]; intros [m].
  destruct (@lex_list_sdec _ (lex2 E0_lt lt) l m); eauto.
Qed.

#[local] Hint Resolve E0_lt_trans E0_lt_irrefl : core.

(* Hence decidable *)
Corollary E0_lt_dec e f : { e <E₀ f } + { ¬ e <E₀ f }.
Proof.
  destruct (E0_lt_sdec e f) as [ | | e f ]; eauto.
  right; intro; apply (@E0_lt_irrefl e); eauto.
Qed.

#[local] Hint Resolve E0_lt_dec : core.

Corollary E0_lt_trans' e f : clos_trans E0_lt e f → e <E₀ f.
Proof. induction 1; eauto. Qed.

(** An "ordinal" of E₀ is in CNF if, recursivelly, it is
   of the shape ω[(e₁,i₁);...;(eₙ,iₙ)] with
   0 < i₁,...,iₙ and e₁ >ε₀ ... >ε₀ eₙ *)

Definition E0_cnf_pred l :=
    (∀ e i, (e,i) ∈ l → 0 < i) ∧ ordered E0_lt⁻¹ (map fst l).

Definition E0_cnf := E0_fall E0_cnf_pred.

Fact E0_cnf_fix l : 
    E0_cnf ω[l]
  ↔ ordered E0_lt⁻¹ (map fst l) ∧ ∀ e i, (e,i) ∈ l → 0 < i ∧ E0_cnf e.
Proof. 
  unfold E0_cnf.
  rewrite E0_fall_fix.
  unfold E0_cnf_pred; firstorder.
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

(* E0_cnf is a strongly decidable predicate *)
Theorem E0_cnf_dec e : { E0_cnf e } + { ¬ E0_cnf e }.
Proof.
  induction e as [ l IHl ].
  destruct (ordered_dec E0_lt⁻¹ (map fst l))
    as [ H1 | H1 ]; eauto.
  + destruct list_fall_choose
      with (P := fun xi => snd xi = 0 \/ ~ E0_cnf (fst xi))
           (Q := fun xi => 0 < snd xi /\ E0_cnf (fst xi))
           (l := l)
      as [ ((x,i) & H2 & H3) | H2 ].
    * intros (x,[|i]) [ H | H ]%IHl; simpl; try tauto.
      right; split; auto; lia.
    * right; rewrite E0_cnf_fix; intros (_ & G).
      simpl in H3; apply G in H2.
      destruct H2, H3; subst; tauto || lia.
    * left; rewrite E0_cnf_fix; split; auto.
      intros; apply (H2 (_,_)); auto.
  + right; rewrite E0_cnf_fix; tauto.
Qed.

Inductive E0_lpo : E0 → E0 → Prop :=
  | E0_lpo_intro l m : lo (lex2 E0_lpo lt) l m → E0_lpo ω[l] ω[m].

#[local] Hint Constructors E0_lpo : core.

Fact E0_lpo_inv l m : E0_lpo ω[l] ω[m] → lo (lex2 E0_lpo lt) l m.
Proof. now inversion 1. Qed.

#[local] Hint Resolve lt_wf : core.

Lemma wf_E0_lpo : well_founded E0_lpo.
Proof.
  intros e.
  induction e as [ l IH ].
  assert (Acc (lo (lex2 E0_lpo lt)) l) as Hl.
  1:{ apply Acc_lo_iff.
      intros [] ?.
      apply Acc_lex2; eauto. }
  revert Hl.
  apply Acc_rel_morph with (f := fun l e => ω[l] = e); auto.
  + intros []; eauto.
  + now intros ? ? ? ? <- <- ?%E0_lpo_inv.
Qed.

Fact Acc_irrefl X (R : X → X → Prop) x : Acc R x → ~ R x x.
Proof. induction 1 as [ x _ IH ]; intros H; exact (IH _ H H). Qed.

Fact E0_lpo_irrefl e : ¬ E0_lpo e e.
Proof. apply Acc_irrefl with (1 := wf_E0_lpo _). Qed.

Fact E0_lpo_trans : transitive E0_lpo.
Proof.
  intros [l] [m] [k] ?%E0_lpo_inv ?%E0_lpo_inv.
  constructor; econstructor 2; eauto.
Qed.

#[local] Hint Resolve E0_lpo_trans : core.

Fact E0_lpo_trans' e f : clos_trans E0_lpo e f → E0_lpo e f.
Proof. induction 1; eauto. Qed.

Definition E0_le e f := e <E₀ f ∨ e = f.

Notation "e '≤E₀' f" := (E0_le e f) (at level 70, format "e  ≤E₀  f").

Fact E0_le_refl e : e ≤E₀ e.
Proof. now right. Qed.

Fact E0_le_trans : transitive E0_le.
Proof. intros ? ? ? [] []; subst; red; eauto. Qed.

#[local] Hint Resolve E0_le_refl E0_le_trans : core.

Fact E0_le_lt_trans e f g : e ≤E₀ f → f <E₀ g → e <E₀ g.
Proof. intros [] ?; subst; eauto. Qed.

Fact E0_lt_le_trans e f g : e <E₀ f → f ≤E₀ g → e <E₀ g.
Proof. intros ? []; subst; eauto. Qed.

Definition E0_zero := ω[[]].

Notation "0₀" := E0_zero.

Fact E0_zero_le e : 0₀ ≤E₀ e.
Proof.
  destruct e as [ [] ]; [ right | left ]; eauto.
  repeat constructor.
Qed.

#[local] Hint Resolve E0_zero_le : core.

Fact E0_zero_not_gt e : ¬ e <E₀ 0₀.
Proof.
  destruct e as [ l ].
  intros ?%E0_lt_inv%lex_list_inv.
  now destruct l.
Qed.

Section squash.

  (* Squashing map a (strongly) decidable predicate into
     an equivalent proof irrelevant one *)

  Variables (P : Prop) (d : {P}+{~P}).

  Definition squash := if d then True else False.

  Fact squash_iff : squash ↔ P.
  Proof. unfold squash; destruct d; tauto. Qed.

  Fact squash_pirr : ∀ p1 p2 : squash, p1 = p2.
  Proof. unfold squash; destruct d; now intros [] []. Qed.

End squash.

(* We convert E0_cnf into an equivalent proof irrelevant predicate *)
Definition cnf e := squash (E0_cnf_dec e).

Fact cnf_iff e : cnf e ↔ E0_cnf e.          Proof. apply squash_iff. Qed.
Fact cnf_pirr e (h1 h2 : cnf e) : h1 = h2.  Proof. apply squash_pirr. Qed.

Fact cnf_fix l : 
    cnf ω[l]
  ↔ ordered E0_lt⁻¹ (map fst l) ∧ ∀ e i, (e,i) ∈ l → 0 < i ∧ cnf e.
Proof.
  rewrite cnf_iff, E0_cnf_fix.
  apply and_iff_compat_l.
  split; intros H ? ? []%H; split; auto; apply cnf_iff; auto.
Qed.

(* We convert the recursor *)
Fact cnf_rect (P : E0 → Type) :
    (∀l, ordered E0_lt⁻¹ (map fst l) 
       → (∀ e i, (e,i) ∈ l → 0 < i)
       → (∀ e i, (e,i) ∈ l → cnf e)
       → (∀ e i, (e,i) ∈ l → P e)
       → P ω[l])
  → ∀e, cnf e → P e.
Proof. 
  intros HP h H%cnf_iff; revert h H.
  induction 1 as [ l [] H2 IH ] using E0_fall_rect.
  apply HP; auto.
  intros ? i ?.
  apply cnf_iff, (H2 _ i); auto.
Qed.

Fact cnf_sg e i : cnf e → 0 < i → cnf ω[[(e,i)]].
Proof.
  rewrite cnf_fix; split.
  + repeat constructor.
  + intros ? ? [[=]|[]]; subst; eauto.
Qed.

Fact cnf_cons_inv e i l : cnf ω[(e,i)::l] → cnf e.
Proof. intros (_ & H)%cnf_fix; eapply H; eauto. Qed.

Fact cnf_app_left_inv l m : cnf ω[l++m] → cnf ω[l].
Proof.
  rewrite !cnf_fix, map_app, ordered_app_iff; auto.
  intros ((? & ? & H) & ?); split; try tauto; eauto.
Qed.

Fact cnf_app_right_inv l m : cnf ω[l++m] → cnf ω[m].
Proof.
  rewrite !cnf_fix, map_app, ordered_app_iff; auto.
  intros ((? & ? & H) & ?); split; try tauto; eauto.
Qed.

#[local] Hint Resolve cnf_sg cnf_cons_inv 
                      cnf_app_left_inv cnf_app_right_inv : core.

Fact ordered_from_lmax x l : ordered_from (λ n m, m ≤ n) x l → lmax l ≤ x.
Proof. induction 1; simpl; lia. Qed.

Fact ordered_lmax l :
    ordered (λ n m, m ≤ n) l
  → match l with
    | []   => True
    | x::l => lmax (x::l) = x
    end.
Proof. induction 1 as [ | ? ? ?%ordered_from_lmax ]; simpl; lia. Qed.

Fact ordered_lmax_cons x l : ordered (λ n m, m ≤ n) (x::l) → lmax (x::l) = x.
Proof. exact (@ordered_lmax (_::_)). Qed.

(** Factor that proof !! *)
Local Lemma E0_lt_ht_rec n e f : E0_ht e < n → E0_ht f < n → cnf e → cnf f → e <E₀ f → E0_ht e ≤ E0_ht f.
Proof.
  revert e f; induction n as [ | n IHn ].
  + intros; lia.
  + intros [ l ] [ m ]; rewrite !E0_ht_fix.
    intros Hl Hm (H1 & H2)%cnf_fix (H3 & H4)%cnf_fix Hlm%E0_lt_inv.
    assert (∀ e i, (e,i) ∈ l → cnf e) as H2'.
    1: intros; eapply H2; eauto.
    assert (∀ e i, (e,i) ∈ m → cnf e) as H4'.
    1: intros; eapply H4; eauto.
    assert (∀ e i, (e,i) ∈ l → E0_ht e < n) as G1.
    1:{ intros e i ?; apply PeanoNat.lt_S_n, Nat.le_lt_trans with (2 := Hl).
        apply lmax_in, in_map_iff; exists (e,i); eauto. }
    assert (∀ e i, (e,i) ∈ m → E0_ht e < n) as G2.
    1:{ intros e i ?; apply PeanoNat.lt_S_n, Nat.le_lt_trans with (2 := Hm).
        apply lmax_in, in_map_iff; exists (e,i); eauto. }
    assert (ordered le⁻¹ (map (λ x, 1 + E0_ht (fst x)) l)) as H1'.
    1:{ revert H1.
        rewrite <- (map_map fst (λ x, S (E0_ht x))).
        apply ordered_mono_map with (f := λ x, S (E0_ht x)).
        intros ? ? ((x,i) & <- & E1)%in_map_iff ((y,j) & <- & E2)%in_map_iff; simpl.
        intros H; apply le_n_S, IHn; eauto. }
    assert (ordered le⁻¹ (map (λ x, 1 + E0_ht (fst x)) m)) as H3'.
    1:{ revert H3.
        rewrite <- (map_map fst (λ x, S (E0_ht x))).
        apply ordered_mono_map with (f := λ x, S (E0_ht x)).
        intros ? ? ((x,i) & <- & E1)%in_map_iff ((y,j) & <- & E2)%in_map_iff; simpl.
        intros H; apply le_n_S, IHn; eauto. }
    assert (∀ e i f j, (e,i) ∈ l → (f,j) ∈ m → e <E₀ f → E0_ht e ≤ E0_ht f) as IH.
    1:{ intros; apply IHn; eauto. }
    clear IHn Hl Hm H1 H2 H3 H4 H2' H4' G1 G2.
    induction Hlm as [ | (e,i) (f,j) | ].
    * simpl; lia.
    * simpl map; rewrite !ordered_lmax_cons; auto.
      apply lex2_inv in H as [ H | (? & _) ]; subst; auto.
      apply le_n_S; eauto.
    * simpl map; rewrite !ordered_lmax_cons; auto.
Qed.

(** The height is an over approx. of <E₀ *)
Theorem E0_lt_ht e f : cnf e → cnf f → e <E₀ f → E0_ht e ≤ E0_ht f.
Proof. apply E0_lt_ht_rec with (n := 1+E0_ht e+E0_ht f); lia. Qed.

Corollary E0_ht_lt e f : cnf e → cnf f → E0_ht e < E0_ht f → e <E₀ f.
Proof.
  intros H1 H2 H3.
  destruct (E0_lt_sdec e f) as [ e f H | e | e f H ]; auto.
  + lia.
  + apply E0_lt_ht in H; auto; lia.
Qed.

Corollary E0_lt_sub x i l : cnf ω[l] → (x,i) ∈ l → x <E₀ ω[l].
Proof.
  intros H1 H2.
  apply E0_ht_lt; auto.
  + apply cnf_fix, proj2 in H1.
    apply (H1 _ _ H2).
  + eapply E0_ht_in; eauto.
Qed.

(** Complete this thing that show that the height is easy quick to compute on cnf *)
Fact cnf_ht e i l : cnf ω[(e,i)::l] → E0_ht ω[(e,i)::l] = 1+E0_ht e.
Proof.
  intros (H1 & H2)%cnf_fix.
  rewrite E0_ht_fix; simpl map.
  rewrite ordered_lmax_cons; auto.
  revert H1.
  rewrite <- (map_map fst (λ x, S (E0_ht x))).
  apply ordered_mono_map with (f := λ x, S (E0_ht x)).
  intros a b ((x,u) & <- & Hx)%in_map_iff ((y,v) & <- & Hy)%in_map_iff ?.
  apply le_n_S, E0_lt_ht; eauto; simpl.
  + apply H2 with v; auto.
  + apply H2 with u; auto.
Qed.

Fact lex2_E0_lpo_lt_trans : transitive (lex2 E0_lpo lt).
Proof. intros a b c; apply lex2_trans with [a] [b] [c]; eauto. Qed.

#[local] Hint Resolve lex2_E0_lpo_lt_trans : core.

Fact lex2_E0_lpo_lt_trans' xi yj : clos_trans (lex2 E0_lpo lt) xi yj → lex2 E0_lpo lt xi yj.
Proof. induction 1; eauto. Qed.

#[local] Hint Resolve lex_list_mono : core.

(** The fundamental theorem: E0_lt is well-founded on CNF *)
Lemma cnf_lt_lpo e f : cnf e → cnf f → e <E₀ f → E0_lpo e f.
Proof.
  intros H1 H2; revert e H1 f H2.
  induction 1 as [ l He1 He2 He3 IH ] using cnf_rect.
  induction 1 as [ m Hf1 Hf2 Hf3 _   ] using cnf_rect.
  intros H%E0_lt_inv.
  constructor.
  apply lo_mono with (1 := lex2_E0_lpo_lt_trans').
  apply ordered_lex_list_lo; eauto.
  + revert He1.
    apply ordered_morphism with (f := fun x y => x = fst y).
    * intros ? ? [] [] ([] & ? & ?)%in_map_iff ([] & ? & ?)%in_map_iff -> ->; right; left; simpl in *; subst; eauto.
    * clear He2 He3 IH H; induction l; simpl; constructor; auto.
  + revert H; apply lex_list_mono.
    intros [] [] ? ? [| (<- & ?)]%lex2_inv; eauto.
Qed.

Fact E0_lt_app_head l m k : ω[m] <E₀ ω[k] → ω[l++m] <E₀ ω[l++k].
Proof.
  intros ?%E0_lt_inv; constructor.
  now apply lex_list_app_head.
Qed.

Fact E0_le_app_head l m k : ω[m] ≤E₀ ω[k] → ω[l++m] ≤E₀ ω[l++k].
Proof.
  intros [ H | H ]; [ left | right ].
  + now apply E0_lt_app_head.
  + inversion H; subst; auto.
Qed.

Fact cnf_zero : cnf 0₀.
Proof.
  apply cnf_fix; simpl; split.
  + constructor.
  + tauto.
Qed.

#[local] Hint Resolve cnf_zero : core.

Definition E0_one := ω[[(0₀, 1)]].

Notation "1₀" := E0_one.

Fact cnf_one : cnf E0_one.
Proof.
  apply cnf_fix; simpl; split.
  + repeat constructor.
  + intros e i [ [=] | [] ]; subst; split; auto; lia.
Qed.

#[local] Hint Resolve cnf_one : core.

Fact E0_one_ge r : r ≠ [] → cnf ω[r] → 1₀ ≤E₀ ω[r].
Proof.
  destruct r as [ | (x,i) r ]; [ easy | intros _ Hr ].
  destruct (E0_zero_le x) as [ Hx | <- ].
  + left; constructor; constructor; now left.
  + destruct i as [ | [ | i ] ].
    * apply cnf_fix, proj2 in Hr.
      destruct (Hr E0_zero 0); auto; lia.
    * apply E0_le_app_head with (l := [_]).
      destruct r.
      - now right.
      - left; constructor; constructor 1.
    * left; constructor; constructor; right; lia.
Qed.

Inductive E0_succ_graph : E0 → E0 → Prop :=
  | E0_succ_graph0   : E0_succ_graph 0₀ 1₀
  | E0_succ_graph1 l i : E0_succ_graph ω[l++[(0₀,i)]] ω[l++[(0₀,S i)]] 
  | E0_succ_graph2 l x i : x ≠ 0₀ → E0_succ_graph ω[l++[(x,i)]] ω[l++[(x,i);(ω[[]],1)]].

(* Inversion lemma for the graph of E0_succ *)
Lemma E0_succ_graph_inv e f :
    E0_succ_graph e f
  → (e = 0₀ → f = 1₀)
  ∧ (∀ l i, e = ω[l++[(0₀,i)]] → f = ω[l++[(0₀,S i)]])
  ∧ (∀ l x i, x ≠ 0₀ → e = ω[l++[(x,i)]] → f = ω[l++[(x,i);(ω[[]],1)]]).
Proof.
  destruct 1 as [ | l i | l x i H ]; (split; [ | split ]); eauto;
    try now intros [].
  + now destruct l.
  + intros ? i' (<- & [=])%E0_eq_inv%app_inj_tail; subst i'; auto.
  + intros l' x i' H (<- & [=])%E0_eq_inv%app_inj_tail; subst x; now destruct H.
  + now destruct l.
  + intros ? i' (<- & [=])%E0_eq_inv%app_inj_tail; subst x; now destruct H.
  + intros m y j G (<- & [=])%E0_eq_inv%app_inj_tail; subst; auto.
Qed.

Corollary E0_succ_graph_fun e f g :
   E0_succ_graph e f → E0_succ_graph e g → f = g.
Proof. intros [] G%E0_succ_graph_inv; symmetry; apply G; auto. Qed.

Definition E0_succ_pwc (e : E0) : sig (E0_succ_graph e).
Proof.
  destruct e as [l].
  destruct l as [ | l (x,i) _ ] using rev_rect.
  + exists ω[(ω[nil],1)::nil]; constructor.
  + destruct x as [ [ | y m ] ].
    * exists ω[l++[(ω[[]],S i)]]; constructor.
    * exists ω[l⊣⊢[(ω[y::m],i);(ω[[]],1)]]; now constructor.
Qed.

Definition E0_succ e := π₁ (E0_succ_pwc e).

Fact E0_succ_spec e : E0_succ_graph e (E0_succ e).
Proof. apply (proj2_sig _). Qed.

(** The successor is <E₀-greater *)
Fact E0_succ_lt e : e <E₀ E0_succ e.
Proof.
  generalize (E0_succ e) (E0_succ_spec e).
  induction 1; constructor.
  + constructor.
  + apply lex_list_app_head.
    constructor 2; right; lia.
  + apply lex_list_app_head.
    constructor 3; constructor.
Qed.

#[local] Hint Resolve E0_succ_lt : core. 

Fact E0_succ_cnf : ∀e, cnf e → cnf (E0_succ e).
Proof.
  intros e.
  generalize (E0_succ e) (E0_succ_spec e).
  induction 1 as [ | l i | l x i ]; eauto; rewrite !cnf_fix;
    intros [H1 H2]; split; simpl in *; eauto.
  + rewrite map_app in * |- *; auto.
  + intros ? ? [ [=] | ]%in_snoc_iff; subst; auto.
    split; auto || lia.
  + rewrite map_app in * |- *; simpl; auto.
    apply ordered_comp with (m := [_]); auto.
    repeat constructor.
    destruct x as [ [] ]; try easy.
    repeat constructor.
  + intros e j; rewrite snoc_assoc. 
    intros [ [=] | ]%in_snoc_iff; subst; auto.
Qed.

#[local] Hint Resolve E0_succ_cnf : core.

Definition E0_add e f :=
  match e, f with
  | ω[l], ω[m] => ω[wlist_combine E0_lt_sdec l m]
  end.

Fact E0_add_cnf : ∀ e f, cnf e → cnf f → cnf (E0_add e f).
Proof.
  intros [l] [m] (H1 & H2)%cnf_fix (H3 & H4)%cnf_fix; apply cnf_fix.
  split.
  + apply wlist_combine_ordered; auto.
  + intros ? ? (? & ? & [[]%H2|[]%H4])%wlist_combine_in;
      split; auto; lia.
Qed.

Fact E0_add_zero : ∀ e, E0_add e 0₀ = e.
Proof. intros []; simpl; auto. Qed.

Fact E0_add_one e : cnf e → E0_add e 1₀ = E0_succ e.
Proof.
  intros He.
  apply E0_succ_graph_fun with (2 := E0_succ_spec _).
  destruct e as [l]; apply cnf_fix in He as [He1 He2].
  unfold E0_add, E0_one, E0_zero.
  destruct (wlist_combine_spec_cons E0_lt_sdec l ω[[]] 1 [])
    as [ (H1 & ->) 
     | [ (k & a & b & E & H1 & ->) 
       | (z & k & a & b & E & H1 & H2 & ->) ] ]; subst.
  + destruct l as [ | ([[]],j) l _ ] using rev_ind.
    * constructor.
    * now apply Forall_app, proj2, Forall_cons_iff, proj1, E0_lt_irrefl in H1.
    * rewrite <- ! app_assoc; simpl; now constructor 3.
  + destruct b as [ | (y,j) b ]; simpl.
    * replace (k+1) with (S k) by lia; constructor.
    * rewrite map_app in He1; simpl in He1.
      now apply ordered_app_tail, ordered_inv, ordered_from_inv, proj1, E0_zero_not_gt in He1.
  + now apply E0_zero_not_gt in H2.
Qed.

Fact E0_add_zero_left e : E0_add 0₀ e = e.
Proof. destruct e as [[ | (x,i) l ]]; auto. Qed.

(* Proof that if cnf u then
   either u is E0_zero                             (limit ordinal)
      or  u is ω[l++[(E0_zero,i)]])                (successor)
      or  u is ω[l++[(e,i)]]) with  E0_zero <E₀ e  (limit ordinal) *)

(** This proof needs much better automation ... *)
Theorem E0_add_mono_left u v e : cnf u → cnf v → cnf e → u ≤E₀ v → E0_add u e ≤E₀ E0_add v e.
Proof.
  intros Hu Hv He [ H | -> ]; [ | right ]; auto.
  revert u v e Hu Hv He H.
  intros [l] [m] [[|(z,h) k]] Hl Hm Hk.
  1: rewrite !E0_add_zero; left; auto.
  intros H; revert H Hl Hm.
  intros [ q p | p (x,i) (y,j) l' m' [ H | (<- & ?) ]%lex2_inv ]%E0_lt_inv%lex_list_invert Hp Hq; clear l m.
  + unfold E0_add.
    destruct (wlist_cut_choice E0_lt_sdec (p++q) z)
      as [ G1 
       | [ (i & l & r & E & G1) 
       |   (x & i & l & r & E & G1 & G2) ] ].
    * rewrite wlist_combine_spec1 with (l := _++_); auto.
      apply Forall_app in G1 as [ G1 G2 ].
      rewrite wlist_combine_spec1; auto.
      left; constructor; rewrite <- app_assoc.
      apply lex_list_app_head.
      destruct q as [ | (v,j) q ]; [ easy | ].
      constructor 2; left.
      apply Forall_cons_iff in G2; tauto.
    * rewrite E.
      rewrite wlist_combine_spec2; auto.
      destruct (@list_split_cons (E0*nat))
        with (1 := E)
        as (m & [ (<- & ->) | (-> & <-) ]).
      - apply Forall_app in G1 as (G1 & G2).
        rewrite wlist_combine_spec1; auto.
        left; constructor.
        rewrite <- app_assoc.
        apply lex_list_app_head.
        apply cnf_fix in Hq as [Hq1 Hq2].
        rewrite !map_app in Hq1.
        apply ordered_app_tail in Hq1.
        rewrite app_assoc in Hq1.
        apply ordered_app_head in Hq1.
        simpl in Hq1.
        destruct m as [ | (u,j) m ].
        ++ constructor 2; right.
           destruct (Hq2 z i); try lia.
           apply in_app_iff; simpl; auto.
        ++ constructor 2; left.
           simpl in Hq1; apply ordered_cons_iff, proj2 in Hq1; auto.
      - rewrite wlist_combine_spec2; auto; right; auto.
    * rewrite E.
      rewrite wlist_combine_spec3; auto.
      destruct (@list_split_cons (E0*nat))
        with (1 := E)
        as (m & [ (<- & ->) | (-> & <-) ]).
      - apply Forall_app in G1 as (G1 & G3).
        rewrite wlist_combine_spec1; auto.
        destruct m as [ | (u,j) m ].
        1: right; rewrite app_nil_r; auto.
        left; constructor.
        rewrite <- app_assoc.
        apply lex_list_app_head.
        constructor 2; left.
        apply Forall_cons_iff, proj1 in G3; auto.
      - rewrite wlist_combine_spec3; auto; right; auto.
  + unfold E0_add.
    destruct (wlist_cut_choice E0_lt_sdec (p++[(y,j)]++m') z)
      as [ G1 
       | [ (i' & l & r & E & G1) 
       |   (x' & i' & l & r & E & G1 & G2) ] ].
    * rewrite wlist_combine_spec1 with (3 := G1); auto.
      simpl in G1; rewrite Forall_app, Forall_cons_iff in G1; simpl in G1.
      destruct G1 as (G1 & G2 & G3).
      rewrite wlist_combine_gt_list; auto.
      simpl app at 2.
      destruct (E0_lt_sdec x z) as [ x z H1 | x | x z H1 ].
      - rewrite wlist_combine_lt; auto.
        left; constructor.
        rewrite <- app_assoc.
        apply lex_list_app_head.
        constructor 2; left; eauto.
      - rewrite wlist_combine_eq; eauto.
        left; constructor.
        rewrite <- app_assoc.
        apply lex_list_app_head.
        constructor 2; left; eauto.
      - rewrite wlist_combine_gt; auto.
        left; constructor.
        rewrite <- app_assoc. 
        apply lex_list_app_head.
        constructor 2; left; auto.
    * apply list_split_cons2 in E
        as [ (<- & [=] & <-) | (m & [ (E1 & E2) | (E1 & E2) ]) ].
      - subst z i'.
        simpl app; rewrite !wlist_combine_gt_list; auto.
        rewrite wlist_combine_lt; auto.
        rewrite wlist_combine_eq; auto.
        left; constructor.
        apply lex_list_app_head.
        constructor 2.
        right.
        apply cnf_fix, proj2 in Hq.
        destruct (Hq y j); auto; lia.
      - subst l m'.
        rewrite !Forall_app in G1.
        destruct G1 as (G1 & G2 & G3).
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        rewrite wlist_combine_gt_list with (3 := G2); auto.
        rewrite wlist_combine_gt_list with (3 := G3); auto.
        simpl app at 6; rewrite wlist_combine_eq; auto.
        simpl app at 2.
        left; constructor; apply lex_list_app_head.
        apply Forall_cons_iff, proj1 in G2.
        destruct (E0_lt_sdec x z) as [ x z Hxz | x | x z Hxz ].
        ++ rewrite wlist_combine_lt; auto.
           constructor 2; left; auto.
        ++ rewrite wlist_combine_eq; auto.
           constructor; left; auto.
        ++ rewrite wlist_combine_gt; auto.
           constructor; left; auto.
      - subst p r.
        rewrite <- !app_assoc.
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        right; do 2 f_equal.
        simpl app; rewrite !wlist_combine_eq; auto.
    * apply list_split_cons2 in E
        as [ (<- & [=] & <-) | (m & [ (E1 & E2) | (E1 & E2) ]) ].
      - subst x' i'.
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        simpl app at 2 4.
        rewrite !wlist_combine_lt; eauto.
      - subst l m'.
        rewrite !Forall_app in G1.
        destruct G1 as (G1 & G4 & G3).
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        rewrite wlist_combine_gt_list with (3 := G4); auto.
        simpl app at 2.
        destruct wlist_combine_choice with (R_sdec := E0_lt_sdec)
          (x := x) (i := i) (y := z) (j := h) (l := l') (m := k)
          as (a & b & c & -> & E); eauto.
        apply Forall_cons_iff, proj1 in G4; simpl in G4.
        left; constructor; apply lex_list_app_head; constructor 2; left.
        destruct E as [ (? & <- & _) | [ (<- & <- & _) | (? & <- & _) ] ]; eauto.
      - subst p r.
        rewrite <- !app_assoc.
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        simpl app at 2 6; rewrite !wlist_combine_lt; auto.
  + unfold E0_add.
    destruct (wlist_cut_choice E0_lt_sdec (p++[(x,j)]++m') z)
      as [ G1 
       | [ (i' & l & r & E & G1) 
       |   (x' & i' & l & r & E & G1 & G2) ] ].
    * rewrite !Forall_app in G1.
      destruct G1 as (G1 & G2 & G3).
      rewrite !wlist_combine_gt_list with (3 := G1); auto.
      simpl app at 2 4.
      apply Forall_cons_iff, proj1 in G2.
      rewrite !wlist_combine_gt; auto.
      left; constructor; apply lex_list_app_head; constructor 2; right; auto.
    * apply list_split_cons2 in E
        as [ (<- & [=] & <-) | (m & [ (E1 & E2) | (E1 & E2) ]) ].
      - subst z i'.
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        simpl app at 2 4; rewrite !wlist_combine_eq; auto.
        left; constructor; apply lex_list_app_head; constructor 2; right; lia.
      - subst l m'.
        rewrite !Forall_app in G1.
        destruct G1 as (G1 & G2 & G3).
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        rewrite !wlist_combine_gt_list with (3 := G2); auto.
        simpl app at 2.
        apply Forall_cons_iff, proj1 in G2.
        rewrite wlist_combine_gt; auto.
        left; constructor; apply lex_list_app_head; constructor 2; right; lia.
      - subst p.
        rewrite <- !app_assoc.
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        simpl app at 2 6.
        rewrite !wlist_combine_eq; auto.
    * apply list_split_cons2 in E
        as [ (<- & [=] & <-) | (m & [ (E1 & E2) | (E1 & E2) ]) ].
      - subst x' i'.
        simpl app.
        rewrite !wlist_combine_gt_list; auto.
        rewrite !wlist_combine_lt; auto.
      - subst l m'.
        rewrite !Forall_app in G1.
        destruct G1 as (G1 & G4 & G3).
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        rewrite !wlist_combine_gt_list with (3 := G4); auto.
        simpl app at 2.
        apply Forall_cons_iff, proj1 in G4.
        rewrite wlist_combine_gt; auto.
        left; constructor; apply lex_list_app_head; constructor 2; right; lia.
      - subst p r.
        rewrite <- !app_assoc.
        rewrite !wlist_combine_gt_list with (3 := G1); auto.
        simpl app at 2 6; rewrite !wlist_combine_lt; auto.
Qed.

Theorem E0_add_incr e f : cnf e → cnf f → E0_zero <E₀ f → e <E₀ E0_add e f.
Proof.
  revert e f.
  intros [l] [[| (y,j) m]] He Hf.
  1: now intros ?%E0_lt_irrefl.
  intros _.
  unfold E0_add.
  destruct (wlist_cut_choice E0_lt_sdec l y)
      as [ G1 
       | [ (i & l' & r & E & G1) 
       |   (x & i & l' & r & E & G1 & G2) ] ].
  + rewrite wlist_combine_spec1; auto.
    constructor; simpl.
    rewrite <- (app_nil_r l) at 1. 
    apply lex_list_app_head; constructor 1.
  + subst l.
    rewrite wlist_combine_spec2; auto.
    constructor; simpl.
    apply lex_list_app_head; constructor 2.
    right.
    apply cnf_fix, proj2 in Hf.
    destruct (Hf y j); auto; lia.
  + subst l.
    rewrite wlist_combine_spec3; auto.
    constructor; simpl.
    apply lex_list_app_head; constructor 2.
    now left.
Qed.

Theorem E0_add_mono_right e u v : cnf e → cnf u → cnf v → u <E₀ v → E0_add e u <E₀ E0_add e v.
Proof.
  revert e u v.
  intros [l] [m] [[|(z,h) k]] Hl Hm Hk.
  1: intros []%E0_zero_not_gt.
  destruct m as [ | yj m ].
  1: intros; apply E0_add_incr; eauto.
  intros [ (y,j) [ Hyz | (<- & Hjh) ]%lex2_inv | Hmk ]%E0_lt_inv%lex_list_inv; constructor.
  + unfold E0_add.
    destruct (wlist_cut_choice E0_lt_sdec l z)
      as [ G1 
       | [ (i & l' & r' & E & G1) 
       |   (x & i & l' & r' & E & G1 & G2) ] ].
    * rewrite !wlist_combine_spec1; auto.
      2: revert G1; apply Forall_impl; eauto.
      apply lex_list_app_head; constructor 2; now left.
    * subst l.
      simpl app.
      rewrite !wlist_combine_gt_list; auto.
      2: revert G1; apply Forall_impl; eauto.
      apply lex_list_app_head.
      rewrite wlist_combine_gt; auto.
      rewrite wlist_combine_eq; auto.
      constructor 2; right.
      apply cnf_fix, proj2 in Hk.
      destruct (Hk z h); eauto; lia.
    * subst l.
      simpl app.
      rewrite !wlist_combine_gt_list; auto.
      2: revert G1; apply Forall_impl; eauto.
      apply lex_list_app_head.
      rewrite wlist_combine_lt with (y := z); auto.
      destruct (wlist_combine_choice E0_lt_sdec)
        with (x := x) (i := i) (y := y) (j := j) (l := r') (m := m)
        as (a & b & c & -> & H); auto.
      constructor 2; left.
      destruct H as [ (_ & <- & _) | [ (_& <- & _) | (_ & -> & _)] ]; auto.
  + destruct (wlist_cut_choice E0_lt_sdec l y)
      as [ G1 
       | [ (i & l' & r' & E & G1) 
       |   (x & i & l' & r' & E & G1 & G2) ] ].
    * rewrite !wlist_combine_spec1; auto.
      apply lex_list_app_head; constructor 2; now right.
    * subst l.
      rewrite !wlist_combine_spec2; auto.
      apply lex_list_app_head; constructor 2; right; lia.
    * subst.
      rewrite !wlist_combine_spec3; auto.
      apply lex_list_app_head; constructor 2; now right.
  + now apply lex_list_app_head.
Qed.

Fact E0_add_lt_cancel e u v :
    cnf e
  → cnf u
  → cnf v
  → E0_add e u <E₀ E0_add e v
  → u <E₀ v.
Proof.
  intros H1 H2 H3 H.
  destruct (E0_lt_sdec u v) as [ u v ? | u | u v G ]; auto.
  + now apply E0_lt_irrefl in H.
  + apply E0_add_mono_right with (1 := H1) in G; auto.
    destruct (@E0_lt_irrefl (E0_add e u)); eauto.
Qed.

(* This one can be proved w/o cnf hypo *)
Fact E0_add_cancel e u v :
    cnf e
  → cnf u
  → cnf v
  → E0_add e u = E0_add e v
  → u = v.
Proof.
  intros H1 H2 H3 H.
  destruct (E0_lt_sdec u v) as [ u v G | u | u v G ]; auto.
  + destruct (@E0_lt_irrefl (E0_add e u)); rewrite H at 2; now apply E0_add_mono_right.
  + destruct (@E0_lt_irrefl (E0_add e u)); rewrite H at 1; now apply E0_add_mono_right.
Qed.

#[local] Hint Resolve in_map : core.

Fact E0_lt_add e f :
    cnf e
  → cnf f
  → e <E₀ f 
  → ∃a, f = E0_add e a ∧ 0₀ <E₀ a ∧ cnf a.
Proof.
  intros He Hf H; revert e f H He Hf.
  intros [l] [m] [ l' m' | p (x,i) (y,j) l' m' [ H | (<- & H) ]%lex2_inv ]%E0_lt_inv%lex_list_invert He Hf.
  + exists ω[l'].
    destruct l' as [ | (y,j) l' ]; try easy; repeat split; eauto.
    2: repeat constructor.
    unfold E0_add.
    rewrite <- (app_nil_r m') at 2.
    rewrite wlist_combine_gt_list; eauto.
    apply cnf_fix, proj1 in Hf.
    rewrite map_app, ordered_app_iff in Hf; auto.
    apply Forall_forall.
    intros; eapply Hf; simpl; eauto.
  + exists ω[(y,j)::m']; repeat split; eauto.
    2: repeat constructor.
    unfold E0_add; f_equal.
    simpl app at 3.
    rewrite wlist_combine_gt_list; auto.
    * rewrite wlist_combine_lt; auto.
    * apply cnf_fix, proj1 in Hf.
      rewrite map_app, ordered_app_iff in Hf; auto.
      apply Forall_forall.
      intros; eapply Hf; simpl; eauto.
  + exists ω[(x,j-i)::m']; repeat split; eauto.
    2: repeat constructor.
    unfold E0_add; f_equal.
    simpl app at 3.
    rewrite wlist_combine_gt_list; auto.
    * rewrite wlist_combine_eq; auto.
      simpl; do 3 f_equal; lia.
    * apply cnf_fix, proj1 in Hf.
      rewrite map_app, ordered_app_iff in Hf; auto.
      apply Forall_forall.
      intros; eapply Hf; simpl; eauto.
    * rewrite cnf_fix in Hf |- *.
      rewrite map_app, ordered_app_iff in Hf; auto.
      split; try tauto.
      apply proj2 in Hf.
      intros u v [ [=] | G ]; subst.
      - split; try lia; eapply Hf; eauto.
      - eapply Hf; eauto.
Qed.

Lemma E0_lt_add_inv e a f :
    cnf e
  → cnf f
  → cnf a
  → e <E₀ E0_add a f
  → e <E₀ a 
  ∨ ∃g, cnf g ∧ e = E0_add a g ∧ g <E₀ f.
Proof.
  intros He Hf Ha H.
  destruct (E0_lt_sdec e a) as [ e a G | e | e a G ]; auto.
  + right; exists 0₀.
    rewrite (E0_add_zero e).
    repeat split; auto.
    apply E0_add_lt_cancel with e; auto.
    now rewrite E0_add_zero.
  + apply E0_lt_add in G as (g & -> & G & ?); auto.
    right; exists g; repeat split; auto.
    eapply E0_add_lt_cancel with a; eauto.
Qed.

Definition E0_is_succ e := ∃f, e = E0_succ f.
Definition E0_is_limit e := e ≠ 0₀ ∧ ¬ ∃f, e = E0_succ f.

Lemma E0_is_succ_iff e :
     cnf e
   → E0_is_succ e
   ↔ ∃ l i, 0 < i ∧ e = ω[l++[(0₀,i)]].
Proof.
  intros He; split.
  + intros (f & ->).
    generalize (E0_succ f) (E0_succ_spec f).
    induction 1 as [ | l i | l x i ].
    * exists [], 1; split; auto.
    * exists l, (S i); split; auto; lia.
    * exists (l++[(x,i)]), 1; split; auto.
      now rewrite <- app_assoc.
  + intros (l & [ | [|i] ] & H1 & ->).
    * lia.
    * exists ω[l].
      apply E0_succ_graph_fun with (2 := E0_succ_spec _).
      destruct l as [ | l (x,i) _ ] using rev_rect.
      1: constructor 1.
      rewrite <- app_assoc; simpl.
      constructor 3.
      intros ->.
      rewrite <- app_assoc, cnf_fix, map_app in He.
      simpl in He.
      apply proj1, ordered_app_tail, 
            ordered_cons_iff, proj2 in He; auto.
      apply (@E0_lt_irrefl 0₀), He; auto. 
    * exists ω[l++[(0₀,S i)]].
      apply E0_succ_graph_fun with (2 := E0_succ_spec _).
      constructor 2.
Qed.

Lemma E0_is_limit_iff e :
    cnf e 
  → E0_is_limit e 
  ↔ ∃ l b i, 0 < i ∧ b ≠ 0₀ ∧ e = ω[l++[(b,i)]].
Proof.
  intros He.
  split.
  + intros (H1 & H2); destruct e as [ l ].
    destruct l as [ | l (b,i) _ ] using rev_rect.
    1: easy.
    destruct i as [ | i ].
    1:{ apply cnf_fix, proj2 in He.
        destruct (He b 0); eauto; lia. }
    exists l, b, (S i); repeat split; auto.
    * lia.
    * intros ->.
      apply H2, E0_is_succ_iff; auto.
      exists l, (S i); split; auto; lia.
  + intros (l & b & i & H1 & H2 & ->).
    split.
    1: now destruct l.
    intros (m & j & H3 & H4)%E0_is_succ_iff; auto.
    injection H4; clear H4.
    intros (_ & [=])%app_inj_tail; now subst.
Qed.

#[local] Hint Resolve E0_add_cnf : core.

(** e + l is a limit if l is *)
Lemma E0_add_is_limit a e : 
    cnf a
  → cnf e
  → E0_is_limit e
  → E0_is_limit (E0_add a e).
Proof.
  intros Ha He (m & b & i & Hi & Hb & ->)%E0_is_limit_iff; auto.
  apply E0_is_limit_iff; eauto.
  destruct a as [l].
  unfold E0_add.
  destruct (wlist_combine_last E0_lt_sdec l m b i)
    as (r & j & ? & ->).
  exists r, b, j; split; auto; lia.
Qed.

Fact E0_omega_is_limit e i :
    cnf e
  → e ≠ 0₀
  → 0 < i
  → E0_is_limit ω[[(e,i)]].
Proof.
  intros H1 H2 H3.
  apply E0_is_limit_iff; auto.
  exists [], e, i; auto.
Qed.

#[local] Hint Resolve E0_add_is_limit E0_omega_is_limit : core.

(** a + ω^e is a limit ordinal *)
Fact E0_add_omega_is_limit a e i : 
    cnf a
  → cnf e
  → e ≠ 0₀
  → 0 < i
  → E0_is_limit (E0_add a ω[[(e,i)]]).
Proof. eauto. Qed.

Inductive E0_decomp : E0 → Type :=
  | E0_decomp_zero : E0_decomp 0₀
  | E0_decomp_succ e : cnf e → E0_decomp (E0_succ e)
  | E0_decomp_limit g e : e <> 0₀ → cnf g → cnf e → E0_decomp (E0_add g ω[[(e,1)]]).

Lemma E0_decomp_compute e : cnf e → E0_decomp e.
Proof.
  induction 1 as [ m H1 H2 H3 _ ] using cnf_rect.
  destruct m as [ | m (e,i) _ ] using rev_rect.
  + constructor 1.
  + destruct i as [ | i ].
    1: destruct (@lt_irrefl 0); eauto.
    destruct e as [[ | yj e ]].
    * destruct i as [ | i ].
      - replace ω[m++[(ω[[]],1)]]
          with (E0_succ ω[m]).
        ++ constructor.
           apply cnf_fix; repeat split; eauto.
           rewrite map_app in H1.
           now apply ordered_app_head in H1.
        ++ apply E0_succ_graph_fun with (1 := E0_succ_spec _).
           destruct m as [ | m (x,i) _ ] using rev_rect.
           ** constructor.
           ** rewrite <- app_assoc.
              constructor.
              intros ->.
              rewrite !map_app, <- app_assoc in H1.
              now apply ordered_app_tail, ordered_inv,
                    ordered_from_inv, proj1, E0_lt_irrefl in H1.
      - replace ω[m++[(ω[[]],S (S i))]]
          with (E0_succ ω[m++[(0₀,S i)]]).
        ++ constructor 2.
           apply cnf_fix; split.
           ** rewrite map_app in H1 |- *; auto.
           ** intros ? ? [|[[=]|[]]]%in_app_iff; split; subst; eauto; lia.
        ++ apply E0_succ_graph_fun with (1 := E0_succ_spec _).
           constructor 2.
    * destruct i as [ | i ].
      - replace ω[m++[(ω[yj::e],1)]]
          with (E0_add ω[m] ω[[(ω[yj::e],1)]]).
        ++ constructor 3; easy || eauto.
           apply cnf_fix; repeat split; eauto.
           rewrite map_app in H1.
           now apply ordered_app_head in H1.
        ++ unfold E0_add.
           rewrite wlist_combine_spec1; eauto.
           rewrite map_app in H1; simpl in H1.
           apply ordered_snoc_iff, proj2 in H1; auto.
           apply Forall_forall.
           now intros (f,i) H; apply H1, in_map.
      - replace ω[m++[(ω[yj::e], S (S i))]]
          with (E0_add ω[m++[(ω[yj::e],S i)]] ω[[(ω[yj::e],1)]]).
        ++ constructor 3; easy || eauto.
           apply cnf_fix; split.
           ** rewrite map_app in H1 |- *; auto.
           ** intros f j [|[[=]|[]]]%in_app_iff; split; subst; eauto; lia.
        ++ unfold E0_add.
           rewrite <- (app_nil_r (_++[_])), <- app_assoc.
           rewrite wlist_combine_spec2; auto.
           ** rewrite app_nil_r; do 4 f_equal; lia.
           ** rewrite map_app in H1; simpl in H1. 
              apply ordered_snoc_iff, proj2 in H1; auto.
              apply Forall_forall.
              intros [] ?; now apply H1, in_map.
Qed.

#[local] Hint Resolve cnf_lt_lpo : core.

Theorem E0_lt_wf : well_founded (λ x y, x <E₀ y ∧ cnf x ∧ cnf y).
Proof.
  generalize wf_E0_lpo.
  apply wf_rel_morph with (f := fun x y => x = y); eauto.
  intros ? ? ? ? -> -> (? & ? & ?); eauto.
Qed.

Inductive E0_fseq_gr : E0 → (nat → E0) → Prop :=
  | E0_fseq_gr_0 g b   : cnf g
                       → cnf b
                       → E0_fseq_gr (E0_add g ω[[(E0_succ b,1)]]) (λ n, E0_add g ω[[(b,1+n)]])
  | E0_fseq_gr_1 g b r : cnf g
                       → cnf b
                       → E0_fseq_gr b r
                       → E0_fseq_gr (E0_add g ω[[(b,1)]]) (λ n, E0_add g ω[[(r n,1)]]).

#[local] Hint Resolve E0_add_cnf cnf_sg : core.

(** WF Induction on e st cnf e *)
Theorem E0_fseq_pwc e : cnf e → E0_is_limit e → sig (E0_fseq_gr e).
Proof.
  induction e as [ e IH ] using (well_founded_induction_type E0_lt_wf).
  intros G1%E0_decomp_compute G2.
  destruct G1 as [ | e He | g e H0 Hg He ].
  + exfalso; now destruct G2.
  + exfalso; destruct G2 as (_ & []); eauto.
  + clear G2.
    apply E0_decomp_compute in He.
    destruct He as [ | b Hb | a e H1 H2 H3 ].
    * now destruct H0.
    * exists (λ n, E0_add g ω[[(b,1+n)]]).
      now constructor.
    * destruct (IH (E0_add a ω[[(e, 1)]])) as (lam & Hlam); eauto.
      - repeat split; eauto.
        ++ rewrite <- (E0_add_zero_left (E0_add a _)) at 1.
           apply E0_le_lt_trans with (E0_add g (E0_add a ω[[(e, 1)]])).
           ** apply E0_add_mono_left; auto.
           ** apply E0_add_mono_right; eauto.
              1: apply cnf_sg; eauto.
              apply E0_lt_sub with 1; auto.
        ++ apply E0_add_cnf; auto.
      - apply E0_add_is_limit; auto.
      - exists (λ n, E0_add g ω[[(lam n,1)]]); constructor; eauto.
Qed.

Definition E0_fseq {e} (h : cnf e) (l : E0_is_limit e) := proj1_sig (@E0_fseq_pwc e h l).
Fact E0_fseq_spec e h l : E0_fseq_gr e (@E0_fseq e h l).
Proof. apply (proj2_sig _). Qed.

Fact E0_fseq_gr_cnf e r : E0_fseq_gr e r → ∀n, cnf (r n).
Proof.
  induction 1; intro.
  + apply E0_add_cnf; auto.
    apply cnf_sg; auto; lia.
  + apply E0_add_cnf; auto.
Qed. 

(** The fundemental sequence is correct *)
Fact E0_fseq_cnf e h l n : cnf (@E0_fseq e h l n).
Proof. generalize (E0_fseq_spec h l) n; apply E0_fseq_gr_cnf. Qed.

#[local] Hint Resolve E0_fseq_gr_cnf E0_fseq_cnf : core.

(** The fundemental sequence is increasing *)
Fact E0_fseq_incr e h l : ∀ n m, n < m → @E0_fseq e h l n <E₀ E0_fseq h l m.
Proof.
  generalize (E0_fseq h l) (E0_fseq_spec h l); clear l.
  induction 1; intros.
  + apply E0_add_mono_right; auto.
    1,2: apply cnf_sg; auto; lia.
    constructor; constructor 2; right; lia.
  + apply E0_add_mono_right; auto.
    1,2: apply cnf_sg; eauto.
    constructor; constructor 2; left; eauto.
Qed.

Lemma E0_succ_next e f : cnf e → cnf f → e <E₀ f → E0_succ e ≤E₀ f.
Proof.
  intros He Hf.
  generalize (E0_succ e) (E0_succ_spec e).
  induction 1 as [ | li | l x i Hx ].
  + destruct f as [ [ | (x,j) l ] ].
    * intros []%E0_lt_irrefl.
    * intros _.
      apply cnf_fix in Hf as (Hl & Hf).
      simpl in Hl; apply ordered_inv in Hl.
      generalize (ordered_from_clos_trans Hl); intros Hl'.
      destruct x as [ [ | u m ] ].
      - destruct j as [ | [| j] ].
        ++ destruct (Hf ω[[]] 0); eauto; lia.
        ++ constructor 2; repeat f_equal.
           destruct l as [ | (g,j) l ]; auto.
           destruct (@E0_zero_not_gt g).
           apply E0_lt_trans', clos_trans_rev_iff, Hl'; simpl; auto.
        ++ left; constructor 1; constructor 2; right; lia.
      - left; constructor; constructor 2; left.
        constructor; constructor.
  + destruct f as [ m ].
    intros H%E0_lt_inv%lex_list_snoc_inv_left.
    destruct H as [ | (y,j) l r H | ].
    * left; constructor.
      rewrite <- !app_assoc.
      apply lex_list_app_head.
      now constructor 2.
    * apply lex2_inv in H as [ H | (<- & H) ].
      - constructor 1.
        constructor.
        apply lex_list_app_head.
        constructor 2; now left.
      - destruct (eq_nat_dec (S i) j) as [ <- | ].
        ++ destruct r.
           ** now right.
           ** left.
              constructor 1.
              apply lex_list_app_head.
              constructor 3; constructor 1.
        ++ left.
           constructor.
           apply lex_list_app_head.
           constructor 2; right; lia.
    * exfalso.
      apply cnf_fix, proj1 in Hf.
      rewrite map_app in Hf; simpl in Hf.
      apply ordered_app_tail, ordered_inv in Hf.
      destruct r as [ | y r ]; [ easy | ].
      simpl in Hf; now apply ordered_from_inv, proj1, E0_zero_not_gt in Hf.
  + destruct f as [ m ].
    intros H%E0_lt_inv%lex_list_snoc_inv_left.
    destruct H as [ | (y,j) l r H | ].
    * left; constructor.
      rewrite <- app_assoc; apply lex_list_app_head.
      now constructor 2.
    * left; constructor.
      apply lex_list_app_head.
      now constructor 2.
    * apply E0_le_app_head.
      apply E0_le_app_head with (l := [_]).
      apply E0_one_ge; auto.
      rewrite cnf_fix in Hf |- *.
      destruct Hf as (H1 & H2); split; eauto.
      - rewrite map_app in H1; simpl in H1.
        now apply ordered_app_tail, ordered_cons_inv in H1.
      - intros ? ? ?; apply H2; eauto.
Qed.

Lemma E0_succ_next_inv e f : cnf e → cnf f → e <E₀ E0_succ f → e ≤E₀ f.
Proof.
  intros He Hf H.
  destruct (E0_lt_sdec e f) as [ e f H1 | e | e f H1 ].
  + now left.
  + now right.
  + apply E0_succ_next in H1; auto.
    destruct (@E0_lt_irrefl e).
    now apply E0_lt_le_trans with (2 := H1).
Qed.

(** inversion for f < ω^b:
    - either f is 0 (and b is also 0)
    - or f is below ω^a.n for some a < b and some n > 0 *)
Lemma E0_lt_omega_inv f b :
    cnf f
  → cnf b
  → f <E₀ ω[[(b, 1)]]
  → f = 0₀
  ∨ ∃n a, 0 < n ∧ f <E₀ ω[[(a, n)]] ∧ a <E₀ b ∧ cnf a.
Proof.
  intros Hf Hb.
  destruct f as [l].
  (* we analyse ω[l] <E₀ ω[(b,1)] *)
  intros ?%E0_lt_inv%lex_list_sg_inv_right.
  destruct H as [ | (x,i) ? [ | (? & ?) ]%lex2_inv ].
  + (* l = [] *)
    now left.
  + (* l = (x,_)::... with x <E₀ b *)
    right.
    exists (S i), x; repeat split; eauto; try lia.
    constructor 2; right; auto.
  + (* i < 1 is absurd *)
    assert (0 < i); [ | lia ].
    apply cnf_fix in Hf.
    eapply Hf; eauto.
Qed.

(** the previous one specialized for _ < ω^{b+1} *)
Lemma E0_lt_omega_succ_inv f b :
    cnf f
  → cnf b
  → f <E₀ ω[[(E0_succ b, 1)]]
  → ∃n, 0 < n ∧ f <E₀ ω[[(b, n)]].
Proof.
  intros Hf Hb [ -> | (n & x & H1 & H2 & H3 & H4) ]%E0_lt_omega_inv; eauto.
  1: exists 1; split; auto; repeat constructor.
  apply E0_succ_next_inv in H3 as [ H3 | -> ]; eauto.
  exists n; split; auto.
  apply E0_lt_trans with (1 := H2).
  repeat constructor; auto.
Qed.

(** Another inversion lemma, but this time
    for the limit of the fundemental sequence

    This is inversion of _ < e when e is a limit ordinal,
    w.r.t. the fundemental sequence of e 

    This has become a nice proof *)
Theorem E0_lt_fseq_inv e h l f : cnf f → f <E₀ e → ∃n, f <E₀ @E0_fseq e h l n.
Proof.
  (* We capture the fundemental sequence via its inductive spec *)
  revert f; generalize (E0_fseq h l) (E0_fseq_spec h l).
  intros f H; revert H h; clear l.
  induction 1 as [ e b Hg Hb | e b r Hg Hb Hr IH ]; intros He f Hf H.
  + (* e is _ + ω^{b+1} *)
    apply E0_lt_add_inv in H as [ H | (g & H1 & -> & H3) ]; eauto.
    * exists 0.
      apply E0_lt_trans with (1 := H).
      apply E0_add_incr; eauto.
      repeat constructor.
    * apply E0_lt_omega_succ_inv in H3 as (n & Hn & H3); eauto.
      exists n; eauto.
      apply E0_add_mono_right; eauto.
      apply E0_lt_trans with (1 := H3).
      do 2 constructor; right; lia.
  + (* e is _ + ω^h where h is itself a limit ordinal *)
    apply E0_lt_add_inv in H as [ H | (g & H1 & -> & H3) ]; eauto.
    * exists 0.
      apply E0_lt_trans with (1 := H).
      apply E0_add_incr; eauto.
      repeat constructor.
    * apply E0_lt_omega_inv in H3 as [ -> | (n & a & Hn & H3 & H4 & H5) ]; eauto.
      - exists 0; apply E0_add_mono_right; eauto; repeat constructor.
      - apply IH in H4 as (i & Hi); auto.
        exists i.
        apply E0_add_mono_right; eauto.
        apply E0_lt_trans with (1 := H3).
        repeat constructor; auto.
Qed.

Definition is_lub {X} (R : X → X → Prop) (P : X → Prop) u := ∀v, (∀x, P x → R x v) ↔ R u v.
Definition dwnwc {X} (R : X → X → Prop) (P : X → Prop) x := ∃y, R x y ∧ P y.

Fact is_lub_dwnwc P u : is_lub E0_le P u → is_lub E0_le (dwnwc E0_le P) u.
Proof.
  intros H v; red in H; split.
  + intros G.
    rewrite <- H.
    intros x Hx; apply G; exists x; split; auto.
  + intros Hu x (e & He & G).
    rewrite <- H in Hu.
    apply E0_le_trans with (1 := He); auto.
Qed.

(** The lub is preserved; for this we need the fundemental sequence *)
Theorem E0_add_lub P u v : 
     (∀e, P e → cnf e)
   → cnf u
   → cnf v
   → is_lub E0_le P v
   → is_lub E0_le (λ x, ∃e, P e ∧ x = E0_add u e) (E0_add u v).
Proof.
  intros H1 H2 H3 H4%is_lub_dwnwc f; split.
  + intros H.
    assert (H' : ∀e, P e → E0_add u e ≤E₀ f).
    1:{ intros e He; apply H; eauto. }
    clear H.
    (* if v is zero
       if v is succ
       if v is limit w[l++(e,i)] with 0₀ < e
       then w[l++(e,i-1)++k] in dwnwc E0_le P (otherwise v is not upper bound) *)
    admit.
  + intros H x (e & He & ->).
    apply E0_le_trans with (2 := H).
(*    assert (e ≤E₀ v) as [ G | ].
    1: apply H4; try red; auto.
    * left; apply E0_add_mono_right; eauto.
    * subst; now right. *)
Admitted.

(** ε₀ is the sub-type of E0 composed of trees in nested lexigraphic order *)

Definition eps0 := { e | cnf e }.

Notation ε₀ := eps0.

Fact eps0_eq_iff (e f : ε₀) : e = f ↔ π₁ e = π₁ f.
Proof.
  split; intro H; subst; auto.
  revert e f H; intros [e He] [f Hf] ?; simpl in *; subst.
  now rewrite (cnf_pirr _ He Hf).
Qed.

(** ε₀ is itself equipped with the restriction of the nested lex. order
    denoted <ε₀ *)

Definition eps0_lt (e f : ε₀) := E0_lt (π₁ e) (π₁ f).

Arguments eps0_lt /.

Notation "e '<ε₀' f" := (eps0_lt e f) (at level 70, format "e  <ε₀  f").

(** The nested lexicographic order <ε₀ is a strict total/decidable order *)

Theorem eps0_lt_irrefl e : ¬ e <ε₀ e.
Proof. destruct e; apply E0_lt_irrefl. Qed.

Theorem eps0_lt_trans : transitive eps0_lt.
Proof. intros [] [] []; apply E0_lt_trans. Qed.

Theorem eps0_lt_sdec e f : sdec eps0_lt e f.
Proof.
  revert e f; intros (e & He) (f & Hf).
  destruct (E0_lt_sdec e f) as []; eauto.
  rewrite (cnf_pirr _ He Hf); auto.
Qed.

#[local] Hint Resolve cnf_lt_lpo : core.

(* <ε₀ is well-founded *)
Theorem wf_eps0_lt : well_founded eps0_lt.
Proof.
  generalize wf_E0_lpo.
  apply wf_rel_morph with (f := fun x y => x = π₁ y).
  + intros []; eauto.
  + unfold eps0_lt; intros ? ? [] [] -> ->; simpl; eauto.
Qed.

Definition eps0_zero : ε₀.
Proof. now exists E0_zero. Defined.

Definition eps0_one : ε₀.
Proof. now exists E0_one. Defined.

Definition eps0_le e f := e <ε₀ f ∨ e = f.

Notation "e '≤ε₀' f" := (eps0_le e f) (at level 70, format "e  ≤ε₀  f").

Fact eps0_le_iff e f : e ≤ε₀ f ↔ π₁ e ≤E₀ π₁ f.
Proof.
  unfold eps0_le, E0_le; rewrite eps0_eq_iff.  
  revert e f; intros [ e He ] [ f Hf ]; simpl; tauto.
Qed.

Fact eps0_zero_least e : eps0_zero ≤ε₀ e.
Proof.
  apply eps0_le_iff.
  destruct e as [ [l] He ]; simpl.
  destruct l as [ | x l ]; [ right | left ]; auto.
  constructor; constructor.
Qed.

(* e is a strict upper bounded of P *)
Definition eps0_is_sub (P : ε₀ → Prop) e := ∀x, P x → x <ε₀ e.

(* e is the least strict upper bound of P *) 
Definition eps0_is_lub (P : ε₀ → Prop) e := eps0_is_sub P e ∧ ∀x, eps0_is_sub P x → e ≤ε₀ x.

(* A limit ordinal is a strict upperbound (of lesser ordinals) *)
Definition eps0_is_limit e := exists P, eps0_is_lub P e.

Fact eps0_zero_is_limit : eps0_is_limit eps0_zero.
Proof.
  exists (fun _ => False); split.
  + intros ? [].
  + intros; apply eps0_zero_least.
Qed.

Fact eps0_zero_or_pos e : { e = eps0_zero } + { eps0_zero <ε₀ e }.
Proof.
  destruct e as [ [ [ | x l ] ] Hl ].
  + left; apply eps0_eq_iff; auto.
  + right; cbv; repeat constructor.
Qed.

Definition eps0_succ (e : ε₀) : ε₀.
Proof.
  destruct e as [ e He ].
  exists (E0_succ e).
  now apply E0_succ_correct.
Defined.

(** The successor of E0_zero is E0_one *) 
Fact eps0_succ_zero_is_one : eps0_succ eps0_zero = eps0_one.
Proof.
  apply eps0_eq_iff; simpl.
  apply E0_succ_graph_fun with (1 := E0_succ_spec _).
  constructor.
Qed.

(** The successor is <ε₀-greater *)
Fact eps0_succ_lt e : e <ε₀ eps0_succ e.
Proof.
  destruct e as (e & He); simpl.
  generalize (E0_succ e) (E0_succ_spec e).
  induction 1; constructor.
  + constructor.
  + apply lex_list_app_head.
    constructor 2; right; lia.
  + apply lex_list_app_head.
    constructor 3; constructor.
Qed. 

(* We show that there is nothing inbetween
   e and eps0_succ e.

   Such a complicated proof is unreasonnable 
   FIND a way to factor this in smaller lemmas *)
Lemma eps0_succ_next e f : e <ε₀ f → eps0_succ e ≤ε₀ f.
Proof.
  rewrite eps0_le_iff; unfold eps0_lt.
  revert e f; intros [ e He ] [ f Hf ]; simpl.
  generalize (E0_succ e) (E0_succ_spec e).
  induction 1 as [ | li | l x i Hx ].
  + destruct f as [ [ | (x,j) l ] ].
    * intros []%E0_lt_irrefl.
    * intros _.
      apply cnf_fix in Hf as (Hl & Hf).
      simpl in Hl; apply ordered_inv in Hl.
      generalize (ordered_from_clos_trans Hl); intros Hl'.
      destruct x as [ [ | u m ] ].
      - destruct j as [ | [| j] ].
        ++ destruct (Hf ω[[]] 0); eauto; lia.
        ++ constructor 2; repeat f_equal.
           destruct l as [ | (g,j) l ]; auto.
           destruct (@E0_zero_not_gt g).
           apply E0_lt_trans', clos_trans_rev_iff, Hl'; simpl; auto.
        ++ left; constructor 1; constructor 2; right; lia.
      - left; constructor; constructor 2; left.
        constructor; constructor.
  + destruct f as [ m ].
    intros H%E0_lt_inv%lex_list_snoc_inv_left.
    destruct H as [ | (y,j) l r H | ].
    * left; constructor.
      rewrite <- !app_assoc.
      apply lex_list_app_head.
      now constructor 2.
    * apply lex2_inv in H as [ H | (<- & H) ].
      - constructor 1.
        constructor.
        apply lex_list_app_head.
        constructor 2; now left.
      - destruct (eq_nat_dec (S i) j) as [ <- | ].
        ++ destruct r.
           ** now right.
           ** left.
              constructor 1.
              apply lex_list_app_head.
              constructor 3; constructor 1.
        ++ left.
           constructor.
           apply lex_list_app_head.
           constructor 2; right; lia.
    * exfalso.
      apply cnf_fix, proj1 in Hf.
      rewrite map_app in Hf; simpl in Hf.
      apply ordered_app_tail, ordered_inv in Hf.
      destruct r as [ | y r ]; [ easy | ].
      simpl in Hf; now apply ordered_from_inv, proj1, E0_zero_not_gt in Hf.
  + destruct f as [ m ].
    intros H%E0_lt_inv%lex_list_snoc_inv_left.
    destruct H as [ | (y,j) l r H | ].
    * left; constructor.
      rewrite <- app_assoc; apply lex_list_app_head.
      now constructor 2.
    * left; constructor.
      apply lex_list_app_head.
      now constructor 2.
    * apply E0_le_app_head.
      apply E0_le_app_head with (l := [_]).
      apply E0_one_ge; auto.
      rewrite cnf_fix in Hf |- *.
      destruct Hf as (H1 & H2); split; eauto.
      - rewrite map_app in H1; simpl in H1.
        now apply ordered_app_tail, ordered_cons_inv in H1.
      - intros ? ? ?; apply H2; eauto.
Qed.

(** There is no ordinal between e and (eps0_succ e) *)
Corollary eps0_no_ordinal_between_n_and_succ e f :
    ¬ (e <ε₀ f ∧ f <ε₀ eps0_succ e).
Proof.
  intros (H1 & H2).
  destruct eps0_succ_next with (1 := H1) as [ | <- ].
  + apply (@eps0_lt_irrefl f), eps0_lt_trans with (1 := H2); auto.
  + revert H2; apply eps0_lt_irrefl.
Qed.

(* Hence a successor is not a limit ordinal 

   Successor is of shape ω[_++[(ω[[]],1+i)]]
   Limit is either ω[[]] or ω[_++[(x,i)]] with 0 < i and x <> ω[[]] *)





