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

Fact lmax_cons x l : lmax (x::l) = max x (lmax l).
Proof. induction l; simpl; lia. Qed.

Fact lmax_bounded n l : (∀ x : nat, x ∈ l → x ≤ n) → lmax l ≤ n.
Proof. rewrite <- Forall_forall; induction 1; simpl; lia. Qed.

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

  Fact wlist_combine_nil_left m : wlist_combine [] m = m.
  Proof. destruct m as [ | [] ]; simpl; auto. Qed.

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
  
  Fact wlist_combine_common l y : ∃ l' i, ∀ j m, wlist_combine l ((y,j)::m) = l'++(y,i+j)::m.
  Proof.
    simpl.
    induction l as [ | (x,i) l (l' & k & Hl') ]; simpl.
    + exists [], 0; auto.
    + destruct (R_sdec x y) as [ x y H | y | x y H ].
      * exists [], 0; auto.
      * exists [], i; auto.
      * exists ((x,i)::l'), k.
        intros; simpl; f_equal; auto.
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

  Fact wlist_combine_middle_lt l x i r y j m :
    R x y → wlist_combine (l++(x,i)::r) ((y,j)::m) = wlist_combine l ((y,j)::m).
  Proof.
    intros Hxy; simpl.
    induction l as [ | (z,p) l IHl ]; simpl.
    + destruct (R_sdec x y) as [ x y H | x | x y H ]; auto.
      * now apply R_irrefl in Hxy.
      * destruct (@R_irrefl x); eauto.
    + destruct (R_sdec z y); simpl; f_equal; auto.
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

  Fact wlist_combine_assoc l m k :
      wlist_combine (wlist_combine l m) k 
    = wlist_combine l (wlist_combine m k).
  Proof.
    destruct m as [ | (y,j) m ].
    1: simpl; now rewrite wlist_combine_nil_left.
    destruct k as [ | (z,p) k ].
    1: simpl; auto.
    destruct (wlist_cut_choice l y)
      as [ G1 
       | [ (i' & l' & r' & E & G1) 
       |   (x' & i' & l' & r' & E & G1 & G2) ] ].
    + rewrite <- (app_nil_r l) at 1.
      rewrite wlist_combine_gt_list; auto.
      rewrite wlist_combine_nil_left; auto.
      destruct (R_sdec y z) as [ y z F | y | y z F ].
      * rewrite wlist_combine_lt; auto.
        rewrite wlist_combine_middle_lt; auto.
      * rewrite wlist_combine_gt_list; auto.
        rewrite !wlist_combine_eq; auto.
        rewrite <- (app_nil_r l) at 2.
        rewrite wlist_combine_gt_list; auto.
      * rewrite wlist_combine_gt; auto.
        rewrite wlist_combine_gt_list; auto.
        2: revert G1; apply Forall_impl; eauto.
        rewrite wlist_combine_gt; auto.
        rewrite <- (app_nil_r l) at 2.
        rewrite wlist_combine_gt_list; auto.
    + subst l.
      rewrite wlist_combine_gt_list; auto.
      simpl app at 2; rewrite wlist_combine_eq; auto.
      destruct (R_sdec y z) as [ y z F | y | y z F ].
      * rewrite wlist_combine_lt; auto.
        simpl app; rewrite !wlist_combine_middle_lt; auto.
      * rewrite wlist_combine_eq; auto.
        simpl app.
        rewrite !wlist_combine_gt_list; auto.
        rewrite !wlist_combine_eq; auto.
        do 3 f_equal; lia.
      * rewrite wlist_combine_gt; auto.
        rewrite wlist_combine_gt_list; auto.
        2: revert G1; apply Forall_impl; eauto.
        simpl app at 2.
        rewrite wlist_combine_gt_list; auto.
        rewrite wlist_combine_eq; auto.
        rewrite wlist_combine_gt; auto.
    + subst l.
      rewrite wlist_combine_gt_list; auto.
      simpl app at 2.
      rewrite wlist_combine_lt; auto.
      destruct (R_sdec y z) as [ y z F | y | y z F ].
      * rewrite wlist_combine_lt; auto.
        simpl app.
        rewrite !wlist_combine_middle_lt; eauto.
      * rewrite wlist_combine_gt_list; auto.
        rewrite !wlist_combine_eq; auto.
        rewrite wlist_combine_gt_list; auto.
        simpl app at 3.
        rewrite wlist_combine_lt; auto.
      * rewrite wlist_combine_gt; auto.
        simpl app at 2.
        rewrite wlist_combine_middle_lt with (y := y); auto.
        rewrite wlist_combine_gt_list; auto.
        2: revert G1; apply Forall_impl; eauto.
        rewrite wlist_combine_gt; auto.
        rewrite <- (app_nil_r l') at 2. 
        rewrite wlist_combine_gt_list with (y := y); auto.
  Qed.
  
  Fact wlist_combine_eq_snoc_inv m x i l y j:
      wlist_combine m [(x,i)] = l⊣⊢[(y,j)]
    → ∃r, m = l++r ∧ x = y ∧ Forall (λ x, R y (fst x)) l ∧ (i = j \/ exists p r', p+i = j /\ r = (x,p)::r').
  Proof.
    destruct (wlist_cut_choice m x)
      as [ G1 
       | [ (i' & l' & r' & E & G1) 
       |   (x' & i' & l' & r' & E & G1 & G2) ] ].
    + rewrite wlist_combine_spec1; auto.
      rewrite app_nil_r.
      intros (<- & [=])%app_inj_tail; subst.
      exists []; repeat split; auto.
      now rewrite app_nil_r.
    + subst m.
      rewrite wlist_combine_spec2; auto.
      rewrite app_nil_r.
      intros (<- & [=])%app_inj_tail; subst.
      exists ((y,i')::r'); repeat split; auto.
      right; exists i', r'; auto.
    + subst m.
      rewrite wlist_combine_spec3; auto.
      rewrite app_nil_r.
      intros (<- & [=])%app_inj_tail; subst.
      exists ((x',i')::r'); repeat split; auto.
  Qed.

End wlist_combine.

Arguments wlist_cut {_ _}.
Arguments wlist_combine {_ _}.

Reserved Notation "a '+₀' b"  (at level 31, left associativity, format "a  +₀  b" ).
Reserved Notation "'ω[' l ]"  (at level 1, no associativity, format "ω[ l ]").
Reserved Notation "⌊ e ⌋₀"    (at level 1, e at level 200, format "⌊ e ⌋₀").
Reserved Notation "e '<E₀' f" (at level 70, format "e  <E₀  f").
Reserved Notation "e '≤E₀' f" (at level 70, format "e  ≤E₀  f").

Section E0.

  Unset Elimination Schemes.

  Inductive E0 : Set :=
    | E0_cons : list (E0*nat) → E0.

  Set Elimination Schemes.

  Notation "ω[ l ]" := (E0_cons l).
  
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

  Notation "⌊ e ⌋₀" := (E0_ht e).

  Fact E0_ht_fix l : ⌊ω[l]⌋₀ = lmax (map (λ x, 1+⌊fst x⌋₀) l).
  Proof. trivial. Qed.

  Fact E0_ht_in e i l : (e,i) ∈ l → ⌊e⌋₀ < ⌊ω[l]⌋₀.
  Proof.
    intros ?; rewrite E0_ht_fix.
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
    apply and_iff_compat_l; split.
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

  Unset Elimination Schemes.

  Inductive E0_lt : E0 → E0 → Prop :=
    | E0_lt_intro l m : lex_list (lex2 E0_lt lt) l m → E0_lt ω[l] ω[m].

  Set Elimination Schemes.

  Hint Constructors E0_lt : core.

  Infix "<E₀" := E0_lt.

  (* This inversion principle is enough to reason about <E₀, 
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

  Hint Resolve lt_trans lex2_trans : core.

  (* transitive *)
  Lemma E0_lt_trans : transitive E0_lt.
  Proof.
    intros e.
    induction e as [ l IH ]. 
    intros [] [] H1%E0_lt_inv H2%E0_lt_inv; constructor.
    revert H1 H2; apply lex_list_trans; eauto.
  Qed.

  Hint Resolve E0_lt_trans E0_lt_irrefl : core.

  Corollary E0_lt_trans' e f : clos_trans E0_lt e f → e <E₀ f.
  Proof. induction 1; eauto. Qed.

  Hint Constructors sdec : core.

  Lemma lt_sdec i j : sdec lt i j.
  Proof. destruct (lt_eq_lt_dec i j) as [ [ | []] | ]; eauto. Qed.

  Hint Resolve lt_sdec lex2_sdec : core.

  (* computably total *)
  Lemma E0_lt_sdec e f : sdec E0_lt e f.
  Proof.
    revert f; induction e as [l]; intros [m].
    destruct (@lex_list_sdec _ (lex2 E0_lt lt) l m); eauto.
  Qed.

  (* Hence decidable *)
  Corollary E0_lt_dec e f : { e <E₀ f } + { ¬ e <E₀ f }.
  Proof.
    destruct (E0_lt_sdec e f) as [ | | e f ]; eauto.
    right; intro; apply (@E0_lt_irrefl e); eauto.
  Qed.

  Hint Resolve E0_lt_dec : core.

  (** An "ordinal" of E₀ is in CNF if, recursivelly, it is
     of the shape ω[(e₁,i₁);...;(eₙ,iₙ)] with
     0 < i₁,...,iₙ and e₁ >ε₀ ... >ε₀ eₙ *)

  Definition E0_cnf_pred l :=
      ordered E0_lt⁻¹ (map fst l)
    ∧ ∀ e i, (e,i) ∈ l → 0 < i.

  Definition E0_cnf := E0_fall E0_cnf_pred.

  Fact E0_cnf_fix l : 
      E0_cnf ω[l]
    ↔ ordered E0_lt⁻¹ (map fst l) ∧ ∀ e i, (e,i) ∈ l → 0 < i ∧ E0_cnf e.
  Proof.
    unfold E0_cnf.
    rewrite E0_fall_fix.
    unfold E0_cnf_pred; firstorder.
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

  Unset Elimination Schemes.

  Inductive E0_lpo : E0 → E0 → Prop :=
    | E0_lpo_intro l m : lo (lex2 E0_lpo lt) l m → E0_lpo ω[l] ω[m].

  Set Elimination Schemes.

  Hint Constructors E0_lpo : core.

  Fact E0_lpo_inv l m : E0_lpo ω[l] ω[m] ↔ lo (lex2 E0_lpo lt) l m.
  Proof. split; auto; now inversion 1. Qed.

  Hint Resolve lt_wf : core.

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

  Fact E0_lpo_irrefl e : ¬ E0_lpo e e.
  Proof. apply Acc_irrefl with (1 := wf_E0_lpo _). Qed.

  Fact E0_lpo_trans : transitive E0_lpo.
  Proof.
    intros [] [] [] ?%E0_lpo_inv ?%E0_lpo_inv.
    constructor; econstructor 2; eauto.
  Qed.

  Hint Resolve E0_lpo_trans : core.

  Fact E0_lpo_trans' e f : clos_trans E0_lpo e f → E0_lpo e f.
  Proof. induction 1; eauto. Qed.

  Definition E0_le e f := e <E₀ f ∨ e = f.

  Infix "≤E₀" := E0_le.

  Fact E0_le_refl e : e ≤E₀ e.
  Proof. now right. Qed.

  Fact E0_le_trans : transitive E0_le.
  Proof. intros ? ? ? [] []; subst; red; eauto. Qed.
  
  Fact E0_le_antisym e f : e ≤E₀ f → f ≤E₀ e → e = f.
  Proof.
    intros [H1 |]  [H2 |]; auto.
    edestruct E0_lt_irrefl; eauto.
  Qed.

  Hint Resolve E0_le_refl E0_le_trans E0_le_antisym : core.

  Fact E0_le_lt_trans e f g : e ≤E₀ f → f <E₀ g → e <E₀ g.
  Proof. intros [] ?; subst; eauto. Qed.

  Fact E0_lt_le_trans e f g : e <E₀ f → f ≤E₀ g → e <E₀ g.
  Proof. intros ? []; subst; eauto. Qed.
  
  Fact E0_le_lt_dec e f : { e ≤E₀ f } + { f <E₀ e }.
  Proof. destruct (E0_lt_sdec e f); simpl; auto; now do 2 left. Qed. 

  Definition E0_zero := ω[[]].
  Notation "0₀" := E0_zero.
  Definition E0_one := ω[[(0₀, 1)]].
  Notation "1₀" := E0_one.

  Fact E0_zero_le : ∀e, 0₀ ≤E₀ e.
  Proof. intros [ [] ]; [ right | left ]; eauto; repeat constructor. Qed.

  Hint Resolve E0_zero_le : core.

  Fact E0_zero_not_gt : ∀e, ¬ e <E₀ 0₀.
  Proof. intros [ l ] ?%E0_lt_inv%lex_list_inv; now destruct l. Qed.
  
  Fact E0_lt_le_dec e f : { e <E₀ f } + { f ≤E₀ e}.
  Proof. unfold E0_le; destruct (E0_lt_sdec e f); auto. Qed.
  
  Fact E0_lt_sdec2 e f a : e <E₀ f → { a <E₀ e } + { a = e } + { e <E₀ a ∧ a <E₀ f } + { a = f } + { f <E₀ a }.
  Proof.
    intros H.
    destruct (E0_lt_sdec a e) as [ | | a e ]; auto.
    destruct (E0_lt_sdec f a); eauto.
  Qed. 

  Fact E0_lt_app_head l m k : ω[m] <E₀ ω[k] → ω[l++m] <E₀ ω[l++k].
  Proof. intros ?%E0_lt_inv; constructor; now apply lex_list_app_head. Qed.

  Fact E0_le_app_head l m k : ω[m] ≤E₀ ω[k] → ω[l++m] ≤E₀ ω[l++k].
  Proof.
    intros [ H | H ]; [ left | right ].
    + now apply E0_lt_app_head.
    + inversion H; subst; auto.
  Qed.

  (* We convert E0_cnf into an equivalent proof irrelevant predicate *)
  Definition cnf e := squash (E0_cnf_dec e).
  Local Fact cnf_iff e : cnf e ↔ E0_cnf e.
  Proof. apply squash_iff. Qed.

  Fact cnf_pirr e (h1 h2 : cnf e) : h1 = h2.
  Proof. apply squash_pirr. Qed.

  Fact cnf_fix l : 
      cnf ω[l]
    ↔ ordered E0_lt⁻¹ (map fst l)
    ∧ ∀ e i, (e,i) ∈ l → 0 < i ∧ cnf e.
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

  Fact cnf_cons_inv_left e i l : cnf ω[(e,i)::l] → cnf e.
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
  
  Fact cnf_cons_inv_right ei l : cnf ω[ei::l] → cnf ω[l].
  Proof. apply cnf_app_right_inv with (l := [_]). Qed.

  Hint Resolve cnf_sg
               cnf_cons_inv_left
               cnf_cons_inv_right
               cnf_app_left_inv
               cnf_app_right_inv : core.

  Fact cnf_zero : cnf 0₀.
  Proof.
    apply cnf_fix; simpl; split.
    + constructor.
    + tauto.
  Qed.

  Hint Resolve cnf_zero : core.

  Fact cnf_one : cnf E0_one.
  Proof. apply cnf_sg; auto. Qed.

  Hint Resolve cnf_one : core.

  Fact E0_one_ge e : e ≠ 0₀ → cnf e → 1₀ ≤E₀ e.
  Proof.
    destruct e as [[ | (x,i) r ]]; [ easy | intros _ Hr ].
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
  
  Fact E0_lt_one : ∀e, cnf e → e <E₀ 1₀ → e = 0₀.
  Proof.
    intros e H1 H2; revert e H2 H1.
    intros [l] [ | (x,i) ? [ []%E0_zero_not_gt | [_ H] ]%lex2_inv ]%E0_lt_inv%lex_list_sg_inv_right Hl; auto.
    assert (0 < i); try lia.
    apply cnf_fix in Hl.
    eapply Hl; eauto.
  Qed.

  (** Factor that proof !! *)
  Local Lemma E0_lt_ht_rec n e f : ⌊e⌋₀ < n → ⌊f⌋₀ < n → cnf e → cnf f → e <E₀ f → ⌊e⌋₀ ≤ ⌊f⌋₀.
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
  Theorem E0_lt_ht e f : cnf e → cnf f → e <E₀ f → ⌊e⌋₀ ≤ ⌊f⌋₀.
  Proof. apply E0_lt_ht_rec with (n := 1+⌊e⌋₀+⌊f⌋₀); lia. Qed.

  Corollary E0_ht_lt e f : cnf e → cnf f → ⌊e⌋₀ < ⌊f⌋₀ → e <E₀ f.
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
  Fact cnf_ht e i l : cnf ω[(e,i)::l] → ⌊ω[(e,i)::l]⌋₀ = 1+⌊e⌋₀.
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

  Hint Resolve lex2_E0_lpo_lt_trans : core.

  Fact lex2_E0_lpo_lt_trans' xi yj : clos_trans (lex2 E0_lpo lt) xi yj → lex2 E0_lpo lt xi yj.
  Proof. induction 1; eauto. Qed.

  Hint Resolve lex_list_mono : core.

  Lemma cnf_lt_lpo e f : cnf e → cnf f → e <E₀ f → E0_lpo e f.
  Proof.
    intros H1 H2; revert e H1 f H2.
    induction 1 as [ l He1 He2 He3 IH ] using cnf_rect.
    induction 1 as [ m Hf1 Hf2 Hf3 _  ] using cnf_rect.
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

  Hint Resolve cnf_lt_lpo : core.

  (** The fundamental theorem: <E₀ is well-founded on cnf *)
  Theorem E0_lt_wf : well_founded (λ x y, x <E₀ y ∧ cnf x ∧ cnf y).
  Proof.
    generalize wf_E0_lpo.
    apply wf_rel_morph with (f := fun x y => x = y); eauto.
    intros ? ? ? ? -> -> (? & ? & ?); eauto.
  Qed.

  (** The successor via an inductive spec *)
  Inductive E0_succ_gr : E0 → E0 → Prop :=
    | E0_succ_gr_0       : E0_succ_gr 0₀ 1₀
    | E0_succ_gr_1 l i   : E0_succ_gr ω[l++[(0₀,i)]] ω[l++[(0₀,S i)]] 
    | E0_succ_gr_2 l x i : x ≠ 0₀
                         → E0_succ_gr ω[l++[(x,i)]] ω[l++[(x,i);(ω[[]],1)]].

  (* Inversion lemma for the graph of E0_succ *)
  Fact E0_succ_gr_inv e f :
      E0_succ_gr e f
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

  Corollary E0_succ_gr_fun e f g : E0_succ_gr e f → E0_succ_gr e g → f = g.
  Proof. intros [] G%E0_succ_gr_inv; symmetry; apply G; auto. Qed.

  Definition E0_succ_pwc (e : E0) : sig (E0_succ_gr e).
  Proof.
    destruct e as [l].
    destruct l as [ | l (x,i) _ ] using rev_rect.
    + exists ω[(ω[nil],1)::nil]; constructor.
    + destruct x as [ [ | y m ] ].
      * exists ω[l++[(ω[[]],S i)]]; constructor.
      * exists ω[l⊣⊢[(ω[y::m],i);(ω[[]],1)]]; now constructor.
  Qed.

  Definition E0_succ e := π₁ (E0_succ_pwc e).

  Notation S₀ := E0_succ.

  Fact E0_succ_spec e : E0_succ_gr e (S₀ e).
  Proof. apply (proj2_sig _). Qed.

  Fact E0_succ_zero : S₀ 0₀ = 1₀.
  Proof. apply E0_succ_gr_fun with (1 := E0_succ_spec _); constructor. Qed.

  Hint Resolve E0_succ_zero : core.

  Fact E0_succ_cnf e : cnf e → cnf (S₀ e).
  Proof.
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

  Hint Resolve E0_succ_cnf : core.

  (** The successor is <E₀-greater *)
  Fact E0_succ_lt e : e <E₀ S₀ e.
  Proof.
    generalize (E0_succ e) (E0_succ_spec e).
    induction 1; constructor.
    + constructor.
    + apply lex_list_app_head.
      constructor 2; right; lia.
    + apply lex_list_app_head.
      constructor 3; constructor.
  Qed.

  Hint Resolve E0_succ_lt : core. 

  (** The ordinal addition via wlist_combine *)

  Definition E0_add e f :=
    match e, f with
    | ω[l], ω[m] => ω[wlist_combine E0_lt_sdec l m]
    end.

  Infix "+₀" := E0_add.

  Fact E0_add_cnf : ∀ e f, cnf e → cnf f → cnf (e +₀ f).
  Proof.
    intros [] [] (H1 & H2)%cnf_fix (H3 & H4)%cnf_fix; apply cnf_fix.
    split.
    + apply wlist_combine_ordered; auto.
    + intros ? ? (? & ? & [[]%H2|[]%H4])%wlist_combine_in;
        split; auto; lia.
  Qed.

  Fact E0_add_zero_right : ∀e, e +₀ 0₀ = e.
  Proof. intros []; simpl; auto. Qed.

  Fact E0_add_zero_left e : 0₀ +₀ e = e.
  Proof. destruct e as [[ | [] ]]; auto. Qed.

  (** Already wlist_combine is associative !! *)
  Lemma E0_add_assoc : ∀ u v w, u +₀ v +₀ w =  u +₀ (v +₀ w).
  Proof.
    intros [] [] []; unfold E0_add; f_equal.
    apply wlist_combine_assoc; auto.
  Qed.

  Lemma E0_add_one_right e : cnf e → e +₀ 1₀ = S₀ e.
  Proof.
    intros He.
    apply E0_succ_gr_fun with (2 := E0_succ_spec _).
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

  (** We show  ω[l] +₀ e ≤E₀ ω[m] +₀ e by induction on lex_list _ l m *)
  Lemma E0_add_mono_left u v e : cnf u → cnf v → cnf e → u ≤E₀ v → u +₀ e ≤E₀ v +₀ e.
  Proof.
    intros Hu Hv He [ H | -> ]; [ | now right ].
    revert u v e Hu Hv He H.
    intros [l] [m] [[ | (y,j) k]] Hl Hm Hk ?%E0_lt_inv.
    1: rewrite !E0_add_zero_right; now left; constructor.
    revert H Hl Hm.
    induction 1 as [ (x,i) m | (a,u) (b,v) l m [Hab | (<- & Huv)]%lex2_inv | (x,i) l m Hlm IH ] in j |- *; intros Hl Hm; unfold E0_add.
    + rewrite wlist_combine_nil_left.
      destruct (E0_lt_sdec x y).
      * rewrite wlist_combine_lt; auto.
      * rewrite wlist_combine_eq; auto.
        left; constructor; constructor 2; right.
        rewrite cnf_fix in Hm.
        assert (0 < i); [ | lia ].
        eapply Hm; eauto.
      * rewrite wlist_combine_gt; auto.
        left; constructor; constructor 2; now left.
    + destruct (@E0_lt_sdec2 a b y)
        as [ [ [ [ | ->] | [] ] | -> ] | ]; auto.
      * rewrite !wlist_combine_gt; eauto.
        left; constructor; constructor 2; now left.
      * rewrite wlist_combine_eq, wlist_combine_gt; auto.
        left; constructor; constructor 2; now left.
      * rewrite wlist_combine_lt, wlist_combine_gt; auto.
        left; constructor; constructor 2; now left.
      * rewrite wlist_combine_lt, wlist_combine_eq; auto.
        left; constructor; constructor 2; right.
        assert (0 < v); [ | lia ].
        apply cnf_fix in Hm.
        eapply Hm; eauto.
      * rewrite !wlist_combine_lt; eauto.
    + destruct (E0_lt_sdec a y).
      * rewrite !wlist_combine_lt; auto.
      * rewrite !wlist_combine_eq; auto.
        left; constructor; constructor 2; right; lia.
      * rewrite !wlist_combine_gt; auto.
        left; constructor; constructor 2; now right.
    + destruct (E0_lt_sdec x y).
      * rewrite !wlist_combine_lt; auto.
      * rewrite !wlist_combine_eq; auto.
      * rewrite !wlist_combine_gt; auto.
        destruct (IH j) as [ ?%E0_lt_inv | ?%E0_eq_inv ]; eauto.
        - left; constructor; now constructor 3.
        - right; do 2 f_equal; auto.
  Qed. 

  Lemma E0_add_incr : ∀ e f, cnf e → cnf f → 0₀ <E₀ f → e <E₀ e +₀ f.
  Proof.
    intros [l] [[| (y,j) m]] He Hf.
    1: now intros ?%E0_lt_irrefl.
    intros _.
    unfold E0_add.
    destruct (wlist_cut_choice E0_lt_sdec l y)
        as [ G1 
         | [ (i & l' & r & E & G1) 
         |   (x & i & l' & r & E & G1 & G2) ] ]; subst.
    + rewrite <- (app_nil_r l) at 2. 
      rewrite wlist_combine_gt_list; auto.
      constructor; apply lex_list_prefix'.
    + rewrite wlist_combine_gt_list; auto.
      simpl app at 4; rewrite wlist_combine_eq; auto.
      constructor; apply lex_list_app_head.
      constructor 2; right.
      apply cnf_fix in Hf.
      assert (0 < j); [ | lia ].
      eapply Hf; eauto.
    + rewrite wlist_combine_gt_list; auto.
      simpl app at 4; rewrite wlist_combine_lt; auto.
      constructor.
      apply lex_list_app_head; constructor 2.
      now left.
  Qed.

  Lemma E0_add_mono_right : ∀ e u v, cnf e → cnf u → cnf v → u <E₀ v → e +₀ u <E₀ e +₀ v.
  Proof.
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
    + destruct (wlist_combine_common E0_lt_sdec l y) as (l' & i & H).
      rewrite !H.
      apply lex_list_app_head.
      constructor 2; right; lia.
    + simpl; now apply lex_list_app_head.
  Qed.

  Hint Resolve in_map : core.

  Lemma E0_lt_inv_add e f : cnf e → cnf f → e <E₀ f → ∃a, f = e +₀ a ∧ 0₀ <E₀ a ∧ cnf a.
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
 
  Definition E0_is_succ e := ∃f, e = E0_succ f ∧ cnf f.
  Definition E0_is_limit e := e ≠ 0₀ ∧ ¬ ∃f, e = E0_succ f ∧ cnf f.

  Lemma E0_is_succ_iff e :
    cnf e → E0_is_succ e ↔ ∃ l i, 0 < i ∧ e = ω[l++[(0₀,i)]].
  Proof.
    intros He; split.
    + intros (f & -> & Hf).
      generalize (E0_succ f) (E0_succ_spec f).
      induction 1 as [ | l i | l x i ].
      * exists [], 1; split; auto.
      * exists l, (S i); split; auto; lia.
      * exists (l++[(x,i)]), 1; split; auto.
        now rewrite <- app_assoc.
    + intros (l & [ | [|i] ] & H1 & ->).
      * lia.
      * exists ω[l]; split; eauto.
        apply E0_succ_gr_fun with (2 := E0_succ_spec _).
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
      * exists ω[l++[(0₀,S i)]]; split; eauto.
        - apply E0_succ_gr_fun with (2 := E0_succ_spec _).
          constructor 2.
        - rewrite cnf_fix, map_app in He |- *.
          destruct He as [ H2 H3 ]; split; auto.
          intros ? ? [| [ [=] | []]]%in_app_iff; eauto.
          subst; split; eauto; lia.
  Qed.

  Lemma E0_is_limit_iff e :
    cnf e → E0_is_limit e ↔ ∃ l b i, 0 < i ∧ b ≠ 0₀ ∧ e = ω[l++[(b,i)]].
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

  Hint Resolve E0_add_cnf : core.

  (** e + l is a limit if l is *)
  Lemma E0_add_is_limit a e : 
    cnf a → cnf e → E0_is_limit e → E0_is_limit (a +₀ e).
  Proof.
    intros Ha He (m & b & i & Hi & Hb & ->)%E0_is_limit_iff; auto.
    apply E0_is_limit_iff; eauto.
    destruct a as [l].
    unfold E0_add.
    destruct (wlist_combine_last E0_lt_sdec l m b i)
      as (r & j & ? & ->).
    exists r, b, j; split; auto; lia.
  Qed.

  Fact E0_exp_is_limit e i :
    cnf e → e ≠ 0₀ → 0 < i → E0_is_limit ω[[(e,i)]].
  Proof.
    intros H1 H2 H3.
    apply E0_is_limit_iff; auto.
    exists [], e, i; auto.
  Qed.

  Hint Resolve E0_add_is_limit E0_exp_is_limit : core.

  (** a + ω^(e.i) is a limit ordinal *)
  Fact E0_add_exp_is_limit a e i : 
    cnf a → cnf e → e ≠ 0₀ → 0 < i → E0_is_limit (a +₀ ω[[(e,i)]]).
  Proof. eauto. Qed.

  (** TODO: maybe add notation for ω[[(e,n)]] ie ω^(e.n) *)
  
  Fact E0_add_exp e i j : ω[[(e,i)]] +₀ ω[[(e,j)]] = ω[[(e,i+j)]].
  Proof.
    unfold E0_add.
    rewrite wlist_combine_eq; auto.
  Qed.

  Definition E0_omega e := ω[[(e,1)]].

  Notation "'ω' '^' e" := (E0_omega e) (at level 1, format "ω ^ e").
  
  Fact E0_omega_zero : ω^0₀ = 1₀.
  Proof. trivial. Qed.

  Fact E0_omega_cnf e : cnf e → cnf ω^e.
  Proof. intros; apply cnf_sg; auto. Qed.

  Hint Resolve E0_omega_cnf : core.

  Fact E0_lt_omega e : cnf e → e <E₀ ω^e.
  Proof. intro; apply E0_lt_sub with 1; auto. Qed.

  Fact E0_add_lt_omega a e : cnf a → e ≠ 0₀ → a <E₀ ω^e → a +₀ ω^e = ω^e.
  Proof.
    destruct a as [ l ]; intros Ha He H.
    revert H Ha He.
    intros [ | (x,i) m [ H | (_ & H) ]%lex2_inv ]%E0_lt_inv%lex_list_sg_inv_right Ha He; unfold E0_add, E0_omega; f_equal.
    + rewrite wlist_combine_lt; eauto.
    + apply cnf_fix in Ha.
      assert (0 < i); [ | lia ].
      eapply Ha; eauto.
  Qed.

  Lemma E0_add_omega_fun_right a b e f : a +₀ ω^e = b +₀ ω^f → e = f.
  Proof.
    revert a b e f.
    intros [a] [b] e f; unfold E0_omega, E0_add.
    destruct (wlist_combine_last E0_lt_sdec a [] e 1)
      as (l & i & H1 & H2).
    destruct (wlist_combine_last E0_lt_sdec b [] f 1)
      as (m & j & H3 & H4).
    simpl app in H2, H4; rewrite H2, H4.
    injection 1.
    intros (_ & [=])%app_inj_tail; now subst.
  Qed.
  
  (* a +₀ ω^e is the limit decomposition of that ordinal
     - e is unique 
     - but a is not and we choose the least one *)
  Definition E0_least_split (a e : E0) :=
    ∀b, cnf b → a +₀ ω^e = b +₀ ω^e → a ≤E₀ b.
    
  Fact E0_split_least_uniq a b e f : 
      cnf a
    → cnf b
    → E0_least_split a e
    → E0_least_split b f
    → a +₀ ω^e = b +₀ ω^f
    → a = b ∧ e = f.
  Proof.
    intros Ha Hb He Hf E.
    assert (e = f) as <-.
    1: now apply E0_add_omega_fun_right in E.
    split; auto.
  Qed.

  (** inversion for f < ω^b:
      - either f is 0 (and b is also 0)
      - or f is below ω^a.n for some a < b and some n > 0 *)
  Lemma E0_lt_omega_inv f b :
      cnf f
    → cnf b
    → f <E₀ ω^b
    → f = 0₀ ∨ ∃n a, 0 < n ∧ f <E₀ ω[[(a, n)]] ∧ a <E₀ b ∧ cnf a.
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
  
  Lemma E0_lt_exp a i b j : a <E₀ b -> ω[[(a, i)]] <E₀ ω[[(b, j)]].
  Proof. constructor; constructor 2; now left. Qed.

  (** any ordinal is either 0, a successor or a limit ordinal *)

  Inductive E0_decomp : E0 → Type :=
    | E0_decomp_zero : E0_decomp 0₀
    | E0_decomp_succ e : cnf e → E0_decomp (S₀ e)
    | E0_decomp_limit g e : e ≠ 0₀ → cnf g → cnf e → E0_least_split g e → E0_decomp (g +₀ ω^e).

  (* Proof that if cnf u then
     either u is E0_zero                             (limit ordinal)
      or  u is ω[l++[(E0_zero,i)]])                (successor)
      or  u is ω[l++[(e,i)]]) with  E0_zero <E₀ e  (limit ordinal) *)

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
          ++ apply E0_succ_gr_fun with (1 := E0_succ_spec _).
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
          ++ apply E0_succ_gr_fun with (1 := E0_succ_spec _).
             constructor 2.
      * destruct i as [ | i ].
        - replace ω[m++[(ω[yj::e],1)]]
            with (E0_add ω[m] ω[[(ω[yj::e],1)]]).
          ++ constructor 3; easy || eauto.
             ** apply cnf_fix; repeat split; eauto.
                rewrite map_app in H1.
                now apply ordered_app_head in H1.
             ** intros [k] Hk; unfold E0_omega, E0_add.
                intros E%E0_eq_inv.
                rewrite <- (app_nil_r m) in E.
                rewrite map_app, ordered_app_iff in H1; eauto.
                rewrite wlist_combine_gt_list in E; eauto.
                2:{ apply Forall_forall.
                    intros (x,i) Hxi; apply H1; simpl; eauto.
                    apply in_map_iff; exists (x,i); auto. }
                simpl wlist_combine at 1 in E.
                symmetry in E.
                apply wlist_combine_eq_snoc_inv in E
                  as (r & -> & _); auto.
                destruct r.
                -- rewrite app_nil_r; now right.
                -- left; constructor.
                   apply lex_list_prefix'.
          ++ unfold E0_add.
             rewrite wlist_combine_spec1; eauto.
             rewrite map_app in H1; simpl in H1.
             apply ordered_snoc_iff, proj2 in H1; auto.
             apply Forall_forall.
             now intros (f,i) H; apply H1, in_map.
        - replace ω[m++[(ω[yj::e], S (S i))]]
            with (E0_add ω[m++[(ω[yj::e],S i)]] ω[[(ω[yj::e],1)]]).
          ++ constructor 3; easy || eauto.
             ** apply cnf_fix; split.
                -- rewrite map_app in H1 |- *; auto.
                -- intros f j [|[[=]|[]]]%in_app_iff; split; subst; eauto; lia.
             ** intros [k] Hk; unfold E0_omega, E0_add.
                intros E%E0_eq_inv.
                rewrite map_app, ordered_app_iff in H1; eauto.
                rewrite wlist_combine_gt_list in E; eauto.
                2:{ apply Forall_forall.
                    intros (y,j) Hxi; apply H1; simpl; eauto.
                    apply in_map_iff; exists (y,j); auto. }
                rewrite wlist_combine_eq in E; auto.
                symmetry in E.
                apply wlist_combine_eq_snoc_inv in E
                  as (r & -> & _ & _ & [ H | (p & r' & ? & ->) ]); auto.
                1: exfalso; lia.
                replace p with (S i) by lia.
                destruct r'; [ now right | ].
                left; constructor.
                apply lex_list_app_head.
                constructor 3; constructor 1.
          ++ unfold E0_add.
             rewrite <- (app_nil_r (_++[_])), <- app_assoc.
             rewrite wlist_combine_spec2; auto.
             ** rewrite app_nil_r; do 4 f_equal; lia.
             ** rewrite map_app in H1; simpl in H1. 
                apply ordered_snoc_iff, proj2 in H1; auto.
                apply Forall_forall.
                intros [] ?; now apply H1, in_map.
  Qed.

  Section cnf_add_rect.

    Variables (P : ∀e, cnf e → Type)
              (HP0 : ∀ h, P 0₀ h)
              (HP1 : ∀ e he h, P e he → P (S₀ e) h)
              (HP2 : ∀ g e hg he h, e ≠ 0₀ → E0_least_split g e → P g hg → P e he → P (g +₀ ω^e) h).

    Theorem cnf_add_rect e he : P e he.
    Proof.
      induction e as [ e IHe ] in he |- * using (well_founded_induction_type E0_lt_wf).
      destruct (E0_decomp_compute e he) as [ | e h | g e h hg he' ]; auto.
      + apply HP1 with h, IHe; auto.
      + apply HP2 with (hg := hg) (he := he'); auto.
      * apply IHe; split; auto.
        rewrite <- (E0_add_zero_right g) at 1.
        apply E0_add_mono_right; auto.
        apply E0_le_lt_trans with (2 := E0_lt_omega _ he'); auto.
      * apply IHe; split; auto.
        apply E0_le_lt_trans with (g +₀ e).
        - rewrite <- (E0_add_zero_left e) at 1.
          apply E0_add_mono_left; auto.
        - apply E0_add_mono_right, E0_lt_omega; auto.
    Qed.

  End cnf_add_rect.

End E0.

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

#[local] Hint Resolve eps0_lt_trans : core.

#[local] Hint Constructors sdec : core.

Theorem eps0_lt_sdec e f : sdec eps0_lt e f.
Proof.
  revert e f; intros (e & He) (f & Hf).
  destruct (E0_lt_sdec e f) as []; eauto.
  rewrite (cnf_pirr _ He Hf); auto.
Qed.

Fact eps0_eq_dec (e f : ε₀) : { e = f } + { e ≠ f }.
Proof.
  destruct (eps0_lt_sdec e f) as [ e f H | | e f H ]; auto;
    right; intros <-; revert H; apply eps0_lt_irrefl.
Qed.

#[local] Hint Resolve cnf_lt_lpo : core.

(* <ε₀ is well-founded *)
Theorem wf_eps0_lt : well_founded eps0_lt.
Proof.
  generalize E0_lt_wf.
  apply wf_rel_morph with (f := fun x y => x = π₁ y).
  + intros []; eauto.
  + unfold eps0_lt; intros ? ? [] [] -> ->; simpl; eauto.
Qed.

#[local] Hint Resolve cnf_zero cnf_one : core.

Definition eps0_zero : ε₀.
Proof. now exists E0_zero. Defined.

Definition eps0_one : ε₀.
Proof. now exists E0_one. Defined.

Notation "0₀" := eps0_zero.
Notation "1₀" := eps0_one.

Fact eps0_zero_not_gt : ∀e, ¬ e <ε₀ 0₀.
Proof. intros []; apply E0_zero_not_gt. Qed.

Definition eps0_le e f := e <ε₀ f ∨ e = f.

Notation "e '≤ε₀' f" := (eps0_le e f) (at level 70, format "e  ≤ε₀  f").

Fact eps0_le_iff e f : e ≤ε₀ f ↔ E0_le (π₁ e) (π₁ f).
Proof.
  unfold eps0_le, E0_le; rewrite eps0_eq_iff.  
  revert e f; intros [ e He ] [ f Hf ]; simpl; tauto.
Qed.

Fact eps0_zero_least e : 0₀ ≤ε₀ e.
Proof.
  apply eps0_le_iff.
  destruct e as [ [l] He ]; simpl.
  destruct l; [ right | left ]; auto.
  constructor; constructor.
Qed.

Fact eps0_lt_le_weak e f : e <ε₀ f → e ≤ε₀ f.
Proof. now left. Qed. 

Fact eps0_le_refl e : e ≤ε₀ e.
Proof. now right. Qed.

Fact eps0_le_antisym e f : e ≤ε₀ f → f ≤ε₀ e → e = f.
Proof. rewrite !eps0_le_iff, eps0_eq_iff; apply E0_le_antisym. Qed.

Fact eps0_le_trans e f g : e ≤ε₀ f → f ≤ε₀ g → e ≤ε₀ g.
Proof. rewrite !eps0_le_iff; apply E0_le_trans. Qed.

Fact eps0_lt_le_trans e f g : e <ε₀ f → f ≤ε₀ g → e <ε₀ g.
Proof. rewrite eps0_le_iff; apply E0_lt_le_trans. Qed.

Fact eps0_le_lt_trans e f g : e ≤ε₀ f → f <ε₀ g → e <ε₀ g.
Proof. rewrite eps0_le_iff; apply E0_le_lt_trans. Qed.

Hint Resolve eps0_zero_least eps0_lt_le_weak
             eps0_le_refl eps0_le_antisym
             eps0_le_trans eps0_le_lt_trans
             eps0_lt_le_trans : core.

Fact eps0_zero_or_pos e : { e = 0₀ } + { 0₀ <ε₀ e }.
Proof.
  destruct e as [ [ [ | x l ] ] Hl ].
  + left; apply eps0_eq_iff; auto.
  + right; cbv; repeat constructor.
Qed.

Fact eps0_le_lt_dec e f : { e ≤ε₀ f } + { f <ε₀ e }.
Proof. destruct (eps0_lt_sdec e f); auto. Qed.

Fact eps0_le_zero e : e ≤ε₀ 0₀ → e = 0₀.
Proof. intros []; auto. Qed.

#[local] Hint Resolve E0_succ_cnf : core.

Definition eps0_succ (e : ε₀) : ε₀.
Proof.
  destruct e as [ e He ].
  exists (E0_succ e); apply E0_succ_cnf, He.
Defined.

Notation "'S₀' e" := (eps0_succ e) (at level 28).

#[local] Hint Resolve E0_succ_zero E0_succ_lt : core.

(** The successor of E0_zero is E0_one *) 
Fact eps0_succ_zero_is_one : S₀ 0₀ = 1₀.
Proof. apply eps0_eq_iff; simpl; auto. Qed.

(** The successor is <ε₀-greater *)
Fact eps0_lt_succ e : e <ε₀ S₀ e.
Proof. destruct e; simpl; auto. Qed.

Fact eps0_lt_one : ∀e, e <ε₀ 1₀ → e = 0₀.
Proof. intros []; rewrite eps0_eq_iff; apply E0_lt_one; auto. Qed.

Fact eps0_le_not_succ e : ¬ S₀ e ≤ε₀ e.
Proof. intros H; apply (@eps0_lt_irrefl e), eps0_lt_le_trans with (2 := H), eps0_lt_succ. Qed.

Fact eps0_zero_not_succ e : 0₀ ≠ S₀ e.
Proof.
  intros H.
  apply (@eps0_lt_irrefl 0₀).
  rewrite H at 2.
  apply eps0_le_lt_trans with (2 := eps0_lt_succ _).
  apply eps0_zero_least.
Qed.

#[local] Hint Resolve E0_add_cnf : core.

Definition eps0_add : ε₀ → ε₀ → ε₀.
Proof. intros [e] [f]; exists (E0_add e f); eauto. Defined.

Infix "+₀" := eps0_add.

Fact eps0_add_zero_left : ∀e, 0₀ +₀ e = e.
Proof. intros []; apply eps0_eq_iff, E0_add_zero_left. Qed.

Fact eps0_add_zero_right : ∀e, e +₀ 0₀ = e.
Proof. intros []; apply eps0_eq_iff, E0_add_zero_right. Qed.

Fact eps0_add_assoc : ∀ e f g, (e +₀ f) +₀ g = e +₀ (f +₀ g).
Proof. intros [] [] []; apply eps0_eq_iff; simpl; apply E0_add_assoc. Qed.

Fact eps0_add_one_right : ∀e, e +₀ 1₀ = S₀ e.
Proof. intros []; apply eps0_eq_iff, E0_add_one_right; auto. Qed.

(** The defining equation for _ + S _ *)
Fact eps0_add_succ_right e f : e +₀ S₀ f = S₀ (e +₀ f).
Proof. now rewrite <- eps0_add_one_right, <- eps0_add_assoc, eps0_add_one_right. Qed.

Fact eps0_lt_inv_add : ∀ e f, e <ε₀ f → ∃a, f = e +₀ a ∧ 0₀ <ε₀ a.
Proof.
  intros [e] [f] (a & ? & ? & Ha)%E0_lt_inv_add; auto; simpl in *.
  exists (exist _ a Ha); rewrite eps0_eq_iff; simpl; auto.
Qed.

Fact eps0_add_mono_left : ∀ e f g, e ≤ε₀ f → e +₀ g ≤ε₀ f +₀ g.
Proof. intros [] [] []; rewrite !eps0_le_iff; simpl; apply E0_add_mono_left; auto. Qed.

Fact eps0_add_incr : ∀ e f, 0₀ <ε₀ f → e <ε₀ e +₀ f.
Proof. intros [] []; apply E0_add_incr; auto. Qed.

Fact eps0_add_mono_right : ∀ e f g, f <ε₀ g → e +₀ f <ε₀ e +₀ g.
Proof. intros [] [] []; simpl; apply E0_add_mono_right; auto. Qed.

Hint Resolve eps0_add_mono_left eps0_add_mono_right : core.

Fact eps0_add_mono e e' f f' : e ≤ε₀ e' → f ≤ε₀ f' → e +₀ f ≤ε₀ e' +₀ f'.
Proof. intros ? [ | <- ]; eauto. Qed.

Fact eps0_add_lt_cancel e u v : e +₀ u <ε₀ e +₀ v → u <ε₀ v.
Proof. 
  intros H.
  destruct (eps0_lt_sdec u v) as [ u v ? | u | u v G ]; auto.
  + now apply E0_lt_irrefl in H.
  + apply eps0_add_mono_right with (e := e) in G.
    destruct (@eps0_lt_irrefl (e +₀ v)); eauto.
Qed.

Fact eps0_add_eq_zero e f : e +₀ f = 0₀ → e = 0₀ ∧ f = 0₀.
Proof.
  intros H.
  destruct (eps0_zero_or_pos f) as [ -> | Hf ].
  + now rewrite eps0_add_zero_right in H.
  + apply eps0_add_incr with (e := e) in Hf.
    rewrite H in Hf.
    now apply eps0_zero_not_gt in Hf.
Qed.

Lemma eps0_lt_add_inv_add : ∀ e a f, e <ε₀ a +₀ f → e <ε₀ a ∨ ∃g, e = a +₀ g ∧ g <ε₀ f.
Proof.
  intros e a f H.
  destruct (eps0_lt_sdec e a) as [ e a G | e | e a G ]; auto.
  + right; exists 0₀.
    rewrite eps0_add_zero_right; split; auto.
    destruct (eps0_zero_or_pos f) as [ -> | ]; auto.
    exfalso; revert H; rewrite eps0_add_zero_right; apply eps0_lt_irrefl.
  + right.
    apply eps0_lt_inv_add in G as (b & -> & Hb).
    apply eps0_add_lt_cancel in H; eauto.
Qed.

Fact eps0_succ_next e f : e <ε₀ f → S₀ e ≤ε₀ f.
Proof.
  intros H.
  destruct (eps0_le_lt_dec (S₀ e) f) as [ | C ]; auto; exfalso.
  rewrite <- eps0_add_one_right in C; auto.
  apply eps0_lt_add_inv_add in C as [ C | (g & -> & Hg) ]; eauto.
  + apply (@eps0_lt_irrefl e); eauto.
  + apply eps0_lt_one in Hg as ->; auto.
    revert H; rewrite eps0_add_zero_right; apply E0_lt_irrefl.
Qed.

Fact eps0_succ_next_inv e f : e <ε₀ S₀ f → e ≤ε₀ f.
Proof.
  intros H.
  destruct (eps0_lt_sdec e f) as [ e f H1 | e | e f H1%eps0_succ_next ].
  + now left.
  + now right.
  + destruct (@eps0_lt_irrefl e).
    now apply eps0_lt_le_trans with (2 := H1).
Qed.

Hint Resolve eps0_le_lt_trans eps0_lt_succ eps0_le_not_succ : core.

Fact eps0_succ_mono e f : e <ε₀ f ↔ S₀ e <ε₀ S₀ f.
Proof.
  split.
  + intros H%eps0_succ_next; eauto.
  + intros H%eps0_succ_next_inv.
    destruct (eps0_le_lt_dec f e); eauto.
Qed.

Fact eps0_succ_inj e f : S₀ e = S₀ f → e = f.
Proof.
  intros E.
  destruct (eps0_lt_sdec e f) as [ e f G | e | e f G ]; auto.
    all: apply eps0_succ_mono in G; auto; rewrite E in G; destruct (eps0_lt_irrefl G).
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

Fact eps0_add_cancel e u v : e +₀ u = e +₀ v → u = v.
Proof.
  intros H.
  destruct (eps0_lt_sdec u v) as [ u v G | u | u v G ]; auto;
    apply eps0_add_mono_right with (e := e) in G; rewrite H in G;
    edestruct eps0_lt_irrefl; eauto.
Qed.

Fact eps0_add_le_cancel e u v : e +₀ u ≤ε₀ e +₀ v → u ≤ε₀ v.
Proof. now intros [ ?%eps0_add_lt_cancel | ?%eps0_add_cancel ]; [ left | right ]. Qed.

(* Hence a successor is not a limit ordinal 

   Successor is of shape ω[_++[(ω[[]],1+i)]]
   Limit is either ω[[]] or ω[_++[(x,i)]] with 0 < i and x <> ω[[]] *)

Definition eps0_is_succ e := ∃f, e = S₀ f.

Fact eps0_is_succ_S e : eps0_is_succ (S₀ e).
Proof. now exists e. Qed.

Hint Resolve eps0_is_succ_S : core.

Fact eps0_is_succ_iff e : eps0_is_succ e ↔ E0_is_succ (π₁ e).
Proof.
  split.
  + intros ((f & ?) & ->); exists f; auto.
  + intros (f & H1 & H2); exists (exist _ f H2).
    apply eps0_eq_iff; now rewrite H1.
Qed.

Definition eps0_is_limit e := e ≠ 0₀ ∧ ¬ eps0_is_succ e.

(** Notice that the converse MAY NOT HOLD *)
Fact eps0_is_limit_iff e : eps0_is_limit e ↔ E0_is_limit (π₁ e).
Proof.
  split; intros (H1 & H2); split.
  + contradict H1; subst; now apply eps0_eq_iff.
  + contradict H2; destruct H2 as (f & H2 & H3).
    exists (exist _ f H3); now apply eps0_eq_iff.
  + contradict H1; now apply eps0_eq_iff in H1.
  + contradict H2; destruct H2 as ((f & Hf) & ->); now exists f.
Qed.

Fact eps0_add_is_limit a e : eps0_is_limit e → eps0_is_limit (a +₀ e).
Proof.
  rewrite !eps0_is_limit_iff.
  destruct a; destruct e; apply E0_add_is_limit; auto.
Qed.

Inductive eps0_choice : ε₀ → Type :=
  | eps0_choice_0 : eps0_choice 0₀
  | eps0_choice_1 e : eps0_choice (S₀ e)
  | eps0_choice_2 e : eps0_is_limit e → eps0_choice e.

Fact eps0_choose : ∀e, eps0_choice e.
Proof.
  intros (e & He).
  destruct E0_decomp_compute with (1 := He).
  + rewrite (cnf_pirr _ He cnf_zero); constructor.
  + rewrite (cnf_pirr _ He (E0_succ_cnf _ c)). 
    exact (eps0_choice_1 (exist _ e c)).
  + constructor 3.
    apply eps0_is_limit_iff; red; simpl.
    apply E0_add_is_limit; auto.
    * now apply E0_omega_cnf.
    * apply E0_exp_is_limit; auto.
Defined.

(* ω^{e.(S n)} *)
Definition eps0_exp_S : ε₀ → nat → ε₀.
Proof.
  intros (e & He) n.
  exists (E0_cons [(e,1+n)]).
  apply cnf_sg; auto; lia.
Defined.

Fact eps0_lt_exp_S e n : e <ε₀ eps0_exp_S e n.
Proof.
  destruct e as [e]; unfold eps0_exp_S; cbn.
  apply E0_lt_sub with (1+n); auto.
  apply cnf_sg; auto; lia.
Qed.

Fact eps0_lt_zero_exp_S e n : 0₀ <ε₀ eps0_exp_S e n.
Proof. apply eps0_le_lt_trans with (2 := eps0_lt_exp_S _ _); auto. Qed.

Fact eps0_exp_S_mono_right : ∀ e n m, n < m → eps0_exp_S e n <ε₀ eps0_exp_S e m.
Proof. intros [] ? ?; simpl; constructor; constructor 2; right; lia. Qed.

Fact eps0_exp_S_mono_left : ∀ e f n m, e <ε₀ f → eps0_exp_S e n <ε₀ eps0_exp_S f m.
Proof. intros [] [] ? ?; apply E0_lt_exp. Qed.

Fact eps0_is_limit_exp_S e n : e ≠ 0₀ → eps0_is_limit (eps0_exp_S e n).
Proof.
  intros H.
  apply eps0_is_limit_iff.
  destruct e; simpl.
  apply E0_exp_is_limit; auto.
  + contradict H; now apply eps0_eq_iff.
  + lia.
Qed.

Fact eps0_add_exp_S e i j : eps0_exp_S e i +₀ eps0_exp_S e j = eps0_exp_S e (i+j+1).
Proof.
  destruct e as (e & He); apply eps0_eq_iff; unfold eps0_add, eps0_exp_S, proj1_sig.
  rewrite E0_add_exp; do 3 f_equal; lia.
Qed.

(* ω^e *)
Definition eps0_omega : ε₀ → ε₀.
Proof. intro e; apply (eps0_exp_S e 0). Defined.

Notation "'ω' '^' e" := (eps0_omega e) (at level 1, format "ω ^ e").

Fact eps0_omega_zero : ω^0₀ = 1₀.
Proof. apply eps0_eq_iff; trivial. Qed.

Fact eps0_lt_omega e : e <ε₀ ω^e.
Proof. apply eps0_lt_exp_S. Qed.

Fact eps0_omega_mono_lt : ∀ e f, e <ε₀ f → ω^e <ε₀ ω^f.
Proof. intros [] [] ?; constructor; constructor 2; left; auto. Qed.

Fact eps0_omega_mono_le e f : e ≤ε₀ f → ω^e ≤ε₀ ω^f.
Proof. intros [ | <- ]; auto; left; now apply eps0_omega_mono_lt. Qed.

Fact eps0_omega_inj e f : ω^e = ω^f → e = f.
Proof.
  intros E.
  destruct (eps0_lt_sdec e f) as [ e f H | | e f H ]; auto;
    apply eps0_omega_mono_lt in H; rewrite E in H; now apply eps0_lt_irrefl in H.
Qed.

Fact eps0_one_eq_omega e : 1₀ = ω^e → e = 0₀.
Proof.
  rewrite <- eps0_omega_zero.
  now intros <-%eps0_omega_inj.
Qed. 

Fact eps0_zero_lt_omega e : 0₀ <ε₀ ω^e.
Proof. apply eps0_lt_zero_exp_S. Qed.

Hint Resolve eps0_zero_lt_omega : core.

Fact eps0_zero_neq_omega e : 0₀ ≠ ω^e.
Proof. 
  intros H.
  apply (@eps0_lt_irrefl 0₀).
  rewrite H at 2.
  apply eps0_zero_lt_omega.
Qed.

Fact eps0_is_limit_omega e : e ≠ 0₀ → eps0_is_limit ω^e.
Proof. apply eps0_is_limit_exp_S. Qed.

Fact eps0_is_limit_add_omega a e : e ≠ 0₀ → eps0_is_limit (a +₀ ω^e).
Proof. intro; apply eps0_add_is_limit, eps0_is_limit_omega; auto. Qed.

Fact eps0_add_omega_not_zero a e : 0₀ ≠ a +₀ ω^e.
Proof.
  intros H.
  apply (@eps0_lt_irrefl (a+₀ω^e)).
  rewrite <- H at 1.
  apply eps0_lt_le_trans with (1 := eps0_zero_lt_omega e).
  rewrite <- (eps0_add_zero_left ω^e) at 1.
  apply eps0_add_mono_left, eps0_zero_least.
Qed.

Fact eps0_add_omega_not_succ a b e : e ≠ 0₀ → S₀ a ≠ b +₀ ω^e.
Proof.
  intros E H.
  assert (eps0_is_limit (S₀ a)) as [ _ [] ]; eauto.
  rewrite H.
  now apply eps0_is_limit_add_omega.
Qed.

Fact eps0_succ_eq_add_omega a b e : S₀ a = b +₀ ω^e → e = 0₀.
Proof.
  intros H.
  destruct (eps0_eq_dec e 0₀); auto.
  now apply eps0_add_omega_not_succ in H.
Qed.

Fact eps0_succ_eq_omega a e : S₀ a = ω^e → e = 0₀.
Proof.
  rewrite <- (eps0_add_zero_left ω^e).
  apply eps0_succ_eq_add_omega.
Qed.

Fact eps0_add_lt_omega : ∀ a e, e ≠ 0₀ → a <ε₀ ω^e → a +₀ ω^e = ω^e.
Proof.
  intros [a Ha] [e He] He' H.
  apply eps0_eq_iff; simpl in H |- *.
  revert H; apply E0_add_lt_omega; auto.
  contradict He'; subst; now apply eps0_eq_iff.
Qed.

Lemma eps0_add_omega_fun_right : ∀ a b e f, a +₀ ω^e = b +₀ ω^f → e = f.
Proof.
  intros [] [] [] []; rewrite !eps0_eq_iff; simpl.
  apply E0_add_omega_fun_right.
Qed.

(* a +₀ ω^e is the limit decomposition of that ordinal
 - e is unique 
 - but a is not and we choose the least one *)
Definition eps0_least_split a e  :=
    ∀b, a +₀ ω^e = b +₀ ω^e → a ≤ε₀ b.
    
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

Fact eps0_one_eq_least_split a e :
    eps0_least_split a e
  → 1₀ = a +₀ ω^e
  → a = 0₀ ∧ e = 0₀.
Proof.
  intros H1.
  replace 1₀ with (0₀ +₀ ω^0₀).
  + intros (<- & <-)%eps0_split_least_uniq; eauto.
    red; eauto.
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
  red; auto.
Qed.

Section eps0_add_rect.

  (** Induction principle corresponding to the following building rules 
      for ordinals below ε₀:

                    e      g  e  e≠0₀  eps0_least_split g e
        ------   ------   ----------------------------------
          0₀      S₀ e             g +₀ ω^e
   *)

  Variables (P : ε₀ → Type)
            (HP0 : P 0₀)
            (HP1 : ∀ e, P e → P (S₀ e))
            (HP2 : ∀ g e, e ≠ 0₀ → eps0_least_split g e → P g → P e → P (g +₀ ω^e)).

  Local Fact P_pirr e h1 h2 : P (exist _ e h1) → P (exist _ e h2).
  Proof. now rewrite (cnf_pirr _ h1 h2). Qed.

  Theorem eps0_add_rect e : P e.
  Proof.
    destruct e as (e & He); revert e He; apply cnf_add_rect.
    + intro; eapply P_pirr, HP0.
    + intros e he h H; eapply P_pirr, (HP1 H).
    + intros g e hg he h H1 H2 H3 H4.
      eapply P_pirr.
      apply HP2 with (3 := H3) (4 := H4).
      * now intros ?%eps0_eq_iff.
      * intros []; rewrite !eps0_eq_iff, eps0_le_iff; simpl; auto.
  Qed.

End eps0_add_rect.

Fact eps0_least_split_find e : eps0_is_limit e → { a : _ & { g | e = a+₀ω^g ∧ g ≠ 0₀ ∧ eps0_least_split a g } }.
Proof.
  destruct e as [ | | a g H1 H2 _ _ ] using eps0_add_rect.
  + now intros [ [] _ ].
  + intros [ _ [] ]; auto.
  + exists a, g; auto.
Qed.

(* can we define multiplication using 
   the decomposition 0, S α or α + ω^γ decomposition ?
    α.0 = 0
    α· S(β) = (α · β) + α
    α(β + γ) = αβ + αγ

    α^1 = α.
    α^β·α^γ = α^(β + γ).
    α.(β + ω^γ) = αβ + α.ω^γ *)
    
    
(*

    + γ = 0 
      * e.ω^γ = e.ω^0 = e.1 = e
    + γ ≠ 0
      * 0.ω^γ = 0
      * (S α).ω^γ = (α+1).ω^γ 
        - α = 0 -> ω^γ
        - α ≠ 0 -> α.ω^γ
      * (α+ω^β).ω^γ 
        - α < ω^β then α+ω^β = ω^β and (α+ω^β).ω^γ = ω^(β+γ) 
        - ω^β ≤ α then (α+ω^β).ω^γ = α.ω^γ. *)

Inductive eps0_mult_omega_gr γ : ε₀ → ε₀ → Prop :=
  | eps0_mult_omega_gr_0       : eps0_mult_omega_gr γ 0₀ 0₀
  | eps0_mult_omega_gr_1       : eps0_mult_omega_gr γ 1₀ ω^γ
  | eps0_mult_omega_gr_2 α r   : α ≠ 0₀
                               → eps0_mult_omega_gr γ α r
                               → eps0_mult_omega_gr γ (S₀ α) r
  | eps0_mult_omega_gr_3 β     : β ≠ 0₀
                               → eps0_mult_omega_gr γ ω^β ω^(β+₀γ)
  | eps0_mult_omega_gr_4 α β r : β ≠ 0₀
                               → ω^β ≤ε₀ α
                               → eps0_least_split α β
                               → eps0_mult_omega_gr γ α r 
                               → eps0_mult_omega_gr γ (α+₀ω^β) r
  .

Local Lemma eps0_mult_omega_gr_fun_rec γ e f r s :
    eps0_mult_omega_gr γ e r
  → eps0_mult_omega_gr γ f s
  → e = f
  → r = s.
Proof.
  intros H1 H2; revert H1 f s H2.
  induction 1 as [ | | a r H1 H2 IH2 | b H1 | a b r H1 H2 H3 H4 IH4 ].
  + induction 1 as [ | | a' r' G1 G2 IG2 | b' G1 | a' b' r' G1 G2 G3 G4 IG4 ]; easy || auto.
    * now intros ?%eps0_zero_not_succ.
    * now intros ?%eps0_zero_neq_omega.
    * now intros ?%eps0_add_omega_not_zero.
  + induction 1 as [ | | a' r' G1 G2 IG2 | b' G1 | a' b' r' G1 G2 G3 G4 IG4 ]; easy || auto.
    * rewrite <- eps0_succ_zero_is_one.
      now intros <-%eps0_succ_inj.
    * now intros ->%eps0_one_eq_omega.
    * now intros (-> & ->)%eps0_one_eq_least_split.
  + induction 1 as [ | | a' r' G1 G2 IG2 | b' G1 | a' b' r' G1 G2 G3 G4 IG4 ]; easy || auto.
    * intros H; symmetry in H; now apply eps0_zero_not_succ in H.
    * rewrite <- eps0_succ_zero_is_one.
      now intros ->%eps0_succ_inj.
    * intros <-%eps0_succ_inj; eauto.
    * now intros ->%eps0_succ_eq_omega.
    * now intros ->%eps0_succ_eq_add_omega.
  + induction 1 as [ | | a' r' G1 G2 IG2 | b' G1 | a' b' r' G1 G2 G3 G4 IG4 ]; easy || auto.
    * intros H; symmetry in H; revert H.
      now intros ?%eps0_zero_neq_omega.
    * intros H; symmetry in H; revert H.
      now intros ->%eps0_one_eq_omega.
    * intros H; symmetry in H; revert H.
      now intros ->%eps0_succ_eq_omega.
    * intros <-%eps0_omega_inj; auto.
    * intros (-> & <-)%eps0_omega_eq_least_split; auto.
  + induction 1 as [ | | a' r' G1 G2 IG2 | b' G1 | a' b' r' G1 G2 G3 G4 IG4 ]; easy || auto.
    * intros H; symmetry in H; revert H.
      now intros ?%eps0_add_omega_not_zero.
    * intros H; symmetry in H; revert H.
      now intros (-> & ->)%eps0_one_eq_least_split.
    * intros H; symmetry in H; revert H.
      now intros ->%eps0_succ_eq_add_omega.
    * intros H; symmetry in H; revert H.
      intros (-> & ->)%eps0_omega_eq_least_split; auto.
      destruct (@eps0_lt_irrefl ω^b); eauto.
    * intros (<- & <-)%eps0_split_least_uniq; eauto.
Qed.

Theorem eps0_mult_omega_gr_fun γ e r s :
    eps0_mult_omega_gr γ e r
  → eps0_mult_omega_gr γ e s
  → r = s.
Proof.
  intros H1 H2; generalize (eq_refl e); revert H1 H2.
  apply eps0_mult_omega_gr_fun_rec.
Qed.

Definition eps0_mult_omega_pwc e γ : sig (eps0_mult_omega_gr γ e).
Proof.
  induction e as [ | e (r & Hr) | g e H1 H2 (r & Hr) _ ] using eps0_add_rect.
  + exists 0₀; constructor.
  + destruct (eps0_eq_dec e 0₀) as [ -> | He ].
    * exists ω^γ; rewrite eps0_succ_zero_is_one; constructor.
    * exists r; constructor; auto.
  + destruct (eps0_le_lt_dec ω^e g) as [ H | H ].
    * exists r; constructor; auto.
    * exists ω^(e+₀γ).
      assert (g = 0₀) as ->.
      - apply eps0_le_zero, H2.
        rewrite eps0_add_zero_left, eps0_add_lt_omega; auto.
      - rewrite eps0_add_zero_left; constructor; auto.
Qed.

Definition eps0_mult_omega e γ := proj1_sig (eps0_mult_omega_pwc e γ).

Fact eps0_mult_omega_spec e γ : eps0_mult_omega_gr γ e (eps0_mult_omega e γ).
Proof. apply (proj2_sig _). Qed.

Fact eps0_mult_omega_fix_0 γ : eps0_mult_omega 0₀ γ = 0₀.
Proof.
  intros.
  apply eps0_mult_omega_gr_fun with (1 := eps0_mult_omega_spec _ _); constructor; auto. 
Qed.

(* 1₀.ω^γ = ω^γ *)
Fact eps0_mult_omega_fix_1 γ : eps0_mult_omega 1₀ γ = ω^γ.
Proof. 
  intros.
  apply eps0_mult_omega_gr_fun with (1 := eps0_mult_omega_spec _ _); constructor; auto.
Qed.

(* (S₀ a).ω^γ = a.ω^γ if a ≠ 0₀ *)
Fact eps0_mult_omega_fix_2 e γ : e ≠ 0₀ → eps0_mult_omega (S₀ e) γ = eps0_mult_omega e γ.
Proof.
  intros.
  apply eps0_mult_omega_gr_fun with (1 := eps0_mult_omega_spec _ _).
  constructor; auto.
  apply eps0_mult_omega_spec.
Qed.

Fact eps0_mult_omega_fix_3 b g : b ≠ 0₀ → eps0_mult_omega ω^b g = ω^(b+₀g).
Proof.
  intros; apply eps0_mult_omega_gr_fun with (1 := eps0_mult_omega_spec _ _).
  constructor 4; auto.
Qed.

Fact eps0_mult_omega_fix_4 a b g :
  b ≠ 0₀ → ω^b ≤ε₀ a → eps0_least_split a b → eps0_mult_omega (a+₀ω^b) g = eps0_mult_omega a g.
Proof.
  intros Hb Ha Hab.
  apply eps0_mult_omega_gr_fun with (1 := eps0_mult_omega_spec _ _).
  constructor 5; auto.
  apply eps0_mult_omega_spec.
Qed.

Inductive eps0_momega_gr e : ε₀ → ε₀ → Prop :=
  | eps0_momega_gr_0 : eps0_momega_gr e 0₀ e
  | eps0_momega_gr_1 γ r : γ ≠ 0₀ → eps0_mult_omega_gr γ e r → eps0_momega_gr e γ r.
  
Fact eps0_momega_inv e γ r : γ ≠ 0₀ → eps0_momega_gr e γ r → eps0_mult_omega_gr γ e r.
Proof.
  intros H1 H2; revert H2 H1.
  induction 1; now auto.
Qed.

Local Lemma eps0_momega_gr_fun_rec e f g r s :
    eps0_momega_gr e f r
  → eps0_momega_gr e g s
  → f = g 
  → r = s.
Proof.
  induction 1 as [ | f r Hf H ]; induction 1 as [ | g s Hg G ]; auto.
  + now intros <-.
  + now intros ->.
  + intros <-; revert H G; apply eps0_mult_omega_gr_fun.
Qed.

Fact eps0_momega_gr_fun e f r s :
    eps0_momega_gr e f r
  → eps0_momega_gr e f s
  → r = s.
Proof. 
 intros H1 H2; generalize (eq_refl f); revert H1 H2.
 apply eps0_momega_gr_fun_rec.
Qed.

Definition eps0_momega_pwc e γ : sig (eps0_momega_gr e γ).
Proof.
  destruct (eps0_eq_dec γ 0₀) as [ -> | ].
  + exists e; constructor 1.
  + destruct (eps0_mult_omega_pwc e γ) as (r & Hr).
    exists r; now constructor.
Qed.

Definition eps0_momega e g := proj1_sig (eps0_momega_pwc e g).

Fact eps0_momega_spec e g : eps0_momega_gr e g (eps0_momega e g).
Proof. apply (proj2_sig _). Qed.

Fact eps0_momega_fix e γ : γ ≠ 0₀ → eps0_momega e γ = eps0_mult_omega e γ.
Proof.
  intro.
  apply eps0_momega_gr_fun with (1 := eps0_momega_spec _ _); auto.
  constructor 2; auto.
  apply eps0_mult_omega_spec.
Qed.

(** e.ω^0 = 1 *)
Fact eps0_momega_zero_right e : eps0_momega e 0₀ = e.
Proof. apply eps0_momega_gr_fun with (1 := eps0_momega_spec _ _); constructor. Qed.

(* 0₀.ω^γ = 0₀ *)
Fact eps0_momega_zero_left γ : γ ≠ 0₀ → eps0_momega 0₀ γ = 0₀.
Proof. intros; rewrite eps0_momega_fix, eps0_mult_omega_fix_0; auto. Qed.

(* 1₀.ω^γ = ω^γ *)
Fact eps0_momega_one_left γ : γ ≠ 0₀ → eps0_momega 1₀ γ = ω^γ.
Proof. intros; rewrite eps0_momega_fix, eps0_mult_omega_fix_1; auto. Qed.

(* (S₀ a).ω^γ = a.ω^γ if a ≠ 0₀ *)
Fact eps0_momega_succ_left e γ : e ≠ 0₀ → γ ≠ 0₀ → eps0_momega (S₀ e) γ = eps0_momega e γ.
Proof. intros; rewrite !eps0_momega_fix, eps0_mult_omega_fix_2; auto. Qed.

(* ω^e.ω^γ = ω^(e+₀γ) *)
Fact eps0_momega_omega_left e γ : e ≠ 0₀ → γ ≠ 0₀ → eps0_momega ω^e γ = ω^(e+₀γ).
Proof. intros; rewrite !eps0_momega_fix, eps0_mult_omega_fix_3; auto. Qed.

Fact eps0_momega_add_omega a e γ :
  e ≠ 0₀ → γ ≠ 0₀ → ω^e ≤ε₀ a → eps0_least_split a e → eps0_momega (a+₀ω^e) γ = eps0_momega a γ.
Proof. intros; rewrite !eps0_momega_fix, eps0_mult_omega_fix_4; auto. Qed.

Fact eps0_momega_assoc a f g : eps0_momega (eps0_momega a f) g = eps0_momega a (f+₀g).
Proof.
  destruct (eps0_eq_dec g 0₀) as [ -> | Hg ].
  1: now rewrite eps0_momega_zero_right, eps0_add_zero_right.
  destruct (eps0_eq_dec f 0₀) as [ -> | Hf ].
  1: now rewrite eps0_momega_zero_right, eps0_add_zero_left.
  induction a as [ | a | a b H1 H2 IH1 IH2 ] using eps0_add_rect.
  + rewrite !eps0_momega_zero_left; auto.
    now intros (-> & ->)%eps0_add_eq_zero.
  + destruct (eps0_eq_dec a 0₀) as [ -> | Ha ].
    * rewrite eps0_succ_zero_is_one, !eps0_momega_one_left, eps0_momega_omega_left; auto.
      now intros (-> & ->)%eps0_add_eq_zero.
    * rewrite !eps0_momega_succ_left; auto.
      now intros (-> & ->)%eps0_add_eq_zero.
  + destruct (eps0_le_lt_dec ω^b a).
    * rewrite !eps0_momega_add_omega; auto.
      now intros (-> & ->)%eps0_add_eq_zero.
    * rewrite eps0_add_lt_omega; auto.
      rewrite !eps0_momega_omega_left; auto.
      - now rewrite eps0_add_assoc.
      - now intros (-> & ->)%eps0_add_eq_zero.
      - now intros (-> & ->)%eps0_add_eq_zero.
Qed.

Fact eps0_momega_power e g : g ≠ 0₀ → e ≠ 0₀ → { f | eps0_momega e g = ω^f ∧ g ≤ε₀ f }.
Proof.
  intros Hg.
  induction e as [ | e | e b H1 H2 IH1 IH2 ] using eps0_add_rect.
  + now intros [].
  + intros _.
    destruct (eps0_eq_dec e 0₀) as [ -> | ].
    * rewrite eps0_succ_zero_is_one, eps0_momega_one_left; auto.
      exists g; split; auto.
    * destruct IHe as (f & []); auto.
      exists f; split; auto.
      rewrite eps0_momega_succ_left; auto.
  + intros H.
    destruct (eps0_le_lt_dec ω^b e).
    * rewrite !eps0_momega_add_omega; auto.
      apply IH1.
      intros ->.
      apply (@eps0_lt_irrefl ω^b); eauto.
    * rewrite eps0_add_lt_omega; auto.
      rewrite eps0_momega_omega_left; auto.
      exists (b+₀g); split; auto.
      rewrite <- (eps0_add_zero_left g) at 1.
      apply eps0_add_mono; auto.
Qed.

Fact eps0_momega_add e g : g ≠ 0₀ → e +₀ eps0_momega e g = eps0_momega e g.
Proof.
  intros Hg.
  induction e as [ | e | e b H1 H2 IH1 IH2 ] using eps0_add_rect.
  + now rewrite eps0_add_zero_left.
  + destruct (eps0_eq_dec e 0₀) as [ -> | He ].
    * rewrite eps0_succ_zero_is_one, eps0_momega_one_left; auto.
      apply eps0_add_lt_omega; auto.
      rewrite <- eps0_omega_zero.
      apply eps0_omega_mono_lt.
      destruct (eps0_zero_or_pos g); now subst.
    * rewrite eps0_momega_succ_left; auto.
      destruct (@eps0_momega_power e g) as (f & Hf1 & Hf2); auto.
      rewrite Hf1, <- eps0_add_one_right, eps0_add_assoc.
      rewrite eps0_add_lt_omega.
      - rewrite <- Hf1; auto.
      - contradict Hg; subst; auto.
      - rewrite <- eps0_omega_zero.
        apply eps0_omega_mono_lt.
        apply eps0_lt_le_trans with (2 := Hf2).
        destruct (eps0_zero_or_pos g); now subst.
  + destruct (eps0_le_lt_dec ω^b e).
    * rewrite !eps0_momega_add_omega; auto.
Admitted.

Inductive eps0_mult_gr α : ε₀ → ε₀ → Prop :=
  | eps0_mult_gr_0         : eps0_mult_gr α 0₀ 0₀
  | eps0_mult_gr_1 β r     : eps0_mult_gr α β r
                           → eps0_mult_gr α (S₀ β) (r+₀α)
  | eps0_mult_gr_2 β γ r s : γ ≠ 0₀
                           → eps0_least_split β γ
                           → eps0_mult_gr α β r
                           → eps0_momega_gr α γ s
                           → eps0_mult_gr α (β+₀ω^γ) (r+₀s)
  .

Local Lemma eps0_mult_gr_fun_rec α e f r s :
    eps0_mult_gr α e r
  → eps0_mult_gr α f s
  → e = f
  → r = s.
Proof.
  intros H1 H2; revert H1 f s H2.
  induction 1 as [ | b r H1 IH1 | b g r s H1 H2 H3 IH3 H4 ].
  + induction 1 as [ | b' r' G1 IG1 | b' g' r' s' G1 G2 G3 IG3 G4 ]; easy || auto.
    * now intros ?%eps0_zero_not_succ.
    * now intros ?%eps0_add_omega_not_zero.
  + induction 1 as [ | b' r' G1 IG1 | b' g' r' s' G1 G2 G3 IG3 G4 ]; easy || auto.
    * intros H; symmetry in H; revert H.
      now intros ?%eps0_zero_not_succ.
    * intros <-%eps0_succ_inj; f_equal; eauto.
    * now intros ->%eps0_succ_eq_add_omega.
  + induction 1 as [ | b' r' G1 IG1 | b' g' r' s' G1 G2 G3 IG3 G4 ]; easy || auto.
    * intros H; symmetry in H; revert H.
      now intros ?%eps0_add_omega_not_zero.
    * intros H; symmetry in H; revert H.
      now intros ->%eps0_succ_eq_add_omega.
    * intros (<- & <-)%eps0_split_least_uniq; auto.
      generalize (eps0_momega_gr_fun H4 G4); intros <-; f_equal; eauto.
Qed.

Theorem eps0_mult_gr_fun α e r s :
    eps0_mult_gr α e r
  → eps0_mult_gr α e s
  → r = s.
Proof.
  intros H1 H2; generalize (eq_refl e); revert H1 H2.
  apply eps0_mult_gr_fun_rec.
Qed.

Definition eps0_mult_pwc α e : sig (eps0_mult_gr α e).
Proof.
  induction e as [ | e (r & Hr) | g e H1 H2 (r & Hr) _ ] using eps0_add_rect.
  + exists 0₀; constructor.
  + exists (r+₀α); now constructor 2.
  + exists (r+₀eps0_momega α e).
    constructor 3; auto.
    apply eps0_momega_spec.
Qed.

Definition eps0_mult e f := proj1_sig (eps0_mult_pwc e f).

Notation "e '*₀' f" := (eps0_mult e f) (at level 30).

Fact eps0_mult_spec e f : eps0_mult_gr e f (e*₀f).
Proof. apply (proj2_sig _). Qed.

Fact eps0_mult_fix_0 e : e *₀ 0₀ = 0₀.
Proof.
  apply eps0_mult_gr_fun with (1 := eps0_mult_spec _ _).
  constructor.
Qed.

Fact eps0_mult_succ e f : e *₀ (S₀ f) = e *₀ f +₀ e.
Proof.
  apply eps0_mult_gr_fun with (1 := eps0_mult_spec _ _).
  constructor 2; apply eps0_mult_spec.
Qed.

(** e.(a+ω^g) = e.a + e.ω^g *)
Fact eps0_mult_fix_2 e a g : 
  g ≠ 0₀ → eps0_least_split a g → e *₀ (a +₀ ω^g) = e *₀ a +₀ eps0_momega e g.
Proof.
  intros H1 H2.
  apply eps0_mult_gr_fun with (1 := eps0_mult_spec _ _).
  constructor; auto.
  + apply eps0_mult_spec.
  + apply eps0_momega_spec.
Qed.

Fact eps0_mult_zero_left e : 0₀ *₀ e = 0₀.
Proof.
  induction e as [ | a IHa | a b H1 H2 IH1 IH2 ] using eps0_add_rect.
  + now rewrite eps0_mult_fix_0.
  + now rewrite eps0_mult_succ, IHa, eps0_add_zero_left.
  + rewrite eps0_mult_fix_2, IH1, eps0_momega_zero_left, eps0_add_zero_left; auto.
Qed.

Definition eps0_mult_zero_right := eps0_mult_fix_0.

Fact eps0_mult_one_left e : 1₀ *₀ e = e.
Proof.
  induction e as [ | a IHa | a b H1 H2 IH1 IH2 ] using eps0_add_rect.
  + now rewrite eps0_mult_zero_right.
  + now rewrite eps0_mult_succ, IHa, eps0_add_one_right.
  + rewrite eps0_mult_fix_2, IH1, eps0_momega_one_left; auto.
Qed.

Fact eps0_mult_one_right e : e *₀ 1₀ = e.
Proof. now rewrite <- eps0_succ_zero_is_one, eps0_mult_succ, eps0_mult_fix_0, eps0_add_zero_left. Qed.

(** This was the equation we wanted for eps0_momega !! *)
Fact eps0_mult_omega_eq a e : a *₀ ω^e = eps0_momega a e.
Proof.
  destruct (eps0_eq_dec e 0₀) as [ -> | H ].
  + now rewrite eps0_momega_zero_right, eps0_omega_zero, eps0_mult_one_right.
  + rewrite <- (eps0_add_zero_left ω^e), eps0_mult_fix_2, 
               eps0_mult_zero_right, eps0_add_zero_left; auto.
    red; auto.
Qed.

(** This one looks harder **)
Fact eps0_mult_add_omega e a g : e *₀ (a +₀ ω^g) = e *₀ a +₀ e *₀ ω^g.
Proof.
  destruct (eps0_eq_dec g 0₀) as [ -> | Hg ].
  1: now rewrite eps0_omega_zero, eps0_add_one_right, eps0_mult_succ, eps0_mult_one_right.
  induction a as [ | a IHc | a f H1 H2 IH1 IH2 ] using eps0_add_rect.
  + now rewrite eps0_mult_zero_right, !eps0_add_zero_left.
  + rewrite <- eps0_add_one_right at 1. 
    rewrite eps0_mult_succ, eps0_add_assoc.
    rewrite eps0_add_lt_omega; auto.
    2:{ rewrite <- eps0_omega_zero.
        apply eps0_omega_mono_lt; auto.
        destruct (eps0_zero_or_pos g) as [ -> | ]; now auto. }
    rewrite IHc,  eps0_add_assoc; f_equal.
    rewrite eps0_mult_omega_eq.
        Search (_ <> 0₀).
    Search (_ +₀ _^_).
     eps0_add_one_is_succ.
  
  destruct (@eps0_least_split_find (a+₀ω^g)) as (b & f & H1 & H2 & H3); eauto.
  1: now apply eps0_is_limit_add_omega.
  generalize H1; intros <-%eps0_add_omega_fun_right.
  symmetry in H1.
  generalize (H3 _ H1); intros H4.
  destruct (eps0_le_lt_dec ω^g b) as [ H5 | H5 ].
  + Check eps0_momega_add_omega.
  admit.
  + 
  rewrite H1, eps0_mult_fix_2; auto.
  rewrite <- eps0_mult_omega_eq.
  symmetry in H1.
  f_equal.
  
  generalize H1; intros H4%H3.
Admitted.

Fact eps0_mult_distr a b c : a *₀ (b +₀ c) = a *₀ b +₀ a *₀ c.
Proof.
  induction c as [ | c IHc | c e H1 H2 IH1 IH2 ] using eps0_add_rect.
  + now rewrite eps0_mult_zero_right, !eps0_add_zero_right.
  + now rewrite eps0_add_succ_right, !eps0_mult_succ, IHc, eps0_add_assoc.
  + now rewrite <- eps0_add_assoc, !eps0_mult_add_omega, IH1, eps0_add_assoc.
Qed.

Fact eps0_mult_assoc a b c : a *₀ (b *₀ c) = (a *₀ b) *₀ c.
Proof.
  induction c as [ | c IHc | c e H1 H2 IH1 IH2 ] using eps0_add_rect.
  + now rewrite !eps0_mult_zero_right.
  + now rewrite !eps0_mult_succ, eps0_mult_distr, IHc.
  + rewrite !eps0_mult_distr, IH1.
    f_equal.
    rewrite !eps0_mult_omega_eq.
  rewrite eps0_mult_fix_1.

(** Now we need to show the equations for multiplication 
    and exponentiation based on these specs *)

(** We build the fundemental sequence *)

Inductive eps0_fseq_gr : ε₀ → (nat → ε₀) → Prop :=
  | eps0_fseq_gr_0 g b   : eps0_least_split g (S₀ b)
                         → eps0_fseq_gr (g +₀ ω^(S₀ b)) (λ n, g +₀ eps0_exp_S b n)
  | eps0_fseq_gr_1 g b r : eps0_is_limit b
                         → eps0_least_split g b
                         → eps0_fseq_gr b r
                         → eps0_fseq_gr (g +₀ ω^b) (λ n, g +₀ ω^(r n)).

Local Lemma eps0_fseq_gr_fun_rec e se f sf :
  eps0_fseq_gr e se → eps0_fseq_gr f sf → e = f → ∀n, se n = sf n.
Proof.
  intros H; revert H f sf.
  induction 1 as [ g b Hs | g b r H0 Hs H1 IH1 ].
  + induction 1 as [ g' b' Hs' | g' b' r' H0' Hs' H2 IH2 ].
    * intros (<- & <-%eps0_succ_inj)%eps0_split_least_uniq; auto.
    * intros <-%eps0_add_omega_fun_right; eauto.
      destruct H0' as (_ & []); eauto.
  + induction 1 as [ g' b' Hs' | g' b' r' H0' Hs' H2 IH2 ].
    * intros ->%eps0_add_omega_fun_right; eauto.
      destruct H0 as (_ & []); eauto.
    * intros (<- & <-)%eps0_split_least_uniq; auto.
      intro; now rewrite IH1 with (1 := H2).
Qed.

Hint Resolve eps0_is_limit_exp_S eps0_is_limit_omega 
             eps0_add_is_limit : core.

Lemma eps0_fseq_gr_fun e r r' : eps0_fseq_gr e r → eps0_fseq_gr e r' → ∀n, r n = r' n.
Proof. intros H1 H2; now apply (eps0_fseq_gr_fun_rec H1 H2). Qed.

(** By WF induction, we build the fundemental sequence of a limit
    ordinal, packed with conformity (pwc) as spec'd with eps0_fseq_gr *)
Theorem eps0_fseq_pwc e : eps0_is_limit e → sig (eps0_fseq_gr e).
Proof.
  destruct e as [ | e | g e H1 H2 _ _ ]
    using eps0_add_rect.
  + now intros [ [] _ ].
  + intros [ _ [] ]; eauto.
  + intros _.
    induction e as [ | e | h e H3 H4 _ IH ]
      in H1, g, H2 |- *
      using eps0_add_rect.
    * now destruct H1.
    * exists (λ n, g +₀ eps0_exp_S e n); now constructor.
    * destruct (IH h) as (lam & Hlam); auto.
      exists (λ n, g +₀ ω^(lam n)).
      constructor; auto.
Qed.

Definition eps0_fseq {e} (l : eps0_is_limit e) := π₁ (@eps0_fseq_pwc e l).

Fact eps0_fseq_spec e l : eps0_fseq_gr e (@eps0_fseq e l).
Proof. apply (proj2_sig _). Qed.

(** The fundemental sequence is monotonic *)
Fact eps0_fseq_mono e l : ∀ n m, n < m → @eps0_fseq e l n <ε₀ eps0_fseq l m.
Proof.
  generalize (eps0_fseq l) (eps0_fseq_spec l); clear l.
  induction 1; intros.
  + apply eps0_add_mono_right; auto.
    destruct b; simpl.
    constructor; constructor 2; right; lia.
  + apply eps0_add_mono_right; auto.
    apply eps0_omega_mono_lt; auto.
Qed.

Lemma eps0_lt_omega_inv : ∀ f b, f <ε₀ ω^b → f = 0₀ ∨ ∃ a n, f <ε₀ eps0_exp_S a n ∧ a <ε₀ b.
Proof.
  intros [f Hf] [b Hb] H%E0_lt_omega_inv; simpl in H; auto.
  destruct H as [ -> | ([|n] & a & ? & ? & ? & Ha) ].
  + left; now apply eps0_eq_iff.
  + lia.
  + right; exists (exist _ a Ha), n; auto.
Qed.

Fact eps0_max u v b : u <ε₀ b → v <ε₀ b → { w | u ≤ε₀ w ∧ v ≤ε₀ w ∧ w <ε₀ b }.
Proof. intros ? ?; destruct (eps0_le_lt_dec u v); eauto. Qed.

(** Notice that this does not work for e,f <ε₀ ω^b.n where n > 1
   eg ω < ω.2 and ω+1 < ω.2 but ω+(ω+1) = ω.2+1 is not < ω.2 *)
Lemma eps0_add_lt_omega_both e f b : e <ε₀ ω^b → f <ε₀ ω^b → e +₀ f <ε₀ ω^b.
Proof.
  intros [ -> | (u & i & H1 & H2) ]%eps0_lt_omega_inv.
  1: now rewrite eps0_add_zero_left.
  intros [ -> | (v & j & H3 & H4) ]%eps0_lt_omega_inv.
  1:{ rewrite eps0_add_zero_right.
      now apply eps0_lt_trans with (1 := H1), eps0_exp_S_mono_left. }
  destruct (@eps0_max u v b) as (m & G1 & G2 & G3); auto.
  apply eps0_le_lt_trans with (eps0_exp_S m i +₀ eps0_exp_S m j).
  + apply eps0_add_mono.
    * left; apply eps0_lt_le_trans with (1 := H1).
      destruct G1 as [ | <- ]; [ left | right ]; auto.
      now apply eps0_exp_S_mono_left.
    * left; apply eps0_lt_le_trans with (1 := H3).
      destruct G2 as [ | <- ]; [ left | right ]; auto.
      now apply eps0_exp_S_mono_left.
  + rewrite eps0_add_exp_S.
    now apply eps0_exp_S_mono_left.
Qed. 

(** the previous one specialized for _ < ω^{b+1} *)
Lemma eps0_lt_omega_succ_inv f b : f <ε₀ ω^(S₀ b) → ∃n, f <ε₀ eps0_exp_S b n.
Proof.
  intros [ -> | (a & n & H1 & H2) ]%eps0_lt_omega_inv.
  + exists 0.
    apply eps0_le_lt_trans with (2 := eps0_lt_exp_S _ _); auto.
  + exists n.
    apply eps0_lt_le_trans with (1 := H1).
    destruct (eps0_lt_sdec a b) as [ a b H | a | a b H ].
    * left; apply eps0_exp_S_mono_left; auto.
    * right; auto.
    * destruct (@eps0_lt_irrefl a).
      apply eps0_lt_le_trans with (1 := H2).
      now apply eps0_succ_next.
Qed.

  (** Another inversion lemma, but this time
      for the limit of the fundemental sequence

      This is inversion of _ < e when e is a limit ordinal,
      w.r.t. the fundemental sequence of e 

      This has become a nice proof *)
Theorem eps0_lt_fseq_inv e l f : f <ε₀ e → ∃n, f <ε₀ @eps0_fseq e l n.
Proof.
  (* We capture the fundemental sequence via its inductive spec *)
  revert f; generalize (eps0_fseq l) (eps0_fseq_spec l).
  clear l.
  induction 1 as [ e b Hs | e b r Hr H0 Hs IH ]; intros f H.
  + (* e is _ + ω^{b+1} *)
    apply eps0_lt_add_inv_add in H as [ H | (g & -> & H) ]; auto.
    * exists 0.
      apply eps0_lt_trans with (1 := H).
      apply eps0_add_incr; auto.
      apply eps0_lt_zero_exp_S.
    * apply eps0_lt_omega_succ_inv in H as (n & Hn).
      exists n.
      apply eps0_add_mono_right; auto.
  + apply eps0_lt_add_inv_add in H as [ H | (g & -> & H) ]; auto.
    * exists 0.
      apply eps0_lt_trans with (1 := H).
      apply eps0_add_incr, eps0_lt_zero_exp_S.
    * apply eps0_lt_omega_inv in H as [ -> | (a & n & Ha & H) ].
      - exists 0.
        apply eps0_add_mono_right, eps0_lt_zero_exp_S.
      - apply IH in H as (i & Hi).
        exists i.
        apply eps0_add_mono_right.
        apply eps0_lt_trans with (1 := Ha).
        now apply eps0_exp_S_mono_left.
Qed.  

(** The fundemental sequence is lesser than its limit *)
Theorem eps0_fseq_lt e l n : @eps0_fseq e l n <ε₀ e.
Proof.
  generalize (eps0_fseq l) (eps0_fseq_spec l) n; clear n l.
  induction 1 as [ | g b r Hr IH ].
  + intros; apply eps0_add_mono_right; eauto.
    apply eps0_exp_S_mono_left, eps0_lt_succ.
  + intros; apply eps0_add_mono_right, eps0_exp_S_mono_left; auto.
Qed.

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

  Hypothesis (R_refl : reflexive _ R)
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

(* for a limit ordinal e, it is the ≤ε₀-lub of its fundemental sequence *) 
Theorem eps0_fseq_lub e l : lub eps0_le (λ x, ∃n, x = @eps0_fseq e l n) e.
Proof.
  split.
  + intros x (n & ->); left; apply eps0_fseq_lt.
  + intros u Hu.
    destruct (eps0_lt_sdec u e) as [ x e H | | ].
    2,3: red; auto.
    apply eps0_lt_fseq_inv with (l := l) in H as (n & Hn); auto.
    exfalso.
    apply (@eps0_lt_irrefl x).
    apply eps0_lt_le_trans with (1 := Hn); eauto.
Qed.

(* A limit ordinal is the ≤ε₀-lub of <ε₀-smaller ordinals.
   This is also the case of 0₀. But of course, this is not
   the case for successor ordinals *)
Theorem eps0_is_limit_lub e : eps0_is_limit e → lub eps0_le (λ x, x <ε₀ e) e.
Proof.
  intros l; split.
  + now left.
  + intros v Hv.
    destruct (eps0_le_lt_dec e v) as [ | C ]; auto; exfalso.
    apply eps0_lt_fseq_inv with (l := l) in C as (n & Hn).
    apply (@eps0_lt_irrefl v).
    apply eps0_lt_le_trans with (1 := Hn), Hv.
    apply eps0_fseq_lt.
Qed.

(* For a successor ordinal S₀ e, the lub of its <ε₀-smaller ordinals
   is e (and not S₀ e). *)
Theorem eps0_is_succ_lub e : lub eps0_le (λ x, x <ε₀ S₀ e) e.
Proof.
  split.
  + now intros ? ?%eps0_succ_next_inv.
  + intros v Hv; apply Hv, eps0_lt_succ.
Qed.

(** Addition respects the limit *)
Theorem eps0_add_lub e u :
    eps0_is_limit u
  → lub eps0_le (λ x, ∃v, x = e +₀ v ∧ v <ε₀ u) (e +₀ u).
Proof.
  intros l.
  split.
  + intros ? (v & -> & Hv).
    left; now apply eps0_add_mono_right.
  + intros v Hv.
    red in Hv.
    destruct (eps0_le_lt_dec (e +₀ u) v) as [ |H1]; auto; exfalso.
    apply eps0_lt_add_inv_add in H1 as [ H1 | (g & -> & Hg) ].
    * apply (@eps0_lt_irrefl v).
      apply eps0_lt_le_trans with (1 := H1), Hv.
      exists 0₀; split.
      - now rewrite eps0_add_zero_right.
      - destruct (eps0_zero_or_pos u) as [ C%l | ]; now auto.
    * apply eps0_lt_fseq_inv with (l := l) in Hg as (n & Hn).
      destruct (@eps0_lt_irrefl g).
      apply eps0_lt_le_trans with (1 := Hn).
      apply eps0_add_le_cancel with e, Hv.
      exists (eps0_fseq l n); split; auto.
      apply eps0_fseq_lt.
Qed.

(** Construction of the Grzegorczyk Fast Growing Hierarchy 

    F 0₀ n      := S n             for 0₀
    F (S₀ e) n  := (F e)^{S n} n   for a successor ordinal
    F λ n       := F λ[n] n        for a limit ordinal, using the fund. seq. λ[_]

    We specify it as a relation between ε₀ and nat → nat

*)

Inductive fgh_gr : ε₀ → (nat → nat) → Prop :=
  | fgh_gr_0       : fgh_gr 0₀ S
  | fgh_gr_1 e F   : fgh_gr e F
                   → fgh_gr (S₀ e) (λ n, iter F (S n) n)
  | fgh_gr_2 e l F : (∀n, fgh_gr (@eps0_fseq e l n) (F n))
                   → fgh_gr e (λ n, F n n).

Lemma fgh_gr_fun e E f F : fgh_gr e E → fgh_gr f F → e = f → ∀n, E n = F n.
Proof.
  intros H; revert H f F.
  induction 1 as [ | e E H1 IH1 | e l E H1 IH1 ].
  + induction 1 as [ | f F H2 IH2 | f m F H2 IH2 ]; auto.
    * intros C; exfalso; revert C; apply eps0_zero_not_succ.
    * intros <-; destruct m as [ [] _ ]; auto.
  + induction 1 as [ | f F H2 _ | f m F H2 _ ].
    * intros C; symmetry in C; exfalso; revert C; apply eps0_zero_not_succ.
    * intros ?%eps0_succ_inj ?.
      apply iter_ext; eauto.
    * intros <-; destruct m as [ ? [] ]; auto.
  + induction 1 as [ | f F H2 _ | f m F H2 _ ].
    * intros ->; destruct l as [ [] _ ]; auto.
    * intros ->; destruct l as [ ? [] ]; auto.
    * intros <- n; eapply IH1; eauto.
      apply (@eps0_fseq_gr_fun e); apply eps0_fseq_spec.
Qed.

#[local] Hint Resolve eps0_lt_succ : core.

(** This is the Grzegorczyk hierarchy *)
Definition fg_hierarchy e : { F | fgh_gr e F }.
Proof.
  induction e as [ e IH ] using (well_founded_induction_type wf_eps0_lt).
  destruct (eps0_choose e) as [ | e | e l ].
  + exists S; constructor.
  + destruct (IH e) as (F & ?); auto.
    exists (λ n, iter F (S n) n).
    now constructor.
  + set (F i := π₁ (IH (eps0_fseq l i) (eps0_fseq_lt _ _))).
    exists (λ n, F n n).
    constructor 3 with l.
    intro; apply (proj2_sig (IH (eps0_fseq l n) (eps0_fseq_lt _ _))).
Qed.

(* The hierarchy is uniquely characterized, up to extensionality 
   provided the fundemental sequence is uniquely characterized 
   as well !! *)

Definition F e := π₁ (fg_hierarchy e). 

Fact F_spec e : fgh_gr e (F e).
Proof. apply (proj2_sig _). Qed.

(** We establish the defining equations using the spec *)

Theorem F_fix_zero n : F 0₀ n = S n.
Proof.
  apply fgh_gr_fun with (1 := F_spec _) (3 := eq_refl).
  constructor.
Qed.

Theorem F_fix_succ e n : F (S₀ e) n = iter (F e) (S n) n.
Proof.
  change (F (S₀ e) n = (fun n => iter (F e) (S n) n) n).
  apply fgh_gr_fun with (1 := F_spec _) (3 := eq_refl).
  constructor; apply F_spec.
Qed.

Theorem F_fix_limit e l n : F e n = F (@eps0_fseq e l n) n.
Proof.
  change (F e n = (λ n, F (@eps0_fseq e l n) n) n).
  apply fgh_gr_fun with (1 := F_spec _) (3 := eq_refl).
  constructor 3 with l.
  intro; apply F_spec.
Qed.

Definition is_lub {X} (R : X → X → Prop) (P : X → Prop) u := ∀v, (∀x, P x → R x v) ↔ R u v.

(* for a limit ordinal e, it is the ≤ε₀-lub of its fundemental sequence *) 
Theorem eps0_fseq_is_lub e l : is_lub eps0_le (λ x, ∃n, x = @eps0_fseq e l n) e.
Proof.
  intros x; split.
  + intros Hx.
    destruct (eps0_lt_sdec x e) as [ x e H | | ].
    2,3: red; auto.
    apply eps0_lt_fseq_inv with (l := l) in H as (n & Hn); auto.
    exfalso.
    apply (@eps0_lt_irrefl x).
    apply eps0_lt_le_trans with (1 := Hn), Hx; eauto.
  + intros H y (n & ->); left.
    apply eps0_lt_le_trans with (2 := H), eps0_fseq_lt.
Qed.
