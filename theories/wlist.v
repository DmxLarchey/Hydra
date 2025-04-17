(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Utf8.
From Hydra Require Import utils pos ordered lex_list.

Import ListNotations.

Set Implicit Arguments.

#[local] Infix "∈" := In (at level 70, no associativity).
#[local] Hint Resolve transitive_rev : core.
#[local] Hint Resolve in_cons in_eq in_elt in_or_app : core.

Section wlist_add.

  Variables (X : Type) (R : X → X → Prop)
            (R_sdec : ∀ x y, sdec R x y)
            (R_irrefl : ∀x, ¬ R x x)
            (R_trans : transitive R).

  Implicit Type (l m : list (X*pos)).

  Fixpoint wlist_cut m y j :=
    match m with
    | []       => [(y,j)]
    | (x,i)::m =>
      match R_sdec x y with
      | sdec_lt _ _ _ _ => [(y,j)]
      | sdec_eq _ _     => [(x,i +ₚ j)]
      | sdec_gt _ _ _ _ => (x,i)::wlist_cut m y j
      end
    end.

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
    destruct sdec_gt_inv with (s := R_sdec x y); auto.
    f_equal; auto.
  Qed.

  Fact wlist_cut_gt x i r y j :
      R y x
    → wlist_cut ((x,i)::r) y j = (x,i)::wlist_cut r y j.
  Proof.
    intro; apply wlist_cut_gt_list with (l := [_]).
    constructor; auto.
  Qed.

  Fact wlist_cut_eq i r y j : wlist_cut ((y,i)::r) y j = [(y,i +ₚ j)].
  Proof. simpl; destruct sdec_eq_inv with (s := R_sdec y y); auto. Qed.

  Fact wlist_cut_lt x i r y j : R x y → wlist_cut ((x,i)::r) y j = [(y,j)].
  Proof. simpl; intro; destruct sdec_lt_inv with (s := R_sdec x y); auto. Qed.

  Fact wlist_cut_spec2 l y i r j :
      Forall (λ x, R y (fst x)) l
    → wlist_cut (l++[(y,i)]++r) y j = l++[(y,i +ₚ j)].
  Proof.
    induction 1 as [ | (x,k) m H1 H2 IH2 ]; simpl; auto.
    + destruct sdec_eq_inv with (s := R_sdec y y); auto.
    + destruct sdec_gt_inv with (s := R_sdec x y); auto.
      simpl in IH2; rewrite IH2; auto.
  Qed.

  Fact wlist_cut_spec3 l x y i r j :
      Forall (λ x, R y (fst x)) l
    → R x y 
    → wlist_cut (l++[(x,i)]++r) y j = l++[(y,j)].
  Proof.
    intros H1 Hxy; revert H1.
    induction 1 as [ | (u,k) m H1 H2 IH2 ]; simpl; auto.
    + destruct sdec_lt_inv with (s := R_sdec x y); auto.
    + destruct sdec_gt_inv with (s := R_sdec u y); auto.
      simpl in IH2; rewrite IH2; auto.
  Qed.

  Fact wlist_cut_last l y j : ∃m k, j ≤ k ∧ wlist_cut l y j = m++[(y,k)].
  Proof.
    induction l as [ | (x,i) l (m & k & Hk & Hw) ]; simpl.
    + exists [], j; auto.
    + destruct (R_sdec x y) as [ x y H | x | x y H ].
      * exists [], j; auto.
      * exists [], (i +ₚ j); split; auto.
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

  Definition wlist_add l m :=
    match m with
    | []       => l
    | (y,j)::m => wlist_cut l y j ++ m
    end.

  Fact wlist_add_cons_right l y j m :
      wlist_add l ((y,j)::m)
    = wlist_cut l y j ++ m.
  Proof. trivial. Qed. 

  Fact wlist_add_nil_right l : wlist_add l [] = l.
  Proof. trivial. Qed.

  Fact wlist_add_nil_left m : wlist_add [] m = m.
  Proof. destruct m as [ | [] ]; simpl; auto. Qed.

  Fact wlist_add_gt_list l r y j m :
      Forall (λ x, R y (fst x)) l
    → wlist_add (l++r) ((y,j)::m)
    = l++wlist_add r ((y,j)::m).
  Proof.
    simpl; intros.
    rewrite wlist_cut_gt_list; auto.
    now rewrite app_assoc.
  Qed.

  Fact wlist_add_gt x i r y j m :
      R y x
    → wlist_add ((x,i)::r) ((y,j)::m)
    = (x,i)::wlist_add r ((y,j)::m).
  Proof.
    intros.
    apply wlist_add_gt_list with (l := [_]).
    constructor; auto.
  Qed.

  Fact wlist_add_eq i r y j m :
      wlist_add ((y,i)::r) ((y,j)::m)
   = (y,i +ₚ j)::m.
  Proof.
    unfold wlist_add.
    now rewrite wlist_cut_eq.
  Qed.

  Fact wlist_add_lt x i r y j m :
      R x y
    → wlist_add ((x,i)::r) ((y,j)::m)
    = (y,j)::m.
  Proof.
    unfold wlist_add; intro.
    now rewrite wlist_cut_lt.
  Qed.

  Fact wlist_add_spec_1 l y j m :
      Forall (λ x, R y (fst x)) l
    → wlist_add l ((y,j)::m)
    = l++(y,j)::m.
  Proof.
    intros H.
    rewrite <- (app_nil_r l) at 1.
    now rewrite wlist_add_gt_list.
  Qed.

  Fact wlist_add_spec_2 l y i r j m :
      Forall (λ x, R y (fst x)) l
    → wlist_add (l++[(y,i)]++r) ((y,j)::m)
    = l++[(y,i +ₚ j)]++m.
  Proof.
    intros H.
    simpl app at 2.
    rewrite wlist_add_gt_list, wlist_add_eq; auto.
  Qed.

  Fact wlist_add_spec_3 l x i r y j m :
      Forall (λ x, R y (fst x)) l
    → R x y
    → wlist_add (l++[(x,i)]++r) ((y,j)::m)
    = l++[(y,j)]++m.
  Proof.
    intros H1 H2; simpl app at 2.
    rewrite wlist_add_gt_list, wlist_add_lt; auto.
  Qed.
  
  Fact wlist_add_common l y : ∃ l' i, ∀ j m, wlist_add l ((y,j)::m) = l'++(y,i + j)::m.
  Proof.
    simpl.
    induction l as [ | (x,i) l (l' & k & Hl') ]; simpl.
    + exists [], 0; auto.
    + destruct (R_sdec x y) as [ x y H | y | x y H ].
      * exists [], 0; auto.
      * exists [], (1+i); auto.
      * exists ((x,i)::l'), k.
        intros; simpl; f_equal; auto.
  Qed. 

  Fact wlist_add_choice x i l y j m :
    ∃ z k r, wlist_add ((x,i)::l) ((y,j)::m) = (z,k)::r
           ∧ ( R x y ∧ z = y ∧ k = j ∧ r = m
             ∨ x = y ∧ z = x ∧ k = i +ₚ j ∧ r = m
             ∨ R y x ∧ z = x ∧ k = i ∧ r = wlist_add l ((y,j)::m) ).
  Proof.
    destruct (R_sdec x y) as [ x y H | x | x y H ].
    + rewrite wlist_add_lt; auto.
      exists y, j, m; split; auto.
    + rewrite wlist_add_eq.
      exists x, (i +ₚ j), m; split; auto; right; auto.
    + rewrite wlist_add_gt; auto.
      exists x, i, (wlist_add l ((y,j)::m)); split; auto; do 2 right; auto.
  Qed.

  Fact in_wlist_add l m x i : (x,i) ∈ wlist_add l m → ∃j, j ≤ i ∧ ((x,j) ∈ l ∨ (x,j) ∈ m).
  Proof.
    destruct m as [ | (y,j) m ].
    + rewrite wlist_add_nil_right.
      exists i; auto.
    + destruct (wlist_cut_choice l y)
        as [ H 
         | [ (k & a & b & -> & H1)
           | (z & k & a & b & -> & H1 & H2)
           ] ].
      * rewrite wlist_add_spec_1; auto.
        intros []%in_app_iff; eauto.
      * simpl app at 2.
        rewrite wlist_add_gt_list, wlist_add_eq; auto.
        intros [H|[[=]|H]]%in_app_iff; subst; eauto.
        exists i; rewrite in_app_iff; auto.
      * simpl app at 2. 
        rewrite wlist_add_gt_list, wlist_add_lt; auto. 
        intros []%in_app_iff; eauto.
        exists i; rewrite in_app_iff; eauto.
  Qed.

  Fact wlist_add_last l m y j :
    ∃ r (k : pos), j ≤ k ∧ wlist_add l (m++[(y,j)]) = r++[(y,k)].
  Proof.
    destruct m as [ | (z,p) m ]; simpl.
    + destruct (wlist_cut_last l y j) as (r & k & ? & E).
      exists r, k; split; auto; now rewrite app_nil_r.
    + exists (wlist_cut l z p ++ m), j; split; auto.
      now rewrite app_assoc.
  Qed.

  Fact wlist_add_middle_lt l x i r y j m :
    R x y → wlist_add (l++(x,i)::r) ((y,j)::m) = wlist_add l ((y,j)::m).
  Proof.
    intros Hxy; simpl.
    induction l as [ | (z,p) l IHl ]; simpl.
    + destruct (R_sdec x y) as [ x y H | x | x y H ]; auto.
      * now apply R_irrefl in Hxy.
      * destruct (@R_irrefl x); eauto.
    + destruct (R_sdec z y); simpl; f_equal; auto.
  Qed.

  Fact wlist_add_ordered l m :
      ordered R⁻¹ (map fst l)
    → ordered R⁻¹ (map fst m)
    → ordered R⁻¹ (map fst (wlist_add l m)).
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

  Fact wlist_add_assoc l m k :
      wlist_add (wlist_add l m) k 
    = wlist_add l (wlist_add m k).
  Proof.
    destruct m as [ | (y,j) m ].
    1: simpl; now rewrite wlist_add_nil_left.
    destruct k as [ | (z,p) k ].
    1: simpl; auto.
    destruct (wlist_cut_choice l y)
      as [ G1 
       | [ (i' & l' & r' & -> & G1) 
       |   (x' & i' & l' & r' & -> & G1 & G2) ] ].
    + rewrite wlist_add_spec_1 with (1 := G1).
      destruct (R_sdec y z) as [ y z F | y | y z F ].
      * rewrite wlist_add_lt, wlist_add_middle_lt; auto.
      * rewrite wlist_add_gt_list, !wlist_add_eq, wlist_add_spec_1; auto.
      * rewrite wlist_add_gt, wlist_add_gt_list; auto.
        2: revert G1; apply Forall_impl; eauto.
        rewrite wlist_add_gt, wlist_add_spec_1 with (1 := G1); auto.
    + rewrite wlist_add_gt_list with (1 := G1). auto.
      simpl app at 2; rewrite wlist_add_eq; auto.
      destruct (R_sdec y z) as [ y z F | y | y z F ]; simpl app.
      * rewrite wlist_add_lt, !wlist_add_middle_lt; auto.
      * rewrite wlist_add_eq, !wlist_add_gt_list, !wlist_add_eq; auto.
        now rewrite pos_add_assoc.
      * rewrite wlist_add_gt, wlist_add_gt_list,
                wlist_add_gt_list, wlist_add_eq,
                wlist_add_gt; auto.
        revert G1; apply Forall_impl; eauto.
    + rewrite wlist_add_gt_list; auto.
      simpl app at 2.
      rewrite wlist_add_lt; auto.
      destruct (R_sdec y z) as [ y z F | y | y z F ]; simpl app.
      * rewrite wlist_add_lt, !wlist_add_middle_lt; eauto.
      * rewrite wlist_add_gt_list, !wlist_add_eq,
                wlist_add_gt_list, wlist_add_lt; auto.
      * rewrite wlist_add_gt, wlist_add_middle_lt with (y := y),
                wlist_add_gt_list, wlist_add_gt,
                wlist_add_spec_1 with (1 := G1); auto.
        revert G1; apply Forall_impl; eauto.
  Qed.
  
  Fact wlist_add_eq_snoc_inv m x i l y j:
      wlist_add m [(x,i)] = l++[(y,j)]
    → ∃r, m = l++r
        ∧ x = y
        ∧ Forall (λ x, R y (fst x)) l
        ∧ (i = j ∨ ∃ p r', p +ₚ i = j ∧ r = (x,p)::r').
  Proof.
    destruct (wlist_cut_choice m x)
      as [ G1 
       | [ (i' & l' & r' & -> & G1) 
       |   (x' & i' & l' & r' & -> & G1 & G2) ] ].
    + rewrite wlist_add_spec_1; auto.
      intros (<- & [=])%app_inj_tail; subst.
      exists []; repeat split; auto.
      now rewrite app_nil_r.
    + rewrite wlist_add_spec_2, app_nil_r; auto.
      intros (<- & [=])%app_inj_tail; subst.
      exists ((y,i')::r'); repeat split; auto.
      right; exists i', r'; auto.
    + rewrite wlist_add_spec_3, app_nil_r; auto.
      intros (<- & [=])%app_inj_tail; subst.
      exists ((x',i')::r'); repeat split; auto.
  Qed.

End wlist_add.

Arguments wlist_cut {_ _}.
Arguments wlist_add {_ _}.

Opaque wlist_add.
