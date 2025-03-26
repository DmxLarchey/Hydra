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

  Local Fact R_sdec_refl x y : 
      x = y
    → match R_sdec x y with
      | sdec_lt _ _ _ _ => False
      | sdec_eq _ _     => True
      | sdec_gt _ _ _ _ => False
      end.
  Proof. intros; destruct (R_sdec x y); auto; subst; eapply R_irrefl; eauto. Qed.

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

  Fact wlist_combine_ordered l m : ordered R⁻¹ (map fst l) → ordered R⁻¹ (map fst m) → ordered R⁻¹ (map fst (wlist_combine l m)).
  Proof.
    destruct m as [ | (y,j) m ]; simpl; auto.
    intros Hl Hm%ordered_inv.
    rewrite map_app.
    apply wlist_cut_ordered with (y := y) (j := j) in Hl.
    generalize (wlist_cut_ub l y j); intros H.
    apply ordered_from_app_middle with y; eauto.
    + now apply transitive_rev.
    + intros ? ((x,i) & <- & ?)%in_map_iff; simpl; eauto.
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

Definition E0_zero := ω[[]].

Fact E0_zero_lt e : E0_zero = e ∨ E0_zero <E₀ e.
Proof.
  destruct e as [ [] ]; [ left | right ]; eauto.
  repeat constructor.
Qed.

Definition E0_le e f := e <E₀ f ∨ e = f.

Notation "e '≤E₀' f" := (E0_le e f) (at level 70, format "e  ≤E₀  f").

Fact E0_zero_not_gt e : ¬ e <E₀ E0_zero.
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

Fact cnf_zero : cnf ω[nil].
Proof.
  apply cnf_fix; simpl; split.
  + constructor.
  + tauto.
Qed.

#[local] Hint Resolve cnf_zero : core.

Definition E0_one := ω[[(E0_zero, 1)]].

Fact cnf_one : cnf E0_one.
Proof.
  apply cnf_fix; simpl; split.
  + repeat constructor.
  + intros e i [ [=] | [] ]; subst; split; auto; lia.
Qed.

#[local] Hint Resolve cnf_one : core.

Fact E0_one_ge r : r ≠ [] → cnf ω[r] → E0_one ≤E₀ ω[r].
Proof.
  destruct r as [ | (x,i) r ]; [ easy | intros _ Hr ].
  destruct (E0_zero_lt x) as [ <- | Hx ].
  + destruct i as [ | [ | i ] ].
    * apply cnf_fix, proj2 in Hr.
      destruct (Hr E0_zero 0); auto; lia.
    * apply E0_le_app_head with (l := [_]).
      destruct r.
      - now right.
      - left; constructor; constructor 1.
    * left; constructor; constructor; right; lia.
  + left; constructor; constructor; now left.
Qed.

Inductive E0_succ_graph : E0 → E0 → Prop :=
  | E0_succ_graph0   : E0_succ_graph ω[[]] ω[[(ω[[]],1)]]
  | E0_succ_graph1 l i : E0_succ_graph ω[l++[(ω[[]],i)]] ω[l++[(ω[[]],S i)]] 
  | E0_succ_graph2 l x i : x ≠ E0_zero → E0_succ_graph ω[l++[(x,i)]] ω[l++[(x,i);(ω[[]],1)]].

(* Inversion lemma for the graph of E0_succ *)
Lemma E0_succ_graph_inv e f :
    E0_succ_graph e f
  → (e = ω[[]] → f = ω[[(ω[[]],1)]])
  ∧ (∀ l i, e = ω[l++[(ω[[]],i)]] → f = ω[l++[(ω[[]],S i)]])
  ∧ (∀ l x i, x ≠ E0_zero → e = ω[l++[(x,i)]] → f = ω[l++[(x,i);(ω[[]],1)]]).
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

Definition E0_add e f :=
  match e, f with
  | ω[l], ω[m] => ω[wlist_combine E0_lt_sdec l m]
  end.

Fact E0_add_correct : ∀ e f, cnf e → cnf f → cnf (E0_add e f).
Proof.
  intros [l] [m] (H1 & H2)%cnf_fix (H3 & H4)%cnf_fix; apply cnf_fix.
  split.
  + apply wlist_combine_ordered; auto.
  + intros ? ? (? & ? & [[]%H2|[]%H4])%wlist_combine_in;
      split; auto; lia.
Qed.

Fact E0_add_zero : ∀ e, E0_add e E0_zero = e.
Proof. intros []; simpl; auto. Qed.

Fact E0_add_one e : cnf e → E0_add e E0_one = E0_succ e.
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

(* Proof that if cnf u then
   either u is E0_zero                             (limit ordinal)
      or  u is ω[l++[(E0_zero,i)]])                (successor)
      or  u is ω[l++[(e,i)]]) with  E0_zero <E₀ e  (limit ordinal) *)

Fact E0_add_mono u v e : cnf u → cnf v → cnf e → u ≤E₀ v → E0_add u e ≤E₀ E0_add v e.
Proof.
  intros Hu Hv He [ H | -> ]; [ | right ]; auto.
  revert u v e Hu Hv He H.
  intros [l] [m] [[|(z,h) k]] Hl Hm Hk.
  1: rewrite !E0_add_zero; left; auto.
  intros H; revert H Hl Hm.
  intros [ q p | p (x,i) (y,j) l' m' H ]%E0_lt_inv%lex_list_invert Hp Hq; clear l m.
  + unfold E0_add.
    destruct (wlist_cut_choice E0_lt_sdec (p++q) z)
      as [ G1 
       | [ (i & l & r & E & G1) 
       |   (x & i & l & r & E & G1) ] ].
    * rewrite wlist_combine_spec1 with (l := _++_); auto.
      apply Forall_app in G1 as [ G1 G2 ].
      rewrite  wlist_combine_spec1; auto.
      left; constructor; rewrite <- app_assoc.
      apply lex_list_app_head.
      destruct q as [ | (v,j) q ]; [ easy | ].
      constructor 2; left.
      apply Forall_cons_iff in G2; tauto.
    * admit.
    * admit.
  + apply lex2_inv in H as [ H | (<- & ?) ].
Admitted.

Definition is_lub {X} (R : X → X → Prop) (P : X → Prop) u := ∀v, (∀x, P x → R x v) ↔ R u v.

(** The lub is preserved *)
Theorem E0_add_lub P u v : 
     (∀e, P e → cnf e)
   → cnf u
   → cnf v
   → is_lub E0_le P u
   → is_lub E0_le (λ x, ∃e, P e ∧ x = E0_add e v) (E0_add u v).

(** Then show that 
      E0_add e E0_zero = e
  and E0_add e E0_one = E0_succ e 
    Show also the preservation of lubs *)

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

Fact E0_succ_correct : ∀e, cnf e → cnf (E0_succ e).
Proof.
  intros e.
  generalize (E0_succ e) (E0_succ_spec e).
  induction 1 as [ | l i | l x i ]; rewrite !cnf_fix;
    intros [H1 H2]; split; simpl in *; eauto.
  + repeat constructor.
  + intros ? ? [ [=] | [] ]; subst; auto.
  + rewrite map_app in * |- *; auto.
  + intros ? ? [ [=] | ]%in_snoc_iff; subst; auto.
    split; auto || lia.
  + rewrite map_app in * |- *; simpl; auto.
    apply ordered_comp with (m := [_]); auto.
    repeat constructor.
    destruct (E0_zero_lt x) as [ <- | ]; auto.
    now destruct H.
  + intros e j; rewrite snoc_assoc. 
    intros [ [=] | ]%in_snoc_iff; subst; auto.
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





