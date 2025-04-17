(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils pos ordered lex2 lex_list list_order wlist1.

Import ListNotations.

Set Implicit Arguments.

#[local] Notation π₁ := proj1_sig.
#[local] Notation π₂ := proj2_sig.

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.
#[local] Hint Resolve clos_trans_rev transitive_rev : core.
#[local] Hint Constructors lex2 : core.

#[global] Reserved Notation "a '+₀' b"  (at level 31, left associativity, format "a  +₀  b" ).
#[global] Reserved Notation "a '*₀' b"  (at level 29, left associativity, format "a  *₀  b" ).
#[global] Reserved Notation "'ω^⟨' e , i '⟩'" (at level 0, format "ω^⟨ e , i ⟩").
#[global] Reserved Notation "'ω^' e" (at level 0, format "ω^ e").

#[local] Reserved Notation "'[' l ']₀'"  (at level 0, no associativity, format "[ l ]₀").
#[local] Reserved Notation "⌊ e ⌋₀"    (at level 0, e at level 200, format "⌊ e ⌋₀").
#[local] Reserved Notation "e '<E₀' f" (at level 70, format "e  <E₀  f").
#[local] Reserved Notation "e '≤E₀' f" (at level 70, format "e  ≤E₀  f").

Section E0.

  Unset Elimination Schemes.

  Inductive E0 : Set :=
    | E0_cons : list (E0*pos) → E0.

  Set Elimination Schemes.

  Definition E0_inv (e : E0) := match e with E0_cons l => l end.

  Notation "[ l ]₀" := (E0_cons l).
  
  Fact E0_eq_inv l m : [l]₀ = [m]₀ → l = m.
  Proof. now inversion 1. Qed.

  Section E0_rect.

    Notation E0_sub e f := (∃n, (e,n) ∈ E0_inv f).

    Local Lemma E0_sub_wf : well_founded (λ e f, E0_sub e f).
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
              (HP : ∀l, (∀ e n, (e,n) ∈ l → P e) → P [l]₀).

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

  Definition E0_fall P : E0 → Prop :=
    fix loop e :=
      match e with
      | [l]₀ => P l ∧ fold_right (λ p, and (loop (fst p))) True l
      end.

  Lemma E0_fall_fix P l : E0_fall P [l]₀ ↔ P l ∧ ∀ x i, (x,i) ∈ l → E0_fall P x.
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
                      → Q [l]₀).

    Theorem E0_fall_rect e : E0_fall P e → Q e.
    Proof. induction e; intros []%E0_fall_fix; eauto. Qed.

  End E0_fall_rect.

  Unset Elimination Schemes.

  Inductive E0_lt : E0 → E0 → Prop :=
    | E0_lt_intro l m : lex_list (lex2 E0_lt lt) l m → E0_lt [l]₀ [m]₀.

  Set Elimination Schemes.

  Hint Constructors E0_lt : core.

  Infix "<E₀" := E0_lt.

  (* This inversion principle is enough to reason about <E₀, 
     proceeding by induction on arguments *)
  Fact E0_lt_inv l m : [l]₀ <E₀ [m]₀ ↔ lex_list (lex2 E0_lt lt) l m.
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

  Definition E0_cnf_pred (l : list (E0*pos)) := ordered E0_lt⁻¹ (map fst l).

  Definition E0_cnf := E0_fall E0_cnf_pred.

  Fact E0_cnf_fix l : 
      E0_cnf [l]₀
    ↔ ordered E0_lt⁻¹ (map fst l) ∧ ∀ e i, (e,i) ∈ l → E0_cnf e.
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
        with (P := fun xi : E0*pos => ~ E0_cnf (fst xi))
             (Q := fun xi : E0*pos => E0_cnf (fst xi))
             (l := l)
      as [ ((x,i) & H2 & H3) | H2 ].
      * intros (x,i) []%IHl; auto.
      * right; rewrite E0_cnf_fix; intros (_ & G).
        simpl in H3; now apply G in H2.
      * left; rewrite E0_cnf_fix; split; auto.
        intros ? ?; apply (H2 (_,_)).
    + right; rewrite E0_cnf_fix; tauto.
  Qed.

  Unset Elimination Schemes.

  Inductive E0_lpo : E0 → E0 → Prop :=
    | E0_lpo_intro l m : lo (lex2 E0_lpo lt) l m → E0_lpo [l]₀ [m]₀.

  Set Elimination Schemes.

  Hint Constructors E0_lpo : core.

  Fact E0_lpo_inv l m : E0_lpo [l]₀ [m]₀ ↔ lo (lex2 E0_lpo lt) l m.
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
    apply Acc_rel_morph with (f := fun l e => [l]₀ = e); auto.
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

  Fact E0_lt_le_dec e f : { e <E₀ f } + { f ≤E₀ e}.
  Proof. unfold E0_le; destruct (E0_lt_sdec e f); auto. Qed.
  
  Fact E0_lt_sdec2 e f a : e <E₀ f → { a <E₀ e } + { a = e } + { e <E₀ a ∧ a <E₀ f } + { a = f } + { f <E₀ a }.
  Proof.
    intros H.
    destruct (E0_lt_sdec a e) as [ | | a e ]; auto.
    destruct (E0_lt_sdec f a); eauto.
  Qed. 

  Fact E0_lt_app_head l m k : [m]₀ <E₀ [k]₀ → [l++m]₀ <E₀ [l++k]₀.
  Proof. intros ?%E0_lt_inv; constructor; now apply lex_list_app_head. Qed.

  Fact E0_le_app_head l m k : [m]₀ ≤E₀ [k]₀ → [l++m]₀ ≤E₀ [l++k]₀.
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
      cnf [l]₀
    ↔ ordered E0_lt⁻¹ (map fst l)
    ∧ ∀ e i, (e,i) ∈ l → cnf e.
  Proof.
    rewrite cnf_iff, E0_cnf_fix.
    apply and_iff_compat_l.
    split; intros; apply cnf_iff; eauto.
  Qed.

  (* We convert the recursor *)
  Fact cnf_rect (P : E0 → Type) :
     (∀l, ordered E0_lt⁻¹ (map fst l) 
       → (∀ e i, (e,i) ∈ l → cnf e)
       → (∀ e i, (e,i) ∈ l → P e)
       → P [l]₀)
    → ∀e, cnf e → P e.
  Proof. 
    intros HP h H%cnf_iff; revert h H.
    induction 1 as [ l H1 H2 IH ] using E0_fall_rect.
    apply HP; auto.
    intros ? i ?.
    apply cnf_iff, (H2 _ i); auto.
  Qed.

  Fact cnf_sg e i : cnf e → cnf [[(e,i)]]₀.
  Proof.
    rewrite cnf_fix; split.
    + repeat constructor.
    + intros ? ? [[=]|[]]; subst; eauto.
  Qed.

  Fact cnf_cons_inv_left e i l : cnf [(e,i)::l]₀ → cnf e.
  Proof. intros (_ & H)%cnf_fix; eapply H; eauto. Qed.

  Fact cnf_app_left_inv l m : cnf [l++m]₀ → cnf [l]₀.
  Proof.
    rewrite !cnf_fix, map_app, ordered_app_iff; auto.
    intros ((? & ? & H) & ?); split; try tauto; eauto.
  Qed.

  Fact cnf_app_right_inv l m : cnf [l++m]₀ → cnf [m]₀.
  Proof.
    rewrite !cnf_fix, map_app, ordered_app_iff; auto.
    intros ((? & ? & H) & ?); split; try tauto; eauto.
  Qed.

  Fact cnf_cons_inv_right ei l : cnf [ei::l]₀ → cnf [l]₀.
  Proof. apply cnf_app_right_inv with (l := [_]). Qed.

  Hint Resolve cnf_sg
               cnf_cons_inv_left
               cnf_cons_inv_right
               cnf_app_left_inv
               cnf_app_right_inv : core.

  Definition E0_zero := [[]]₀.
  Notation "0₀" := E0_zero.

  Fact cnf_zero : cnf 0₀.
  Proof.
    apply cnf_fix; simpl; split.
    + constructor.
    + tauto.
  Qed.

  Hint Resolve cnf_zero : core.

  Fact E0_not_lt_zero e : ¬ e <E₀ 0₀.
  Proof. destruct e as [[]]; now intros ?%E0_lt_inv%lex_list_inv. Qed.

  Fact E0_zero_or_pos e : { e = 0₀ } + { 0₀ <E₀ e }.
  Proof.
    destruct (E0_le_lt_dec e 0₀) as [ H | ]; auto.
    left; now destruct H as [ ?%E0_not_lt_zero | ].
  Qed.

  (* Notation for ωᵉ.i *)
  Notation "ω^⟨ e , i ⟩" := [[(e,i)]]₀.

  Definition E0_one := ω^⟨0₀,1ₚ⟩.
  Notation "1₀" := E0_one.

  Fact cnf_one : cnf E0_one.
  Proof. apply cnf_sg; auto. Qed.

  Hint Resolve cnf_one : core.

  Fact E0_zero_le : ∀e, 0₀ ≤E₀ e.
  Proof. intros [ [] ]; [ right | left ]; eauto; repeat constructor. Qed.

  Hint Resolve E0_zero_le : core.

  Fact E0_zero_not_gt : ∀e, ¬ e <E₀ 0₀.
  Proof. intros [ l ] ?%E0_lt_inv%lex_list_inv; now destruct l. Qed.

  Fact E0_one_ge e : e ≠ 0₀ → cnf e → 1₀ ≤E₀ e.
  Proof.
    destruct e as [[ | (x,i) r ]]; [ easy | intros _ Hr ].
    destruct (E0_zero_le x) as [ Hx | <- ].
    + left; constructor; constructor; now left.
    + destruct i as [ | i ].
      * apply E0_le_app_head with (l := [_]).
        destruct r.
        - now right.
        - left; constructor; constructor 1.
      * left; constructor; constructor; right; auto.
  Qed.
  
  Fact E0_lt_one : ∀e, e <E₀ 1₀ → e = 0₀.
  Proof.
    intros [l] [ | (x,i) ? [ []%E0_zero_not_gt | [_ H%pos_not_lt_one] ]%lex2_inv ]%E0_lt_inv%lex_list_sg_inv_right; 
      now auto.
  Qed.

  Lemma E0_lt_head e i l : e <E₀ [(e,i)::l]₀.
  Proof.
    induction e as [ [ | []  ]] in i, l |- *;
      constructor.
    + constructor 1.
    + constructor 2; left; eauto.
  Qed.

  Corollary E0_lt_sub l e i : cnf [l]₀ → (e,i) ∈ l → e <E₀ [l]₀.
  Proof.
    intros H1 (l' & r & ->)%in_split.
    apply E0_lt_le_trans with (1 := E0_lt_head e i r).
    destruct l' as [ | (f,j) l ]; auto.
    left; constructor; constructor 2; left.
    apply cnf_fix in H1 as [ H1 _ ].
    simpl in H1; rewrite map_app in H1; simpl in H1.
    apply ordered_cons_iff, proj2 in H1; auto.
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
    induction 1 as [ l He1 He2 IH ] using cnf_rect.
    destruct 1 as [ m Hf1 Hf2 _  ] using cnf_rect.
    intros H%E0_lt_inv.
    constructor.
    apply lo_mono with (1 := lex2_E0_lpo_lt_trans').
    apply ordered_lex_list_lo; eauto.
    + revert He1.
      apply ordered_morphism with (f := fun x y => x = fst y).
      * intros ? ? [] [] ([] & ? & ?)%in_map_iff ([] & ? & ?)%in_map_iff -> ->; right; left; simpl in *; subst; eauto.
      * clear He2 IH H; induction l; simpl; constructor; auto.
    + revert H; apply lex_list_mono.
      intros [] [] ? ? [| (<- & ?)]%lex2_inv; eauto.
  Qed.

  Hint Resolve cnf_lt_lpo : core.

  (** The fundamental theorem: <E₀ is well-founded on cnf *)
  Theorem E0_lt_wf : well_founded (λ x y, x <E₀ y ∧ cnf x ∧ cnf y).
  Proof.
    generalize wf_E0_lpo.
    apply wf_rel_morph with (f := eq); eauto.
    intros ? ? ? ? -> -> (? & ? & ?); eauto.
  Qed.

(*
  (** The successor via an inductive spec *)
  Inductive E0_succ_gr : E0 → E0 → Prop :=
    | E0_succ_gr_0       : E0_succ_gr 0₀ 1₀
    | E0_succ_gr_1 l i   : E0_succ_gr [l++[(0₀,i)]]₀ [l++[(0₀,S i)]]₀ 
    | E0_succ_gr_2 l x i : x ≠ 0₀
                         → E0_succ_gr [l++[(x,i)]]₀ [l++[(x,i);(0₀,1)]]₀.

  (* Inversion lemma for the graph of E0_succ *)
  Fact E0_succ_gr_inv e f :
      E0_succ_gr e f
    → (e = 0₀ → f = 1₀)
    ∧ (∀ l i, e = [l++[(0₀,i)]]₀ → f = [l++[(0₀,S i)]]₀)
    ∧ (∀ l x i, x ≠ 0₀ → e = [l++[(x,i)]]₀ → f = [l++[(x,i);(0₀,1)]]₀).
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
    + exists [[(0₀,1)]]₀; constructor.
    + destruct x as [ [ | y m ] ].
      * exists [l++[(0₀,S i)]]₀; constructor.
      * exists [l++[([y::m]₀,i);(0₀,1)]]₀; now constructor.
  Qed.

  Definition E0_succ e := π₁ (E0_succ_pwc e).

  Notation S₀ := E0_succ.

  Fact E0_succ_spec e : E0_succ_gr e (S₀ e).
  Proof. apply (proj2_sig _). Qed.

  Fact E0_succ_zero : S₀ 0₀ = 1₀.
  Proof. apply E0_succ_gr_fun with (1 := E0_succ_spec _); constructor. Qed.

  Fact E0_succ_pos n : S₀ ω^⟨0₀,n⟩ = ω^⟨0₀,S n⟩.
  Proof.
    apply E0_succ_gr_fun with (1 := E0_succ_spec _).
    constructor 2 with (l := []).
  Qed.

  Hint Resolve E0_succ_zero : core.

  Fact E0_succ_cnf e : cnf e → cnf (S₀ e).
  Proof.
    generalize (E0_succ e) (E0_succ_spec e).
    induction 1 as [ | l i | l x i ]; auto; rewrite !cnf_fix;
    intros [H1 H2]; split; simpl in *; auto.
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
*)

  (** The ordinal addition via wlist_add *)

  Opaque wlist_add.

  Definition E0_add e f :=
    match e, f with
    | [l]₀, [m]₀ => [wlist_add E0_lt_sdec l m]₀
    end.

  Infix "+₀" := E0_add.

  Fact E0_add_cnf : ∀ e f, cnf e → cnf f → cnf (e +₀ f).
  Proof.
    intros [] [] []%cnf_fix []%cnf_fix; apply cnf_fix.
    split.
    + apply wlist_add_ordered; auto.
    + intros ? ? (? & ? & [])%in_wlist_add; eauto.
  Qed.

  Fact E0_add_zero_right : ∀e, e +₀ 0₀ = e.
  Proof. intros []; simpl; auto. Qed.

  Fact E0_add_zero_left e : 0₀ +₀ e = e.
  Proof. destruct e as [[|[]]]; auto. Qed.

  (** Already wlist_combine is associative !! *)
  Lemma E0_add_assoc : ∀ u v w, u +₀ v +₀ w =  u +₀ (v +₀ w).
  Proof.
    intros [] [] []; unfold E0_add; f_equal.
    apply wlist_add_assoc; auto.
  Qed.

(*
  Lemma E0_add_one_right e : cnf e → e +₀ 1₀ = S₀ e.
  Proof.
    intros He.
    apply E0_succ_gr_fun with (2 := E0_succ_spec _).
    destruct e as [l]; apply cnf_fix in He as [He1 He2].
    unfold E0_add, E0_one, E0_zero.
    destruct (wlist_cut_choice E0_lt_sdec l 0₀)
        as [ H 
         | [ (k & a & b & -> & H1)
           | (z & k & a & b & -> & H1 & H2)
           ] ].
    + rewrite wlist_add_spec_1; auto.
      destruct l as [ | ([[]],j) l _ ] using rev_ind.
      * constructor.
      * now apply Forall_app, proj2, Forall_cons_iff, proj1, E0_lt_irrefl in H.
      * rewrite <- ! app_assoc; simpl; now constructor 3.
    + rewrite wlist_add_spec_2; auto.
      destruct b as [ | (y,j) b ]; simpl.
      * replace (k+1) with (S k) by lia; constructor.
      * rewrite map_app in He1; simpl in He1.
        now apply ordered_app_tail, ordered_inv, ordered_from_inv, proj1, E0_zero_not_gt in He1.
    + now apply E0_zero_not_gt in H2.
  Qed.
*)

  (** We show  ω[l] +₀ e ≤E₀ ω[m] +₀ e by induction on lex_list _ l m *)
  Lemma E0_add_mono_left u v e : cnf u → cnf v → cnf e → u ≤E₀ v → u +₀ e ≤E₀ v +₀ e.
  Proof.
    intros Hu Hv He [ H | -> ]; [ | now right ].
    revert u v e Hu Hv He H.
    intros [l] [m] [[ | (y,j) k]] Hl Hm Hk ?%E0_lt_inv.
    1: rewrite !E0_add_zero_right; now left; constructor.
    revert H Hl Hm.
    induction 1 as [ (x,i) m | (a,u) (b,v) l m [Hab | (<- & Huv)]%lex2_inv | (x,i) l m Hlm IH ] in j |- *; intros Hl Hm; unfold E0_add.
    + rewrite wlist_add_nil_left.
      destruct (E0_lt_sdec x y).
      * rewrite wlist_add_lt; auto.
      * rewrite wlist_add_eq; auto.
        left; constructor; constructor 2; right; auto.
      * rewrite wlist_add_gt; auto.
        left; constructor; constructor 2; now left.
    + destruct (@E0_lt_sdec2 a b y)
        as [ [ [ [ | ->] | [] ] | -> ] | ]; auto.
      * rewrite !wlist_add_gt; eauto.
        left; constructor; constructor 2; now left.
      * rewrite wlist_add_eq, wlist_add_gt; auto.
        left; constructor; constructor 2; now left.
      * rewrite wlist_add_lt, wlist_add_gt; auto.
        left; constructor; constructor 2; now left.
      * rewrite wlist_add_lt, wlist_add_eq; auto.
        left; constructor; constructor 2; right; auto.
      * rewrite !wlist_add_lt; eauto.
    + destruct (E0_lt_sdec a y).
      * rewrite !wlist_add_lt; auto.
      * rewrite !wlist_add_eq; auto.
        left; constructor; constructor 2; right; auto.
      * rewrite !wlist_add_gt; auto.
        left; constructor; constructor 2; now right.
    + destruct (E0_lt_sdec x y).
      * rewrite !wlist_add_lt; auto.
      * rewrite !wlist_add_eq; auto.
      * rewrite !wlist_add_gt; auto.
        destruct (IH j) as [ ?%E0_lt_inv | ?%E0_eq_inv ]; auto.
        1,2: eapply cnf_cons_inv_right; eassumption.
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
         |   (x & i & l' & r & E & G1 & G2) ] ]; subst; simpl.
    + rewrite wlist_add_spec_1; auto.
      constructor; apply lex_list_prefix'.
    + rewrite wlist_add_gt_list, wlist_add_eq; auto.
      constructor; apply lex_list_app_head.
      constructor 2; right.
      apply cnf_fix in Hf; auto.
    + rewrite wlist_add_gt_list, wlist_add_lt; auto.
      constructor; apply lex_list_app_head.
      constructor 2; now left.
  Qed.

  Lemma E0_add_mono_right : ∀ e u v, cnf e → cnf u → cnf v → u <E₀ v → e +₀ u <E₀ e +₀ v.
  Proof.
    intros [l] [m] [[|(z,h) k]] Hl Hm Hk.
    1: intros []%E0_zero_not_gt.
    destruct m as [ | yj m ].
    1: intros; apply E0_add_incr; eauto.
    intros [ (y,j) [ Hyz | (<- & Hjh) ]%lex2_inv | Hmk ]%E0_lt_inv%lex_list_inv; constructor.
    + destruct (wlist_cut_choice E0_lt_sdec l z)
        as [ G1 
         | [ (i & l' & r' & E & G1) 
         |   (x & i & l' & r' & E & G1 & G2) ] ]; subst; simpl app.
      * rewrite !wlist_add_spec_1; auto.
        - apply lex_list_app_head; constructor 2; now left.
        - revert G1; apply Forall_impl; eauto.
      * rewrite !wlist_add_gt_list, wlist_add_gt, wlist_add_eq; auto.
        2: revert G1; apply Forall_impl; eauto.
        apply lex_list_app_head.
        constructor 2; right; auto.
      * rewrite !wlist_add_gt_list; auto.
        2: revert G1; apply Forall_impl; eauto.
        apply lex_list_app_head.
        rewrite wlist_add_lt with (y := z); auto.
        destruct (wlist_add_choice E0_lt_sdec)
          with (x := x) (i := i) (y := y) (j := j) (l := r') (m := m)
          as (a & b & c & -> & H); auto.
        constructor 2; left.
        destruct H as [ (_ & <- & _) | [ (_& <- & _) | (_ & -> & _)] ]; auto.
    + destruct (wlist_add_common E0_lt_sdec l y) as (l' & i & H).
      rewrite !H.
      apply lex_list_app_head.
      constructor 2; right; lia.
    + rewrite !wlist_add_cons_right. 
      now apply lex_list_app_head.
  Qed.

  Hint Resolve in_map : core.

  Lemma E0_lt_inv_add e f : cnf e → cnf f → e <E₀ f → ∃a, f = e +₀ a ∧ 0₀ <E₀ a ∧ cnf a.
  Proof.
    intros He Hf H; revert e f H He Hf.
    intros [l] [m] [ l' m' | p (x,i) (y,j) l' m' [ H | (<- & H) ]%lex2_inv ]%E0_lt_inv%lex_list_invert He Hf.
    + exists [l']₀.
      destruct l' as [ | (y,j) l' ]; try easy; repeat split; eauto.
      2: repeat constructor.
      unfold E0_add.
      rewrite wlist_add_spec_1; auto.
      apply cnf_fix, proj1 in Hf.
      rewrite map_app, ordered_app_iff in Hf; auto.
      apply Forall_forall.
      intros; eapply Hf; simpl; eauto.
    + exists [(y,j)::m']₀; repeat split; eauto.
      2: repeat constructor.
      simpl; f_equal.
      rewrite wlist_add_gt_list, wlist_add_lt; auto.
      apply cnf_fix, proj1 in Hf.
      rewrite map_app, ordered_app_iff in Hf; auto.
      apply Forall_forall.
      intros; eapply Hf; simpl; eauto.
    + destruct pos_lt_sub with (1 := H) as (k & ->).
      exists [(x,k)::m']₀; repeat split; auto.
      2: repeat constructor.
      * simpl; f_equal.
        rewrite wlist_add_gt_list, wlist_add_eq; auto.
        apply cnf_fix, proj1 in Hf.
        rewrite map_app, ordered_app_iff in Hf; auto.
        apply Forall_forall.
        intros; eapply Hf; simpl; eauto.
      * rewrite cnf_fix in Hf |- *.
        rewrite map_app, ordered_app_iff in Hf; auto.
        split; try tauto.
        apply proj2 in Hf.
        intros u v [ [=] | G ]; subst; eapply Hf; eauto.
  Qed.

  Fact E0_add_exp e i j : ω^⟨e,i⟩ +₀ ω^⟨e,j⟩ = ω^⟨e,i +ₚ j⟩.
  Proof. simpl; rewrite wlist_add_eq; auto. Qed.

  Definition E0_succ e := E0_add e 1₀.

  Notation S₀ := E0_succ.

  Fact E0_succ_zero : S₀ 0₀ = 1₀.
  Proof. reflexivity. Qed.

  Fact E0_succ_pos n : S₀ ω^⟨0₀,n⟩ = ω^⟨0₀,n +ₚ 1ₚ⟩.
  Proof. unfold E0_succ, E0_one; now rewrite E0_add_exp. Qed.

  Hint Resolve E0_succ_zero : core.

  Fact E0_succ_cnf e : cnf e → cnf (S₀ e).
  Proof. intros; unfold E0_succ; apply E0_add_cnf; auto. Qed.
 
  Definition E0_is_succ e := ∃f, e = E0_succ f ∧ cnf f.
  Definition E0_is_limit e := e ≠ 0₀ ∧ ¬ ∃f, e = E0_succ f ∧ cnf f.

  Lemma E0_is_succ_iff e :
    cnf e → E0_is_succ e ↔ ∃ l i, e = [l++[(0₀,i)]]₀.
  Proof.
    intros He; split.
    + intros ([l] & -> & Hf).
      destruct l as [ | l (x,i) _ ] using rev_rect.
      * exists [], 1ₚ; simpl.
        now rewrite wlist_add_nil_left.
      * destruct (E0_zero_or_pos x) as [ -> | Hx ].
        - exists l, (i +ₚ 1ₚ).
          unfold E0_succ; simpl; f_equal.
          rewrite wlist_add_gt_list, wlist_add_eq; auto.
          apply Forall_forall.
          apply cnf_fix, proj1 in Hf.
          rewrite map_app in Hf; simpl in Hf.
          rewrite ordered_snoc_iff in Hf; auto.
          intros [] ?; apply Hf; eauto.
        - exists (l++[(x, i)]), 1ₚ.
          unfold E0_succ; simpl; f_equal.
          rewrite wlist_add_gt_list, wlist_add_gt,
                  wlist_add_nil_left, <- app_assoc; auto.
          apply Forall_forall.
          apply cnf_fix, proj1 in Hf.
          rewrite map_app in Hf; simpl in Hf.
          rewrite ordered_snoc_iff in Hf; auto.
          intros [] H; simpl.
          apply E0_lt_trans with (1 := Hx), Hf; eauto.
          apply in_map_iff; exists (e,p); auto.
    + intros (l & i & ->).
      assert (Forall (fun x => 0₀ <E₀ fst x) l) as Hl.
      1:{ apply Forall_forall.
          apply cnf_fix, proj1 in He.
          rewrite map_app in He; simpl in He.
          rewrite ordered_snoc_iff in He; auto.
          intros [] H; apply He; auto. }
      destruct (pos_one_or_succ i) as [ -> | (j & ->) ].
      * exists [l]₀; split; eauto.
        unfold E0_succ; simpl; f_equal.
        rewrite wlist_add_spec_1; auto.
      * exists [l++[(0₀,j)]]₀; split; auto.
        - unfold E0_succ; simpl; f_equal.
          rewrite wlist_add_gt_list, wlist_add_eq; auto.
        - rewrite cnf_fix, map_app in He |- *.
          destruct He as [ H2 H3 ]; split; auto.
          intros ? ? [| [ [=] | []]]%in_app_iff; subst; eauto.
  Qed.

  Lemma E0_is_limit_iff e :
    cnf e → E0_is_limit e ↔ ∃ l b i, b ≠ 0₀ ∧ e = [l++[(b,i)]]₀.
  Proof.
    intros He.
    split.
    + intros (H1 & H2); destruct e as [ l ].
      destruct l as [ | l (b,i) _ ] using rev_rect.
      1: easy.
      exists l, b, i; repeat split; auto.
      intros ->; apply H2.
      apply E0_is_succ_iff; eauto.
    + intros (l & b & i & H1 & ->).
      split.
      * contradict H1.
        apply E0_eq_inv in H1; now destruct l.
      * intros (m & j & H3)%E0_is_succ_iff; auto.
        injection H3; clear H3.
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
    destruct (wlist_add_last E0_lt_sdec l m b i)
      as (r & j & ? & ->).
    exists r, b, j; split; auto; lia.
  Qed.

  Lemma E0_add_is_limit_inv a e : 
    cnf a → cnf e → E0_is_limit (a +₀ e) → e = 0₀ ∨ E0_is_limit e.
  Proof.
    intros Ha He (m & b & i & Hi & Hb & E)%E0_is_limit_iff; auto.
    destruct a as [l]; destruct e as [k].
    destruct k as [|k (c,j) _] using rev_rect; auto; right.
    unfold E0_add in E; apply E0_eq_inv in E.
    destruct (wlist_add_last E0_lt_sdec l k c j)
      as (r & p & Hp & H).
    rewrite H in E.
    apply app_inj_tail in E as (<- & [=]); subst p c.
    apply E0_is_limit_iff; auto.
    exists k, b, j; split; auto.
    apply cnf_app_right_inv, cnf_fix in He.
    eapply He; eauto.
  Qed.

  Fact E0_exp_is_limit e i :
    cnf e → e ≠ 0₀ → 0 < i → E0_is_limit [[(e,i)]]₀.
  Proof.
    intros H1 H2 H3.
    apply E0_is_limit_iff; auto.
    exists [], e, i; auto.
  Qed.

  Hint Resolve E0_add_is_limit E0_exp_is_limit : core.

  (** a + ω^(e.i) is a limit ordinal *)
  Fact E0_add_exp_is_limit a e i : 
    cnf a → cnf e → e ≠ 0₀ → 0 < i → E0_is_limit (a +₀ ω^⟨e,i⟩).
  Proof. eauto. Qed.
 

  Definition E0_omega e := ω^⟨e,1⟩.

  Notation "ω^ e" := (E0_omega e).
  
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
    + rewrite wlist_add_lt; eauto.
    + apply cnf_fix in Ha.
      assert (0 < i); [ | lia ].
      eapply Ha; eauto.
  Qed.

  Lemma E0_add_omega_fun_right a b e f : a +₀ ω^e = b +₀ ω^f → e = f.
  Proof.
    revert a b e f.
    intros [a] [b] e f; unfold E0_omega, E0_add.
    destruct (wlist_add_last E0_lt_sdec a [] e 1)
      as (l & i & H1 & H2).
    destruct (wlist_add_last E0_lt_sdec b [] f 1)
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
  Lemma E0_lt_omega_inv' f b :
      cnf f
    → cnf b
    → f <E₀ ω^b
    → f = 0₀ ∨ ∃n a, 0 < n ∧ f <E₀ [[(a, n)]]₀ ∧ a <E₀ b ∧ cnf a.
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

  Lemma E0_lt_exp a i b j : a <E₀ b → ω^⟨a,i⟩ <E₀ ω^⟨b,j⟩.
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
        - replace [m++[([[]]₀,1)]]₀
            with (S₀ [m]₀).
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
        - replace [m++[([[]]₀,S (S i))]]₀
            with (S₀ [m++[(0₀,S i)]]₀).
          ++ constructor 2.
             apply cnf_fix; split.
             ** rewrite map_app in H1 |- *; auto.
             ** intros ? ? [|[[=]|[]]]%in_app_iff; split; subst; eauto; lia.
          ++ apply E0_succ_gr_fun with (1 := E0_succ_spec _).
             constructor 2.
      * destruct i as [ | i ].
        - replace [m++[([yj::e]₀,1)]]₀
            with ([m]₀ +₀ [[([yj::e]₀,1)]]₀).
          ++ constructor 3; easy || eauto.
             ** apply cnf_fix; repeat split; eauto.
                rewrite map_app in H1.
                now apply ordered_app_head in H1.
             ** intros [k] Hk; unfold E0_omega, E0_add.
                intros E%E0_eq_inv.
                rewrite <- (app_nil_r m) in E.
                rewrite map_app, ordered_app_iff in H1; eauto.
                rewrite wlist_add_gt_list in E; eauto.
                2:{ apply Forall_forall.
                    intros (x,i) Hxi; apply H1; simpl; eauto.
                    apply in_map_iff; exists (x,i); auto. }
                rewrite wlist_add_nil_left in E.
                symmetry in E.
                apply wlist_add_eq_snoc_inv in E
                  as (r & -> & _); auto.
                destruct r.
                -- rewrite app_nil_r; now right.
                -- left; constructor.
                   apply lex_list_prefix'.
          ++ simpl.
             rewrite wlist_add_spec_1; auto.
             rewrite map_app in H1; simpl in H1.
             apply ordered_snoc_iff, proj2 in H1; auto.
             apply Forall_forall.
             now intros (f,i) H; apply H1, in_map.
        - replace [m++[([yj::e]₀, S (S i))]]₀
            with ([m++[([yj::e]₀,S i)]]₀ +₀ [[([yj::e]₀,1)]]₀).
          ++ constructor 3; easy || eauto.
             ** apply cnf_fix; split.
                -- rewrite map_app in H1 |- *; auto.
                -- intros f j [|[[=]|[]]]%in_app_iff; split; subst; eauto; lia.
             ** intros [k] Hk; unfold E0_omega; simpl.
                intros E%E0_eq_inv.
                rewrite map_app, ordered_app_iff in H1; eauto.
                rewrite wlist_add_gt_list, wlist_add_eq in E; eauto.
                2:{ apply Forall_forall.
                    intros (y,j) Hxi; apply H1; simpl; eauto.
                    apply in_map_iff; exists (y,j); auto. }
                symmetry in E.
                apply wlist_add_eq_snoc_inv in E
                  as (r & -> & _ & _ & [ H | (p & r' & ? & ->) ]); auto.
                1: exfalso; lia.
                replace p with (S i) by lia.
                destruct r'; [ now right | ].
                left; constructor.
                apply lex_list_app_head.
                constructor 3; constructor 1.
          ++ simpl.
             rewrite <- (app_nil_r (_++[_])), <- app_assoc.
             rewrite wlist_add_spec_2; auto.
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
  
  Fact E0_cnf_lt_omega e n l j : cnf [(e,n)::l]₀ → [l]₀ <E₀ [[(e,j)]]₀.
  Proof.
    intros (H1 & H2)%cnf_fix; constructor.
    destruct l as [ | (x,i) l ].
    + constructor.
    + constructor 2; left.
      simpl in H1.
      apply ordered_cons_iff in H1; auto.
      apply H1; auto.
  Qed.
  
  Fact E0_add_head_normal e i l : cnf [l]₀ → [l]₀ <E₀ ω^e → ω^⟨e,i⟩ +₀ [l]₀ = [(e, i)::l]₀.
  Proof.
    intros G H%E0_lt_inv; unfold E0_add; f_equal.
    revert H G.
    intros [ | (y,j) m [ H | (-> & H2) ]%lex2_inv ]%lex_list_sg_inv_right G; auto.
    + rewrite wlist_add_gt; auto.
    + assert (0 < j); [ | lia ].
      apply cnf_fix in G.
      eapply G; eauto.
  Qed.

  Fact E0_add_below_omega e l m :
      [l]₀ <E₀ ω^e
    → [m]₀ <E₀ ω^e
    → [l]₀ +₀ [m]₀ <E₀ ω^e.
  Proof.
    unfold E0_add.
    intros [ | (x,i) l' H1 ]%E0_lt_inv%lex_list_sg_inv_right.
    1: now rewrite wlist_add_nil_left.
    intros [ | (y,j) m' H2 ]%E0_lt_inv%lex_list_sg_inv_right.
    1: now rewrite wlist_add_nil_right; constructor; constructor 2.
    constructor.
    destruct (E0_lt_sdec x y) as [ x y H | x | x y H ].
    + rewrite wlist_add_lt; auto.
      now constructor 2.
    + rewrite wlist_add_eq; auto.
      constructor 2.
      apply lex2_inv in H1 as [ H1 | (-> & H1) ].
      1: now constructor 1.
      apply lex2_inv in H2 as [ H2 | (_ & H2) ].
      1: now apply E0_lt_irrefl in H2.
      constructor 2; lia.
    + rewrite wlist_add_gt; auto.
      now constructor 2.
  Qed.

  Fact E0_add_head_lt e i f j l m : e <E₀ f → [(e,i)::l]₀ +₀ [(f,j)::m]₀ = [(f,j)::m]₀.
  Proof. simpl; intro; rewrite wlist_add_lt; auto. Qed.

  Fact E0_add_head_eq e i j l m : [(e,i)::l]₀ +₀ [(e,j)::m]₀ = [(e,i+j)::m]₀.
  Proof. simpl; rewrite wlist_add_eq; auto. Qed.

  Fact E0_add_head_gt e i f j l m :
      f <E₀ e
    → [l]₀ <E₀ ω^e
    → [m]₀ <E₀ ω^f
    → cnf [l]₀
    → cnf [m]₀
    → cnf f
    → 0 < j
    →  [(e,i)::l]₀ +₀ [(f,j)::m]₀ = ω^⟨e,i⟩ +₀ ([l]₀ +₀ [(f,j)::m]₀)
     ∧ [l]₀ +₀ [(f,j)::m]₀ <E₀ ω^e.
  Proof.
    intros H1 H2 H3 H4 H5 H6.
    assert ([l]₀ +₀ [(f,j)::m]₀ <E₀ ω^e).
    1:{ apply E0_add_below_omega; auto.
        constructor; constructor 2; now left. }
    split; auto.
    unfold E0_add at 1 3.
    unfold E0_add in H.
    rewrite wlist_add_gt; auto.
    rewrite E0_add_head_normal; auto.
    fold ([l]₀ +₀ [(f,j)::m]₀).
    apply E0_add_cnf; auto.
    rewrite <- E0_add_head_normal; auto.
  Qed.

  Section cnf_head_rect.

    Variables (P : ∀e, cnf e → Type)
              (HP0 : ∀ h, P 0₀ h)
              (HP1 : ∀ e he i f hf h, 0 < i → f <E₀ ω^e → P f hf → P e he → P (ω^⟨e,i⟩ +₀ f) h).

    Theorem cnf_head_rect e he : P e he.
    Proof.
      induction e as [ e IHe ] in he |- * using (well_founded_induction_type E0_lt_wf).
      destruct e as [ [ | (x,i) l ] ].
      1: apply HP0.
      generalize he.
      rewrite <- E0_add_head_normal; eauto.
      + intro h.
        assert (h1 : cnf x) by eauto.
        assert (h2 : cnf [l]₀) by eauto.
        apply HP1 with (he := h1) (hf := h2); eauto.
        * constructor.
          apply cnf_fix, proj1 in he; simpl in he.
          apply ordered_cons_iff, proj2 in he; auto.
          destruct l as [ | (y,j) l ].
          - constructor 1.
          - constructor 2; left; apply he; simpl; auto.
        * apply IHe; split; auto.
          constructor.
          apply cnf_fix, proj1 in he; simpl in he.
          apply ordered_cons_iff, proj2 in he; auto.
          destruct l as [ | (y,j) l ].
          - constructor 1.
          - constructor 2; left; apply he; simpl; auto.
        * apply IHe; split; auto.
          apply E0_lt_head; auto.
      + eapply E0_cnf_lt_omega; eauto.
    Qed.

  End cnf_head_rect.

End E0.

#[global] Opaque E0_add.
