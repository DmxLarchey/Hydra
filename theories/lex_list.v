(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.
From Hydra Require Import utils list_order ordered.

Import ListNotations.

Set Implicit Arguments.

#[local] Hint Resolve in_cons in_eq in_elt in_or_app : core.
#[local] Hint Constructors clos_trans clos_refl_trans : core.
#[local] Hint Resolve clos_refl_trans_rev clos_trans_rev : core.

Section lex_list.

  Variables (X : Type) (R : X → X → Prop).

  (* lexicographic order on lists, head is most significant *)
  Inductive lex_list : list X → list X → Prop :=
    | lex_list_nil x m : lex_list [] (x::m)
    | lex_list_lt x y l m : R x y → lex_list (x::l) (y::m)
    | lex_list_eq x l m : lex_list l m → lex_list (x::l) (x::m).

  Hint Constructors lex_list : core.

  (* introduction lemmas *)

  Fact lex_list_app_head c l m : lex_list l m → lex_list (c++l) (c++m).
  Proof. induction c; simpl; eauto. Qed.

  Hint Resolve lex_list_app_head : core.

  Fact lex_list_prefix' p x l : lex_list p (p++x::l).
  Proof. rewrite <- (app_nil_r p) at 1; auto. Qed.

  Hint Resolve lex_list_prefix' : core.

  Fact lex_list_prefix p l : l ≠ [] → lex_list p (p++l).
  Proof. destruct l; [ easy | auto ]. Qed. 

  Fact lex_list_snoc h l : lex_list l (l++[h]).
  Proof. now apply lex_list_prefix. Qed.

  (* inversion lemmas *)

  Inductive lex_list_inv_shape l m y : X → Prop :=
    | in_lex_list_inv_shape0 x : R x y → lex_list_inv_shape l m y x
    | in_lex_list_inv_shape1 : lex_list l m → lex_list_inv_shape l m y y.

  Hint Constructors lex_list_inv_shape : core.

  Fact lex_list_inv l m :
      lex_list l m 
    ↔ match m with 
      | []   => False
      | y::m =>
        match l with
        | [] => True
        | x::l => lex_list_inv_shape l m y x
        end
      end.
  Proof. 
    split.
    + intros []; eauto.
    + revert l m; intros [] [] []; eauto.
  Qed.
  
  Fact lex_list_cons_inv x l y m :
      lex_list (x::l) (y::m)
     → R x y ∨ x = y ∧ lex_list l m.
  Proof. intros []%lex_list_inv; auto. Qed.

  Inductive lex_list_invert_shape : list X → list X → Prop :=
    | in_lex_list_invert_shape0 k l : k ≠ [] → lex_list_invert_shape l (l++k)
    | in_lex_list_invert_shape1 p x y l m : R x y → lex_list_invert_shape (p++[x]++l) (p++[y]++m).

  Hint Constructors lex_list_invert_shape : core.

  Lemma lex_list_invert l m : lex_list l m → lex_list_invert_shape l m.
  Proof.
    induction 1 as [ x m | x y l m H | z l m _ [] ].
    + now constructor 1 with (l := []).
    + now constructor 2 with (p := []).
    + now constructor 1 with (l := _::_).
    + now constructor 2 with (p := _::_).
  Qed.

  Local Fact lex_list_app_inv_right_rec l m :
      lex_list l m
    → ∀ m₁ m₂, m = m₁++m₂ → lex_list l m₁ ∨ ∃r, l = m₁++r ∧ lex_list r m₂.
  Proof.
    induction 1 as [ x m | x y l m H | z l m H IH ];
      (intros [] ?; simpl; [ intros <-; right | intros [=]; subst ]; eauto).
    destruct (IH _ _ eq_refl) as [ | (? & -> & ?) ]; eauto.
  Qed.

  Lemma lex_list_app_inv_right l m₁ m₂ :
      lex_list l (m₁++m₂)
    → lex_list l m₁ 
    ∨ ∃r, l = m₁++r ∧ lex_list r m₂.
  Proof. intros; eapply lex_list_app_inv_right_rec; eauto. Qed.

  Inductive lex_list_snoc_inv_shape_l x : list X → list X → Prop :=
    | in_lex_list_snoc_inv_shape0_l0 l a b r r' : R a b → lex_list_snoc_inv_shape_l x (l++[a]++r) (l++[b]++r')
    | in_lex_list_snoc_inv_shape0_l1 y l r : R x y → lex_list_snoc_inv_shape_l x l (l++[y]++r)
    | in_lex_list_snoc_inv_shape0_l2 l r : r ≠ [] → lex_list_snoc_inv_shape_l x l (l++[x]++r).

  Local Fact lex_list_snoc_inv_left_rec lx m : 
    lex_list lx m → ∀ l x, lx = l++[x] → lex_list_snoc_inv_shape_l x l m.
  Proof.
    intros [k lx' H|p x y l m' H]%lex_list_invert.
    + intros l x ->; rewrite <- app_assoc; now constructor 3.
    + intros l' u.
      destruct l as [ | v l _ ] using rev_ind.
      * simpl; intros (<- & <-)%app_inj_tail.
        now constructor 2. 
      * rewrite !app_assoc.
        intros (<- & <-)%app_inj_tail.
        rewrite <- !app_assoc.
        now constructor 1.
  Qed.

  Fact lex_list_snoc_inv_left l x m : 
    lex_list (l++[x]) m → lex_list_snoc_inv_shape_l x l m.
  Proof. intros H; now apply lex_list_snoc_inv_left_rec with (2 := eq_refl). Qed.

  Remark lex_list_snoc_inv_left' l x m : 
      lex_list (l++[x]) m 
    → (∃ p a b q r, l = p++[a]++q ∧ m = p++[b]++r ∧ R a b)
    ∨ (∃ y r, m = l++[y]++r ∧ R x y)
    ∨ (∃ r, m = l++[x]++r ∧ r ≠ []).
  Proof.
    intros [ l' a b r r' | y l' r | l' r ]%lex_list_snoc_inv_left.
    + left; now exists l', a, b, r, r'.
    + right; left; eauto.
    + do 2 right; eauto.
  Qed.

  Inductive lex_list_snoc_inv_shape y : list X → list X → Prop :=
    | in_lex_list_snoc_inv_shape0 l m : lex_list_snoc_inv_shape y l (l++m)
    | in_lex_list_snoc_inv_shape1 x l m : R x y → lex_list_snoc_inv_shape y (l++[x]++m) l
    | in_lex_list_snoc_inv_shape2 p u v l m : R u v → lex_list_snoc_inv_shape y (p++[u]++l) (p++[v]++m).

  Local Lemma lex_list_snoc_inv_rec l m' : lex_list l m' → ∀ m y, m' = m++[y] → lex_list_snoc_inv_shape y l m.
  Proof.
    intros [ ? m [k x]%list_snoc_inv | ]%lex_list_invert.
    + intros ? ?; rewrite app_assoc; intros [ <- <- ]%app_inj_tail; constructor.
    + destruct m as [ | m z _ ] using rev_rect.
      * intros ? ?; rewrite app_nil_r; intros [ <- <- ]%app_inj_tail; now constructor.
      * intros ? ?; rewrite !app_assoc; intros [ <- <- ]%app_inj_tail; rewrite <- !app_assoc; now constructor.
  Qed.

  Lemma lex_list_snoc_inv l y m : lex_list l (m++[y]) → lex_list_snoc_inv_shape y l m.
  Proof. intros; eapply lex_list_snoc_inv_rec; eauto. Qed.

  Inductive lex_list_sg_inv_right_shape y : list X → Prop :=
    | in_lex_list_sg_inv_right_shape0 : lex_list_sg_inv_right_shape y []
    | in_lex_list_sg_inv_right_shape1 x l : R x y → lex_list_sg_inv_right_shape y (x::l).

  Lemma lex_list_sg_inv_right l y : lex_list l [y] → lex_list_sg_inv_right_shape y l.
  Proof.
    revert l; intros [ | x l ].
    + intros []%lex_list_inv; constructor.
    + intros [ | H%lex_list_inv ]%lex_list_inv; constructor; auto.
      now destruct l.
  Qed.

  Section lex_list_irrefl.

    Local Lemma ll_irrefl_rec l m : lex_list l m → l = m → ∃x, x ∈ l ∧ R x x.
    Proof.
      induction 1 as [ | | x l m H IH ]; try easy.
      * inversion 1; subst; eauto.
      * injection 1; intros (? & [])%IH; eauto.
    Qed.

    Lemma lex_list_irrefl l : lex_list l l → ∃x, x ∈ l ∧ R x x.
    Proof. intros ?%ll_irrefl_rec; auto. Qed.

  End lex_list_irrefl.

  Section lex_list_trans.

    Variables (l m k : list X)
              (Hlmk : ∀ x y z, x ∈ l → y ∈ m → z ∈ k → R x y → R y z → R x z).

    Lemma lex_list_trans : lex_list l m → lex_list m k → lex_list l k.
    Proof.
      intros H1 H2; revert H1 k H2 Hlmk.
      induction 1 as [ y m | x y l m H1 | x l m H1 IH1 ];
        intros [] Hk%lex_list_inv; destruct Hk; eauto.
      constructor 3; apply IH1; eauto.
    Qed.

  End lex_list_trans.

  Hint Constructors sdec : core.

  Section lex_list_sdec.

    Variables (l m : list X)
              (Hlm : ∀ x y, x ∈ l → y ∈ m → sdec R x y).

    Theorem lex_list_sdec : sdec lex_list l m.
    Proof.
      revert m Hlm.
      rename l into l'.
      induction l' as [ | x l IHl ]; intros [ | y m ] Hlm; eauto.
      destruct (Hlm x y); eauto.
      destruct (IHl m); eauto.
    Qed.

  End lex_list_sdec.

End lex_list.

#[local] Hint Constructors lex_list : core.

Fact lex_list_mono X R T l m : 
    (∀ x y, x ∈ l → y ∈ m → R x y → T x y)
  → @lex_list X R l m
  → @lex_list X T l m.
Proof. induction 2; eauto; constructor 3; eauto. Qed.

Fact Acc_lex_list_nil X P R : Acc (λ l m : list X, P l ∧ lex_list R l m) [].
Proof. constructor; intros _ (_ & []%lex_list_inv). Qed.

Section Acc_lex_list.

  Variables (X : Type) (R : X → X → Prop).

  Hint Constructors ordered_from ordered clos_refl_trans : core.

  Hint Resolve ordered_from_clos_trans clos_rt_t
               ordered_cons_inv transitive_clos_rt : core.

  (** On ordered list, the lexicographic ordering is included
      in the list_order *)

  Fact ordered_crt_lex_list_lo l m : ordered (clos_refl_trans R⁻¹) l → lex_list R l m → lo (clos_trans R) l m.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1 as [ x m | x y l m H1 | x l m H1 IH1 ]; intros H.
    + apply lo_app_tail with (l := [_]), lo_intro; now simpl.
    + apply lo_app_tail with (l := [_]), lo_intro.
      apply ordered_inv in H.
      intros z [ <- | Hz ]; auto.
      apply clos_rt_t with x; auto.
      apply clos_refl_trans_rev, transitive__clos_trans; eauto.
    + apply lo_cons; eauto.
  Qed.

  Hint Resolve ordered_crt_lex_list_lo
               ordered_from_crt_Acc : core.

  (* The proof of this lemma uses Acc for lo & the inclusion ordered_lex_list_lo 
     CAN WE PROVIDE A MORE DIRECT PROOF 

     After giving some though about this, I think we cannot implement
     a direct proof. Indeed, from this result, we can build the
     induction principle for ε₀ using elementary reasonning (ie
     which can be formalized in Heyting/Peano arithmetic), hence this
     would give a proof of this induction principle in PA which
     is impossible.

     The proof argument is simple BUT it require strong tools not
     available in PA. *)
  Lemma Acc_lex_list_ordered_from_crt x l :
      Acc R x
    → ordered_from (clos_refl_trans R⁻¹) x l
    → Acc (λ l m, ordered (clos_refl_trans R⁻¹) l ∧ lex_list R l m) l.
  Proof. 
    intros H1 H2.
    cut (Acc (lo (clos_trans R)) l).
    + apply Acc_incl.
      intros ? ? []; auto.
    + apply Acc_lo_iff.
      intros; apply Acc_clos_trans; eauto.
  Qed.

  Hint Resolve Acc_lex_list_ordered_from_crt
               Acc_lex_list_nil : core.

  Theorem Acc_lex_list_ordered_crt l :
      Forall (Acc R) l
    → ordered (clos_refl_trans R⁻¹) l
    → Acc (λ l m, ordered (clos_refl_trans R⁻¹) l ∧ lex_list R l m) l.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1; intros H2; auto.
    apply Forall_cons_iff in H2 as []; eauto.
  Qed.

End Acc_lex_list.
