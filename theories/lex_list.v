(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8 Arith Lia.
From Hydra Require Import hydra ordered.

Import ListNotations.

Set Implicit Arguments.

#[local] Infix "∈" := In (at level 70, no associativity).
#[local] Arguments clos_trans {_}.
#[local] Arguments clos_refl_trans {_}.
#[local] Arguments transitive {_}.

#[local] Hint Constructors clos_trans clos_refl_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro in_cons in_eq in_elt in_or_app : core.

Section clos_trans.

  Variables (X : Type).

  Implicit Type (R T : X → X → Prop).

  Hint Constructors clos_refl_trans : core.

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

End clos_trans.

Fact list_snoc_rect {X} (P : list X → Type) :
           P []
         → (∀ l x, P l → P (l++[x]))
         → ∀ l, P l.
Proof.
  intros H1 H2 l; revert P H1 H2.
  induction l as [ | x l IHl ]; auto.
  intros P H1 H2.
  apply (IHl (fun l => P (x::l))).
  + apply (H2 []), H1.
  + intros ? ?; apply (H2 (_::_)).
Qed.

Inductive list_snoc_inv_shape X : list X → Type :=
  | in_list_snoc_inv_shape l x : list_snoc_inv_shape (l++[x]).

Fact list_snoc_inv X (l : list X) : l ≠ [] → list_snoc_inv_shape l.
Proof.
  destruct l as [ | l x ] using list_snoc_rect.
  + now intros [].
  + intros; constructor.
Qed.

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
  Proof. rewrite (app_nil_end p) at 1; auto. Qed.

  Hint Resolve lex_list_prefix' : core.

  Fact lex_list_prefix p l : l <> [] → lex_list p (p++l).
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
       ↔ match l, m with 
         | _, []      => False
         | [], _      => True
         | x::l, y::m => lex_list_inv_shape l m y x
         end.
  Proof. 
    split.
    + intros []; eauto.
    + revert l m; intros [] [] []; eauto.
  Qed.

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

  Inductive lex_list_snoc_inv_shape_l x : list X → list X → Prop :=
    | in_lex_list_snoc_inv_shape0_l0 l a b r r' : R a b → lex_list_snoc_inv_shape_l x (l++[a]++r) (l++[b]++r')
    | in_lex_list_snoc_inv_shape0_l1 y l r : R x y → lex_list_snoc_inv_shape_l x l (l++[y]++r)
    | in_lex_list_snoc_inv_shape0_l2 l r : r ≠ [] → lex_list_snoc_inv_shape_l x l (l++[x]++r).

  Fact lex_list_snoc_inv_left_rec lx m : 
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
     -> (exists p a b q r, l = p++[a]++q /\ m = p++[b]++r /\ R a b)
     \/ (exists y r, m = l++[y]++r /\ R x y)
     \/ (exists r, m = l++[x]++r /\ r <> []).
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
    + intros ? ?; rewrite <- app_ass; intros [ <- <- ]%app_inj_tail; constructor.
    + destruct m as [ | m z _ ] using list_snoc_rect.
      * intros ? ?; rewrite <- app_nil_end; intros [ <- <- ]%app_inj_tail; now constructor.
      * intros ? ?; rewrite <- !app_ass; intros [ <- <- ]%app_inj_tail; rewrite !app_ass; now constructor.
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

    Let ll_irrefl_rec l m : lex_list l m → l = m → ∃x, x ∈ l ∧ R x x.
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

  Section lex_list_total.

    Variables (l m : list X)
              (Hlm : ∀ x y, x ∈ l → y ∈ m → sdec R x y).

    Theorem lex_list_sdec : sdec lex_list l m.
    Proof.
      revert m Hlm.
      rename l into l'.
      induction l' as [ | x l IHl ]; intros [ | y m ] Hlm; eauto.
      destruct (Hlm x y) as [ x y H | x | x y H ]; eauto.
      destruct (IHl m); eauto.
    Qed.

  End lex_list_total.

  Lemma lex_list_ge_length l m : 
           (∀ x y, x ∈ l → y ∈ m → ge R y x)
         → length l < length m
         → lex_list l m.
  Proof.
    revert m; induction l as [ | x l IHl ]; intros [ | y m ]; simpl; (lia || eauto).
    intros H0 H1.
    destruct (H0 x y) as [ -> | ? ]; eauto.
    constructor 3; apply IHl; (lia || eauto).
  Qed.

End lex_list.

Section mono.

  Hint Constructors lex_list : core.

  Variables (X : Type) (R T : X → X → Prop).

  Fact lex_list_mono l m : 
          (∀ x y, x ∈ l → y ∈ m → R x y → T x y)
        → lex_list R l m → lex_list T l m.
  Proof.
    intros H.
    induction 1 as [ | | x l m H1 IH1 ]; eauto.
    constructor 3; eauto.
  Qed.

  Fact lo_step_mono :
          (∀ x y, R x y → T x y)
        → (∀ l m, lo_step R l m → lo_step T l m).
  Proof. induction 2; constructor; eauto. Qed.

  Hint Resolve lo_step_mono : core.

  Fact lo_mono :
          (∀ x y, R x y → T x y)
        → (∀ l m, lo R l m → lo T l m).
  Proof. intro; apply clos_trans_mono; eauto. Qed.

End mono.

Section lex_list_sim.

  (* Simulation *)

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (sim : X → Y → Prop)
            (sim_fun : ∀ x y y', sim x y → sim x y' → y = y')
            (Hsim : ∀ x y x' y', sim x y → sim x' y' → R x x' → T y y').

  Hint Constructors lex_list : core.

  Theorem lex_list_sim l l' m m' :
            Forall2 sim l m
          → Forall2 sim l' m'
          → lex_list R l l'
          → lex_list T m m'.
  Proof.
    intros H1 H2 H3; revert H3 m m' H1 H2.
    induction 1 as [ x l' | x x' l l' | x l l' ];
      do 2 inversion 1; subst; eauto.
    match goal with |- lex_list _ (?a::_) (?b::_) => assert (a=b) as ->; eauto end.
  Qed.

End lex_list_sim. 


Fact Acc_lex_list_nil X P (R : X → X → Prop) : Acc (λ l m, P l ∧ lex_list R l m) [].
Proof. constructor; intros [] (? & []%lex_list_inv). Qed.

#[local] Hint Resolve Acc_lex_list_nil : core.

Section lex_list_wf.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Type (x : X).

  Hint Constructors ordered_from clos_refl_trans : core.

  Hint Resolve ordered_from_clos_trans
               clos_t_ge_rt clos_rt_t 
               ordered_cons_inv : core.

  Fact ordered_lex_list_lo l m : ordered (ge R) l → lex_list R l m → lo (clos_trans R) l m.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1 as [ x m | x y l m H1 | x l m H1 IH1 ]; intros H.
    + apply lo_app_tail with (l := [_]), lo_intro; now simpl.
    + apply lo_app_tail with (l := [_]), lo_intro.
      apply ordered_inv in H.
      intros ? [ <- | ]; eauto.
    + apply lo_cons; eauto.
  Qed.

  Hint Resolve ordered_lex_list_lo : core.

  Fact ordered_lex_list_lo_restr P l m : Forall P l → ordered (ge R) l → lex_list R l m → lo (λ x y, P x ∧ clos_trans R x y) l m.
  Proof.
    intros H0 H1 H2; revert H2 H1 H0.
    induction 1 as [ x m | x y l m H1 | x l m H1 IH1 ]; intros H2 H3.
    + apply lo_app_tail with (l := [_]), lo_intro; now simpl.
    + apply lo_app_tail with (l := [_]), lo_intro.
      apply ordered_inv in H2.
      apply Forall_cons_iff in H3 as [ H3 H4 ].
      rewrite Forall_forall in H4.
      intros ? [ <- | ]; split; eauto.
    + apply Forall_cons_iff in H3 as [].
      apply lo_cons; eauto.
  Qed.

  Hint Resolve ordered_from_ge_Acc : core.

  (* The proof of this lemma uses Acc for lo & the inclusion ordered_lex_list_lo 
     CAN WE PROVIDE A MORE DIRECT PROOF *)
  Lemma lex_list_Acc_ordered_from x l : Acc R x → ordered_from (ge R) x l → Acc (λ l m, ordered (ge R) l ∧ lex_list R l m) l.
  Proof. 
    intros H1 H2.
    cut (Acc (lo (clos_trans R)) l).
    + apply Acc_incl.
      intros ? ? []; auto.
    + apply Acc_lo_iff.
      intros y Hy.
      apply Acc_clos_trans; eauto.
  Qed.

  Hint Resolve ordered_lex_list_lo_restr : core.

  (*

  Lemma lex_list_Acc_ordered_from_restr P x l :
             Acc (λ x y, P x ∧ R x y) x
           → Forall P l
           → ordered_from (ge R) x l
           → Acc (λ l m, (Forall P l ∧ ordered (ge R) l) ∧ lex_list R l m) l.
  Proof.
    intros H1 H2 H3.
    cut (Acc (lo (λ x y, P x ∧ clos_trans R x y)) l).
    + apply Acc_incl.
      intros ? ? [[]]; eauto.
    + apply Acc_lo_iff.
      intros z Hz.
      cut (Acc (clos_trans (λ x y, P x ∧ R x y)) z).
      * apply Acc_incl.
 admit.
      * apply Acc_clos_trans.
        revert H1 z Hz. 
        apply ordered_from_ge_Acc.
        revert H3 H2.
        induction 1 as [ x | x y l H1 H2 IH2 ]; auto.
        intros []%Forall_cons_iff; constructor; eauto; tauto.
  Admitted.

  *)

  Theorem lex_list_Acc_ordered l : Forall (Acc R) l → ordered (ge R) l → Acc (λ l m, ordered (ge R) l ∧ lex_list R l m) l.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1 as [ | x l H1 ]; intros H2; auto.
    apply lex_list_Acc_ordered_from with x; eauto.
    eapply Forall_forall; eauto.
  Qed.
 
  (*

  Theorem lex_list_Acc_ordered_restr P l :
           Forall P l 
         → Forall (Acc (λ x y, P x ∧ R x y)) l 
         → ordered (ge R) l 
         → Acc (λ l m, (Forall P l ∧ ordered (ge R) l) ∧ lex_list R l m) l.
  Proof.
    intros H0 H1 H2; revert H2 H1 H0.
    induction 1 as [ | x l H1 ]; intros H2 H3; auto.
    apply lex_list_Acc_ordered_from_restr with x; eauto.
    eapply Forall_forall; eauto.
  Qed.

  *)

End lex_list_wf.
