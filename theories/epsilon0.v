(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.
From Hydra Require Import hydra.

Import ListNotations hydra_notations.

Set Implicit Arguments.

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.

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

Inductive sdec {X} (R : X → X → Prop) : X → X → Type :=
  | sdec_lt x y : R x y → sdec R x y
  | sdec_eq x : sdec R x x
  | sdec_gt x y : R y x → sdec R x y.

Definition dec (P : Prop) := {P} + {~P}. 

Section llt.

  Variables (X : Type) (R : X → X → Prop).

  Inductive ordered_from : X → list X → Prop :=
    | ordered_from_nil x : ordered_from x []
    | ordered_from_cons x y l : R x y → ordered_from y l → ordered_from x (y::l).

  Inductive ordered : list X → Prop :=
    | ordered_nil : ordered []
    | ordered_cons x l : ordered_from x l → ordered (x::l).

  Hint Constructors ordered_from ordered : core.

  Fact ordered_from_inv x y l : ordered_from x (y::l) → R x y ∧ ordered_from y l.
  Proof. inversion 1; auto. Qed.

  Fact ordered_inv x l : ordered (x::l) → ordered_from x l.
  Proof. now inversion 1. Qed.

  Fact ordered_from_ordered x l : ordered_from x l → ordered l.
  Proof. induction 1; eauto. Qed.

  Hint Resolve ordered_inv ordered_from_ordered : core.

  Fact ordered_cons_inv x l : ordered (x::l) → ordered l.
  Proof. eauto. Qed.

  Hint Constructors clos_trans : core.

  Fact ordered_from_clos_trans x l : ordered_from x l → ∀ y, y ∈ l → clos_trans R x y.
  Proof.
    induction 1 as [ | x y l H1 H2 IH2 ]; [ easy | ].
    intros ? [ <- | ? ]; eauto.
  Qed.

  Fact ordered_from_dec x l : 
        (∀ u v, u ∈ x::l → v ∈ x::l → { R u v } + { ~ R u v })
      → { ordered_from x l } + { ~ ordered_from x l }.
  Proof.
    revert x.
    induction l as [ | y l IHl ]; intros x H.
    + left; eauto.
    + destruct (H x y) as [ G | G ]; eauto.
      * destruct (IHl y) as [ F | F ]; eauto.
        right; contradict F; now inversion F.
      * right; contradict G; now inversion G.
  Qed.

  Fact ordered_dec l : 
        (∀ u v, u ∈ l → v ∈ l → { R u v } + { ~ R u v })
      → { ordered l } + { ~ ordered l }.
  Proof.
    destruct l as [ | x ].
    + left; eauto.
    + intros []%ordered_from_dec; [ left | right ]; eauto.
  Qed.

  Inductive llt : list X → list X → Prop :=
    | llt_nil x m : llt [] (x::m)
    | llt_lt x y l m : R x y → llt (x::l) (y::m)
    | llt_eq x l m : llt l m → llt (x::l) (x::m).

  Hint Constructors llt : core.

  Fact llt_inv l m :
         llt l m 
       ↔ match l, m with 
         | _, []      => False
         | [], _      => True
         | x::l, y::m => R x y ∨ x = y ∧ llt l m
         end.
  Proof. 
    split. 
    + intros []; eauto.
    + revert l m; intros [ | x l ] [ | y m ]; try easy.
      intros [ | [] ]; subst; eauto.
  Qed.

  Hint Constructors llt sdec : core.

  Section llt_total.

    Variables (l m : list X)
              (Hlm : ∀ x y, x ∈ l → y ∈ m → sdec R x y).

    Theorem llt_sdec : sdec llt l m.
    Proof.
      revert m Hlm.
      rename l into l'.
      induction l' as [ | x l IHl ]; intros [ | y m ] Hlm; eauto.
      destruct (Hlm x y) as [ x y H | x | x y H ]; eauto.
      destruct (IHl m); eauto.
    Qed.

  End llt_total.

  Section llt_irrefl.

    Let llt_irrefl_rec l m : llt l m → l = m → ∃x, x ∈ l ∧ R x x.
    Proof.
      induction 1 as [ | | x l m H IH ]; try easy.
      * inversion 1; subst; eauto.
      * injection 1; intros (? & ? & ?)%IH; eauto.
    Qed.

    Lemma llt_irrefl l : llt l l → ∃x, x ∈ l ∧ R x x.
    Proof. intros ?%llt_irrefl_rec; auto. Qed.

  End llt_irrefl.

  Section llt_trans.

    Variables (l m k : list X)
              (Hlmk : ∀ x y z, x ∈ l → y ∈ m → z ∈ k → R x y → R y z → R x z).

    Lemma llt_trans : llt l m → llt m k → llt l k.
    Proof.
      intros H; revert H k Hlmk.
      induction 1 as [ y m | x y l m H1 | x l m H1 IH1 ].
      + intros [ | z k ] H1 H2%llt_inv; [ easy | ]. 
        destruct H2 as [ | (<- & ?) ]; eauto.
      + intros [ | z k ] H2 H3%llt_inv; [ easy | ].
        destruct H3 as [ | (<- & ?) ]; eauto.
      + intros [ | z k ] H2 H3%llt_inv; [ easy | ].
        destruct H3 as [ | (<- & ?) ]; eauto.
        constructor 3.
        apply IH1; auto.
        intros ? ? ? ? ? ?; apply H2; eauto.
    Qed.

  End llt_trans.

End llt.

Fact Acc_llt_nil X P (R : X → X → Prop) : Acc (λ l m, P l ∧ llt R l m) [].
Proof. constructor; intros [] (? & []%llt_inv). Qed.

#[local] Hint Resolve Acc_llt_nil : core.

Notation ge R := (λ x y, x = y ∨ R y x).


Require Import Lia Arith.
Section llt_wf.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Type (x : X).

  Hint Constructors ordered_from : core.

  Inductive nprefix x n : list X -> Prop :=
    | nprefix_0 h : Forall (eq x) h -> length h = n -> nprefix x n h
    | nprefix_1 y h m : Forall (eq x) h -> length h = n -> R y x -> ordered_from (ge R) y m -> nprefix x n (h++m).

  Hint Constructors nprefix : core.

  Fact nprefix_S x n l : nprefix x n l -> nprefix x (S n) (x::l).
  Proof.
    intros [ h H1 H2 | y h m H1 H2 H3 ].
    + constructor 1; simpl; eauto.
    + constructor 2 with (y := y) (h := _::_); simpl; eauto.
  Qed.

  Hint Resolve nprefix_S : core.

  Fact ordered_from_nprefix x l : ordered_from (ge R) x l -> exists n, nprefix x n l.
  Proof.
    induction 1 as [ | x y l [ <- | H1 ] H2 (n & Hn) ].
    + exists 0; constructor 1; auto.
    + exists (S n).
      destruct Hn as [ l H3 H4 | y h m H3 H4 H5 H6 ].
      * constructor 1; simpl; auto.
      * constructor 2 with (h := _::_) (y := y); simpl; auto.
    + exists 0.
      destruct Hn as [ l H3 H4 | z h m H3 H4 H5 H6 ];
        constructor 2 with (y := y) (h := []); simpl; eauto.
  Qed.

  Fact ordered_from_ge_inv x l : ordered_from (ge R) x l -> Forall (eq x) l \/ exists y h m, R y x /\ l = h++m /\ Forall (eq x) h /\ ordered_from (ge R) y m.
  Proof.
    induction 1 as [ | x y l [ <- | H1 ] H2 IH2 ]; eauto.
    + destruct IH2 as [ ? | (y & h & m & ? & -> & ? & ?) ]; auto; right.
      exists y, (x::h), m; simpl; auto.
    + right; destruct IH2 as [ ? | (z & h & m & ? & -> & ? & ?) ].
      * exists y, [], (y::l); simpl; repeat split;eauto.
      * exists y, [], (y::h++m); repeat split; auto.
  Qed.

  Hint Resolve ordered_from_ordered : core.

  (* False : Counter-example ltt [3;1] [3;2] *)  
  Fact llt_nprefix_inv l m x n : 
              llt R l m -> nprefix x n m -> ordered (ge R) l -> (exists p, p < n /\ nprefix x p l) \/ exists y k, R y x /\ nprefix y k l.
  Proof.
    intros H1 H2; revert H2 H1.
    intros [ h H1 H2 | y h m' H1 H2 H3 ].
    + clear m. 
      intros H3; revert H3 x n H1 H2.
      induction 1 as [ y h | x y l m H1 | x l m H1 IH1 ]; intros z n G1 G2 G3.
      * left; exists 0; subst; simpl; split; auto; lia.
      * right; exists x.
        apply ordered_inv, ordered_from_nprefix in G3 as (k & Hk).
        apply Forall_cons_iff in G1 as [ -> G1 ].
        exists (S k); split; auto.
      * apply Forall_cons_iff in G1 as [ -> G1 ].
        apply ordered_inv in G3.
        destruct (IH1 _ _ G1 eq_refl)
          as [ (p & G4 & G5) | (y & k & G4 & G5) ]; eauto.
        - left; exists (S p); split; eauto.
          subst; simpl; lia.
  Admitted.

  Lemma llt_Acc_prefix x n l : Acc R x -> nprefix x n l -> Acc (λ l m, ordered (ge R) l ∧ llt R l m) l.
  Proof.
    intros H; revert H n l.
    induction 1 as [ x Hx IHx ].
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros m Hm; constructor; intros l (Hl & H).
    destruct (llt_nprefix_inv H Hm Hl) as [ (p & ? & ?) | (y & k & ? & ?) ]; eauto.
  Qed.

  Hint Resolve llt_Acc_prefix : core.

  (* This is the lemma we want to show but the proof is not going to work that way *)
  Lemma llt_Acc_ordered_from x l : Acc R x → ordered_from (ge R) x l → Acc (λ l m, ordered (ge R) l ∧ llt R l m) l.
  Proof. intros ? (? & ?)%ordered_from_nprefix; eauto. Qed.

  Hint Resolve llt_Acc_ordered_from : core.

  Theorem llt_Acc P l :
        Forall P l
     -> Forall (Acc (λ x y, P x ∧ R x y)) l 
     -> ordered (ge R) l 
     -> Acc (λ l m, Forall P l ∧ ordered (ge R) l ∧ llt R l m) l.
  Proof. Admitted.

End llt_wf.

Section epsilon0.

  Inductive olt : hydra → hydra → Prop :=
    | olt_intro l m : llt olt l m → olt ⟨l⟩ ⟨m⟩.

  Hint Constructors olt : core.

  Fact olt_inv l m : olt ⟨l⟩ ⟨m⟩ ↔ llt olt l m.
  Proof. split; auto; now inversion 1. Qed.

  Theorem olt_sdec g h : sdec olt g h.
  Proof.
    revert h; induction g as [ l IHg ]; intros [ m ].
    destruct (@llt_sdec _ olt l m) as [ l m H3 | l | l m H3 ]; eauto.
    + constructor 1; constructor; auto.
    + constructor 2.
    + constructor 3; constructor; auto.
  Qed.

  Theorem olt_irrefl h : ~ olt h h.
  Proof.
    induction h as [ l IH ].
    intros (g & G1 & G2)%olt_inv%llt_irrefl.
    now apply (IH _ G1).
  Qed.

  Theorem olt_trans f g h : olt f g → olt g h → olt f h.
  Proof.
    revert g h.
    induction f as [ l IHl ].
    intros [m] [k] H1%olt_inv H2%olt_inv.
    constructor; try tauto.
    revert H1 H2; apply llt_trans; eauto.
  Qed.

  Hint Resolve olt_trans olt_irrefl : core.

  Fact olt_dec g h : { olt g h } + { ~ olt g h }.
  Proof.
    destruct (olt_sdec g h) as [ g h H | h | g h H ].
    + now left.
    + now right.
    + right; intro G; eapply olt_irrefl; eauto.
  Qed.

  Corollary olt_trans' g h : clos_trans olt g h → olt g h.
  Proof. induction 1; eauto. Qed.

  Definition oge := λ g h, g = h ∨ olt h g.

  Fact oge_dec g h : { oge g h } + { ~ oge g h }.
  Proof.
    destruct (olt_sdec g h) as [ g h H | h | g h H ].
    + right; intros [<-|]; eapply olt_irrefl; eauto.
    + left; left; auto.
    + left; right; auto.
  Qed.

  Fact clos_trans_oge g h : clos_trans oge g h → g = h ∨ olt h g.
  Proof. induction 1 as [ ? ? [] | ? ? ? _ [] _ [] ]; subst; eauto. Qed.

  Definition E0 := hydra_fall (ordered oge).

  Fact E0_fix l : E0 ⟨l⟩ ↔ ordered oge l ∧ ∀x, x ∈ l → E0 x.
  Proof. apply hydra_fall_fix. Qed.

  Fact E0_rect (P : hydra → Type) :
          (∀l, ordered oge l 
             → (∀x, x ∈ l → E0 x)
             → (∀x, x ∈ l → P x)
             → P ⟨l⟩)
        → ∀h, E0 h → P h.
  Proof. apply hydra_fall_rect. Qed.

  Lemma olt_E0_wf h : E0 h → Acc (λ s t, E0 s ∧ olt s t) h.
  Proof.
    induction 1 as [ l H1 H2 IH2 ] using E0_rect.
    assert (Acc (λ l m, Forall E0 l /\ ordered oge l ∧ llt olt l m) l).
    + apply llt_Acc; auto; now apply Forall_forall.
    + clear H2 IH2; revert H H1.
      induction 1 as [ m Hm IHm ].
      constructor.
      intros [l] ((H2 & H3)%E0_fix & H4%olt_inv).
      apply IHm; auto.
      rewrite Forall_forall; auto.
  Qed.

  Hint Resolve oge_dec : core.

  Theorem E0_dec h : { E0 h } + { ~ E0 h }.
  Proof.
    induction h as [ l IH ].
    destruct (ordered_dec oge l) as [ H1 | H1 ]; eauto.
    2:{ right; intros []%E0_fix; eauto. }
    destruct list_fall_choose 
      with (P := fun h => ~ E0 h)
           (Q := E0) (l := l) 
      as [ (h & H2 & H3) | H ].
    + intros ? []%IH; auto.
    + right; intros []%E0_fix; apply H3; eauto.
    + left; apply E0_fix; auto.
  Qed. 

  Hint Resolve ordered_cons_inv : core.
  Hint Constructors clos_refl_trans : core.

  Lemma E0_olt_lpo g h : E0 g → E0 h → olt g h → lpo g h.
  Proof.
    intros H1 H2; revert g H1 h H2.
    induction 1 as [ l Hg1 Hg2 IHg ] using E0_rect.
    induction 1 as [ m Hh1 Hh2 _ ] using E0_rect.
    intros H%olt_inv.
    induction H as [ y m | x y l m | x l m H1 IH1 ].
    + constructor.
      apply lo_app_tail with (l := [_]).
      now apply lo_intro.
    + constructor.
      apply lo_app_tail with (l := [_]).
      apply lo_intro; auto.
      intros z [ <- | Hz ].
      1: apply IHg; eauto.
      apply ordered_inv in Hg1.
      apply IHg; eauto.
      apply olt_trans'.
      apply clos_rt_t with x; eauto.
      generalize (ordered_from_clos_trans Hg1 _ Hz).
      clear Hg2 IHg y m Hh1 Hh2 H l Hg1 Hz.
      induction 1 as [ x z [ <- | ] | ]; eauto.
    + constructor.
      apply lo_cons, lpo_inv.
      apply IH1; eauto.
  Qed.

  (* Since olt is maximal on E0 ... *)
  Corollary E0_lpo_olt g h : E0 g → E0 h → lpo g h → olt g h.
  Proof.
    intros Hg Hh H.
    destruct (olt_sdec g h) as [ g h G | g | g h G ]; auto.
    + contradict H; apply lpo_irrefl.
    + apply E0_olt_lpo in G; auto.
      destruct (@lpo_irrefl h).
      eapply lpo_trans; eauto.
  Qed.

  Hint Resolve E0_olt_lpo E0_lpo_olt : core.

  (** lpo and olt are IDENTICAL on E0 *)
  Theorem E0_olt_lpo_iff g h : E0 g → E0 h → olt g h ↔ lpo g h.
  Proof. split; auto. Qed.

  Definition power h := ⟨[h]⟩.

  Lemma olt_sons h : E0 h → match h with ⟨l⟩ => ∀g, g ∈ l → olt g h end. 
  Proof.
    induction 1 as [ m H1 H2 IH ] using E0_rect.
    intros [l] Hl.
    constructor.
    specialize (IH _ Hl); simpl in IH.
    destruct l as [ | x l ].
    + destruct m; [ easy | constructor ].
    + destruct m as [ | y m ]; [ easy | ].
      destruct Hl as [ -> | Hl ].
      * constructor 2; eauto.
      * apply ordered_inv in H1.
        apply ordered_from_clos_trans with (2 := Hl) in H1.
        apply clos_trans_oge in H1 as [ -> | H1 ].
        - constructor 2; auto.
        - constructor 2.
          apply olt_trans with (2 := H1); eauto.
  Qed.

  Fact E0_power h : E0 h → E0 (power h).
  Proof.
    intros; apply E0_fix; split.
    + repeat constructor.
    + now intros ? [ <- | [] ].
  Qed.

  Hint Resolve E0_power : core.
 
  Fact olt_power h : E0 h → olt h (power h).
  Proof. intro; apply (olt_sons (power h)); auto. Qed.

  Definition eps0 h := if E0_dec h then True else False.

  Fact eps0_iff h : eps0 h ↔ E0 h.
  Proof.
    unfold eps0.
    destruct (E0_dec h); tauto.
  Qed.

  Fact eps0_pirr h (E1 E2 : eps0 h) : E1 = E2.
  Proof.
    unfold eps0 in *.
    destruct (E0_dec h); [ | easy ].
    now destruct E1; destruct E2.
  Qed.

  Definition epsilon0 := sig eps0.

  Implicit Type (o : epsilon0). 

  Definition lt_epsilon0 o o' := olt (proj1_sig o) (proj1_sig o').

  Notation lt0 := lt_epsilon0.

  Theorem lt_epsilon0_sdec : ∀ o o', sdec lt0 o o'.
  Proof. 
    intros [g H1] [h H2].
    destruct (olt_sdec g h).
    + constructor 1; auto.
    + rewrite <- (eps0_pirr _ H1 H2); constructor 2.
    + constructor 3; auto.
  Qed.

  Theorem lt_epsilon0_irrefl o : ~ lt0 o o.
  Proof. destruct o; apply olt_irrefl. Qed.

  Theorem lt_epsilon0_trans o1 o2 o3 :
       lt0 o1 o2 → lt0 o2 o3 → lt0 o1 o3.
  Proof. revert o1 o2 o3; intros [] [] []; apply olt_trans. Qed.

  Theorem lt_epsilon0_wf : well_founded lt_epsilon0.
  Proof. 
    set (R o o' := lpo (proj1_sig o) (proj1_sig o')).
    cut (well_founded R).
    + apply wf_incl.
      intros [] []; unfold lt0, R; simpl.
      apply E0_olt_lpo; apply eps0_iff; auto.
    + unfold R; apply wf_inverse_image.
      exact wf_lpo.
   Qed.

End epsilon0.














 
