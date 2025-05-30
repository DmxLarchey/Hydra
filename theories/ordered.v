(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia List Relations Wellfounded Eqdep_dec Utf8.

Import ListNotations.

Set Implicit Arguments.

#[local] Infix "∈" := In (at level 70, no associativity).
#[local] Arguments clos_trans {_}.

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro in_cons in_eq in_elt in_or_app : core.

#[global] Notation ge R := (λ x y, x = y ∨ R y x).

#[global] Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.
Arguments transitive {_}.

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve in_cons in_eq in_elt in_or_app : core.

Fact clos_trans_rev X R x y : @clos_trans X R x y → clos_trans R⁻¹ y x. 
Proof. induction 1; eauto. Qed.

#[local] Hint Resolve clos_trans_rev : core.

Fact clos_trans_rev_iff X R x y : @clos_trans X R⁻¹ x y ↔ (clos_trans R)⁻¹ x y.
Proof. split; auto. Qed.

Fact transitive_rev X R : @transitive X R → transitive R⁻¹.
Proof. unfold transitive; eauto. Qed.

#[local] Hint Resolve transitive_rev : core.

Definition dec (P : Prop) := {P} + {~P}. 

Section sdec.

  Variables (X : Type)
            (R : X → X → Prop).

  Inductive sdec : X → X → Type :=
    | sdec_lt x y : R x y → sdec x y
    | sdec_eq x   :         sdec x x
    | sdec_gt x y : R y x → sdec x y.

  Inductive sdec_lt_inv_t {x y} : sdec x y → Prop := 
    | sdec_lt_inv_intro h : sdec_lt_inv_t (sdec_lt h).

  Inductive sdec_eq_inv_t {x} : sdec x x → Prop :=
    | sdec_eq_inv_intro : sdec_eq_inv_t (sdec_eq x).

  Inductive sdec_gt_inv_t {x y} : sdec x y → Prop := 
    | sdec_gt_inv_intro h : sdec_gt_inv_t (sdec_gt h).

  Hint Constructors sdec_lt_inv_t sdec_eq_inv_t sdec_gt_inv_t : core.

  Fact sdec_inv x y (s : sdec x y) :
    match s with
    | sdec_lt _ as s => sdec_lt_inv_t s
    | sdec_eq _ as s => sdec_eq_inv_t s
    | sdec_gt _ as s => sdec_gt_inv_t s
    end.
  Proof. destruct s; auto. Qed.

  Hypothesis (R_sdec : ∀ x y, sdec x y)
             (R_irrefl : ∀x, ¬ R x x).

  Fact sdec_eq_dec (x y : X) : { x = y } + { x ≠ y }.
  Proof.
    destruct (R_sdec x y); auto; right; intro; subst; eapply R_irrefl; eassumption.
  Qed.

  Fact sdec_uip (x : X) (h : x = x) : h = eq_refl. 
  Proof. apply UIP_dec, sdec_eq_dec. Qed.

  Local Fact sdec_eq_inv_dep {x y} (s : sdec x y) : ∀e, sdec_eq_inv_t (eq_rect y (sdec x) s x e).
  Proof.
    destruct s as [ x y H | | x y H ]; auto.
    1,3: intros <-; destruct (R_irrefl H).
    intros e; now rewrite (sdec_uip e).
  Qed.

  Theorem sdec_eq_inv x (s : sdec x x) : sdec_eq_inv_t s.
  Proof. exact (sdec_eq_inv_dep s eq_refl). Qed.

  Hypothesis (R_trans : transitive R).

  Theorem sdec_lt_inv x y (s : sdec x y) : R x y → sdec_lt_inv_t s.
  Proof.
    intros H; destruct s; eauto.
    + now apply R_irrefl in H.
    + destruct (@R_irrefl x); eauto.
  Qed.

  Theorem sdec_gt_inv x y (s : sdec x y) : R y x → sdec_gt_inv_t s.
  Proof.
    intros H; destruct s; eauto.
    + destruct (@R_irrefl x); eauto.
    + now apply R_irrefl in H.
  Qed.

End sdec.

Section ordered.

  Variables (X : Type).

  Implicit Type (R : X → X → Prop).

  Inductive ordered_from R : X → list X → Prop :=
    | ordered_from_nil x : ordered_from R x []
    | ordered_from_cons x y l : R x y → ordered_from R y l → ordered_from R x (y::l).

  Inductive ordered R : list X → Prop :=
    | ordered_nil : ordered R []
    | ordered_cons x l : ordered_from R x l → ordered R (x::l).

  Hint Constructors ordered_from ordered : core.

  Fact ordered_from_inv R x y l : ordered_from R x (y::l) → R x y ∧ ordered_from R y l.
  Proof. inversion 1; auto. Qed.

  Fact ordered_from_inv_iff R x y l : ordered_from R x (y::l) ↔ R x y ∧ ordered_from R y l.
  Proof. split; [ inversion 1 | intros []; constructor ]; auto. Qed.

  Fact ordered_inv_iff R x l : ordered R (x::l) ↔ ordered_from R x l.
  Proof. split; [ now inversion 1 | now constructor ]. Qed.

  Fact ordered_inv R x l : ordered R (x::l) → ordered_from R x l.
  Proof. now inversion 1. Qed.

  Fact ordered_from_ordered R x l : ordered_from R x l → ordered R l.
  Proof. induction 1; eauto. Qed.

  Hint Resolve ordered_inv ordered_from_ordered : core.

  Fact ordered_cons_inv R x l : ordered R (x::l) → ordered R l.
  Proof. eauto. Qed.

  Fact ordered_from_app_head R x l m : ordered_from R x (l++m) → ordered_from R x l.
  Proof. induction l in x |- *; simpl; eauto; intros []%ordered_from_inv; eauto. Qed.

  Fact ordered_from_app_tail R x l m : ordered_from R x (l++m) → ordered R m.
  Proof. induction l in x |- *; simpl; eauto. Qed.

  Hint Resolve ordered_from_app_head ordered_from_app_tail : core.

  Fact ordered_app_head R l m : ordered R (l++m) → ordered R l.
  Proof. destruct l; auto; simpl; intros ?%ordered_inv; eauto. Qed.

  Fact ordered_app_tail R l m : ordered R (l++m) → ordered R m.
  Proof. destruct l; simpl; auto; intros ?%ordered_inv; eauto. Qed.

  Fact ordered_from_comp R x l y m : ordered_from R x (l++[y]) → ordered_from R y m → ordered_from R x (l++[y]++m).
  Proof. induction l in x |- *; simpl; intros []%ordered_from_inv; eauto. Qed.

  Fact ordered_from_trans R x y l : transitive R → ordered_from R x l → R y x → ordered_from R y l.
  Proof. induction 2 in y |- *; eauto. Qed.

  Fact ordered_from_app_middle R l x m : 
       transitive R
     → ordered R l 
     → (∀y, y ∈ l → R y x ∨ y = x)
     → ordered_from R x m
     → ordered R (l++m).
  Proof.
    intros HR.
    induction 1 as [ | a l Hl ]; simpl; eauto.
    revert Hl x; induction 1 as [ a | a b l H1 H2 IH2 ]; intros x Hx H; simpl.
    + constructor.
      destruct (Hx a) as [ Ha | ]; subst; auto.
      revert Ha; apply ordered_from_trans; auto.
    + constructor.
      apply IH2 in H; eauto.
  Qed.

  Fact ordered_comp R l x m : ordered R (l++[x]) → ordered R (x::m) → ordered R (l++[x]++m).
  Proof.
    destruct l; simpl; auto; intros ?%ordered_inv ?%ordered_inv.
    now constructor; apply ordered_from_comp.
  Qed.

  Fact ordered_from_tail R x l y z : ordered_from R x (l++[y]) → (∀u, R u y → R u z) → ordered_from R x (l++[z]).
  Proof. induction l in x |- *; simpl; intros []%ordered_from_inv; constructor; eauto. Qed.

  Hint Resolve ordered_from_tail : core.

  Fact ordered_tail R l x y : ordered R (l++[x]) → (∀u, R u x → R u y) → ordered R (l++[y]).
  Proof. destruct l; simpl; eauto. Qed.

  Fact ordered_from_rev R x l : ordered_from R x l → ordered R⁻¹ (rev l++[x]).
  Proof.
    induction 1 as [ | x y l H _ IH ]; simpl; auto.
    rewrite <- app_assoc.
    apply ordered_comp with (m := [_]); auto.
  Qed.

  Hint Resolve ordered_from_rev : core.

  Fact ordered_rev R l : ordered R l → ordered R⁻¹ (rev l).
  Proof. induction 1; simpl; auto. Qed.

  Fact ordered_rev_iff R l : ordered R l ↔ ordered R⁻¹ (rev l).
  Proof.
    split.
    + apply ordered_rev.
    + intros ?%ordered_rev.
      now rewrite <- rev_involutive.
  Qed.

  Hint Constructors clos_trans : core.

  Fact ordered_from_clos_trans R x l : ordered_from R x l → ∀ y, y ∈ l → clos_trans R x y.
  Proof.
    induction 1 as [ | x y l H1 H2 IH2 ]; [ easy | ].
    intros ? [ <- | ? ]; eauto.
  Qed.

  Fact ordered_app_clos_trans R l m : ordered R (l++m) → ∀ x y, x ∈ l → y ∈ m → clos_trans R x y.
  Proof.
    destruct l as [ | x l ]; simpl.
    1: easy.
    intros H%ordered_inv; revert H.
    induction l in x |- *; simpl.
    + intros ? ? ? [ <- | [] ]; now apply ordered_from_clos_trans.
    + intros []%ordered_from_inv ? ? [ <- | ] ?; eauto.
  Qed.

  Fact ordered_from_dec R x l : 
        (∀ u v, u ∈ x::l → v ∈ x::l → { R u v } + { ~ R u v })
      → { ordered_from R x l } + { ~ ordered_from R x l }.
  Proof.
    revert x.
    induction l as [ | y l IHl ]; intros x H.
    + left; eauto.
    + destruct (H x y) as [ G | G ]; eauto.
      * destruct (IHl y) as [ F | F ]; eauto.
        right; contradict F; now inversion F.
      * right; contradict G; now inversion G.
  Qed.

  Fact ordered_dec R l : 
        (∀ u v, u ∈ l → v ∈ l → { R u v } + { ~ R u v })
      → { ordered R l } + { ~ ordered R l }.
  Proof.
    destruct l as [ | x ].
    + left; eauto.
    + intros []%ordered_from_dec; [ left | right ]; eauto.
  Qed.

End ordered.

Fact ordered_from_ge_Acc X R (x : X) l : ordered_from (ge R) x l → Acc R x → ∀y, y ∈ l → Acc R y.
Proof. induction 1 as [ | ? ? ? [ <- | ] ]; intros ? ? []; subst; eauto. Qed.

Fact ordered_mono_map X Y (f : X → Y) (R : X → X → Prop) (T : Y → Y → Prop) l :
         (∀ a b, a ∈ l → b ∈ l → R a b → T (f a) (f b))
        → ordered R l → ordered T (map f l).
Proof.
  intros H1 H2; revert H2 H1.
  induction 1 as [ | x l H1 ]; [ constructor | ].
  intros H2; simpl; constructor 2.
  revert H1 H2.
  induction 1 as [ x | x y l H1 IH1 ]; simpl; intros H2.
  + constructor 1.
  + constructor 2; auto.
Qed.

Fact ordered_map_iff X Y (f : X -> Y) R T :
         (∀ a b, R a b ↔ T (f a) (f b))
        → ∀l, ordered R l ↔ ordered T (map f l).
Proof.
  intros E l.
  destruct l as [ | x l ]; simpl.
  1: split; constructor.
  rewrite !ordered_inv_iff.
  induction l as [ | y l IHl ] in x |- *; simpl.
  1: split; constructor.
  now rewrite !ordered_from_inv_iff, E, IHl.
Qed.

Section mono.

  Hint Constructors ordered_from ordered : core.

  Variables (X : Type) (R T : X → X → Prop).

  Fact ordered_from_mono a l : 
          (∀ x y, x ∈ a::l → y ∈ a::l → R x y → T x y)
        → ordered_from R a l → ordered_from T a l.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1; intro; eauto.
    constructor 2; eauto.
  Qed.

  Hint Resolve ordered_from_mono : core.

  Fact ordered_mono l : 
          (∀ x y, x ∈ l → y ∈ l → R x y → T x y)
        → ordered R l → ordered T l.
  Proof. induction 2; eauto. Qed.

  Fact clos_trans_mono : 
          (∀ x y, R x y → T x y)
        → (∀ l m, clos_trans R l m → clos_trans T l m).
  Proof. induction 2; eauto. Qed.

End mono.

Section ordered_morphism.

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (f : X → Y → Prop).

  Fact ordered_from_morphism x l y m : 
      (∀ x₁ x₂ y₁ y₂, x₁ ∈ x::l → x₂ ∈ x::l → f x₁ y₁ → f x₂ y₂ → R x₁ x₂ → T y₁ y₂)
    → f x y 
    → Forall2 f l m
    → ordered_from R x l
    → ordered_from T y m. 
  Proof.
    intros f_morph H1 H2 H3; revert H3 y m H1 H2.
    induction 1.
    + inversion 2; constructor.
    + inversion 2; subst; constructor 2; eauto.
  Qed.

  Hint Resolve ordered_from_morphism : core.
 
  Fact ordered_morphism l m :
      (∀ x₁ x₂ y₁ y₂, x₁ ∈ l → x₂ ∈ l → f x₁ y₁ → f x₂ y₂ → R x₁ x₂ → T y₁ y₂)
    → Forall2 f l m
    → ordered R l
    → ordered T m.
  Proof. intros ? H; induction 1; inversion H; subst; constructor; eauto. Qed.

End ordered_morphism.

Section ordered_trans.

  Variables (X : Type) (R : X → X → Prop) (HR : transitive R).

  Local Fact transitive_clos_trans x y : clos_trans R x y → R x y.
  Proof. induction 1; eauto. Qed.

  Hint Resolve transitive_clos_trans
               ordered_from_ordered
               ordered_from_clos_trans : core.

  Fact ordered_cons_iff x l : ordered R (x::l) ↔ ordered R l ∧ ∀y, y ∈ l → R x y.
  Proof.
    split.
    + intros ?%ordered_inv; eauto.
    + intros (H1 & H2); constructor.
      induction H1; constructor; eauto.
  Qed.

  Fact ordered_app_iff l m : ordered R (l++m) ↔ ordered R l ∧ ordered R m ∧ ∀ x y, x ∈ l → y ∈ m → R x y.
  Proof.
    induction l as [ | x l IH ]; simpl; split; try tauto.
    + repeat split; tauto || constructor.
    + rewrite !ordered_cons_iff, IH; firstorder; subst; eauto.
    + rewrite !ordered_cons_iff, IH; intros ([] & ? & ?); repeat split; auto.
      intros ? []%in_app_iff; eauto.
  Qed.

  Fact ordered_snoc_iff x l : ordered R (l++[x]) ↔ ordered R l ∧ ∀y, y ∈ l → R y x.
  Proof.
    rewrite ordered_app_iff; split.
    + intros (? & _ & ?); eauto.
    + intros []; repeat split; eauto.
      * repeat constructor.
      * intros ? ? ? [ <- | [] ]; eauto.
  Qed.

End ordered_trans.

Definition lmax := fold_right max 0.

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

Section list_plus.

  Variables (X : Type) (R : X → X → Prop).

  Inductive list_plus_rel : list X → list X → list X → Prop :=
    | list_plus_rel_nil_l m : list_plus_rel [] m m
    | list_plus_rel_nil_r l : list_plus_rel l [] l
    | list_plus_rel_stop x y l m : R x y → list_plus_rel (x::l) (y::m) (y::m)
    | list_plus_rel_next x y l m k : ge R x y → list_plus_rel l (y::m) k → list_plus_rel (x::l) (y::m) (x::k).

  Hint Constructors list_plus_rel : core.

  Fact list_plus_rel_In l m k : list_plus_rel l m k → ∀x, x ∈ k → x ∈ l ∨ x ∈ m.
  Proof. 
    induction 1 as [ | | | w y l m k H1 H2 IH2 ]; eauto.
    intros ? [<- | []%IH2 ]; eauto.
  Qed.

  Fact list_plus_rel_nil_inv l m : list_plus_rel l m [] → l = [] ∧ m = [].
  Proof. now inversion 1. Qed.

  Section list_plus_fun.

    Hypothesis R_anti : ∀ x y, R x y → ge R x y → False.

    Fact list_plus_rel_fun l m k1 k2 : list_plus_rel l m k1 → list_plus_rel l m k2 → k1 = k2.
    Proof.
      intros H; revert H k2.
      induction 1; inversion 1; subst; eauto.
      3: f_equal; eauto.
      all: now destruct (@R_anti x y).
    Qed.

  End list_plus_fun.

  Hint Constructors ordered_from ordered : core.

  Section list_plus_ordered.

    (* Those two proofs need cleanup beacuse they are ugly *)

    Lemma list_plus_rel_ordered_from x l y m k : 
               ordered_from (ge R) x l
             → ordered_from (ge R) y m
             → list_plus_rel l (y::m) k
             → ge R x y
             → ordered_from (ge R) x k.
    Proof. intros H1 H2; induction H1 in k |- *; inversion 1; subst; eauto. Qed.

    Theorem list_plus_rel_ordered l m k : list_plus_rel l m k → ordered (ge R) l → ordered (ge R) m → ordered (ge R) k.
    Proof.
      intros H1 H2 H3.
      induction H3 as [ | y m H3 ].
      1: inversion H1; now subst.
      destruct H2 as [ | x l H2 ].
      1: inversion H1; now constructor.
      inversion H1; subst.
      1: now constructor.
      constructor.
      eapply list_plus_rel_ordered_from; eauto.
   Qed.

  End list_plus_ordered.

  Section list_plus_compute.

    Variables R_dec : ∀ x y, { R x y } + { ge R x y }.

    Definition list_plus_compute l m : sig (list_plus_rel l m).
    Proof.
      destruct m as [ | y ]; eauto.
      induction l as [ | x ]; eauto.
      destruct (R_dec x y); eauto.
      destruct IHl; eauto.
    Qed.

    Definition list_plus l m := proj1_sig (list_plus_compute l m).

    Fact list_plus_spec l m : list_plus_rel l m (list_plus l m).
    Proof. apply (proj2_sig _). Qed.

    Hint Resolve list_plus_spec list_plus_rel_fun : core.

    Fact list_plus_ordered l m : ordered (ge R) l → ordered (ge R) m → ordered (ge R) (list_plus l m).
    Proof. now apply list_plus_rel_ordered. Qed. 

    Hypothesis R_anti : ∀ x y, R x y → ge R x y → False.

    Fact list_plus_fix0 m : list_plus [] m = m.     Proof. eauto. Qed.
    Fact list_plus_fix1 l : list_plus l [] = l.     Proof. eauto. Qed.

    Fact list_plus_fix2 {x y l m} : R x y → list_plus (x::l) (y::m) = y::m.
    Proof. eauto. Qed.

    Fact list_plus_fix3 {x y l m} : ge R x y → list_plus (x::l) (y::m) = x::list_plus l (y::m).
    Proof. eauto. Qed.

    Fact list_plus_app_tail l m z k : 
              (∀x, x ∈ l → ge R x z)
            → list_plus l (m++[z]++k) = (list_plus l m)++[z]++k.
    Proof.
      intros Hl.
      destruct m as [ | y m ].
      + simpl; rewrite list_plus_fix1.
        revert Hl; rewrite <- Forall_forall.
        induction 1.
        * now rewrite list_plus_fix0.
        * rewrite list_plus_fix3; simpl; auto; f_equal; eauto.
      + clear Hl.
        induction l as [ | x ]; simpl.
        * now rewrite !list_plus_fix0.
        * destruct (R_dec x y).
          - rewrite !list_plus_fix2; auto.
          - rewrite !list_plus_fix3; auto; simpl; f_equal; auto.
    Qed.

    Hypothesis Rtrans : ∀ x y z, R x y → R y z → R x z.

    Lemma list_plus_assoc l m p : list_plus (list_plus l m) p = list_plus l (list_plus m p).
    Proof.
      destruct p as [ | z p ].
      1: now rewrite !list_plus_fix1.
      induction l as [ | x l IHl ] in m |- *.
      1: now rewrite !list_plus_fix0.
      destruct m as [ | y m ].
      1: now rewrite list_plus_fix0, list_plus_fix1.
      destruct (R_dec x y) as [ Hxy | Hxy ].
      + rewrite (list_plus_fix2 Hxy).
        destruct (R_dec y z) as [ Hyz | Hyz ].
        * rewrite !list_plus_fix2; eauto.
        * now rewrite (list_plus_fix3 Hyz), (list_plus_fix2 Hxy).
      + rewrite (list_plus_fix3 Hxy).
        destruct (R_dec x z) as [ Hxz | Hxz ].
        * rewrite (list_plus_fix2 Hxz).
          rewrite !list_plus_fix2; auto.
          destruct Hxy as [ <- | ]; eauto.
        * rewrite (list_plus_fix3 Hxz), IHl.
          destruct (R_dec y z) as [ Hyz | Hyz ].
          - rewrite (list_plus_fix2 Hyz), list_plus_fix3; auto.
          - now rewrite (list_plus_fix3 Hyz), (list_plus_fix3 Hxy).
    Qed.

    Fact list_plus_In l m x : x ∈ list_plus l m → x ∈ l ∨ x ∈ m.
    Proof. now apply list_plus_rel_In. Qed.

    Fact list_plus_cons_app l x m r : list_plus l (x::m++r) = list_plus l (x::m) ++ r.
    Proof.
      induction l as [ | y l IHl ].
      + now rewrite !list_plus_fix0.
      + destruct (R_dec y x) as [ H | H ].
        * rewrite !list_plus_fix2; auto.
        * rewrite !list_plus_fix3; simpl; auto; f_equal; auto.
    Qed.
 
    Fact list_search_choice m x : { l : _ & { r | m = l++r ∧ Forall (λ y, ge R y x) l ∧ match r with [] => True | y::_ => R y x end /\ forall k, list_plus r (x::k) = x::k } }.
    Proof.
      induction m as [ | y m IHm ].
      + exists [], []; simpl; repeat split; auto.
        intros; now rewrite list_plus_fix0.
      + destruct  (R_dec y x) as [ H | H ].
        * exists [], (y::m); simpl; repeat split; auto.
          intro; now rewrite list_plus_fix2.
        * destruct IHm as (l & r & -> & H2 & H3).
          exists (y::l), r; simpl; auto.
    Qed.

    Fact Forall_list_plus l r x m : Forall (λ y, ge R y x) l → list_plus (l++r) (x::m) = l++list_plus r (x::m).
    Proof. induction 1; simpl; auto; rewrite list_plus_fix3; f_equal; auto. Qed.

    Fact list_plus_nil_inv l m : list_plus l m = [] -> l = [] ∧ m = [].
    Proof. intros E; generalize (list_plus_spec l m); rewrite E; apply list_plus_rel_nil_inv. Qed.

(*
    Fact list_plus_snoc l m x : list_plus l (m++[x]) = (list_plus l m)++[x] 
                             \/ m = [] /\ exists l' y r', R y x /\ Forall (λ y, ge R y x) l' ∧ l = l'++[y]++r' /\ list_plus l [x] = l'++[x].
    Proof.
      destruct m; simpl.
      2: left; apply list_plus_cons_app.
      destruct (list_search_choice l x) as (l' & r' & -> & H1 & H2).
      destruct r' as [ | y r' ].
      + left; rewrite <- app_nil_end.
        rewrite (app_nil_end l') at 1.
        rewrite Forall_list_plus, list_plus_fix0, list_plus_fix1; auto.
      + right; split; auto.
        exists l', y, r'; repeat split; auto.
        rewrite Forall_list_plus; auto.
        now rewrite list_plus_fix2.
    Qed.

    Fact list_plus_special m l :
              (forall k, list_plus m (l++k) = list_plus (m++l) k)
           \/ exists m1 x m2 y l', l = y::l' /\ m = m1++[x]++m2 /\ Forall (λ x, ge R x y) m1 /\ R x y.
    Proof.
      destruct l as [ | y l ].
      1: left; rewrite <- app_nil_end; auto.
      destruct (list_search_choice m y) as (m1 & [ | x m2 ] & G1 & G2 & G3).
      + subst m.

 left; intro. 
        rewrite app_ass; simpl.
        rewrite Forall_list_plus, list_plus_fix0; auto.
        rewrite 
rewrite <- app_nil_end.
        intros; simpl. rewrite Forall_list_plus.
*)

  End list_plus_compute.

End list_plus.

Check list_plus_ordered.

Arguments list_plus {_ _}.

