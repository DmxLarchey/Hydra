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
Arguments transitive {_}.

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.

Definition iter {X} (f : X → X) :=
  fix loop n x := match n with 0 => x | S n => loop n (f x) end.

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

Notation ge R := (λ x y, x = y ∨ R y x).

Section clos_trans.

  Variables (X : Type).

  Implicit Type (R : X → X → Prop).

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

End clos_trans.

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

Section list_sig.

  Variables (X : Type) (P : X → Prop).

  Implicit Type (l : list (sig P)).

  Fact list_sig_proj1 l : ∀x, x ∈ map (@proj1_sig _ _) l → P x.
  Proof.
    induction l as [ | [] ]; simpl; [ easy | ].
    intros ? [ <- | ]; eauto.
  Qed.

  Definition list_sig_list l : { m | ∀x, x ∈ m → P x }.
  Proof.
    exists (map (@proj1_sig _ _) l).
    apply list_sig_proj1.
  Defined.

  Fact list_forall_reif m : (∀x, x ∈ m → P x) → { l : list (sig P)| m = map (@proj1_sig _ _) l }.
  Proof.
    induction m as [ | x m IHm ]; intros Hm.
    + exists []; auto.
    + destruct IHm as (l & Hl); eauto.
      eexists ((exist _ x _)::l); eauto.
      simpl; f_equal; auto.
      Unshelve.
      eauto.
  Qed.

End list_sig.

Inductive sdec {X} (R : X → X → Prop) : X → X → Type :=
  | sdec_lt x y : R x y → sdec R x y
  | sdec_eq x : sdec R x x
  | sdec_gt x y : R y x → sdec R x y.

Definition dec (P : Prop) := {P} + {~P}. 

Section ordered.

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

  Fact ordered_from_inv_iff x y l : ordered_from x (y::l) ↔ R x y ∧ ordered_from y l.
  Proof. split; [ inversion 1 | intros []; constructor ]; auto. Qed.

  Fact ordered_inv_iff x l : ordered (x::l) ↔ ordered_from x l.
  Proof. split; [ now inversion 1 | now constructor ]. Qed.

  Fact ordered_inv x l : ordered (x::l) → ordered_from x l.
  Proof. now inversion 1. Qed.

  Fact ordered_from_ordered x l : ordered_from x l → ordered l.
  Proof. induction 1; eauto. Qed.

  Hint Resolve ordered_inv ordered_from_ordered : core.

  Fact ordered_cons_inv x l : ordered (x::l) → ordered l.
  Proof. eauto. Qed.

  Fact ordered_from_app_head x l m : ordered_from x (l++m) → ordered_from x l.
  Proof.
    induction l as [ | y l IHl ] in x |- *; simpl; eauto.
    intros []%ordered_from_inv; eauto.
  Qed.

  Fact ordered_from_app_tail x l m : ordered_from x (l++m) → ordered m.
  Proof. induction l in x |- *; simpl; eauto. Qed.

  Hint Resolve ordered_from_app_head ordered_from_app_tail : core.

  Fact ordered_from_comp x l y m : ordered_from x (l++[y]) → ordered_from y m → ordered_from x (l++[y]++m).
  Proof. induction l in x |- *; simpl; intros []%ordered_from_inv; eauto. Qed.

  Fact ordered_from_tail x l y z : ordered_from x (l++[y]) → (∀u, R u y → R u z) → ordered_from x (l++[z]).
  Proof. induction l in x |- *; simpl; intros []%ordered_from_inv; constructor; eauto. Qed.

  Fact ordered_app_head l m : ordered (l++m) → ordered l.
  Proof.
    destruct l; auto; simpl.
    intros ?%ordered_inv; eauto.
  Qed.

  Fact ordered_app_tail l m : ordered (l++m) → ordered m.
  Proof.
    destruct l; simpl; auto.
    intros ?%ordered_inv; eauto.
  Qed.

  Fact ordered_comp l x m : ordered (l++[x]) → ordered (x::m) → ordered (l++[x]++m).
  Proof.
    destruct l; simpl; auto; intros ?%ordered_inv ?%ordered_inv.
    now constructor; apply ordered_from_comp.
  Qed.

  Hint Resolve ordered_from_tail : core.

  Fact ordered_tail l x y : ordered (l++[x]) → (∀u, R u x → R u y) → ordered (l++[y]).
  Proof. destruct l; simpl; eauto. Qed.

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

End ordered.

Fact ordered_from_ge_Acc X R (x : X) l : ordered_from (ge R) x l → Acc R x → ∀y, y ∈ l → Acc R y.
Proof. induction 1 as [ | ? ? ? [ <- | ] ]; intros ? ? []; subst; eauto. Qed.

Fact ordered_map X Y (f : X -> Y) R T :
         (forall a b, R a b <-> T (f a) (f b))
      -> forall l, ordered R l <-> ordered T (map f l).
Proof.
  intros E l.
  destruct l as [ | x l ]; simpl.
  1: split; constructor.
  rewrite !ordered_inv_iff.
  induction l as [ | y l IHl ] in x |- *; simpl.
  1: split; constructor.
  now rewrite !ordered_from_inv_iff, E, IHl.
Qed.

Section repeat.

  Variables (X : Type) (x : X).

  Definition repeat :=
    fix loop n := match n with 0 => [] | S n => x::loop n end.

  Fact repeat_add a b : repeat (a+b) = repeat a++repeat b.
  Proof. induction a; simpl; f_equal; auto. Qed.

  Fact repeat_S n : repeat (S n) = repeat n++[x].
  Proof. now rewrite <- PeanoNat.Nat.add_1_r, repeat_add. Qed.

  Fact In_repeat n y : y ∈ repeat n → x = y.
  Proof. induction n; simpl; intros []; auto. Qed.

  Fact ordered_repeat R n : ordered (ge R) (repeat n).
  Proof.
    destruct n as [ | n ]; simpl; constructor.
    induction n; simpl; constructor; eauto.
  Qed.

End repeat.

Section lex_list.

  Variables (X : Type) (R : X → X → Prop).

  (* lexicographic order on lists, head is most significant *)
  Inductive lex_list : list X → list X → Prop :=
    | lex_list_nil x m : lex_list [] (x::m)
    | lex_list_lt x y l m : R x y → lex_list (x::l) (y::m)
    | lex_list_eq x l m : lex_list l m → lex_list (x::l) (x::m).

  Hint Constructors lex_list : core.

  Fact lex_list_inv l m :
         lex_list l m 
       ↔ match l, m with 
         | _, []      => False
         | [], _      => True
         | x::l, y::m => R x y ∨ x = y ∧ lex_list l m
         end.
  Proof. 
    split. 
    + intros []; eauto.
    + revert l m; intros [ | x l ] [ | y m ]; try easy.
      intros [ | [] ]; subst; eauto.
  Qed.

  Hint Constructors sdec : core.

  Lemma lex_list_invert l m :
         lex_list l m 
       → (∃k, k ≠ [] ∧ m = l++k)
       ∨ (∃ c x y p q, l = c++[x]++p ∧ m = c++[y]++q ∧ R x y).
  Proof.
    induction 1 as [ x m | x y l m H | z l m _ [ (k & ? & ?) | (c & x & y & p & q & -> & -> & ?) ] ].
    + left; now exists (x::m).
    + right; now exists [], x, y, l, m.
    + left; exists k; now subst.
    + right; now exists (z::c), x, y, p, q.
  Qed.

  Fact lex_list_app_head c l m : lex_list l m → lex_list (c++l) (c++m).
  Proof. induction c; simpl; eauto. Qed.

  Fact lex_list_prefix p l : l <> [] → lex_list p (p++l).
  Proof. 
    destruct l; [ easy | intros _ ].
    rewrite (app_nil_end p) at 1.
    apply lex_list_app_head; auto.
  Qed.

  Fact lex_list_snoc h l : lex_list l (l++[h]).
  Proof. now apply lex_list_prefix. Qed.

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

  Section lex_list_irrefl.

    Let ll_irrefl_rec l m : lex_list l m → l = m → ∃x, x ∈ l ∧ R x x.
    Proof.
      induction 1 as [ | | x l m H IH ]; try easy.
      * inversion 1; subst; eauto.
      * injection 1; intros (? & ? & ?)%IH; eauto.
    Qed.

    Lemma lex_list_irrefl l : lex_list l l → ∃x, x ∈ l ∧ R x x.
    Proof. intros ?%ll_irrefl_rec; auto. Qed.

  End lex_list_irrefl.

  Section lex_list_trans.

    Variables (l m k : list X)
              (Hlmk : ∀ x y z, x ∈ l → y ∈ m → z ∈ k → R x y → R y z → R x z).

    Lemma lex_list_trans : lex_list l m → lex_list m k → lex_list l k.
    Proof.
      intros H; revert H k Hlmk.
      induction 1 as [ y m | x y l m H1 | x l m H1 IH1 ].
      + intros [ | z k ] H1 H2%lex_list_inv; [ easy | ]. 
        destruct H2 as [ | (<- & ?) ]; eauto.
      + intros [ | z k ] H2 H3%lex_list_inv; [ easy | ].
        destruct H3 as [ | (<- & ?) ]; eauto.
      + intros [ | z k ] H2 H3%lex_list_inv; [ easy | ].
        destruct H3 as [ | (<- & ?) ]; eauto.
        constructor 3.
        apply IH1; auto.
        intros ? ? ? ? ? ?; apply H2; eauto.
    Qed.

  End lex_list_trans.

End lex_list.

Fact Acc_lex_list_nil X P (R : X → X → Prop) : Acc (λ l m, P l ∧ lex_list R l m) [].
Proof. constructor; intros [] (? & []%lex_list_inv). Qed.

#[local] Hint Resolve Acc_lex_list_nil : core.

Section lex_list_sim.

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

Section mono.

  Hint Constructors ordered_from ordered : core.

  Fact ordered_from_mono X (R T : X → X → Prop) a l : 
          (∀ x y, x ∈ a::l → y ∈ a::l → R x y → T x y)
        → ordered_from R a l → ordered_from T a l.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1; intro; eauto.
    constructor 2; eauto.
  Qed.

  Hint Resolve ordered_from_mono : core.

  Fact ordered_mono X (R T : X → X → Prop) l : 
          (∀ x y, x ∈ l → y ∈ l → R x y → T x y)
        → ordered R l → ordered T l.
  Proof. induction 2; eauto. Qed.

  Hint Constructors lex_list : core.
  Hint Resolve in_or_app in_eq in_cons : core.

  Fact lex_list_mono X (R T : X → X → Prop) l m : 
          (∀ x y, x ∈ l → y ∈ m → R x y → T x y)
        → lex_list R l m → lex_list T l m.
  Proof.
    intros H.
    induction 1 as [ | | x l m H1 IH1 ]; eauto.
    constructor 3; eauto.
  Qed.

  Fact clos_trans_mono X (R T : X → X → Prop) : 
          (∀ x y, R x y → T x y)
        → (∀ l m, clos_trans R l m → clos_trans T l m).
  Proof. induction 2; eauto. Qed.

  Fact lo_step_mono X (R T : X → X → Prop) :
          (∀ x y, R x y → T x y)
        → (∀ l m, lo_step R l m → lo_step T l m).
  Proof. induction 2; constructor; eauto. Qed.

  Hint Resolve lo_step_mono : core.

  Fact lo_mono X (R T : X → X → Prop) :
          (∀ x y, R x y → T x y)
        → (∀ l m, lo R l m → lo T l m).
  Proof. intro; apply clos_trans_mono; eauto. Qed.

End mono.

Section epsilon0.

  Inductive olt : hydra → hydra → Prop :=
    | olt_intro l m : lex_list olt l m → olt ⟨l⟩ ⟨m⟩.

  Hint Constructors olt : core.

  Fact olt_inv l m : olt ⟨l⟩ ⟨m⟩ ↔ lex_list olt l m.
  Proof. split; auto; now inversion 1. Qed.

  Theorem olt_sdec g h : sdec olt g h.
  Proof.
    revert h; induction g as [ l IHg ]; intros [ m ].
    destruct (@lex_list_sdec _ olt l m) as [ l m H3 | l | l m H3 ]; eauto.
    + constructor 1; constructor; auto.
    + constructor 2.
    + constructor 3; constructor; auto.
  Qed.

  Theorem olt_irrefl h : ~ olt h h.
  Proof.
    induction h as [ l IH ].
    intros (g & G1 & G2)%olt_inv%lex_list_irrefl.
    now apply (IH _ G1).
  Qed.

  Hint Resolve lex_list_trans : core.

  Theorem olt_trans : transitive olt.
  Proof.
    intros f; induction f.
    intros [] [] ?%olt_inv ?%olt_inv; eauto.
  Qed.

  Hint Resolve olt_trans olt_irrefl : core.

  Fact olt_dec g h : { olt g h } + { ~ olt g h }.
  Proof.
    destruct (olt_sdec g h); eauto.
    right; intro; eapply olt_irrefl; eauto.
  Qed.

  Corollary olt_trans' g h : clos_trans olt g h → olt g h.
  Proof. induction 1; eauto. Qed.

  Definition oge := ge olt.

  Fact oge_dec g h : { oge g h } + { ~ oge g h }.
  Proof.
    destruct (olt_sdec g h) as [ g h H | h | g h H ].
    + right; intros [<-|]; eapply olt_irrefl; eauto.
    + left; left; auto.
    + left; right; auto.
  Qed.

  Definition E0 := hydra_fall (ordered oge).

  Fact E0_fix l : E0 ⟨l⟩ ↔ ordered oge l ∧ ∀x, x ∈ l → E0 x.
  Proof. apply hydra_fall_fix. Qed.

  Hint Resolve oge_dec : core.

  (* E0 is a strongly decidable predicate *)
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

  (* We convert E0 into an equivalent proof irrelevant predicate *)
  Definition eps0 h := squash (E0_dec h).
  Fact eps0_iff h : eps0 h ↔ E0 h.              Proof. apply squash_iff. Qed.
  Fact eps0_pirr h (e1 e2 : eps0 h) : e1 = e2.  Proof. apply squash_pirr. Qed.

  (* Now we work with eps0 instead of E0 *)

  (* We convert the fixpoint equation *)
  Fact eps0_fix l : eps0 ⟨l⟩ ↔ ordered oge l ∧ ∀x, x ∈ l → eps0 x.
  Proof.
    rewrite eps0_iff, E0_fix.
    split; intros []; split; auto; intros; apply eps0_iff; auto.
  Qed.

  (* We convert the recursor *)
  Fact eps0_rect (P : hydra → Type) :
          (∀l, ordered oge l 
             → (∀x, x ∈ l → eps0 x)
             → (∀x, x ∈ l → P x)
             → P ⟨l⟩)
        → ∀h, eps0 h → P h.
  Proof. 
    intros HP h H%eps0_iff; revert h H.
    induction 1 as [ l H1 H2 IH ]using hydra_fall_rect.
    apply HP; auto.
    intros; apply eps0_iff, H2; auto.
  Qed.

  (*

  (* This proof relies on llt_Acc_ordered_restr which is not proved yet
     There is completed an indirect proof below *)
  Lemma olt_eps0_wf h : eps0 h → Acc (λ s t, eps0 s ∧ olt s t) h.
  Proof.
    induction 1 as [ l H1 H2 IH2 ] using eps0_rect.
    assert (Acc (λ l m, (Forall eps0 l ∧ ordered oge l) ∧ lex_list olt l m) l).
    + apply lex_list_Acc_ordered_restr; auto; now apply Forall_forall.
    + clear H2 IH2; revert H H1.
      induction 1 as [ m Hm IHm ].
      constructor.
      intros [l] ((H2 & H3)%eps0_fix & H4%olt_inv).
      apply IHm; auto.
      rewrite Forall_forall; auto.
  Qed.

  *)

  Hint Resolve ordered_cons_inv lpo_trans : core.
  Hint Constructors clos_refl_trans : core.

  Local Fact lpo_trans' l m : clos_trans lpo l m → lpo l m.
  Proof. induction 1; eauto. Qed.

  Hint Resolve lex_list_mono : core.

  Lemma eps0_olt_lpo g h : eps0 g → eps0 h → olt g h → lpo g h.
  Proof.
    intros H1 H2; revert g H1 h H2.
    induction 1 as [ l Hg1 Hg2 IHg ] using eps0_rect.
    intros [m] [Hh1 Hh2]%eps0_fix H%olt_inv. 
    constructor.
    apply lo_mono with (1 := lpo_trans').
    apply ordered_lex_list_lo; eauto.
    apply ordered_mono with (2 := Hg1).
    intros ? ? ? ? []; eauto.
  Qed.

  (* Since olt is maximal on eps0 ... *)
  Corollary eps0_lpo_olt g h : eps0 g → eps0 h → lpo g h → olt g h.
  Proof.
    intros Hg Hh H.
    destruct (olt_sdec g h) as [ g h G | g | g h G ]; auto.
    + contradict H; apply lpo_irrefl.
    + apply eps0_olt_lpo in G; auto.
      destruct (@lpo_irrefl h); eauto.
  Qed.

  Hint Resolve eps0_olt_lpo eps0_lpo_olt : core.

  (** lpo and olt are IDENTICAL on eps0 *)
  Theorem E0_olt_lpo_iff g h : eps0 g → eps0 h → olt g h ↔ lpo g h.
  Proof. split; auto. Qed.

  Definition power h := ⟨[h]⟩.

  Lemma olt_sons h :
             eps0 h
           → match h with
             | ⟨l⟩ => ∀g, g ∈ l → olt g h
             end. 
  Proof.
    induction 1 as [ m H1 H2 IH ] using eps0_rect.
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
        apply clos_trans_ge in H1 as [ -> | H1 ]; auto.
        - constructor 2; auto.
        - constructor 2.
          apply olt_trans with (2 := H1); eauto.
  Qed.

  Fact eps0_power h : eps0 h → eps0 (power h).
  Proof.
    intros; apply eps0_fix; split.
    + repeat constructor.
    + now intros ? [ <- | [] ].
  Qed.

  Hint Resolve eps0_power : core.
 
  Fact olt_power h : eps0 h → olt h (power h).
  Proof. intro; apply (olt_sons (power h)); auto. Qed.

  Definition hydra_succ h := 
    match h with
    | ⟨l⟩ => ⟨l++[⨸]⟩
    end.

  Hint Constructors ordered_from ordered : core.

  Fact eps0_zero : eps0 ⨸.
  Proof. apply eps0_fix; split; eauto; easy. Qed.

  Fact zero_smallest h : oge h ⨸.
  Proof.
    destruct h as [ [ | x l ] ]; [ left | right ]; auto.
    do 2 constructor.
  Qed.

  Hint Resolve eps0_zero zero_smallest : core.

  Fact zero_smallest' h : ~ olt h ⨸.
  Proof.
    destruct (zero_smallest h) as [ <- | H ].
    + apply olt_irrefl.
    + intro; eapply olt_irrefl, olt_trans; eauto.
  Qed.

  Fact ordered_snoc_zero l : ordered oge l → ordered oge l⊣⊢[⨸].
  Proof.
    induction 1 as [ | x l H ]; simpl; eauto.
    constructor.
    induction H; simpl; eauto.
  Qed.

  Hint Resolve ordered_snoc_zero : core.

  Fact eps0_hydra_succ h : eps0 h → eps0 (hydra_succ h).
  Proof.
    revert h; intros [l]; simpl.
    rewrite !eps0_fix.
    intros [H1 H2]; split; auto.
    intros ? [ | [<- | []]]%in_app_iff; auto.
  Qed.

  Hint Resolve ordered_app_head : core.

  Fact eps0_rem_tail l h : eps0 ⟨l++[h]⟩ → eps0 ⟨l⟩.
  Proof. rewrite !eps0_fix; intros []; split; eauto. Qed.

  Fact oge_zero_dec h : { h = ⨸ } + { olt ⨸ h }.
  Proof.
    destruct h as [ [] ]; auto.
    right; do 2 constructor.
  Qed.

  Hint Resolve lex_list_prefix lex_list_snoc : core.

  Lemma lex_list_olt_tail l m x y :
           olt x y 
         → ordered oge m⊣⊢[y]
         → lex_list olt l m⊣⊢[y]
         → lex_list olt l⊣⊢[x] m⊣⊢[y].
  Proof.
    intros H1 H2 [ (q & H5 & H6) | (c & u & v & p & q & -> & H6 & H7) ]%lex_list_invert.
    + destruct q as [ | q z _ ] using list_snoc_rect; [ easy | clear H5 ].
      rewrite <- app_ass in H6.
      apply app_inj_tail in H6 as (-> & <-).
      rewrite app_ass in H2 |- *. 
      apply lex_list_app_head.
      apply ordered_app_tail in H2.
      destruct q as [ | z q ]; constructor 2; auto.
      simpl in H2; apply ordered_inv in H2.
      apply olt_trans'.
      apply clos_t_rt with y; eauto.
      apply clos_t_ge_rt.
      eapply ordered_from_clos_trans; eauto.
    + rewrite H6, !app_ass.
      apply lex_list_app_head.
      now constructor 2.
  Qed.

  Lemma olt_inv_snoc_right g m h : 
           olt g ⟨m++[h]⟩ 
        → (∃ c x y p q, olt x y ∧ g = ⟨c++[x]++p⟩ ∧ m = c++[y]++q)
        ∨ (∃ x p, olt x h ∧ g = ⟨m++[x]++p⟩)
        ∨ (∃ p q, g = ⟨p⟩ ∧ m = p++q).
  Proof.
    destruct g as [l]; intros [(k & H1 & H2)| (c & x & y & p & q & H1 & H2 & H3)]%olt_inv%lex_list_invert.
    + destruct k as [ | k y _ ] using list_snoc_rect; [ easy | clear H1 ].
      rewrite <- app_ass in H2.
      apply app_inj_tail in H2 as (-> & <-).
      right; eauto.
    + destruct q as [ | q z _ ] using list_snoc_rect.
      * rewrite <- app_nil_end in H2.
        apply app_inj_tail in H2 as (<- & <-); subst l.
        right; left; eauto.
      * rewrite <- !app_ass in H2.
        apply app_inj_tail in H2 as (H2 & <-).
        rewrite app_ass in H2; subst.
        left; exists c, x, y, p, q; auto.
   Qed.

  Corollary olt_succ_inv g l : olt g ⟨l++[⨸]⟩ → g = ⟨l⟩ ∨ olt g ⟨l⟩.
  Proof.
    intros [ (c & x & y & p & q & H1 & H2 & H3) 
        |[ (x & p & H1 & H2)
         | (p & q & H1 & H2) ] ]%olt_inv_snoc_right.
    + subst; right; constructor.
      apply lex_list_app_head; constructor 2; auto.
    + now apply zero_smallest' in H1.
    + subst; destruct q; [ left | right ].
      * now rewrite <- app_nil_end.
      * constructor.
        now apply lex_list_prefix.
  Qed.

  Lemma olt_inv_single_right g h : 
          olt g ⟨[h]⟩ 
        → g = ⨸ ∨ ∃ x p, olt x h ∧ g = ⟨[x]++p⟩.
  Proof.
    intros H.
    apply olt_inv_snoc_right with (m := []) in H
      as [ (c & x & y & p & q & _ & _ & H) 
        |[ (x & p & H1 & H2)
         | (p & q & H1 & H2) ] ].
    + now destruct c.
    + subst; right; simpl; eauto.
    + left; subst; now destruct p.
  Qed.

  (** Every ordinal is either a successor, 
      or a limit, ie forall x < lim, succ x < lim *)

  Theorem eps0_zero_succ_or_limit h : eps0 h → (h = ⨸) + { l | h = ⟨l++[⨸]⟩ } + { l : _ & { g | h = ⟨l++[g]⟩ /\ olt ⨸ g } }.
  Proof.
    destruct 1 as [ l H1 H2 _ ] using eps0_rect.
    destruct l as [ | l h _ ] using list_snoc_rect; eauto.
    destruct (oge_zero_dec h) as [ -> | Hm ]; eauto.
  Qed.

  Definition eps0_limit h := ∀p, eps0 p → olt p h → olt (hydra_succ p) h.
 
  Fact eps0_limit_zero : eps0_limit ⨸.
  Proof. intros ? _ []%zero_smallest'. Qed.

  Fact eps0_limit_tail l h : eps0 ⟨l++[h]⟩ → olt ⨸ h → eps0_limit ⟨l++[h]⟩.
  Proof.
    intros [H1 H2]%eps0_fix H3 [g] H4 H5%olt_inv.
    constructor.
    apply lex_list_olt_tail; auto.
  Qed.

  Hint Resolve ordered_app_head eps0_limit_zero eps0_limit_tail : core.

  Fact eps0_succ_not_limit l : eps0 ⟨l⟩ → ~ eps0_limit ⟨l⊣⊢[⨸]⟩.
  Proof.
    intros H1 H2.
    destruct (@olt_irrefl ⟨l⊣⊢[⨸]⟩).
    apply H2 with (p := ⟨l⟩); auto.
  Qed.

  Fact eps0_limit_iff h : eps0 h → eps0_limit h → h ≠ ⨸ → { l : _ & { g | h = ⟨l++[g]⟩ /\ olt ⨸ g } }.
  Proof.
    intros H1 H2 H3.
    destruct (eps0_zero_succ_or_limit _ H1) as [ [ -> | (l & ->) ] | ? ]; auto; try easy.
    apply eps0_succ_not_limit in H2 as []. 
    revert H1; rewrite !eps0_fix; intros []; split; eauto.
  Qed.

  Theorem succ_or_limit h : eps0 h → { p | eps0 p ∧ h = hydra_succ p } + { eps0_limit h }.
  Proof.
    intros H.
    destruct (eps0_zero_succ_or_limit _ H) as [ [ -> | (l & ->) ] | (l & g & -> & ?) ]; eauto.
    left; exists ⟨l⟩; split; auto.
    rewrite eps0_fix in H |- *.
    destruct H; split; eauto.
  Qed.

  (* We want to build the fundamental sequence according to the Weiner hierarchy *)

  Inductive fseq : hydra → nat → hydra → Prop :=
    | fseq_0 l n : fseq ⟨[⟨l++[⨸]⟩]⟩ n ⟨repeat ⟨l⟩ n⟩
    | fseq_1 l h n g : olt ⨸ h → fseq ⟨l++[h]⟩ n g → fseq ⟨[⟨l++[h]⟩]⟩ n ⟨[g]⟩
    | fseq_2 l h n g : l ≠ [] → fseq ⟨[h]⟩ n ⟨g⟩ → fseq ⟨l++[h]⟩ n ⟨l++g⟩.

  Lemma fseq_eps0 h n g : eps0 h → fseq h n g → eps0 g ∧ olt g h.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1 as [ l n | l h n g H1 H2 IH2 | l h n g H1 H2 IH2 ]; intros [H3 H4]%eps0_fix.
    + rewrite eps0_fix; split; [ split | ].
      * apply ordered_repeat.
      * intros ? <-%In_repeat.
        specialize (H4 _ (or_introl eq_refl)).
        apply eps0_fix in H4 as [].
        apply eps0_fix; split; eauto.
      * simpl; constructor.
        destruct n as [ | n]; simpl.
        - constructor.
        - constructor 2; constructor; eauto.
    + destruct IH2 as (H5 & H6); eauto.
      rewrite eps0_fix; split; [ split | ].
      * repeat constructor.
      * intros ? [ <- | [] ]; auto.
      * constructor.
        now constructor 2.
    + destruct IH2 as (H5 & H6); eauto.
      1: apply eps0_fix; split; eauto.
      apply olt_inv in H6.
      apply eps0_fix in H5 as [ H5 H7 ].
      rewrite eps0_fix; split; [ split | ].
      * destruct g as [ | x g ].
        - rewrite <- app_nil_end; eauto.
        - apply ordered_comp; auto.
          eapply ordered_tail; eauto.
          apply lex_list_inv in H6
            as [ H6 | (_ & ?%lex_list_inv) ].
          2: now destruct g.
          intros u [ <- | ? ]; right; eauto.
      * intros ? [ ]%in_app_iff; eauto.
      * constructor; apply lex_list_app_head; auto.
  Qed.

  Fact fseq_inv h n g :
         fseq h n g → (∃ l, h = ⟨[⟨l++[⨸]⟩]⟩ ∧ g = ⟨repeat ⟨l⟩ n⟩)
                    ∨ (∃ l h' g', h = ⟨[⟨l++[h']⟩]⟩ ∧ g = ⟨[g']⟩ ∧ olt ⨸ h' ∧ fseq ⟨l++[h']⟩ n g')
                    ∨ (∃ l h' g', h = ⟨l++[h']⟩ ∧ g = ⟨l++g'⟩ ∧ l ≠ [] ∧ fseq ⟨[h']⟩ n ⟨g'⟩).
  Proof. 
    induction 1 as [ | l h n g H1 H2 _ | l h n g H1 H2 _ ]; eauto.
    + right; left; exists l, h, g; eauto.
    + right; right; exists l, h, g; eauto.
  Qed.

  Fact fseq_zero_inv l n g : fseq ⟨[⟨l++[⨸]⟩]⟩ n g → g = ⟨repeat ⟨l⟩ n⟩.
  Proof.
    intros [(l' & E1 & E2) | [ (l' & h' & g' & E1 & E2 & H1 & H2) | (l' & h' & g' & E1 & E2 & H1 & H2) ] ]%fseq_inv.
    + now apply hydra_cons_inj, cons_inj in E1 as ((-> & _)%hydra_cons_inj%app_inj_tail & _).
    + apply hydra_cons_inj, cons_inj in E1 as ((-> & <-)%hydra_cons_inj%app_inj_tail & _).
      exfalso; revert H1; apply olt_irrefl.
    + now apply hydra_cons_inj, (app_inj_tail []) in E1 as (<- & <-).
  Qed.

  Fact fseq_olt_inv l h n g : olt ⨸ h → fseq ⟨[⟨l++[h]⟩]⟩ n g → ∃g', g = ⟨[g']⟩ ∧ fseq ⟨l++[h]⟩ n g'.
  Proof.
    intros H0 [(l' & E1 & E2) | [ (l' & h' & g' & E1 & E2 & H1 & H2) | (l' & h' & g' & E1 & E2 & H1 & H2) ] ]%fseq_inv.
    + apply hydra_cons_inj, cons_inj in E1 as ((-> & ->)%hydra_cons_inj%app_inj_tail & _).
      exfalso; revert H0; apply olt_irrefl.
    + exists g'; split; auto.
      now apply hydra_cons_inj, cons_inj in E1 as ((-> & ->)%hydra_cons_inj%app_inj_tail & _).
    + now apply hydra_cons_inj, (app_inj_tail []) in E1 as (<- & _).
  Qed.

  Fact fseq_seq_inv l h n g : l ≠ [] → fseq ⟨l++[h]⟩ n g → ∃g', g = ⟨l++g'⟩ ∧ fseq ⟨[h]⟩ n ⟨g'⟩.
  Proof.
    intros H0 [(l' & E1 & E2) | [ (l' & h' & g' & E1 & E2 & H1 & H2) | (l' & h' & g' & E1 & E2 & H1 & H2) ] ]%fseq_inv.
    1,2: now apply hydra_cons_inj, (app_inj_tail _ []) in E1 as (-> & _).
    apply hydra_cons_inj, app_inj_tail in E1 as (<- & <-); eauto.
  Qed.

  Lemma fseq_fun h n g1 g2 : fseq h n g1 → fseq h n g2 → g1 = g2.
  Proof.
    intros H1; revert H1 g2.
    induction 1 as [ l n | l h n g H1 H2 IH2 | l h n g H1 H2 IH2 ].
    + now intros ? ->%fseq_zero_inv.
    + intros ? (g' & -> & ?)%fseq_olt_inv; auto.
      do 2 f_equal; eauto.
    + intros ? (g' & -> & ->%IH2%hydra_cons_inj)%fseq_seq_inv; auto.
  Qed.

  (* The "set" P intersects ]g,h[ for any g < h, ie P is as close
     to h as one could wish *)
  Definition is_limit (P : hydra → Prop) h :=
    forall g, eps0 g → olt g h → exists u, P u ∧ olt g u ∧ olt u h.

  Lemma olt_repeat_snoc l n h : olt ⟨repeat ⟨l⟩ n⟩ ⟨[⟨l++[h]⟩]⟩.
  Proof. 
    constructor; destruct n as [ | n ]; simpl.
    + constructor.
    + constructor 2; constructor; auto.
  Qed.

  Fact ordered_from_oge_olt x l y : oge y x -> ordered_from oge x l -> olt ⟨x::l⟩ ⟨repeat y (2+length l)⟩.
  Proof.
    intros [ -> | H ] G; constructor; revert G.
    + induction 1 as [ | x y l [ <- | H ] ]; simpl.
      * constructor 3; constructor.
      * constructor 3; auto.
      * constructor 3; constructor 2; auto.
    + constructor 2; auto.
  Qed.

  Hint Resolve olt_repeat_snoc : core. 

(*
  Lemma is_limit_repeat l : ordered oge l → is_limit (fun u => exists n, u = ⟨repeat ⟨l⟩ n⟩) ⟨[⟨l++[⨸]⟩]⟩.
  Proof.
    intros ol h.
    induction 1 as [ m E1 E2 _ ] using eps0_rect.
    intros [(k & H1 & H2)| (c & x & y & p & q & H1 & H2 & H3)]%olt_inv%lex_list_invert.
    + destruct k as [ | k g _ ] using list_snoc_rect; [ easy | clear H1 ].
      rewrite <- app_ass in H2.
      apply app_inj_tail with (x := []) in H2 as (H2 & <-).
      destruct m; [ | easy ]; simpl in H2; subst.
      exists ⟨repeat ⟨l⟩ 1⟩; repeat split; eauto; simpl; repeat constructor; auto.
    + destruct c as [ | ? [ | ? [] ] ]; try easy.
      apply cons_inj in H2 as (<- & <-); simpl in H1; subst m.
      destruct x as [m].
      apply olt_inv in H3 as [(q & H3 & H4)|(c & x & y & u & v & H4 & H5 & H6)]%lex_list_invert.
      * destruct q as [ | q g _ ] using list_snoc_rect; [ easy | clear H3 ].
        rewrite <- app_ass in H4.
        apply app_inj_tail in H4 as (-> & <-).
        apply ordered_inv in E1.
        exists ⟨repeat ⟨m++q⟩ (2+length p)⟩; split; eauto.
        split; auto.
        apply ordered_from_oge_olt; auto.
        destruct q; [ left | right ].
        1: now rewrite <- app_nil_end.
        constructor; auto.
        now apply lex_list_prefix.
      * destruct v as [ | v' ? _ ] using list_snoc_rect.
        - rewrite <- app_nil_end in H5.
          apply app_inj_tail in H5 as (<- & <-); subst.
          apply zero_smallest' in H6 as [].
        - rewrite <- !app_ass in H5.
          apply app_inj_tail in H5 as (H5 & <-).
          rewrite app_ass in H5.
          exists ⟨repeat ⟨l⟩ 1⟩; split; eauto. 
          split; auto; simpl.
          constructor; constructor 2; subst.
          constructor; apply lex_list_app_head.
          constructor 2; auto.
  Qed.

  *)

  Definition epsilon0 := sig eps0.

  Implicit Type (o : epsilon0).

  Hint Resolve eps0_pirr : core.

  (* This result in the main reason why we use 
     the proof irrelevant eps0 instead of E0 *)
  Fact epsilon0_eq_iff o o' : o = o' ↔ proj1_sig o = proj1_sig o'.
  Proof.
    split.
    + now intros <-.
    + revert o o'; intros [] [] ?; simpl in *; subst; f_equal; auto.
  Qed.

  Definition lt_epsilon0 o o' := olt (proj1_sig o) (proj1_sig o').

  Notation lt0 := lt_epsilon0.

  Theorem lt_epsilon0_sdec : ∀ o o', sdec lt0 o o'.
  Proof. 
    intros [g Hg] [h Hh].
    destruct (olt_sdec g h).
    + constructor 1; auto.
    + rewrite <- (eps0_pirr _ Hg Hh); constructor 2.
    + constructor 3; auto.
  Qed.

  Theorem lt_epsilon0_irrefl o : ~ lt0 o o.
  Proof. destruct o; apply olt_irrefl. Qed.

  Theorem lt_epsilon0_trans : transitive lt0.
  Proof. intros [] [] []; apply olt_trans. Qed.

  Theorem lt_epsilon0_wf : well_founded lt_epsilon0.
  Proof. 
    set (R o o' := lpo (proj1_sig o) (proj1_sig o')).
    cut (well_founded R).
    + apply wf_incl.
      intros [] []; unfold lt0, R; simpl.
      apply eps0_olt_lpo; auto.
    + unfold R; apply wf_inverse_image.
      exact wf_lpo.
  Qed.

  (* Transfinite induction principle for epsilon0 *)
  Definition epsilon0_trans_rect (P : epsilon0 → Type) :
              (∀o, (∀o', lt0 o' o → P o') → P o)
             → ∀o, P o.
  Proof. exact (well_founded_induction_type lt_epsilon0_wf P). Qed.

  Section eps0_trans_rect.

    Variables (P : hydra → Type)
              (HP : ∀h, eps0 h → (∀g, eps0 g → olt g h → P g) → P h).

    Let Q o := P (proj1_sig o).
    Let HQ o : Q o.
    Proof.
      induction o as [ [ h e ] IH ] using epsilon0_trans_rect;
        unfold Q; simpl.
      apply HP; auto.
      intros g H ?.
      apply (IH (exist _ g H)); auto.
    Qed.

    Theorem eps0_trans_rect h : eps0 h → P h.
    Proof. intros H; apply (HQ (exist _ _ H)). Qed.

  End eps0_trans_rect.

  Section fseq_special_rect.

    (* This induction principle follow the computational path of
       fseq, see below *)

    Variables (P : hydra → Type)
              (HP0 : ∀ l, eps0 ⟨l⊣⊢[⨸]⟩ → P ⟨[⟨l⊣⊢[⨸]⟩]⟩)
              (HP1 : ∀ l h, eps0 ⟨l⊣⊢[h]⟩ → olt ⨸ h → P ⟨l⊣⊢[h]⟩ → P ⟨[⟨l⊣⊢[h]⟩]⟩)
              (HP2 : ∀ l h, eps0 ⟨l⊣⊢[h]⟩ → olt ⨸ h → l ≠ [] → P ⟨[h]⟩ → P ⟨l⊣⊢[h]⟩).

    Lemma fseq_special_rect h : eps0 h → h ≠ ⨸ → eps0_limit h → P h.
    Proof.
      induction 1 as [ [l] H1 IH ] using eps0_trans_rect; intros H2 H3.
      destruct (eps0_limit_iff H1 H3 H2) as (m & h & H4 & H5).
      inversion H4; subst l; clear H4.
      destruct (list_nil_choose m) as [ -> | Hm ]; simpl.
      + destruct h as [ l ].
        destruct l as [ | l h _ ] using list_snoc_rect.
        * apply olt_irrefl in H5 as [].
        * destruct (oge_zero_dec h) as [ -> | H6 ].
          - apply HP0.
            simpl in H1; apply eps0_fix in H1 as []; eauto.
          - simpl in H1; apply eps0_fix in H1 as []; eauto.
            apply HP1; eauto.
            apply IH; eauto.
            ++ simpl in *; auto.
               apply olt_power; auto.
            ++ intros ?%hydra_cons_inj; now destruct l.
      + apply HP2; eauto.
        apply eps0_fix in H1 as (H1 & H4).
        apply IH; eauto.
        * apply eps0_fix; auto.
        * constructor.
          destruct m as [ | x m ]; [ easy | ].
          simpl in H1; apply ordered_inv in H1.
          assert (oge x h) as [ -> | H ].
          1:{ apply clos_trans_ge; auto.
              apply (ordered_from_clos_trans H1); eauto. }
          - simpl; constructor 3.
            destruct m; now constructor 1.
          - now constructor 2.
        * easy.
        * apply eps0_limit_tail with (l := []); simpl; auto.
          apply eps0_fix; split; eauto.
    Qed.

  End fseq_special_rect.

  Local Lemma compute_fseq h n : eps0 h → h ≠ ⨸ → eps0_limit h → sig (fseq h n).
  Proof.
    revert h; apply fseq_special_rect.
    + intros l ?; exists ⟨repeat ⟨l⟩ n⟩; constructor.
    + intros ? ? ? ? (g & ?); exists ⟨[g]⟩; now constructor.
    + intros l ? ? ? ? ([g] & ?); exists ⟨l++g⟩; constructor; auto.
  Qed.

  (* The fundamental sequence of a limit ordinal has this ordinal 
     as an accumulation point for the order topology (generated by open intervals) *) 
  Theorem is_limit_fseq h : eps0 h → h ≠ ⨸ → eps0_limit h → is_limit (λ g, ∃n, fseq h n g) h.
  Proof.
    revert h; apply fseq_special_rect.
    + intros l Hl h H1 H2.
      apply olt_inv_single_right in H2 as [ -> | (g & m & H2 & ->) ].
      * exists ⟨repeat ⟨l⟩ 1⟩; split; [ | split; auto ].
        - exists 1; constructor.
        - simpl; repeat constructor.
      * apply olt_succ_inv in H2 as [ -> | H2 ].
        - exists ⟨repeat ⟨l⟩ (2+length m)⟩; split; [ | split; auto ].
          ++ exists (2+length m); constructor.
          ++ apply ordered_from_oge_olt.
             ** left; auto.
             ** now apply eps0_fix in H1 as (H1%ordered_inv & _).
        - exists ⟨repeat ⟨l⟩ 1⟩; split; [ | split; auto ].
          ++ exists 1; constructor.
          ++ simpl; repeat constructor; auto.
    + intros l h H1 H2 H3 g G1 G2.
      apply olt_inv_single_right in G2 as [ -> | (k & m & G2 & ->) ].
      * destruct (H3 ⨸) as (g & (n & Eg) & E2 & E3); eauto.
        - constructor; destruct l; constructor.
        - exists ⟨[g]⟩; repeat split.
          ++ exists n; constructor 2; auto.
          ++ constructor.
          ++ constructor 2; auto.
      * destruct H3 with (2 := G2) as (g & (n & Eg) & E2 & E3); eauto.
        - apply eps0_fix in G1 as []; eauto.
        - exists ⟨[g]⟩; repeat split.
          ++ exists n; constructor; auto.
          ++ constructor 2; auto.
          ++ constructor 2; auto.
    + intros l h H1 H2 H3 H4 g G1 G2.
      apply olt_inv_snoc_right in G2
       as [ (c & x & y & p & q & G2 & G3 & G4)
         |[ (x & p & G2 & ->) 
          | (p & q & -> & ->) ] ].
      * destruct (H4 ⨸) as ([k] & (n & En) & E2 & E3); eauto.
        - repeat constructor.
        - exists ⟨l⊣⊢k⟩; repeat split.
          ++ exists n; constructor; auto.
          ++ subst; constructor.
             rewrite !app_ass.
             apply lex_list_app_head; constructor 2; auto.
          ++ apply olt_inv in E3.
             now apply lex_list_app_head.
      * destruct (H4 ⟨[x]++p⟩) as ([k] & (n & En) & E2 & E3); eauto.
        - apply eps0_fix in G1 as [G1 G3]; apply eps0_fix; split; eauto.
          eapply ordered_app_tail; eauto.
        - constructor; constructor 2; auto.
        - exists ⟨l⊣⊢k⟩; repeat split.
          ** exists n; constructor; auto.
          ** apply lex_list_app_head.
             now apply olt_inv in E2.
          ** apply lex_list_app_head.
             now apply olt_inv in E3.
      * destruct (H4 ⨸) as ([k] & (n & En) & E2 & E3); eauto.
        - apply olt_trans with (1 := H2), olt_power.
          apply eps0_fix in H1 as []; eauto.
        - exists ⟨(p⊣⊢q)⊣⊢k⟩; split; [ | split ].
          ** exists n; constructor; auto.
          ** constructor.
             rewrite app_ass, (app_nil_end p) at 1.
             apply lex_list_app_head.
             apply olt_inv in E2.
             destruct q; auto; constructor.
          ** constructor.
             apply olt_inv in E3.
             apply lex_list_app_head; eauto.
  Qed.

  Lemma fseq_S_olt h n g g': h ≠ ⨸ → fseq h n g → fseq h (S n) g' → olt g g'.
  Proof.
    intros _ H2; revert H2 g'.
    induction 1 as [ l n | l h n g H1 H2 IH2 | l h n g H1 H2 IH2 ]; intros g'.
    + intros ->%fseq_zero_inv.
      constructor.
      rewrite repeat_S.
      now apply lex_list_prefix.
    + intros (g'' & -> & H%IH2)%fseq_olt_inv; auto.
      now constructor; constructor 2.
    + intros (g'' & -> & H%IH2%olt_inv)%fseq_seq_inv; auto.
      constructor.
      now apply lex_list_app_head.
  Qed.

  Section fund_seq.

    Variables (h : hydra) (n : nat)
              (e1 : eps0 h)
              (e2 : h ≠ ⨸)
              (e3 : eps0_limit h).

    Definition fund_seq := proj1_sig (compute_fseq n e1 e2 e3).

    Local Fact fund_seq_spec : fseq h n fund_seq.
    Proof. apply (proj2_sig _). Qed.

    Fact fund_seq_eps0 : eps0 fund_seq.
    Proof. now apply fseq_eps0 with (2 := fund_seq_spec). Qed.

    Fact fund_seq_olt : olt fund_seq h.
    Proof. now apply fseq_eps0 with (2 := fund_seq_spec). Qed.

  End fund_seq.

  Arguments fund_seq : clear implicits.

  Fact fund_seq_pirr h n e1 f1 e2 f2 e3 f3 :
           fund_seq h n e1 e2 e3
         = fund_seq h n f1 f2 f3.
  Proof. apply fseq_fun with h n; apply fund_seq_spec. Qed.

  Fact fund_sec_olt_inc h n e1 e2 e3 :
         olt (fund_seq h n e1 e2 e3) (fund_seq h (S n) e1 e2 e3).
  Proof. apply fseq_S_olt with h n; auto; apply fund_seq_spec. Qed.

  Fact fund_sec_olt_converges h e1 e2 e3 g :
        eps0 g 
      → olt g h 
      → ∃n, olt g (fund_seq h n e1 e2 e3) 
          ∧ olt (fund_seq h n e1 e2 e3) h.
  Proof.
    intros H1 H2.
    destruct (is_limit_fseq e1 e2 e3 H1 H2)
      as (k & (n & Gn) & G2 & G3).
    exists n.
    now rewrite <- (fseq_fun Gn (fund_seq_spec _ e1 e2 e3)).
  Qed.

  (* The values of the fundemental sequence are proof irrelevant *)
  Check fund_seq_pirr.
  (* The fundemental sequence is composed of ordinals *)
  Check fund_seq_eps0.
  (* The fundemental sequence for h is strictly bounded by h *)
  Check fund_seq_olt.
  (* The fundemental sequence is strictly increasing wrt olt *)
  Check fund_sec_olt_inc.
  (* The fundemental sequence is converging to h *)
  Check fund_sec_olt_converges.

  (* If one needs the fixpoint equations *)

  Fact fund_seq_fix_0 l n e1 e2 e3 :
        fund_seq ⟨[⟨l++[⨸]⟩]⟩ n e1 e2 e3 = ⟨repeat ⟨l⟩ n⟩.
  Proof.
    apply fseq_fun with (1 := fund_seq_spec _ _ _ _); constructor.
  Qed.

  Fact fund_seq_fix_1 l h n e1 e2 e3 f1 f2 f3 :
         olt ⨸ h
       → fund_seq ⟨[⟨l++[h]⟩]⟩ n e1 e2 e3 = ⟨[fund_seq ⟨l++[h]⟩ n f1 f2 f3]⟩.
  Proof.
    intros H; apply fseq_fun with (1 := fund_seq_spec _ _ _ _); constructor; auto.
    apply fund_seq_spec.
  Qed.

  Fact fund_seq_fix_2 l h n e1 e2 e3 f1 f2 f3 :
         l ≠ []
       → fund_seq ⟨l++[h]⟩ n e1 e2 e3 = ⟨l++hydra_sons (fund_seq ⟨[h]⟩ n f1 f2 f3)⟩.
  Proof.
    intros H; apply fseq_fun with (1 := fund_seq_spec _ _ _ _).
    case_eq (fund_seq ⟨[h]⟩ n f1 f2 f3); intros g Hg; simpl.
    constructor 3; auto.
    rewrite <- Hg.
    apply fund_seq_spec.
  Qed.

  Section eps0_wainer_rect.

    (** An induction principle for limit ordinals
        using the Wainer fundemental sequence *)

    Variables (P : hydra → Type)
              (HP0 : P ⨸)
              (HPS : ∀l, eps0 ⟨l⟩ → P ⟨l⟩ → P ⟨l++[⨸]⟩)
              (HPl : ∀h e1 e2 e3, (∀n, P (fund_seq h n e1 e2 e3)) → P h).
 
    Theorem eps0_wainer_rect h : eps0 h → P h.
    Proof.
      induction 1 as [ [l] Hl IH ] using eps0_trans_rect.
      destruct l as [ | l h _ ] using list_snoc_rect.
      1: apply HP0.
      assert (eps0 ⟨l⟩) as H1.
      1: eapply eps0_rem_tail; eauto.
      assert (⟨l⊣⊢[h]⟩ <> ⨸) as H2 by now destruct l.
      destruct (oge_zero_dec h) as [ -> | H ] .
      + assert (olt ⟨l⟩ ⟨l⊣⊢[⨸]⟩) as H4.
        1:{ constructor.
            rewrite (app_nil_end l) at 1.
            apply lex_list_app_head.
            constructor. }
        specialize (IH _ H1 H4).
        now apply HPS.
      + generalize (eps0_limit_tail _ Hl H); intros H3.
        apply (HPl Hl H2 H3).
        intros n; apply IH.
        * apply fund_seq_eps0.
        * apply fund_seq_olt.
    Qed.

  End eps0_wainer_rect.

  Inductive fastgrow_spec : hydra → (nat → nat) → Prop :=
    | fastgrow_spec_0 :                fastgrow_spec ⨸ S
    | fastgrow_spec_1 l f :            fastgrow_spec ⟨l⟩ f
                                     → fastgrow_spec ⟨l++[⨸]⟩ (λ n, iter f n n)
    | fastgrow_spec_2 h e1 e2 e3 f :  (∀n, fastgrow_spec (fund_seq h n e1 e2 e3) (f n))
                                     → fastgrow_spec h (λ n, f n n).

  Definition fastgrow h : eps0 h → sig (fastgrow_spec h).
  Proof.
    induction 1 as [ | l _ (f & Hf) | h e1 e2 e3 fn ] using eps0_wainer_rect.
    + exists S; now constructor.
    + exists (fun n => iter f n n); now constructor.
    + exists (fun n => proj1_sig (fn n) n).
      constructor 3 with e1 e2 e3.
      intros n; apply (proj2_sig (fn n)).
  Qed.

  Definition fast_growing_hierarchy : epsilon0 → nat → nat.
  Proof. intros (h & e); apply (proj1_sig (fastgrow h e)). Defined.

  Fact fast_growing_hierarchy_spec e : fastgrow_spec (proj1_sig e) (fast_growing_hierarchy e).
  Proof. destruct e as (h & e); simpl; apply (proj2_sig _). Qed.

  (* We define the type of ordinals upto eps0 *)

  Local Fact epsilon0_cons_spec l : ordered (ge lt_epsilon0) l → eps0 ⟨map (@proj1_sig _ _) l⟩.
  Proof.
    intros Hl.
    apply eps0_fix; split.
    + induction Hl as [ | x l Hxl ]; simpl; constructor.
      induction Hxl as [ | [] [] l []]; simpl in *; constructor; auto.
      * apply epsilon0_eq_iff in H; simpl in H; subst; now left.
      * right; auto.
    + apply list_sig_proj1.
  Qed.

  Definition epsilon0_cons l : ordered (ge lt_epsilon0) l → epsilon0.
  Proof. 
    exists ⟨map (@proj1_sig _ _) l⟩.
    now apply epsilon0_cons_spec.
  Defined.

  Arguments epsilon0_cons : clear implicits.

  Notation e0cons := epsilon0_cons.

  Fact lt0_cons_iff l l' ol ol' : lt0 (e0cons l ol) (e0cons l' ol') ↔ lex_list lt0 l l'.
  Proof.
    unfold e0cons, lt0; simpl.
    rewrite olt_inv.
    split.
    + apply lex_list_sim with (sim := fun x y => x = proj1_sig y).
      * intros ? ? ? ->; apply epsilon0_eq_iff.
      * intros; subst; auto.
      * clear l' ol ol'; induction l as [  | [] ? ?]; simpl; constructor; auto.
      * clear l ol ol'; induction l' as [  | [] ? ?]; simpl; constructor; auto.
    + apply lex_list_sim with (sim := fun x y => proj1_sig x = y).
      * intros; subst; auto.
      * intros; subst; auto.
      * clear l' ol ol'; induction l as [  | [] ? ?]; simpl; constructor; auto.
      * clear l ol ol'; induction l' as [  | [] ? ?]; simpl; constructor; auto.
  Qed.

  Section epsilon0_rect.

    (* Structural induction principle for epislon0 *)

    Variables (P : epsilon0 → Type)
              (HP : ∀ l ol, (∀o, o ∈ l → P o) → P (e0cons l ol)).

    Theorem epsilon0_rect o : P o.
    Proof.
      induction o as [ ([l] & H) IH ] using epsilon0_trans_rect.
      revert IH; generalize H.
      apply eps0_fix in H as (H1 & H2).
      destruct list_forall_reif with (1 := H2) as (m & Hm).
      assert (Hm' : ordered (ge lt0) m).
      1:{ revert H1; subst l; apply ordered_map with (f := @proj1_sig _ _).
          intros [] []; simpl; rewrite epsilon0_eq_iff; unfold lt0, oge; simpl; tauto. }
      intros H3 H4.
      assert (Hm'' : ∀ o, o ∈ m → P o).
      1:{ intros (o & e) Ho.
          apply H4; red; simpl.
          apply in_map with (f := @proj1_sig _ _) in Ho.
          rewrite <- Hm in Ho; simpl in Ho.
          apply (olt_sons ⟨l⟩); auto. }
      generalize (HP Hm' Hm'').
      match goal with |- P ?x -> P ?y => assert (x=y) as ->; auto end.
      apply epsilon0_eq_iff; subst; auto.
    Qed.

  End epsilon0_rect.

End epsilon0.














 
