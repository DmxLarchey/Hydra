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

Notation ge R := (λ x y, x = y ∨ R y x).


Section clos_trans.

  Variables (X : Type).

  Implicit Type (R : X → X → Prop).

  Hint Constructors clos_refl_trans : core.

  Fact clos_trans_ge R : transitive R → ∀ x y, clos_trans (ge R) x y → ge R x y.
  Proof. 
    intros HR; red in HR.
    induction 1 as [ ? ? [] | ? ? ? _ [] _ [] ]; subst; eauto.
  Qed.

  Fact clos_t_ge_rt R x y : clos_trans (ge R) x y → clos_refl_trans R y x.
  Proof. induction 1 as [ ? ? [ <- | ] | ]; eauto. Qed.

  Fact ordered_from_ge_Acc R x l : ordered_from (ge R) x l → Acc R x → ∀y, y ∈ l → Acc R y.
  Proof. induction 1 as [ | ? ? ? [ <- | ] ]; intros ? ? []; subst; eauto. Qed.

End clos_trans.

Section lex_list_wf.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Type (x : X).

  Hint Constructors ordered_from clos_refl_trans : core.

  Hint Resolve ordered_from_clos_trans : core.

  Hint Resolve clos_t_ge_rt clos_rt_t ordered_cons_inv : core.

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

  Theorem lex_list_Acc_ordered l : Forall (Acc R) l → ordered (ge R) l → Acc (λ l m, ordered (ge R) l ∧ lex_list R l m) l.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1 as [ | x l H1 ]; intros H2; auto.
    apply lex_list_Acc_ordered_from with x; eauto.
    eapply Forall_forall; eauto.
  Qed.

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

Section list_sig.

  Variables (X : Type) (P : X → Prop).

  Fact list_sig_proj1 (l : list (sig P)) :
        ∀x, x ∈ map (@proj1_sig _ _) l → P x.
  Proof.
    induction l as [ | [] ]; simpl; [ easy | ].
    intros ? [ <- | ]; eauto.
  Qed.

  Definition list_sig_list : list (sig P) → { l | ∀x, x ∈ l → P x }.
  Proof.
    intros l.
    exists (map (@proj1_sig _ _) l).
    apply list_sig_proj1.
  Defined.

  Fact list_forall_reif l : (∀x, x ∈ l → P x) → { m : list (sig P) | l = map (@proj1_sig _ _) m }.
  Proof.
    induction l as [ | x l IHl ]; intros Hl.
    + exists []; auto.
    + destruct IHl as (m & Hm); eauto.
      assert (P x) as Hx by eauto.
      exists ((exist _ x Hx)::m); simpl; f_equal; auto.
  Qed.

End list_sig.

Theorem list_snoc_rect {X} (P : list X → Type) :
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

Fact clos_t_rt X (R : X → X → Prop) x y z :
       clos_trans R x y → clos_refl_trans R y z → clos_trans R x z.
Proof. induction 2; eauto. Qed.

Section repeat.

  Variables (X : Type) (x : X).

  Definition repeat :=
    fix loop n := match n with 0 => [] | S n => x::loop n end.

  Fact In_repeat n y : y ∈ repeat n → x = y.
  Proof. induction n; simpl; intros []; auto. Qed.

  Fact ordered_repeat R n : ordered (ge R) (repeat n).
  Proof.
    destruct n as [ | n ]; simpl; constructor.
    induction n; simpl; constructor; eauto.
  Qed.

End repeat.

Fact list_nil_choose X (l : list X) : (l = []) + (l <> []).
Proof. destruct l; eauto; now right. Qed.

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

  Fact oge_zero_dec h : { h = ⨸ } + { olt ⨸ h }.
  Proof.
    destruct h as [ [] ]; auto.
    right; do 2 constructor.
  Qed.

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
      rewrite app_ass in H2 |- *; apply lex_list_app_head.
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
    constructor.
    rewrite (app_nil_end l) at 1.
    apply lex_list_app_head; constructor.
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
        - constructor 2; constructor.
          rewrite (app_nil_end l) at 1.
          apply lex_list_app_head; constructor.
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

  Section olt_rect.

    Variables (P : hydra → Type)
              (HP : forall h, eps0 h → (forall g, eps0 g → olt g h → P g) → P h).

    Let Q o := P (proj1_sig o).
    Let HQ o : Q o.
    Proof.
      induction o as [ [ h e ] IH ] using (well_founded_induction_type lt_epsilon0_wf); unfold Q; simpl.
      apply HP; auto.
      intros g H1 H2.
      apply (IH (exist _ g H1)); auto.
    Qed.

    Theorem olt_rect h : eps0 h → P h.
    Proof. intros H; apply (HQ (exist _ _ H)). Qed.

  End olt_rect.

  Definition build_fseq h n : eps0 h → h ≠ ⨸ → eps0_limit h → sig (fseq h n).
  Proof.
    induction 1 as [ [l] H1 IH ] using olt_rect; intros H2 H3.
    destruct (eps0_limit_iff H1 H3 H2) as (m & h & H4 & H5).
    inversion H4; subst l; clear H4. 
    destruct (list_nil_choose m) as [ -> | Hm ]; simpl.
    + destruct h as [ l ].
      destruct l as [ | l h _ ] using list_snoc_rect.
      * apply eps0_succ_not_limit in H3 as [].
        apply eps0_zero.
      * destruct (oge_zero_dec h) as [ -> | H6 ].
        - exists ⟨repeat ⟨l⟩ n⟩; constructor.
        - simpl in H1; apply eps0_fix in H1 as [H0 H1].
          destruct (IH ⟨l++[h]⟩) as (g & Hg); auto.
          ++ simpl; apply olt_power; auto.
          ++ now destruct l.
          ++ exists ⟨[g]⟩; now constructor.
    + apply eps0_fix in H1 as (H1 & H4).
      destruct (IH ⟨[h]⟩) as ([g] & Hg); eauto.
      * apply eps0_fix; split; eauto.
      * admit.
      * easy.
      * admit.
      * exists ⟨m++g⟩; constructor; auto.
  Admitted.

  Definition epsilon0_cons l : ordered (ge lt_epsilon0) l → epsilon0.
  Proof.
    intros Hl.
    exists ⟨map (@proj1_sig _ _) l⟩.
    apply eps0_fix; split.
    + induction Hl as [ | x l Hxl ]; simpl; constructor.
      induction Hxl as [ | [] [] l []]; simpl in *; constructor; auto.
      * apply epsilon0_eq_iff in H; simpl in H; subst; now left.
      * right; auto.
    + apply list_sig_proj1.
  Defined.

  Arguments epsilon0_cons : clear implicits.

  Notation e0cons := epsilon0_cons.

  Section epsilon0_rect.

    Variables (P : epsilon0 → Type)
              (HP : ∀ l ol, (∀o, o ∈ l → P o) → P (e0cons l ol)).

    Theorem epsilon0_rect o : P o.
    Proof.
      induction o as [ ([l] & H) IH ] using (well_founded_induction_type lt_epsilon0_wf).
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














 
