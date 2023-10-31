(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.
From Hydra Require Import hydra ordered lex_list.

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

Section epsilon0.

  Hint Constructors lex_list sdec ordered ordered_from : core.

  Hint Resolve lex_list_app_head lex_list_prefix' lex_list_prefix lex_list_snoc lex_list_trans : core.

  Inductive olt : hydra → hydra → Prop :=
    | olt_intro l m : lex_list olt l m → olt ⟨l⟩ ⟨m⟩.

  Hint Constructors olt : core.

  Fact olt_inv l m : olt ⟨l⟩ ⟨m⟩ ↔ lex_list olt l m.
  Proof. split; auto; now inversion 1. Qed.

  Theorem olt_sdec g h : sdec olt g h.
  Proof.
    revert h; induction g as [ l IHg ]; intros [ m ].
    destruct (@lex_list_sdec _ olt l m); eauto.
  Qed.

  Theorem olt_irrefl h : ¬ olt h h.
  Proof.
    induction h as [ l IH ].
    intros (g & G1 & G2)%olt_inv%lex_list_irrefl.
    now apply (IH _ G1).
  Qed.

  Theorem olt_trans : transitive olt.
  Proof.
    intros f; induction f.
    intros [] [] ?%olt_inv ?%olt_inv; eauto.
  Qed.

  Hint Resolve olt_trans olt_irrefl : core.

  Fact olt_dec g h : { olt g h } + { ~ olt g h }.
  Proof.
    destruct (olt_sdec g h) as [ | | g h ]; eauto.
    right; intro; apply (@olt_irrefl g); eauto.
  Qed.

  Corollary olt_trans' g h : clos_trans olt g h → olt g h.
  Proof. induction 1; eauto. Qed.

  Definition oge := ge olt.

  Fact oge_dec g h : { oge g h } + { ~ oge g h }.
  Proof.
    destruct (olt_sdec g h) as [ g h H | h | g h H ].
    + right; intros [<-|]; apply (@olt_irrefl g); eauto.
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
    induction 1 as [ m Hh1 Hh2 _   ] using eps0_rect.
    intros H%olt_inv. 
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
    destruct m as [ | y m ]; [ easy | ].
    destruct l as [ | x l ]; eauto.
    destruct Hl as [ -> | Hl ]; eauto.
    apply ordered_inv,
          ordered_from_clos_trans with (2 := Hl),
          clos_trans_ge in H1 as [ -> | ]; eauto.
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
  Proof. destruct h as [ [] ]; [ left | right ]; auto. Qed.

  Hint Resolve eps0_zero zero_smallest : core.

  Fact zero_smallest' h : ¬ olt h ⨸.
  Proof.
    destruct (zero_smallest h) as [ <- | H ]; eauto.
    intro; eapply olt_irrefl, olt_trans; eauto.
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
    intros []; split; auto.
    intros ? [ | [<- | []]]%in_app_iff; auto.
  Qed.

  Hint Resolve ordered_app_head : core.

  Fact eps0_rem_tail l h : eps0 ⟨l++[h]⟩ → eps0 ⟨l⟩.
  Proof. rewrite !eps0_fix; intros []; split; eauto. Qed.

  Fact oge_zero_dec h : { h = ⨸ } + { olt ⨸ h }.
  Proof. destruct h as [ [] ]; auto. Qed.

  Hint Resolve lex_list_prefix lex_list_snoc : core.

  Lemma lex_list_olt_tail l m x y :
           olt x y 
         → ordered oge m⊣⊢[y]
         → lex_list olt l m⊣⊢[y]
         → lex_list olt l⊣⊢[x] m⊣⊢[y].
  Proof.
    intros H1 H2 H3; revert l m H3 x H1 H2.
    intros _ _ [ l m | u l m | p u v l m ]%lex_list_snoc_inv x H1 H2.
    all: rewrite !app_ass in *; apply lex_list_app_head; simpl; eauto.
    destruct m; simpl in *; constructor 2; auto.
    apply ordered_app_tail, ordered_inv in H2.
    apply olt_trans', clos_t_rt with y; auto.
    apply clos_t_ge_rt.
    eapply ordered_from_clos_trans; eauto.
  Qed.

  Inductive olt_inv_snoc_right_shape h : hydra → list hydra → Prop :=
    | in_olt_inv_snoc_right_shape0 p x y l m : olt x y → olt_inv_snoc_right_shape h ⟨p++[x]++l⟩ (p++[y]++m)
    | in_olt_inv_snoc_right_shape1 x l m : olt x h → olt_inv_snoc_right_shape h ⟨l++[x]++m⟩ l
    | in_olt_inv_snoc_right_shape2 l m : olt_inv_snoc_right_shape h ⟨l⟩ (l++m).

  Lemma olt_inv_snoc_right g m h : olt g ⟨m++[h]⟩ → olt_inv_snoc_right_shape h g m.
  Proof. revert g; intros [] []%olt_inv%lex_list_snoc_inv; now constructor. Qed.

  Lemma olt_inv_snoc_right' g m h :
           olt g ⟨m++[h]⟩ 
        → (∃ c x y p q, olt x y ∧ g = ⟨c++[x]++p⟩ ∧ m = c++[y]++q)
        ∨ (∃ x p, olt x h ∧ g = ⟨m++[x]++p⟩)
        ∨ (∃ p q, g = ⟨p⟩ ∧ m = p++q).
  Proof.
    revert g m.
    intros _ _ [ p x y l m | x l m | l m ]%olt_inv_snoc_right.
    + left; exists p, x, y, l, m; auto.
    + right; left; now exists x, m.
    + right; right; eauto.
  Qed.

  Hint Resolve lex_list_app_head lex_list_prefix' : core.

  Corollary olt_succ_inv g l : olt g ⟨l++[⨸]⟩ → g = ⟨l⟩ ∨ olt g ⟨l⟩.
  Proof.
    intros [ | ? ? ? []%zero_smallest' | ? [] ]%olt_inv_snoc_right; simpl; eauto.
    rewrite <- app_nil_end; auto.
  Qed.

  Inductive olt_inv_single_right_shape h : hydra → Prop :=
    | in_olt_inv_single_right_shape0 : olt_inv_single_right_shape h ⨸
    | in_olt_inv_single_right_shape1 x l : olt x h → olt_inv_single_right_shape h ⟨[x]++l⟩.

  Lemma olt_inv_single_right g h : olt g ⟨[h]⟩ → olt_inv_single_right_shape h g.
  Proof.
    intros H.
    apply olt_inv_snoc_right' with (m := []) in H
      as [ (c & x & y & p & q & _ & _ & H) 
        |[ (x & p & H1 & H2)
         | (p & q & H1 & H2) ] ]; subst; simpl.
    + now destruct c.
    + now constructor.
    + destruct p; [ constructor | easy ].
  Qed.

  (** Every ordinal is either a successor, 
      or a limit, ie forall x < lim, succ x < lim *)

  Inductive zero_succ_limit_shape : hydra → Type :=
    | zero_succ_limit_shape0 : zero_succ_limit_shape ⨸
    | zero_succ_limit_shape1 l : eps0 ⟨l⟩ → zero_succ_limit_shape ⟨l++[⨸]⟩
    | zero_succ_limit_shape2 l h : eps0 ⟨l++[h]⟩ → olt ⨸ h → zero_succ_limit_shape ⟨l++[h]⟩.

  Hint Constructors zero_succ_limit_shape : core.

  Theorem eps0_zero_succ_or_limit h : eps0 h → zero_succ_limit_shape h.
  Proof.
    destruct 1 as [ l H1 H2 _ ] using eps0_rect.
    destruct l as [ | l h _ ] using list_snoc_rect; eauto.
    destruct (oge_zero_dec h) as [ -> | Hm ].
    + constructor 2; apply eps0_fix; split; eauto.
    + constructor 3; eauto;apply eps0_fix; split; auto.
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

  Inductive limit_shape : hydra → Type :=
    | in_limit_shape l g : eps0 ⟨l++[g]⟩ → olt ⨸ g → limit_shape ⟨l++[g]⟩.

  Fact eps0_limit_iff h : eps0 h → eps0_limit h → h ≠ ⨸ → limit_shape h.
  Proof.
    intros []%eps0_zero_succ_or_limit H2 H3; try easy; eauto.
    now apply eps0_succ_not_limit in H2 as [].
  Qed.

  Theorem succ_or_limit h : eps0 h → { p | eps0 p ∧ h = hydra_succ p } + { eps0_limit h }.
  Proof. intros []%eps0_zero_succ_or_limit; eauto. Qed.

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
          apply lex_list_inv in H6.
          destruct H6 as [ x h H | h ?%lex_list_inv ].
          2: now destruct g.
          intros ? [ <- | ]; right; eauto.
      * intros ? [ ]%in_app_iff; eauto.
      * constructor; apply lex_list_app_head; auto.
  Qed.

  Inductive fseq_shape n h' : hydra → Prop :=
    | in_fseq_shape0 l : h' = ⟨[⟨l++[⨸]⟩]⟩ → fseq_shape n h' ⟨repeat ⟨l⟩ n⟩
    | in_fseq_shape1 l h g : h' = ⟨[⟨l++[h]⟩]⟩ → olt ⨸ h → fseq ⟨l++[h]⟩ n g → fseq_shape n h' ⟨[g]⟩
    | in_fseq_shape2 l h g : h' = ⟨l++[h]⟩ → l ≠ [] → fseq ⟨[h]⟩ n ⟨g⟩ → fseq_shape n h' ⟨l++g⟩.

  Hint Constructors fseq_shape : core.

  Fact fseq_inv h n g : fseq h n g → fseq_shape n h g.
  Proof. induction 1; eauto. Qed.

  Fact fseq_zero_inv l n g : fseq ⟨[⟨l++[⨸]⟩]⟩ n g → g = ⟨repeat ⟨l⟩ n⟩.
  Proof. 
    revert g; intros _ [l' H | l' h g H E | l' h g H ]%fseq_inv; revert H.
    + now intros [[-> ?]%hydra_cons_inj%app_inj_tail _]%hydra_cons_inj%cons_inj.
    + intros [[_ <-]%hydra_cons_inj%app_inj_tail _]%hydra_cons_inj%cons_inj.
      exfalso; revert E; apply olt_irrefl.
    + now intros [<- _]%hydra_cons_inj%(app_inj_tail []).
  Qed.

  Fact fseq_olt_inv l h n g : olt ⨸ h → fseq ⟨[⟨l++[h]⟩]⟩ n g → ∃g', g = ⟨[g']⟩ ∧ fseq ⟨l++[h]⟩ n g'.
  Proof.
    intros H0 H1; revert g H1 H0.
    intros _ [ l' E | l' h' g E H1 H2  | l' h' g E H1 H2 ]%fseq_inv H3; revert E.
    + intros [_ ->]%hydra_cons_inj%cons_inj%proj1%hydra_cons_inj%app_inj_tail.
      exfalso; revert H3; apply olt_irrefl.
    + intros [-> ->]%hydra_cons_inj%cons_inj%proj1%hydra_cons_inj%app_inj_tail; eauto.
    + now intros [<- _]%hydra_cons_inj%(app_inj_tail []).
  Qed.

  Fact fseq_seq_inv l h n g : l ≠ [] → fseq ⟨l++[h]⟩ n g → ∃g', g = ⟨l++g'⟩ ∧ fseq ⟨[h]⟩ n ⟨g'⟩.
  Proof.
    intros H0 H1; revert g H1 H0.
    intros _ [ l' E | l' h' g E H1 H2  | l' h' g E H1 H2 ]%fseq_inv H3; revert E.
    1,2: now intros [-> ->]%hydra_cons_inj%(app_inj_tail _ []).
    intros [-> ->]%hydra_cons_inj%app_inj_tail; eauto.
  Qed.

  Lemma fseq_fun h n g₁ g₂ : fseq h n g₁ → fseq h n g₂ → g₁ = g₂.
  Proof.
    intros H1; revert H1 g₂.
    induction 1 as [ l n | l h n g H1 H2 IH2 | l h n g H1 H2 IH2 ].
    + now intros ? ->%fseq_zero_inv.
    + intros ? (? & -> & ?)%fseq_olt_inv; auto.
      do 2 f_equal; eauto.
    + intros ? (? & -> & ->%IH2%hydra_cons_inj)%fseq_seq_inv; auto.
  Qed.

  (* The "set" P intersects ]g,h[ for any g < h, ie P is as close
     to h as one could wish *)
  Definition is_limit (P : hydra → Prop) h :=
    ∀g, eps0 g → olt g h → ∃u, P u ∧ olt g u ∧ olt u h.

  Lemma olt_repeat_snoc l n h : olt ⟨repeat ⟨l⟩ n⟩ ⟨[⟨l++[h]⟩]⟩.
  Proof. constructor; destruct n; simpl; eauto. Qed.

  Fact ordered_from_oge_olt x l y : oge y x -> ordered_from oge x l -> olt ⟨x::l⟩ ⟨repeat y (2+length l)⟩.
  Proof.
    intros [ -> | ] G; constructor; revert G; simpl; eauto.
    induction 1 as [ | ? ? ? [ <- | ] ]; simpl; eauto.
  Qed.

  Lemma is_limit_repeat l : ordered oge l → is_limit (λ u, ∃n, u = ⟨repeat ⟨l⟩ n⟩) ⟨[⟨l++[⨸]⟩]⟩.
  Proof.
    intros ol h E H; revert E l H ol.
    induction 1 as [ m E1 E2 _ ] using eps0_rect.
    intros l Hm%olt_inv%lex_list_sg_inv_right Hl.
    destruct Hm as [ | [k] p Hx ].
    + exists ⟨repeat ⟨l⟩ 1⟩; repeat split; eauto; simpl; repeat constructor; auto.
    + apply olt_inv, lex_list_snoc_inv in Hx.
      destruct Hx as [ l m | x l m []%zero_smallest' | q u v l m ].
      * exists ⟨repeat ⟨l++m⟩ (2+length p)⟩; split; eauto; split.
        - apply ordered_from_oge_olt.
          ++ destruct m.
             ** left; now rewrite <- app_nil_end.
             ** right; constructor; now apply lex_list_prefix.
          ++ now apply ordered_inv.
        - constructor; constructor 2; constructor; now apply lex_list_prefix.
      * exists ⟨repeat ⟨q++[v]++m⟩ 1⟩; split; eauto; simpl; split; constructor; constructor 2; constructor.
        - apply lex_list_app_head; now constructor 2.
        - now apply lex_list_prefix.
  Qed.

  Hint Resolve olt_repeat_snoc : core. 

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
      induction 1 as [ g H1 IH ] using eps0_trans_rect; intros H2 H3.
      destruct (eps0_limit_iff H1 H3 H2) as [ m h _ H4 ].
      destruct (list_nil_choose m) as [ -> | Hm ]; simpl.
      + destruct h as [ l ].
        destruct l as [ | l h _ ] using list_snoc_rect.
        * apply olt_irrefl in H4 as [].
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
        apply eps0_fix in H1 as (H1 & H5).
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

  (* The fundemental sequence can be computed in Coq *)
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
    + intros l Hl h H1 H2%olt_inv_single_right.
      destruct H2 as [ | x m H2 ].
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
    + intros l h H1 H2 H3 g G1 G2%olt_inv_single_right.
      destruct G2 as [ | k m G2 ].
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
    + intros l h H1 H2 H3 H4 g G1 G2%olt_inv_snoc_right.
      destruct G2 as [ p x y l m G2 | x l m | l m ].
      * destruct (H4 ⨸) as ([k] & (n & En) & E2 & E3%olt_inv); eauto.
        exists ⟨(p++[y]++m)++k⟩; repeat split; eauto.
        - exists n; now constructor.
        - rewrite !app_ass; simpl; eauto.
      * destruct (H4 ⟨[x]++m⟩) as ([k] & (n & En) & E2%olt_inv & E3%olt_inv); simpl; eauto.
        - apply eps0_fix in G1 as [G1 G3]; apply eps0_fix; split; eauto.
          eapply ordered_app_tail; eauto.
        - exists ⟨l⊣⊢k⟩; repeat split; eauto.
          exists n; constructor; auto.
      * destruct (H4 ⨸) as ([k] & (n & En) & E2 & E3%olt_inv); eauto.
        exists ⟨(l⊣⊢m)⊣⊢k⟩; split; [ | split ]; eauto.
        - exists n; constructor; eauto.
        - rewrite app_ass; constructor.
          apply lex_list_prefix.
          destruct m; [ simpl | easy ].
          intros ->.
          revert E2; apply olt_irrefl.
  Qed.

  Lemma fseq_S_olt h n g g': h ≠ ⨸ → fseq h n g → fseq h (S n) g' → olt g g'.
  Proof.
    intros _ H2; revert H2 g'.
    induction 1 as [ l n | l h n g H1 H2 IH2 | l h n g H1 H2 IH2 ]; intros g'.
    + intros ->%fseq_zero_inv.
      rewrite repeat_S; auto.
    + intros (? & -> & ?%IH2)%fseq_olt_inv; auto.
    + intros (? & -> & ?%IH2%olt_inv)%fseq_seq_inv; auto.
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
           fund_seq h n e1 e2 e3 = fund_seq h n f1 f2 f3.
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
      * clear l' ol ol'; induction l as [|[]]; simpl; constructor; auto.
      * clear l ol ol'; induction l' as [|[]]; simpl; constructor; auto.
    + apply lex_list_sim with (sim := fun x y => proj1_sig x = y).
      * intros; subst; auto.
      * intros; subst; auto.
      * clear l' ol ol'; induction l as [|[]]; simpl; constructor; auto.
      * clear l ol ol'; induction l' as [|[]]; simpl; constructor; auto.
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














 
