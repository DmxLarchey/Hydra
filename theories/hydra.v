(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.
From Coq Require Import PeanoNat Arith.

Import ListNotations Nat.

Arguments In {_}.
Arguments app {_}.
Arguments clos_refl_trans {_}.
Arguments clos_trans {_}.

#[local] Reserved Notation "x '<ₗ' y" (at level 70, no associativity, format "x  <ₗ  y").
#[local] Reserved Notation "x '⊏' y" (at level 70, no associativity, format "x  ⊏  y").
#[local] Reserved Notation "x '⊏⁺' y" (at level 70, no associativity, format "x  ⊏⁺  y").

#[local] Reserved Notation "⟨ l ⟩" (at level 0, l at level 200, format "⟨ l ⟩").
#[local] Reserved Notation "⌊ t ⌋" (at level 0, t at level 200, format "⌊ t ⌋").

#[local] Infix "∈" := In (at level 70, no associativity).

#[local] Notation  "l ⊣ x ⊢ r" := (l++[x]++r) (at level 1, format "l ⊣ x ⊢ r").
#[local] Notation "l '⊣⊢' r" := (l++r) (at level 1, format "l ⊣⊢ r").

#[local] Hint Resolve Acc_inv Acc_intro in_cons in_eq in_elt in_or_app : core.

Fact cons_inj {X} (x y : X) l m : x::l = y::m → x = y ∧ l = m.
Proof. now inversion 1. Qed.

Fact app_nil_inv {X} (l m : list X) : l++m = [] → l = [] ∧ m = [].
Proof. revert l m; now intros [] []. Qed.

(** informative inversions for map f _ = _ :: _ and map f l = _++_ *)

Section map_eq_inv.

  Variables (X Y : Type) (f : X → Y).

  Fact map_cons_inv m fx fl : map f m = fx::fl → { x : _ & { l | m = x::l ∧ f x = fx ∧ map f l = fl } }.
  Proof. destruct m as [ | x m ]; try easy; exists x, m; inversion H; auto. Qed.

  Fact map_app_inv  m fl fr :
     map f m = fl++fr → { l : _ & { r | m = l++r ∧ map f l = fl ∧ map f r = fr } }.
  Proof.
    induction fl as [ | fx fl IH ] in m |- *; simpl.
    + exists [], m; auto.
    + intros (? & ? & -> & <- & E)%map_cons_inv.
      destruct (IH _ E) as (? & ? & ? & ? & ?); subst.
      eexists (_::_), _; simpl; eauto.
  Qed.

End map_eq_inv.

(** Maximum of a list of nat *)

Definition lmax := fold_right max 0.

Fact lmax_bound l : ∀x, x ∈ l → x ≤ lmax l.
Proof.
  apply Forall_forall.
  induction l as [ | x l IH ]; constructor; simpl.
  + apply le_max_l.
  + revert IH; apply Forall_impl.
    intros ? H; apply le_trans with (1 := H), le_max_r.
Qed.

Lemma lmax_locate m : { l : _ & { r | m = l++[lmax m]++r } } + { m = [] }.
Proof.
  induction m as [ | x m [ (l & r & E) | -> ] ]; eauto; simpl; left.
  + destruct (le_lt_dec x (lmax m)).
    * rewrite max_r; auto.
      exists (x::l), r; simpl; f_equal; auto.
    * rewrite max_l; [|now apply lt_le_incl].
      now exists [], m. 
  + exists [], []; simpl; f_equal; now rewrite max_0_r.
Qed.

(** Wellfounded strategy *)

Definition terminating {X} (R : X → X → Prop) x := Acc (λ x y, R y x) x.
Definition terminal {X} (R : X → X → Prop) x := ∀y, ~ R x y.

Section terminating_terminal.

  Variables (X : Type) (R : X → X → Prop)
            (p : nat → X) (Hp : forall n, { R (p n) (p (S n)) } + { terminal R (p n) }).

  Theorem terminating_terminal : terminating R (p 0) → { n | terminal R (p n) }.
  Proof.
    generalize 0.
    refine (fix loop n a { struct a } := _).
    destruct (Hp n) as [ H1 | H1 ].
    + apply (loop (S n)), Acc_inv with (1 := a), H1.
    + now exists n.
  Qed.

End terminating_terminal.

(** Hydras are undecorated rose trees *)

Unset Elimination Schemes.

Inductive hydra := hcons : list hydra → hydra.

Set Elimination Schemes.

#[local] Notation "⟨ l ⟩" := (hcons l).
#[local] Notation "⨸" := ⟨[]⟩.

Section hydra_ind.

  Variables (P : hydra → Prop)
            (HP : ∀l, (∀h, h ∈ l → P h) → P ⟨l⟩).

  Fixpoint hydra_ind h : P h.
  Proof.
    destruct h as [ l ]; apply HP.
    induction l as [ | g l IHl ].
    + intros _ [].
    + intros ? [ <- | H ].
      * apply hydra_ind.
      * apply IHl, H.
  Qed.

End hydra_ind.

Fact hydra_head_eq_dec h : { h = ⨸ } + { h ≠ ⨸ }.
Proof. now destruct h as [ [] ]; [ left | right ]. Qed.

Fixpoint hydra_ht (h : hydra) : nat :=
  match h with
  | ⟨l⟩ => lmax (map (λ g, 1+⌊g⌋) l)
  end
where "⌊ h ⌋" := (hydra_ht h).

Section list_order.

  Variables (X : Type) (R : X → X → Prop).

  Infix "<" := R.
  Notation "l <ₗ y" := (∀x, x ∈ l → x < y).

  (* Inductive definition of the list relation ⊏ 
     of which the transitive closure ⊏⁺ is the lo. The
     least relation containing contextual reduction
     and closed under left permutation *)

  Inductive lo_step : list X → list X → Prop :=
    | lo_step_intro l m x r : m <ₗ x → l++m++r ⊏ l++[x]++r
  where "l ⊏ m" := (lo_step l m).

  Hint Constructors lo_step : core.

  (* The inversion lemma gives an alternate characterization *)
  Fact lo_step_inv k p : 
         k ⊏ p ↔ ∃ l m x r, k = l++m++r ∧ p = l++[x]++r ∧ m <ₗ x.
  Proof.
    split.
    + induction 1 as [ l m x r ].
      now exists l, m, x, r.
    + intros (? & ? & ? & ? & -> & -> & ?); eauto.
  Qed.

  Fact lo_step_inv_sg_rt l x : l ⊏ [x] ↔ l <ₗ x.
  Proof.
    rewrite lo_step_inv; split.
    + intros (a & m & y & b & -> & H2 & H3).
      destruct a as [ | ? [] ]; try easy; simpl in *.
      inversion H2; subst y b.
      now rewrite <- app_nil_end.
    + exists [], l, x, []; simpl; rewrite <- app_nil_end; auto.
  Qed.

  (* Code could be FACTORED here ? *)
  Fact lo_step_inv_sg_lft l x : [x] ⊏ l → x ∈ l ∧ l ≠ [x] ∨ ∃ y, y ∈ l ∧ x < y.
  Proof.
    intros (a & m & y & b & H1 & -> & H3)%lo_step_inv.
    destruct a as [ | x' a ].
    2:{ symmetry in H1; simpl in H1. 
        apply cons_inj in H1 as (<- & (-> & (-> & ->)%app_nil_inv)%app_nil_inv).
        left; subst; simpl; split; now auto. }
    simpl in *.
    destruct m as [ | x' m ].
    2:{ symmetry in H1; simpl in H1. 
        apply cons_inj in H1 as (<- & (-> & ->)%app_nil_inv). 
        right; exists y; subst; split; auto. }
    simpl in *; subst; left; split; now auto.
  Qed.

  (* ⊏ is contextually closed *)
  Fact lo_step_ctx l r u v : u ⊏ v → l++u++r ⊏ l++v++r.
  Proof.
    induction 1 in l, r |- *; eauto.
    rewrite !app_ass, <- !(app_ass l); eauto.
  Qed.

  (* The empty list is minimal for ⊏ *)
  Fact lo_step_nil_inv l : ~ l ⊏ [].
  Proof. now intros ([] & ? & ? & ? & ? & ? & ?)%lo_step_inv. Qed.

  Fact lo_step_cons x l : l ⊏ x::l.
  Proof. now apply @lo_step_intro with (l := []) (m := []); simpl. Qed.

  Section Acc_lo_step.

    Notation W := (Acc lo_step).

    Local Fact Acc_lo_step_nil : W [].
    Proof. constructor 1; intros _ []%lo_step_nil_inv. Qed.

    Let W_app_bound y r :
        (∀x, x < y → ∀l, W l → W (x::l))
       → W r 
       → ∀l, l <ₗ y → W (l++r).
    Proof.
      intros hy hr. 
      induction l; simpl; eauto.
      intros; apply hy; eauto.
    Qed.

    Let lo_step_cons_right_inv k y m : 
          k ⊏ y::m 
        → (∃ u, k = u ++ m ∧ u <ₗ y)
        ∨ (∃ l u x r, m = l++[x]++r ∧ k = y::l++u++r ∧ u <ₗ x).
    Proof.
      intros ([ | z l] & u & x & r & hk & e & hu)%lo_step_inv; simpl in *;
      apply cons_inj in e as [-> ->]; [ left | right ]; eauto.
      exists l, u, x, r; eauto.
    Qed.

    Let W_cons_rec y m :
           (∀x, x < y → ∀l, W l → W (x::l))
         → W m
         → (∀l, l ⊏ m → W (y::l))
         → W (y::m).
    Proof.
      intros hy hm ihm; constructor.
      intros k [ (u & -> & hu) | (l & u & x & r & -> & -> & hu) ]%lo_step_cons_right_inv; eauto.
    Qed.

    Let W_cons y : (∀x, x < y → ∀l, W l → W (x::l)) → ∀l, W l → W (y::l).
    Proof. induction 2; eauto. Qed.

    Local Lemma Acc_lo_step_cons : ∀x, Acc R x → ∀l, W l → W (x::l).
    Proof. induction 1; eauto. Qed.

  End Acc_lo_step.

  Hint Resolve Acc_lo_step_nil 
               Acc_lo_step_cons : core.

  (* W is closed under [] and x::_ for any accessible x
     so it contains any list composed of accessibles *) 
  Local Lemma Forall_Acc_lo_step l : Forall (Acc R) l → Acc lo_step l.
  Proof. induction 1; eauto. Qed.

  Definition lo := clos_trans lo_step.

  Infix "⊏⁺" := lo.

  (** Closure properties of lo/⊏⁺ *)

  (* The constructor for the basic reduction *)
  Fact lo_intro x l : l <ₗ x → l ⊏⁺ [x].
  Proof.
    constructor 1.
    rewrite (app_nil_end l).
    now constructor 1 with (l := []) (r := []).
  Qed.

  Hint Constructors clos_trans : core.
  Hint Resolve lo_step_ctx : core.

  (* Contextual closure *)
  Fact lo_ctx l r u v : u ⊏⁺ v → l++u++r ⊏⁺ l++v++r.
  Proof. unfold lo; induction 1 in l, r |- *; eauto. Qed.

  (* Transitivity *)
  Fact lo_trans l m p : l ⊏⁺ m → m ⊏⁺ p → l ⊏⁺ p.
  Proof. econstructor 2; eassumption. Qed.

  Fact lo_erase l x r : l++r ⊏⁺ l++[x]++r.
  Proof. apply lo_ctx with (u := []), lo_intro; now simpl. Qed.

  (* Closure under right head/tail append *)
  Fact lo_app_head l m r : m ⊏⁺ r → m ⊏⁺ l++r.
  Proof.
    intros H.
    induction l as [ | x l IH ]; simpl; auto. 
    apply lo_trans with (1 := IH),
          lo_erase with (l := []).
  Qed.

  Fact lo_app_tail l m r : m ⊏⁺ l → m ⊏⁺ l++r.
  Proof.
    intros H.
    induction r as [ | x r IH ]; simpl; auto.
    + now rewrite <- app_nil_end.
    + apply lo_trans with (1 := IH), lo_erase.
  Qed. 

  Hint Resolve lo_step_cons : core.

  Fact lo_cons x l : l ⊏⁺ x::l.
  Proof. red; auto. Qed.

  Lemma Acc_lo_forall l : Acc lo l → ∀x, x ∈ l → Acc R x.
  Proof.
    induction 1 as [ l _ IHl ]; intros x Hx.
    constructor; intros y Hy.
    apply IHl with (y := [y]); auto.
    apply in_split in Hx as (l' & r' & ->).
    apply lo_app_head, lo_app_tail with (l := [_]).
    apply lo_intro; now intros ? [ <- | [] ].
  Qed.

  Hint Resolve Acc_lo_forall Forall_Acc_lo_step Acc_clos_trans : core.

  (* This is the main theorem characterizing mso Acc(essibility) *)
  Theorem Acc_lo_iff l : Acc lo l ↔ Forall (Acc R) l.
  Proof. unfold lo; split; eauto; rewrite Forall_forall; eauto. Qed.

  Corollary wf_mso : well_founded R → well_founded lo.
  Proof. intros ? ?; apply Acc_lo_iff, Forall_forall; auto. Qed.
 
End list_order.

Arguments lo {_}.

Section list_path_ordering.

  (* Weak variant of the list path ordering on hydra
     one could add two other constructors and keep it wf *)

  Unset Elimination Schemes.

  Inductive lpo : hydra → hydra → Prop :=
    | lpo_intro l m : lo lpo l m → lpo ⟨l⟩ ⟨m⟩.

  Set Elimination Schemes.

  Hint Resolve Acc_lo_forall : core.

  Theorem wf_lpo : well_founded lpo.
  Proof. 
    intros h; induction h as [ l IHl ].
    revert IHl; rewrite <- Forall_forall, <- Acc_lo_iff.
    induction 1 as [ m _ IHm ].
    constructor.
    intro g; induction g.
    inversion 1; eauto.
  Qed.

End list_path_ordering.

#[local] Notation only_copies x c := (∀ y, y ∈ c → x = y).

Section hercules.

  Inductive hcut_deep : hydra → hydra → Prop :=
    | hcut_deep_0 l₀ r₀ l₁ r₁ m : only_copies ⟨l₀⊣⊢r₀⟩ m → hcut_deep ⟨l₁⊣⟨l₀⊣⨸⊢r₀⟩⊢r₁⟩ ⟨l₁⊣⊢m⊣⊢r₁⟩
    | hcut_deep_1 l h h' r : hcut_deep h h' → hcut_deep ⟨l⊣h⊢r⟩ ⟨l⊣h'⊢r⟩.

  Inductive hcut : hydra → hydra → Prop :=
    | hcut_d1 l r : hcut ⟨l⊣⨸⊢r⟩ ⟨l⊣⊢r⟩
    | hcut_d2 h h' : hcut_deep h h' → hcut h h'.

  Local Fact cut_lpo l r : lpo ⟨l⊣⊢r⟩ ⟨l⊣⨸⊢r⟩.
  Proof.
    constructor.
    change r with ([]⊣⊢r).
    now apply lo_ctx, lo_intro.
  Qed.

  Hint Resolve cut_lpo : core.

  Local Lemma hcut_deep_lpo g h : hcut_deep h g → lpo g h.
  Proof.
    induction 1 as [ l0 r0 l1 r1 c Hc | l h h' r H IH ].
    + constructor.
      rewrite app_ass.
      apply lo_ctx, lo_intro.
      intros ? <-%Hc; auto.
    + constructor.
      apply lo_ctx, lo_intro.
      now intros ? [ <- | [] ].
  Qed.

  Hint Resolve hcut_deep_lpo : core.

  Local Lemma hcut_lpo g h : hcut h g → lpo g h.
  Proof. induction 1; auto. Qed.

  Hint Resolve hcut_lpo : core.

  Theorem hydra_terminating h : terminating hcut h.
  Proof.  apply wf_incl with (2 := wf_lpo); red; eauto. Qed.

  (* Now we study a sequence of moves *)

  Fact hydra_ht_0_inv h : ⌊h⌋ = 0 → h = ⨸.
  Proof.
    destruct h as [ [ | x m ] ]; simpl; auto.
    now destruct (lmax (map (λ g, S ⌊g⌋) m)).
  Qed.

  Fact hydra_ht_S_inv h n : ⌊h⌋ = S n → { l : _ & { g : _ & { r | h = ⟨l⊣g⊢r⟩ /\ ⌊g⌋ = n } } }.
  Proof.
    destruct h as [m]; intros H; simpl in H.
    destruct (lmax_locate (map (λ g, S ⌊g⌋) m)) as [ (l & r & E) | E ].
    + simpl in E.
      apply map_app_inv in E as (l' & ? & H1 & H2 & (g & r' & -> & H3 & H4)%map_cons_inv).
      exists l', g, r'; split; [ f_equal; auto | ].
      rewrite H in H3; now inversion H3.
    + now rewrite E in H.
  Qed.

  Hint Resolve in_or_app in_eq in_cons : core.

  Fact hydra_ht_SS_deep h n : ⌊h⌋ = S (S n) → ex (hcut_deep h).
  Proof.
    revert n; induction h as [ m IH ]; intros [ | n ] E.
    + apply hydra_ht_S_inv in E as (l1 & g & r1 & H1 & E).
      apply hydra_ht_S_inv in E as (l0 & f & r0 & H2 & E).
      apply hydra_ht_0_inv in E; subst.
      rewrite H1.
      exists ⟨l1⊣⊢[]⊣⊢r1⟩.
      constructor 1; intros _ [].
    + apply hydra_ht_S_inv in E as (l & g & r & H1 & E).
      apply IH in E as (f & E).
      * rewrite H1; exists ⟨l⊣f⊢r⟩; now constructor.
      * inversion H1; auto.
  Qed.

  Fact hydra_ht_1_cut h : ⌊h⌋ = 1 → ex (hcut h).
  Proof.
    intros (l & ? & r & -> & ->%hydra_ht_0_inv)%hydra_ht_S_inv.
    exists ⟨l⊣⊢r⟩; constructor.
  Qed.

  Fact hcut_deep_nil_inv h h' : hcut_deep h h' → h ≠ ⨸.
  Proof. now intros [ ? ? [] | [] ]. Qed.

  Fact hcut_nil_inv h h' : hcut h h' → h ≠ ⨸.
  Proof.
    intros [ [] | ]; try easy.
    eapply hcut_deep_nil_inv; eauto.
  Qed.

  Lemma hydra_terminal h : terminal hcut h ↔ h = ⨸.
  Proof.
    split.
    + intros H. 
      case_eq ⌊h⌋.
      * apply hydra_ht_0_inv.
      * intros [ | n ].
        - intros (h' & E)%hydra_ht_1_cut.
          now destruct (H h').
        - intros (h' & ?)%hydra_ht_SS_deep.
          destruct (H h'); now constructor 2.
    + now intros -> ? []%hcut_nil_inv.
  Qed.

  Variables (p : nat → hydra)
            (Hp : ∀n, p n = ⨸ ∨ hcut (p n) (p (S n))).

  Let Hp' n : { hcut (p n) (p (S n)) } + { p n = ⨸ }.
  Proof.
    destruct (hydra_head_eq_dec (p n)) as [ | H ]; auto.
    left; now destruct (Hp n).
  Qed.

  Hint Resolve hydra_terminating : core.

  Corollary hydra_steps : { n | p n = ⨸ }.
  Proof.
    destruct terminating_terminal with (2 := hydra_terminating (p 0))
      as (n & Hn).
    + intros n; destruct (Hp' n); eauto; right; now apply hydra_terminal.
    + exists n; now apply hydra_terminal.
  Qed.

End hercules.

Check hydra_steps.
Print Assumptions hydra_steps.
