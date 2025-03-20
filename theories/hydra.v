(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import PeanoNat Lia List Relations Wellfounded Utf8.

Import ListNotations.

Set Implicit Arguments.

Arguments clos_trans {_}.

(** Notations for the construction of the list order *)
#[local] Reserved Notation "x '≺' y" (at level 70, no associativity, format "x  ≺  y").
#[local] Reserved Notation "x '≺ₗ' y" (at level 70, no associativity, format "x  ≺ₗ  y").
#[local] Reserved Notation "x '⊏' y" (at level 70, no associativity, format "x  ⊏  y").
#[local] Reserved Notation "x '⊏⁺' y" (at level 70, no associativity, format "x  ⊏⁺  y").

(** Notations for hydras *)
#[local] Reserved Notation "⟨ l ⟩" (at level 0, l at level 200, format "⟨ l ⟩").
#[local] Reserved Notation "⌊ t ⌋" (at level 0, t at level 200, format "⌊ t ⌋").

(** Notations for Hercules-Hydra rounds *)
#[local] Reserved Notation "h ⊳ g" (at level 70, format "h  ⊳  g").
#[local] Reserved Notation "h ⊳₁ g" (at level 70, format "h  ⊳₁  g").
#[local] Reserved Notation "h ⊳₂ g" (at level 70, format "h  ⊳₂  g").

(** Notations for lists insertion patterns *)
#[local] Infix "∈" := In (at level 70, no associativity).
#[global] Notation  "l ⊣ x ⊢ r" := (l++[x]++r) (at level 1, format "l ⊣ x ⊢ r").
#[global] Notation "l '⊣⊢' r" := (l++r) (at level 1, format "l ⊣⊢ r").

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.

(** Extra list utilities *)

Fact cons_inj {X} (x y : X) l m : x::l = y::m → x = y ∧ l = m.
Proof. now inversion 1. Qed.

Fact app_nil_inv {X} (l m : list X) : l++m = [] → l = [] ∧ m = [].
Proof. revert l m; now intros [] []. Qed.

Fact sg_eq_insert {X} (x y : X) l r : [x] = l⊣y⊢r → x = y ∧ l = [] ∧ r = [].
Proof. destruct l as [ | ? [] ]; inversion 1; auto. Qed.

(** The list order is a weak variant of the multiset order on list 

   The proof displayed here is largely inspired from 
   the short outline of Tobias Nipkow and Wilfried Buchholz 

     http://www4.in.tum.de/~nipkow/misc/multiset.ps *)

Section list_order.

  Variables (X : Type) (R : X → X → Prop).

  Infix "≺" := R.
  Notation "l ≺ₗ y" := (∀x, x ∈ l → x ≺ y).

  Local Fact lt_fall_sg x y : x ≺ y → [x] ≺ₗ y.
  Proof. now intros ? ? [ <- | [] ]. Qed.

  Hint Resolve lt_fall_sg : core.

  (* Inductive definition of the list relation ⊏ 
     of which the transitive closure ⊏⁺ is the list order. *)

  Inductive lo_step : list X → list X → Prop :=
    | lo_step_intro l m x r : m ≺ₗ x → l++m++r ⊏ l++[x]++r
  where "l ⊏ m" := (lo_step l m).

  Hint Constructors lo_step : core.

  Fact lo_step_ctx l r u v : u ⊏ v → l++u++r ⊏ l++v++r.
  Proof.
    induction 1 in l, r |- *; eauto.
    rewrite !app_ass, <- !(app_ass l); eauto.
  Qed.

  Fact lo_step_cons x l : l ⊏ x::l.
  Proof. now apply @lo_step_intro with (l := []) (m := []); simpl. Qed.

  (* The inversion lemma gives an alternate characterization,
     used below for more specific inversion lemmas below *)
  Local Fact lo_step_inv k p :
         k ⊏ p ↔ ∃ l m x r, k = l++m++r ∧ p = l++[x]++r ∧ m ≺ₗ x.
  Proof.
    split.
    + intros [ l m x r ]; now exists l, m, x, r.
    + intros (? & ? & ? & ? & -> & -> & ?); eauto.
  Qed.

  (* These two are key lemmas in the proof of (Acc lo_step) below *)
  Local Fact lo_step_nil_inv l : ~ l ⊏ [].
  Proof. now intros ([] & ? & ? & ? & ? & ? & ?)%lo_step_inv. Qed.

  Local Lemma lo_step_cons_right_inv k y m : 
          k ⊏ y::m 
        → (∃ u, k = u++m ∧ u ≺ₗ y)
        ∨ (∃ l u x r, m = l++[x]++r ∧ k = y::l++u++r ∧ u ≺ₗ x).
  Proof.
    intros ([ | z l] & u & x & r & hk & e & hu)%lo_step_inv; simpl in *;
    apply cons_inj in e as [-> ->]; [ left | right ]; eauto.
    exists l, u, x, r; eauto.
  Qed.

  Section Acc_lo_step.

    Notation W := (Acc lo_step).

    Local Fact Acc_lo_step_nil : W [].
    Proof. constructor 1; intros _ []%lo_step_nil_inv. Qed.

    Local Fact W_app_bound y r :
        (∀x, x ≺ y → ∀l, W l → W (x::l))
       → W r 
       → ∀l, l ≺ₗ y → W (l++r).
    Proof.
      intros hy ?. 
      induction l; simpl; eauto.
      intros; apply hy; eauto.
    Qed.

    Hint Resolve W_app_bound : core.

    Local Fact W_cons_rec y m :
           (∀x, x ≺ y → ∀l, W l → W (x::l))
         → W m
         → (∀l, l ⊏ m → W (y::l))
         → W (y::m).
    Proof. constructor; intros ? [ (? & -> & ?) | (? & ? & ? & ? & -> & -> & ?) ]%lo_step_cons_right_inv; eauto. Qed.

    Hint Resolve W_cons_rec : core.

    Local Fact W_cons y : (∀x, x ≺ y → ∀l, W l → W (x::l)) → ∀l, W l → W (y::l).
    Proof. induction 2; eauto. Qed.

    Hint Resolve W_cons : core.

    Local Lemma Acc_lo_step_cons x : Acc R x → ∀l, W l → W (x::l).
    Proof. induction 1; eauto. Qed.

  End Acc_lo_step.

  Hint Resolve Acc_lo_step_nil 
               Acc_lo_step_cons : core.

  (* W is closed under [] and x::_ for any accessible x
     so it contains any list composed of accessibles *) 
  Local Lemma forall_Acc_lo_step l : (∀x, x ∈ l → Acc R x) → Acc lo_step l.
  Proof.
    rewrite <- Forall_forall.
    induction 1; eauto.
  Qed.

  Definition lo := clos_trans lo_step.

  Infix "⊏⁺" := lo.

  Hint Resolve lo_step_cons lo_step_ctx : core.

  (** Closure properties of lo/⊏⁺ *)

  (* The constructor for the basic reduction *)
  Fact lo_intro x l : l ≺ₗ x → l ⊏⁺ [x].
  Proof.
    constructor 1.
    rewrite (app_nil_end l).
    now constructor 1 with (l := []) (r := []).
  Qed.

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
    apply lo_trans with (1 := IH), lo_erase with (l := []).
  Qed.

  Fact lo_app_tail l m r : m ⊏⁺ l → m ⊏⁺ l++r.
  Proof.
    intros H.
    induction r as [ | x r IH ]; simpl; auto.
    + now rewrite <- app_nil_end.
    + apply lo_trans with (1 := IH), lo_erase.
  Qed.

  Fact lo_app_head_tail m m' l r : m ⊏⁺ m' → m ⊏⁺ l++m'++r.
  Proof. now intro; apply lo_app_head, lo_app_tail. Qed.

  Fact lo_cons x l m : l ⊏⁺ m → x::l ⊏⁺ x::m.
  Proof. 
    intros; rewrite (app_nil_end l), (app_nil_end m).
    now apply lo_ctx with (l := [_]).
  Qed.

  Lemma Acc_lo_forall l : Acc lo l → ∀x, x ∈ l → Acc R x.
  Proof.
    induction 1 as [ l _ IHl ]; intros x Hx.
    constructor; intros y Hy.
    apply IHl with (y := [y]); auto.
    apply in_split in Hx as (l' & r' & ->).
    apply lo_app_head_tail with (m' := [_]),
          lo_intro; eauto.
  Qed.

  Hint Resolve Acc_lo_forall forall_Acc_lo_step Acc_clos_trans : core.

  (* This is the main theorem characterizing mso Acc(essibility) *)
  Theorem Acc_lo_iff l : Acc lo l ↔ ∀x, x ∈ l → Acc R x.
  Proof. unfold lo; split; eauto. Qed.

  Corollary wf_mso : well_founded R → well_founded lo.
  Proof. intros ? ?; apply Acc_lo_iff; auto. Qed.

End list_order.

Arguments lo {_}.

(** Hydras are undecorated and oriented rose trees.
    We need to generate versatile eliminators by hand
    because Coq does not manage nested inductive types
    automatically. Moreover it cannot guess the
    use of ∈/In and would probably generate an equivalent 
    ad-hoc predicate should it try to invent a more general 
    nested eliminator for hydra. *)

Unset Elimination Schemes.

Inductive hydra := hydra_cons : list hydra → hydra.

Set Elimination Schemes.

#[global] Notation "⟨ l ⟩" := (hydra_cons l).
#[global] Notation "⨸" := ⟨[]⟩.  (* the head hydra *)

Definition hydra_sons h := match h with ⟨l⟩ => l end.

Fact hydra_cons_inj l m : ⟨l⟩ = ⟨m⟩ → l = m.
Proof. now inversion 1. Qed.

Section hydra_ind.

  Variables (P : hydra → Prop)
            (HP : ∀l, (∀h, h ∈ l → P h) → P ⟨l⟩).

  (* The Prop-bounded eliminator proceeds by guarded 
     nested fixpoints, unavoidable in the case of
     nested inductive types *)
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

(** The list path ordering is a weak variant of the multiset 
    path ordering on hydra. One could add two other constructors 
    and stability under permutations and still keep it well-founded *)

Unset Elimination Schemes.

Inductive lpo : hydra → hydra → Prop :=
  | lpo_intro l m : lo lpo l m → lpo ⟨l⟩ ⟨m⟩.

Fact lpo_inv l m : lpo ⟨l⟩ ⟨m⟩ → lo lpo l m.
Proof. now inversion 1. Qed.

Set Elimination Schemes.

(* We get a very short proof compared to the following sources
   of inspiration:
       S. Coupet-Grimmal & W. Delobel
       https://link.springer.com/article/10.1007/s00200-006-0020-y
       J. Goubault-Larrecq
       http://www.lsv.ens-cachan.fr/Publis/PAPERS/PDF/JGL-mfcs13.pdf

   This path ordering is a bit simpler though but it keeps the
   case of the nesting of the list order "lo".

   Three nested inductions for the proof below, based on
   the Acc-characterization of the list ordering:

      Acc (lo lpo) l ↔ ∀x, x ∈ l → Acc lpo x
*)

Theorem wf_lpo h : Acc lpo h.
Proof.
  induction h as [ m IHm%Acc_lo_iff ].
  induction IHm as [ m _ IHm ].
  constructor.
  intro g; induction g as [ l IHl ].
  intros ?%lpo_inv; eauto.
Qed.

Fact Acc_irrefl X (R : X → X → Prop) x : Acc R x → ~ R x x.
Proof. induction 1 as [ x _ IH ]; intros H; exact (IH _ H H). Qed.

Fact lpo_irrefl h : ~ lpo h h.
Proof. apply Acc_irrefl with (1 := wf_lpo h). Qed.

Fact lpo_trans : transitive _ lpo.
Proof.
  intros [l] [m] [k] ?%lpo_inv ?%lpo_inv.
  constructor; econstructor 2; eauto.
Qed.

(** Inductive definition (Acc based) of "R is terminating at x" *)

Definition terminating {X} (R : X → X → Prop) := Acc (λ x y, R y x).

Section hercules_hydra_round_terminating.

  (* m contains only copies of x *)
  Notation only_copies x m := (∀y, y ∈ m → x = y).

  (* A head cut on the root, ie at height 1, no response from the hydra *)
  Inductive hh_round_root : hydra → hydra → Prop :=
    | hh_round_root_0 l r : ⟨l⊣⨸⊢r⟩ ⊳₁ ⟨l⊣⊢r⟩
  where "h ⊳₁ g" := (hh_round_root h g).

  (* A head cut at height ≥ 2, followed by a response of the hydra *)
  Inductive hh_round_deep : hydra → hydra → Prop :=
    | hh_round_deep_0 l₀ r₀ l₁ r₁ m : only_copies ⟨l₀⊣⊢r₀⟩ m → ⟨l₁⊣⟨l₀⊣⨸⊢r₀⟩⊢r₁⟩ ⊳₂ ⟨l₁⊣⊢m⊣⊢r₁⟩
    | hh_round_deep_1 l h g r : h ⊳₂ g  →  ⟨l⊣h⊢r⟩ ⊳₂ ⟨l⊣g⊢r⟩
  where "h ⊳₂ g" := (hh_round_deep h g).

  (* A round is either a root round or a deep round *)
  Inductive hh_round : hydra → hydra → Prop :=
    | hh_round_1 h g : h ⊳₁ g → h ⊳ g
    | hh_round_2 h g : h ⊳₂ g → h ⊳ g
  where "h ⊳ g" := (hh_round h g).

  Hint Constructors hh_round_root hh_round_deep hh_round : core.

  Local Fact cut_lpo l r : lpo ⟨l⊣⊢r⟩ ⟨l⊣⨸⊢r⟩.
  Proof.
    constructor.
    change r with ([]⊣⊢r).
    now apply lo_ctx, lo_intro.
  Qed.

  Hint Resolve cut_lpo : core.

  Local Fact hh_round_root_lpo h g : h ⊳₁ g → lpo g h.
  Proof. intros []; auto. Qed.

  Local Lemma hh_round_deep_lpo g h : h ⊳₂ g → lpo g h.
  Proof.
    induction 1 as [ l0 r0 l1 r1 m H | l h h' r H IH ].
    + constructor.
      rewrite app_ass.
      apply lo_ctx, lo_intro.
      intros ? <-%H; auto.
    + constructor.
      apply lo_ctx, lo_intro.
      now intros ? [ <- | [] ].
  Qed.

  Hint Resolve hh_round_root_lpo hh_round_deep_lpo : core.

  Local Lemma hh_round_lpo g h : h ⊳ g → lpo g h.
  Proof. induction 1; auto. Qed.

  Hint Resolve hh_round_lpo : core.

  Theorem hh_round_terminating h : terminating hh_round h.
  Proof. apply wf_incl with (2 := wf_lpo); red; eauto. Qed.

End hercules_hydra_round_terminating.

(** Terminating implies every R-sequence reaches a terminal point *)

Definition terminal {X} (R : X → X → Prop) x := ∀y, ~ R x y.

Section terminating_terminal.

  Variables (X : Type) (R : X → X → Prop)
            (p : nat → X) 
            (Hp : ∀n, terminal R (p n) ∨ R (p n) (p (S n))).

  Theorem terminating_terminal : terminating R (p 0) → ∃n, terminal R (p n).
  Proof.
    generalize 0.
    refine (fix loop i a { struct a } := _).
    destruct (Hp i) as [ Hi | Hi ].
    + now exists i.
    + apply (loop (S i)), Acc_inv with (1 := a), Hi.
  Qed.

End terminating_terminal.

(** Maximum of a list of natural numbers *)

Definition lmax := fold_right max 0.

Lemma lmax_locate m :  m = [] ∨ ∃ l r, m = l++[lmax m]++r.
Proof.
  induction m as [ | x m [ -> | (l & r & E) ] ]; eauto; simpl; right.
  + exists [], []; simpl; f_equal; now rewrite Nat.max_0_r.
  + destruct (Nat.le_gt_cases x (lmax m)).
    * rewrite max_r; auto.
      exists (x::l), r; simpl; f_equal; auto.
    * rewrite max_l; [|now apply Nat.lt_le_incl].
      now exists [], m. 
Qed.

Fact lmax_in x l : x ∈ l → x ≤ lmax l.
Proof.
  induction l as [ | y l IHl ]; simpl; try tauto. 
  intros [ | ?%IHl ]; subst; simpl; tauto || lia.
Qed.

(** Tools using the height of a hydra *)

(* Like hydra_ind, this is a guarded nested fixpoint *)
Fixpoint hydra_ht (h : hydra) : nat :=
  match h with
  | ⟨l⟩ => lmax (map (λ g, 1+⌊g⌋) l)
  end
where "⌊ h ⌋" := (hydra_ht h).

Fact hydra_ht_cons h l : ⌊⟨h::l⟩⌋ = max (1+⌊h⌋) ⌊⟨l⟩⌋.
Proof. reflexivity. Qed.

Fact hydra_ht_in h l : h ∈ l → 1+⌊h⌋ ≤ ⌊⟨l⟩⌋.
Proof. intros H; simpl; apply lmax_in, in_map_iff; eauto. Qed.

Fact hydra_ht_0_inv h : ⌊h⌋ = 0 → h = ⨸.
Proof.
  destruct h as [ [ | x m ] ]; simpl; auto.
  now destruct (lmax (map (λ g, S ⌊g⌋) m)).
Qed.

Fact hydra_ht_S_inv h n : ⌊h⌋ = S n → ∃ l g r, h = ⟨l⊣g⊢r⟩ ∧ ⌊g⌋ = n.
Proof.
  destruct h as [m]; intros H; simpl in H.
  destruct (lmax_locate (map (λ g, S ⌊g⌋) m)) as [ E | (l & r & E) ].
  + now rewrite E in H.
  + simpl in E.
    apply map_eq_app in E as (l' & ? & H1 & H2 & (g & r' & -> & H3 & H4)%map_eq_cons).
    exists l', g, r'; split; [ f_equal; auto | ].
    rewrite H in H3; now inversion H3.
Qed.

Fact hydra_ht_1_inv h : ⌊h⌋ = 1 → ∃ l₀ r₀, h = ⟨l₀⊣⨸⊢r₀⟩.
Proof. intros (? & ? & ? & ? & ?%hydra_ht_0_inv)%hydra_ht_S_inv; subst; eauto. Qed.

Fact hydra_ht_2_inv h : ⌊h⌋ = 2 → ∃ l₀ r₀ l₁ r₁, h = ⟨l₁⊣⟨l₀⊣⨸⊢r₀⟩⊢r₁⟩.
Proof. intros (? & ? & ? & ? & (? & ? & ?)%hydra_ht_1_inv)%hydra_ht_S_inv; subst; eauto. Qed.

Section hercules_wins.

  Infix "⊳₁" := hh_round_root.
  Infix "⊳₂" := hh_round_deep.
  Infix "⊳" := hh_round.

  Hint Constructors hh_round_deep hh_round_root hh_round : core.

  Local Fact hydra_ht_1_hh_round_root h : ⌊h⌋ = 1 → ∃g, h ⊳₁ g.
  Proof. intros (? & ? & ->)%hydra_ht_1_inv; eauto. Qed.

  Local Fact hydra_ht_2_hh_round_deep h : ∀n, ⌊h⌋ = S (S n) → ∃g, h ⊳₂ g.
  Proof.
    induction h as [ m IH ]; intros [ | n ].
    + intros (l0 & r0 & l1 & r1 & ->)%hydra_ht_2_inv.
      exists ⟨l1⊣⊢[]⊣⊢r1⟩; now constructor 1.
    + intros (? & ? & ? & ->%hydra_cons_inj & []%IH)%hydra_ht_S_inv; eauto.
  Qed.

  Local Fact hh_round_root_nil_inv h g : h ⊳₁ g → h ≠ ⨸.
  Proof. now intros [[] ]. Qed.

  Local Fact hh_round_deep_nil_inv h g : h ⊳₂ g → h ≠ ⨸.
  Proof. now intros [ ? ? [] | [] ]. Qed.

  Hint Resolve hh_round_root_nil_inv hh_round_deep_nil_inv : core.

  Local Fact hh_round_nil_inv h g : h ⊳ g → h ≠ ⨸.
  Proof. intros []; eauto. Qed.

  (* The single head is the only hydra which cannot be cut further *)
  Lemma terminal_hh_round_iff h : terminal hh_round h ↔ h = ⨸.
  Proof.
    split.
    + intros H. 
      case_eq ⌊h⌋.
      * apply hydra_ht_0_inv.
      * intros [ | n ].
        - intros (g & ?)%hydra_ht_1_hh_round_root.
          destruct (H g); auto.
        - intros (g & ?)%hydra_ht_2_hh_round_deep.
          destruct (H g); eauto.
    + now intros -> ? []%hh_round_nil_inv.
  Qed.

  (** A game is a sequence of stages composed of an hydra.
      At every stage, either the hydra is dead, or the hydra
      at the next stage follows from a hercules-hydra round.

      Notice that the stage after a dead hydra can be anything,
      hence can possibly be viewed as the start of a new game. *)

  Variables (game : nat → hydra)
            (game_spec : ∀n, game n = ⨸ ∨ game n ⊳ game (S n)).

  Let game_term n : terminal hh_round (game n) ∨ game n ⊳ game (S n).
  Proof. now rewrite terminal_hh_round_iff. Qed.

  (* In any game, there is a stage with a dead hydra *)
  Corollary hercules_wins : ∃n, game n = ⨸.
  Proof.
    destruct terminating_terminal 
      with (1 := game_term)
           (2 := hh_round_terminating (game 0))
      as (n & Hn).
    exists n; now apply terminal_hh_round_iff.
  Qed.

End hercules_wins.

Check hercules_wins.
Print Assumptions hercules_wins.

Section hydra_rect.

  (* The Type-bounded eliminator/recursor will usefull
     to build the isomorphism between the nested hydra
     and the mutual Hydra/Hydrae below *)

  (* We use the nested elimnator hydra_ind to show that 
     the direct sub-hydra relation is well_founded *)
  Let sub_hydra_wf : well_founded (λ g h, match h with ⟨l⟩ => g ∈ l end).
  Proof. intros h; induction h; now constructor. Qed.

  Variables (P : hydra → Type)
            (HP : ∀l, (∀h, h ∈ l → P h) → P ⟨l⟩).

  (* We use Acc(essibility) for sub_hydra to implement the 
     hydra_rect eliminator in Type, also avoiding large elimination
     of Acc by using Acc_inv in Prop context *)
  Definition hydra_rect h : P h :=
    (fix loop h a { struct a } :=
      match h return Acc _ h → P h with
      | ⟨l⟩ => λ a, HP _ (λ _ H, loop _ (Acc_inv a H))
      end a) h (sub_hydra_wf h).

End hydra_rect.

Definition hydra_rec (P : _ → Set) := hydra_rect P.

Fact fold_right_conj {X} (P : X → Prop) l :
         fold_right (λ x, and (P x)) True l ↔ ∀x, x ∈ l → P x.
Proof.
  rewrite <- Forall_forall.
  induction l; simpl.
  + split; constructor.
  + now rewrite Forall_cons_iff, IHl.
Qed.

Fixpoint hydra_fall (P : list hydra → Prop) (h : hydra) : Prop :=
  match h with
  | ⟨l⟩ => P l ∧ fold_right (λ g, and (hydra_fall P g)) True l
  end.

Fact hydra_fall_fix P l : hydra_fall P ⟨l⟩ ↔ P l ∧ ∀x, x ∈ l → hydra_fall P x.
Proof. now simpl; rewrite fold_right_conj. Qed.

Section hydra_fall_rect.

  Variables (P : list hydra → Prop) (Q : hydra → Type)
            (HQ : ∀l, P l 
                    → (∀x, x ∈ l → hydra_fall P x)
                    → (∀x, x ∈ l → Q x)
                    → Q ⟨l⟩).

  Theorem hydra_fall_rect h : hydra_fall P h → Q h.
  Proof. induction h; intros []%hydra_fall_fix; eauto. Qed.

End hydra_fall_rect.

Module hydra_notations.

  Infix "∈" := In.

  Notation "⟨ l ⟩" := (hydra_cons l).
  Notation "⨸" := ⟨[]⟩.

  Notation  "l ⊣ x ⊢ r" := (l++[x]++r).
  Notation "l ⊣⊢ r" := (l++r).

End hydra_notations.

