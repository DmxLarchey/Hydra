(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import PeanoNat List Relations Wellfounded Utf8.

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
#[local] Notation  "l ⊣ x ⊢ r" := (l++[x]++r) (at level 1, format "l ⊣ x ⊢ r").
#[local] Notation "l '⊣⊢' r" := (l++r) (at level 1, format "l ⊣⊢ r").

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

    Let W_app_bound y r :
        (∀x, x ≺ y → ∀l, W l → W (x::l))
       → W r 
       → ∀l, l ≺ₗ y → W (l++r).
    Proof.
      intros hy ?. 
      induction l; simpl; eauto.
      intros; apply hy; eauto.
    Qed.

    Let W_cons_rec y m :
           (∀x, x ≺ y → ∀l, W l → W (x::l))
         → W m
         → (∀l, l ⊏ m → W (y::l))
         → W (y::m).
    Proof. constructor; intros ? [ (? & -> & ?) | (? & ? & ? & ? & -> & -> & ?) ]%lo_step_cons_right_inv; eauto. Qed.

    Let W_cons y : (∀x, x ≺ y → ∀l, W l → W (x::l)) → ∀l, W l → W (y::l).
    Proof. induction 2; eauto. Qed.

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

  Fact lo_cons x l : l ⊏⁺ x::l.
  Proof. red; auto. Qed.

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

#[local] Notation "⟨ l ⟩" := (hydra_cons l).
#[local] Notation "⨸" := ⟨[]⟩.  (* the head hydra *)

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

(** Tools using the height of a hydra *)

(* Like hydra_ind, this is a guarded nested fixpoint *)
Fixpoint hydra_ht (h : hydra) : nat :=
  match h with
  | ⟨l⟩ => lmax (map (λ g, 1+⌊g⌋) l)
  end
where "⌊ h ⌋" := (hydra_ht h).

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

Section Hydrae.

  Inductive Hydra :=
    | Hydra_node  : Hydrae → Hydra
  with Hydrae :=
    | Hydrae_nil  : Hydrae
    | Hydrae_cons : Hydra → Hydrae → Hydrae.

  Inductive Fall2_Hl {X} (R : Hydra → X → Prop) : Hydrae → list X → Prop :=
    | Fall2_Hl_nil : Fall2_Hl R Hydrae_nil []
    | Fall2_Hl_cons H HH x l : R H x → Fall2_Hl R HH l → Fall2_Hl R (Hydrae_cons H HH) (x::l).

  Fact Fall2_Hl_inv X R HH l :
        @Fall2_Hl X R HH l
      → match HH, l with
        | Hydrae_nil,       []   => True
        | Hydrae_cons H HH, x::l => R H x ∧ Fall2_Hl R HH l
        | _,                _    => False
        end.
  Proof. intros []; eauto. Qed.

  Inductive Hydra_hydra_eq : Hydra → hydra → Prop :=
    | Hh_eq HH m : Fall2_Hl Hydra_hydra_eq HH m → Hydra_hydra_eq (Hydra_node HH) ⟨m⟩.

  Hint Constructors Hydra Hydrae Fall2_Hl Hydra_hydra_eq : core.

  Fact Hydra_hydra_eq_inv HH m : Hydra_hydra_eq (Hydra_node HH) ⟨m⟩ → Fall2_Hl Hydra_hydra_eq HH m.
  Proof. now inversion 1. Qed.

  (* The relation Hydra_hydra_eq is functional and injective *)

  Fixpoint Hydra_hydra_eq_fun H h (e : Hydra_hydra_eq H h) { struct e } : ∀g, Hydra_hydra_eq H g → h = g.
  Proof.
    destruct e as [ HH m E1 ].
    intros [ l ] E2%Hydra_hydra_eq_inv.
    revert l E2.
    induction E1 as [ | H HH x m E1 E2 IHE2 ].
    + intros [] ?%Fall2_Hl_inv; now auto.
    + intros [ | y l ] E3%Fall2_Hl_inv; [ easy | ].
      destruct E3 as [ E3 E4 ].
      do 2 f_equal.
      * apply (Hydra_hydra_eq_fun _ _ E1 _ E3).
      * specialize (IHE2 _ E4); now inversion IHE2.
  Qed.

  Fixpoint Hydra_hydra_eq_inj H h (e : Hydra_hydra_eq H h) { struct e } : ∀G, Hydra_hydra_eq G h → H = G.
  Proof.
    destruct e as [ HH m E1 ].
    intros [ GG ] E2%Hydra_hydra_eq_inv.
    revert GG E2.
    induction E1 as [ | H HH x m E1 E2 IHE2 ].
    + intros [] ?%Fall2_Hl_inv; now auto.
    + intros [ | G GG ] E3%Fall2_Hl_inv; [ easy | ].
      destruct E3 as [ E3 E4 ].
      do 2 f_equal.
      * apply (Hydra_hydra_eq_inj _ _ E1 _ E3).
      * specialize (IHE2 _ E4); now inversion IHE2.
  Qed.

  (* The relation Hydra_hydra_eq can be realized by a function in both directions.
     This is a mutual fixpoint.*)

  Fixpoint Hydra2hydra_pwc H : { h | Hydra_hydra_eq H h }
  with Hydrae2list_hydra_pwc HH : { m | Fall2_Hl Hydra_hydra_eq HH m }.
  Proof.
    + destruct H as [ HH ].
      destruct (Hydrae2list_hydra_pwc HH) as (m & Hm).
      exists ⟨m⟩; eauto.
    + destruct HH as [ | H HH ].
      * exists []; eauto.
      * destruct (Hydra2hydra_pwc H) as (h & ?).
        destruct (Hydrae2list_hydra_pwc HH) as (m & ?).
        exists (h::m); eauto.
  Qed.

  (* We use that hydra_rect recursor above here, which contains a 
     fixpoint itself *)
  Definition hydra2Hydra_pwc (h : hydra) : { H | Hydra_hydra_eq H h }.
  Proof.
    induction h as [ m IHm ] using hydra_rect.
    assert { HH | Fall2_Hl Hydra_hydra_eq HH m } as (HH & ?); eauto.
    revert IHm.
    induction m as [ | h m IHm ]; intros Hm; eauto.
    destruct (Hm h) as (H & ?); auto.
    destruct IHm as (HH & ?); eauto.
  Qed.

  (* hydra2Hydra/Hydra2hydra form a bijection *)

  Definition Hydra2hydra H := proj1_sig (Hydra2hydra_pwc H).
  Definition hydra2Hydra h := proj1_sig (hydra2Hydra_pwc h).

  Fact Hydra2hydra_spec H : Hydra_hydra_eq H (Hydra2hydra H).    Proof. apply (proj2_sig _). Qed.
  Fact hydra2Hydra_spec h : Hydra_hydra_eq (hydra2Hydra h) h.    Proof. exact (proj2_sig (hydra2Hydra_pwc _)). Qed.

  Hint Resolve hydra2Hydra_spec Hydra2hydra_spec : core.

  Theorem hydra2Hydra2hydra H : hydra2Hydra (Hydra2hydra H) = H.
  Proof. apply Hydra_hydra_eq_inj with (1 := hydra2Hydra_spec _); auto. Qed.

  Theorem Hydra2hydra2Hydra h : Hydra2hydra (hydra2Hydra h) = h.
  Proof. apply Hydra_hydra_eq_fun with (1 := Hydra2hydra_spec _); auto. Qed.

  (* We can derive fixpont equations for hydra2Hydra_fix and Hydra2hydra_fix *)

  Fixpoint fold_Hydrae {X} (f : Hydra → X → X) x HH :=
    match HH with
    | Hydrae_nil       => x
    | Hydrae_cons H HH => f H (fold_Hydrae f x HH)
    end.

  Lemma hydra2Hydra_fix l : hydra2Hydra ⟨l⟩ = Hydra_node (fold_right (λ x HH, Hydrae_cons (hydra2Hydra x) HH) Hydrae_nil l).
  Proof.
    apply Hydra_hydra_eq_inj with (1 := hydra2Hydra_spec _).
    constructor.
    induction l; simpl; eauto.
  Qed.

  Lemma Hydra2hydra_fix HH : Hydra2hydra (Hydra_node HH) = ⟨fold_Hydrae (λ H l, (Hydra2hydra H)::l) [] HH⟩.
  Proof.
    apply Hydra_hydra_eq_fun with (1 := Hydra2hydra_spec _).
    constructor.
    induction HH; simpl; eauto.
  Qed.

End Hydrae.








 
