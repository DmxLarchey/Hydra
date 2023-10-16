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

(** Maximum of a list of natural numbers *)

Definition lmax := fold_right max 0.

Lemma lmax_locate m :  m = [] ∨ ∃ l r, m = l++[lmax m]++r.
Proof.
  induction m as [ | x m [ -> | (l & r & E) ] ]; eauto; simpl; right.
  + exists [], []; simpl; f_equal; now rewrite max_0_r.
  + destruct (le_lt_dec x (lmax m)).
    * rewrite max_r; auto.
      exists (x::l), r; simpl; f_equal; auto.
    * rewrite max_l; [|now apply lt_le_incl].
      now exists [], m. 
Qed.

(** Inductiob definition (Acc based) of R is terminating at x *)

Definition terminating {X} (R : X → X → Prop) x := Acc (λ x y, R y x) x.
Definition terminal {X} (R : X → X → Prop) x := ∀y, ~ R x y.

Section terminating_terminal.

  Variables (X : Type) (R : X → X → Prop)
            (p : nat → X) (Hp : ∀n, terminal R (p n) ∨ R (p n) (p (S n))).

  Theorem terminating_terminal : terminating R (p 0) → ∃n, terminal R (p n).
  Proof.
    generalize 0.
    refine (fix loop i a { struct a } := _).
    destruct (Hp i) as [ Hi | Hi ].
    + now exists i.
    + apply (loop (S i)), Acc_inv with (1 := a), Hi.
  Qed.

End terminating_terminal.

(** The list order is a weak variant of the multiset order on list 

   The proof displayed here is largely inspired from 
   the short outline of Tobias Nipkow and Wilfried Buchholz 

     http://www4.in.tum.de/~nipkow/misc/multiset.ps

*)

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
  Local Lemma Forall_Acc_lo_step l : Forall (Acc R) l → Acc lo_step l.
  Proof. induction 1; eauto. Qed.

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

  Hint Resolve Acc_lo_forall Forall_Acc_lo_step Acc_clos_trans : core.

  (* This is the main theorem characterizing mso Acc(essibility) *)
  Theorem Acc_lo_iff l : Acc lo l ↔ Forall (Acc R) l.
  Proof. unfold lo; split; eauto; rewrite Forall_forall; eauto. Qed.

  Corollary wf_mso : well_founded R → well_founded lo.
  Proof. intros ? ?; apply Acc_lo_iff, Forall_forall; auto. Qed.
 
End list_order.

Arguments lo {_}.

(** Hydras are undecorated and oriented rose trees.
    We need to generate versatile eliminators by hand.
*)

Unset Elimination Schemes.

Inductive hydra := hydra_cons : list hydra → hydra.

Set Elimination Schemes.

#[local] Notation "⟨ l ⟩" := (hydra_cons l).
#[local] Notation "⨸" := ⟨[]⟩.

Section hydra_ind.

  Variables (P : hydra → Prop)
            (HP : ∀l, (∀h, h ∈ l → P h) → P ⟨l⟩).

  (* The Prop-bounded eliminator proceeds by nested fixpoints,
     unavoidable for nested inductive types *)
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

Section hydra_rect.

  (* We use the nested elimnator hydra_ind to show that 
     the direct sub-hydra relation is well_founded *)
  Let sub_hydra_wf : well_founded (λ g h, match h with ⟨l⟩ => g ∈ l end).
  Proof. intros h; induction h; now constructor. Qed.

  Variables (P : hydra → Type)
            (HP : ∀l, (∀h, h ∈ l → P h) → P ⟨l⟩).

  (* We use Acc(essibility) for sub_hydra to implement the 
     hydra_rect eliminator in Type, though avoiding large elimination 
     by using Acc_inv *)
  Definition hydra_rect h : P h :=
    (fix loop h a { struct a } :=
      match h return Acc _ h → P h with
      | ⟨l⟩ => λ a, HP _ (λ _ H, loop _ (Acc_inv a H))
      end a) h (sub_hydra_wf h).

End hydra_rect.

(* Like hydra_ind, this is an accepted nested fixpoint *)
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


(** Weak variant of the multiset path ordering on hydra
    one could add two other constructors and stability 
    under permutations and still keep it wf *)

Unset Elimination Schemes.

Inductive lpo : hydra → hydra → Prop :=
  | lpo_intro l m : lo lpo l m → lpo ⟨l⟩ ⟨m⟩.

Set Elimination Schemes.

Theorem wf_lpo h : Acc lpo h.
Proof. 
  induction h as [ l IHl%Forall_forall%Acc_lo_iff ].
  induction IHl as [ m _ IHm ].
  constructor.
  intro g; induction g.
  inversion 1; eauto.
Qed.

#[local] Notation only_copies x c := (∀y, y ∈ c → x = y).

Section hercules.

  Inductive hround_root : hydra → hydra → Prop :=
    | hround_root_0 l r : ⟨l⊣⨸⊢r⟩ ⊳₁ ⟨l⊣⊢r⟩
  where "h ⊳₁ g" := (hround_root h g).

  Inductive hround_deep : hydra → hydra → Prop :=
    | hround_deep_0 l₀ r₀ l₁ r₁ m : only_copies ⟨l₀⊣⊢r₀⟩ m → ⟨l₁⊣⟨l₀⊣⨸⊢r₀⟩⊢r₁⟩ ⊳₂ ⟨l₁⊣⊢m⊣⊢r₁⟩
    | hround_deep_1 l h g r : h ⊳₂ g  →  ⟨l⊣h⊢r⟩ ⊳₂ ⟨l⊣g⊢r⟩
  where "h ⊳₂ g" := (hround_deep h g).

  Inductive hround : hydra → hydra → Prop :=
    | hround_1 h g : h ⊳₁ g → h ⊳ g
    | hround_2 h g : h ⊳₂ g → h ⊳ g
  where "h ⊳ g" := (hround h g).

  Hint Constructors hround_root hround_deep hround : core.

  Local Fact cut_lpo l r : lpo ⟨l⊣⊢r⟩ ⟨l⊣⨸⊢r⟩.
  Proof.
    constructor.
    change r with ([]⊣⊢r).
    now apply lo_ctx, lo_intro.
  Qed.

  Hint Resolve cut_lpo : core.

  Local Fact hround_root_lpo h g : h ⊳₁ g → lpo g h.
  Proof. intros []; auto. Qed.

  Local Lemma hround_deep_lpo g h : h ⊳₂ g → lpo g h.
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

  Hint Resolve hround_root_lpo hround_deep_lpo : core.

  Local Lemma hround_lpo g h : h ⊳ g → lpo g h.
  Proof. induction 1; auto. Qed.

  Hint Resolve hround_lpo : core.

  Theorem hround_terminating h : terminating hround h.
  Proof. apply wf_incl with (2 := wf_lpo); red; eauto. Qed.

  Local Fact hydra_ht_1_hround_root h : ⌊h⌋ = 1 → ∃g, h ⊳₁ g.
  Proof. intros (? & ? & ? & -> & ->%hydra_ht_0_inv)%hydra_ht_S_inv; eauto. Qed.

  Local Fact hydra_ht_2_hround_deep h : ∀n, ⌊h⌋ = S (S n) → ∃g, h ⊳₂ g.
  Proof.
    induction h as [ m IH ]; intros [ | n ] E.
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

  Local Fact hround_root_nil_inv h g : h ⊳₁ g → h ≠ ⨸.
  Proof. now intros [[] ]. Qed.

  Local Fact hround_deep_nil_inv h g : h ⊳₂ g → h ≠ ⨸.
  Proof. now intros [ ? ? [] | [] ]. Qed.

  Hint Resolve hround_root_nil_inv hround_deep_nil_inv : core.

  Local Fact hround_nil_inv h g : h ⊳ g → h ≠ ⨸.
  Proof. intros []; eauto. Qed.

  (* The single head is the only hydra which cannot be cut further *)
  Lemma terminal_hround_iff h : terminal hround h ↔ h = ⨸.
  Proof.
    split.
    + intros H. 
      case_eq ⌊h⌋.
      * apply hydra_ht_0_inv.
      * intros [ | n ].
        - intros (g & ?)%hydra_ht_1_hround_root.
          destruct (H g); auto.
        - intros (g & ?)%hydra_ht_2_hround_deep.
          destruct (H g); eauto.
    + now intros -> ? []%hround_nil_inv.
  Qed.

  Variables (play : nat → hydra)
            (Hplay : ∀n, play n = ⨸ ∨ play n ⊳ play (S n)).

  Let Hplay_spec n : terminal hround (play n) ∨ play n ⊳ play (S n).
  Proof. now rewrite terminal_hround_iff. Qed.

  Corollary hercules_hydra_rounds : ∃n, play n = ⨸.
  Proof.
    destruct terminating_terminal 
      with (1 := Hplay_spec)
           (2 := hround_terminating (play 0))
      as (n & Hn).
    exists n; now apply terminal_hround_iff.
  Qed.

End hercules.

Check hercules_hydra_rounds.
Print Assumptions hercules_hydra_rounds.
