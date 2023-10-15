(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

From Coq Require Import List Permutation Relations Wellfounded Utf8.
From Coq Require Import PeanoNat Arith Lia.

Import ListNotations Nat.

Arguments In {_}.
Arguments app {_}.
Arguments clos_refl_trans {_}.
Arguments clos_trans {_}.

#[local] Reserved Notation "f ↑ n" (at level 1, left associativity, format "f ↑ n").

#[local] Reserved Notation "x '<ₗ' y" (at level 70, no associativity, format "x  <ₗ  y").
#[local] Reserved Notation "x '⊏' y" (at level 70, no associativity, format "x  ⊏  y").
#[local] Reserved Notation "x '⊏⁺' y" (at level 70, no associativity, format "x  ⊏⁺  y").

#[local] Reserved Notation "⟨ l ⟩" (at level 0, l at level 200, format "⟨ l ⟩").
#[local] Reserved Notation "⌊ t ⌋" (at level 0, t at level 200, format "⌊ t ⌋").

#[local] Infix "∈" := In (at level 70, no associativity).
#[local] Notation "l '~ₚ' m" := (@Permutation _ l m) (at level 70, no associativity, format "l  ~ₚ  m").

#[local] Notation  "l ⟞ x ⟝ r" := (l++[x]++r) (at level 1, format "l ⟞ x ⟝ r").
#[local] Notation "l ⟛ r" := (l++r) (at level 1, format "l ⟛ r").

#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app 

                      Permutation_app_inv Permutation_app_middle Permutation_app
                      Permutation_sym Permutation_trans Permutation_cons_app
                      Permutation_in

                      : core.

Fact cons_inj {X} (x y : X) l m : x::l = y::m → x = y ∧ l = m.
Proof. now inversion 1. Qed.

Fact app_nil_inv {X} (l m : list X) : l⟛m = [] → l = [] ∧ m = [].
Proof. revert l m; now intros [] []. Qed.

Fact Permutation_middle_inv {X} l (x : X) r m :
       l++[x]++r ~ₚ m → ∃ l' r', m = l'++[x]++r' ∧ l++r ~ₚ l'++r'.
Proof.
  intros H.
  assert (x ∈ m) as (l' & r' & ->)%in_split; 
    simpl in H |- *; eauto.
Qed.

Fixpoint iter {X} (f : X → X) n :=
  match n with
  | 0 =>   λ x, x
  | S n => λ x, f↑n (f x)
  end
where "f ↑ n" := (iter f n).

(** Wellfounded strategy *)

Definition terminating {X} (R : X → X → Prop) x := Acc (λ x y, R y x) x.
Definition terminal {X} (R : X → X → Prop) x := ∀y, ~ R x y.
Definition move {X} (R : X → X → Prop) s := ∀x, { R x (s x) } + { terminal R x }.

Section well_founded_play.

  Variables (X : Type) (R : X → X → Prop)
            (p : nat → X) (Hp : forall n, { R (p n) (p (S n)) } + { terminal R (p n) }).

  Local Fixpoint play_until n (a : Acc (λ x y, R y x) (p n)) { struct a } : { m | terminal R (p m) }.
  Proof.
    destruct (Hp n) as [ H1 | H1 ].
    + apply (play_until (S n)), Acc_inv with (1 := a), H1.
    + now exists n.
  Qed.

  Theorem play_terminates : terminating R (p 0) → { n | terminal R (p n) }.
  Proof. apply play_until. Qed.

End well_founded_play.

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

Lemma lmax_locate ll : { l : _ & { r | ll = l⟞lmax ll⟝r } } + { ll = [] }.
Proof.
  induction ll as [ | x ll [ (l & r & E) | -> ] ]; eauto; simpl; left.
  + destruct (le_lt_dec x (lmax ll)).
    * rewrite max_r; auto.
      exists (x::l), r; simpl;f_equal; auto.
    * rewrite max_l; [|now apply lt_le_incl].
      now exists [], ll. 
  + exists [], []; simpl; f_equal; now rewrite max_0_r.
Qed.

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
    + intros (x & m' & -> & <- & E)%map_cons_inv.
      destruct (IH _ E) as (l & r & ? & ? & ?).
      exists (x::l), r; subst; simpl; auto.
  Qed.

End map_eq_inv.

(** Hydras are undecorated rose trees *)

Unset Elimination Schemes.
Inductive hydra := hcons : list hydra → hydra.
Set Elimination Schemes.

#[local] Notation "⟨ l ⟩" := (hcons l).

Section hydra_rect.

  Let sub_wf : well_founded (λ g h, match h with ⟨l⟩ => g ∈ l end).
  Proof.
    refine (fix loop h :=
      match h with 
      | ⟨l⟩ => Acc_intro _ _
      end).
    induction l as [ | g l IHl ].
    + intros ? [].
    + intros ? [ <- | H ].
      * apply loop.
      * now apply IHl.
  Qed.

  Variables (P : hydra → Type)
            (HP : ∀l, (∀h, h ∈ l → P h) → P ⟨l⟩).

  Theorem hydra_rect h : P h.
  Proof.
    generalize (sub_wf h); revert h.
    refine (fix loop h d { struct d } := _).
    destruct h as [ l ]; apply HP.
    intros ? H; apply loop.
    apply Acc_inv with (1 := d), H.
  Qed.

End hydra_rect.

Definition hydra_rec (P : _ → Set) := @hydra_rect P.
Definition hydra_ind (P : _ → Prop) := @hydra_rect P.

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

  Inductive mso_step : list X → list X → Prop :=
    | mso_step_intro l m x r : m <ₗ x 
                             → l++m++r ⊏ l++[x]++r
    | mso_step_perm_l l m k  : l ~ₚ m 
                             → l ⊏ k 
                             → m ⊏ k
  where "l ⊏ m" := (mso_step l m).

  Hint Constructors mso_step : core.

  (* The inversion lemma gives an alternate characterization *)
  Fact mso_step_inv k p : 
         k ⊏ p ↔ ∃ l m x r, k ~ₚ l++m++r ∧ p = l++[x]++r ∧ m <ₗ x.
  Proof.
    split.
    + induction 1 as [ l m x r | ? ? ? ? ? (l' & m' & x' & r' & ? & -> & ?) ].
      * now exists l, m, x, r.
      * exists l', m', x', r'; eauto.
    + intros (? & ? & ? & ? & ? & -> & ?); eauto.
  Qed.

  Fact mso_step_inv_sg_rt l x : l ⊏ [x] ↔ l <ₗ x.
  Proof.
    rewrite mso_step_inv; split.
    + intros (a & m & y & b & H1 & H2 & H3).
      destruct a as [ | ? [] ]; try easy; simpl in *.
      inversion H2; subst y b.
      rewrite <- app_nil_end in H1.
      revert H3; apply perm_forall_less; auto.
    + exists [], l, x, []; simpl; rewrite <- app_nil_end; auto.
  Qed.

  Fact mso_step_inv_sg_lft l x : [x] ⊏ l → x ∈ l ∧ l ≠ [x] ∨ ∃ y, y ∈ l ∧ x < y.
  Proof.
    intros (a & m & y & b & H1%Permutation_length_1_inv & H2 & H3)%mso_step_inv.
    destruct a as [ | x' a ].
    2:{ simpl in H1; apply cons_inj in H1 as (<- & (-> & (-> & ->)%app_nil_inv)%app_nil_inv).
        left; subst; simpl; split; now auto. }
    simpl in *.
    destruct m as [ | x' m ].
    2:{ simpl in H1; apply cons_inj in H1 as (<- & (-> & ->)%app_nil_inv). 
        right; exists y; subst; split; auto. }
    simpl in *; subst; left; split; now auto.
  Qed.

  (* ⊏ is contextually closed *)
  Fact mso_step_ctx l r u v : u ⊏ v → l++u++r ⊏ l++v++r.
  Proof.
    induction 1 in l, r |- *; eauto.
    rewrite !app_ass, <- ! (app_ass l); eauto.
  Qed.

  (* ⊏ is closed under right permutation *)
  Fact mso_step_perm_r l m k : l ~ₚ m → k ⊏ l → k ⊏ m.
  Proof.
    intros H1 H2; revert H2 m H1.
    induction 1 as [ | ? ? ? ? ? IH ]; intro.
    + intros (? & ? & -> & ?)%Permutation_middle_inv; eauto.
    + intros ?%IH; eauto.
  Qed.

  (* The empty list is minimal for ⊏ *)
  Fact mso_step_nil_inv l : ~ l ⊏ [].
  Proof. now intros ([|] & ? & ? & ? & ? & ? & ?)%mso_step_inv. Qed.

  Fact mso_step_cons x l : l ⊏ x::l.
  Proof. now apply @mso_step_intro with (l := []) (m := []); simpl. Qed.

  Notation W := (Acc mso_step).

  Hint Resolve mso_step_perm_r Acc_intro : core.

  Fact Permutation_Acc_mso_step l m : l ~ₚ m → W m → W l.
  Proof. intros ? []; eauto. Qed.

  Fact Acc_mso_step_nil : W [].
  Proof. constructor 1; intros _ []%mso_step_nil_inv. Qed.

  Section Acc_mso_step_cons.

    Let W_app_bound y r :
        (∀x, x < y → ∀l, W l → W (x::l))
       → W r 
       → ∀l, l <ₗ y → W (l++r).
    Proof.
      intros hy hr. 
      induction l; simpl; eauto.
      intros; apply hy; eauto.
    Qed.

    Let mso_step_cons_right_inv k y m : 
          k ⊏ y::m 
        → (∃ u, k ~ₚ u ++ m ∧ u <ₗ y)
        ∨ (∃ l u x r, m = l++[x]++r ∧ k ~ₚ y::l++u++r ∧ u <ₗ x).
    Proof.
      intros ([ | z l] & u & x & r & hk & e & hu)%mso_step_inv; simpl in *;
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
      intros k [ (u & hk & hu) | (l & u & x & r & -> & hk & hu) ]%mso_step_cons_right_inv.
      + apply Permutation_Acc_mso_step with (1 := hk).
        apply (W_app_bound _ _ hy hm _ hu).
      + apply Permutation_Acc_mso_step with (1 := hk), ihm; eauto.
    Qed.

    Let W_cons y : (∀x, x < y → ∀l, W l → W (x::l)) → ∀l, W l → W (y::l).
    Proof. induction 2; eauto. Qed.

    Local Lemma Acc_mso_step_cons : ∀x, Acc R x → ∀l, W l → W (x::l).
    Proof. induction 1; eauto. Qed.

  End Acc_mso_step_cons.

  Hint Resolve Acc_mso_step_nil 
               Acc_mso_step_cons : core.

  (* W is closed under [] and x::_ for any accessible x
     so it contains any list composed of accessibles *) 
  Local Lemma Forall_Acc_mso_step l : Forall (Acc R) l → W l.
  Proof. induction 1; eauto. Qed.

  Definition mso := clos_trans mso_step.

  Infix "⊏⁺" := mso.

  (** Closure properties of mso/⊏⁺ *)

  (* The constructor for the basic reduction *)
  Fact mso_intro x l : l <ₗ x → l ⊏⁺ [x].
  Proof.
    constructor 1.
    rewrite (app_nil_end l).
    now constructor 1 with (l := []) (r := []).
  Qed.

  Hint Constructors clos_trans : core.
  Hint Resolve mso_step_ctx : core.

  (* Contextual closure *)
  Fact mso_ctx l r u v : u ⊏⁺ v → l++u++r ⊏⁺ l++v++r.
  Proof. unfold mso; induction 1 in l, r |- *; eauto. Qed.

  (* Transitivity *)
  Fact mso_trans l m p : l ⊏⁺ m → m ⊏⁺ p → l ⊏⁺ p.
  Proof. econstructor 2; eassumption. Qed.

  Hint Resolve mso_step_perm_l mso_step_perm_r : core.

  (* Closure under left/right permutations *)

  Fact mso_perm_l l m k : l ~ₚ m → l ⊏⁺ k → m ⊏⁺ k.
  Proof. unfold mso; intros H1 H2; revert m H1; induction H2; eauto. Qed.

  Fact mso_perm_r l m k : l ~ₚ m → k ⊏⁺ l → k ⊏⁺ m.
  Proof. unfold mso; intros H1 H2; revert m H1; induction H2; eauto. Qed.

  Fact mso_erase l x r : l++r ⊏⁺ l++[x]++r.
  Proof. apply mso_ctx with (u := []), mso_intro; now simpl. Qed.

  (* Closure under right head/tail append *)
  Fact mso_app_head l m r : m ⊏⁺ r → m ⊏⁺ l++r.
  Proof.
    intros H.
    induction l as [ | x l IH ]; simpl; auto. 
    apply mso_trans with (1 := IH),
          mso_erase with (l := []).
  Qed.

  Fact mso_app_tail l m r : m ⊏⁺ l → m ⊏⁺ l++r.
  Proof.
    intros H.
    induction r as [ | x r IH ]; simpl; auto.
    + now rewrite <- app_nil_end.
    + apply mso_trans with (1 := IH),
            mso_erase.
  Qed. 

  Hint Resolve mso_step_cons : core.

  Fact mso_cons x l : l ⊏⁺ x::l.
  Proof. red; auto. Qed.

  Lemma Acc_mso_forall l : Acc mso l → ∀x, x ∈ l → Acc R x.
  Proof.
    induction 1 as [ l _ IHl ]; intros x Hx.
    constructor; intros y Hy.
    apply IHl with (y := [y]); auto.
    apply in_split in Hx as (l' & r' & ->).
    apply mso_app_head, mso_app_tail with (l := [_]).
    apply mso_intro; now intros ? [ <- | [] ].
  Qed.

  Hint Resolve Acc_mso_forall Forall_Acc_mso_step Acc_clos_trans : core.

  (* This is the main theorem characterizing mso Acc(essibility) *)
  Theorem Acc_mso_iff l : Acc mso l ↔ Forall (Acc R) l.
  Proof. unfold mso; split; eauto; rewrite Forall_forall; eauto. Qed.

  Corollary wf_mso : well_founded R → well_founded mso.
  Proof. intros ? ?; apply Acc_mso_iff, Forall_forall; auto. Qed.
 
End multiset_order.

Arguments mso {_}.

Section multiset_path_ordering.

  (* Weak variant of the multiset path ordering on hydra
     one could add two other constructors and keep it wf *)

  Unset Elimination Schemes.

  Inductive mpo : hydra → hydra → Prop :=
    | mpo_list l m : mso mpo l m → mpo ⟨l⟩ ⟨m⟩.

  Set Elimination Schemes.

  Hint Resolve Acc_mso_forall : core.

  Theorem wf_mpo : well_founded mpo.
  Proof. 
    intros h; induction h as [ l IHl ].
    revert IHl; rewrite <- Forall_forall, <- Acc_mso_iff.
    induction 1 as [ m _ IHm ].
    constructor.
    intro g; induction g.
    inversion 1; eauto.
  Qed.

End multiset_path_ordering.

#[local] Notation "⨸" := ⟨[]⟩.
#[local] Notation only_copies x c := (∀ y, y ∈ c → x = y).

Section hercules.

  Inductive hcut_deep : hydra → hydra → Prop :=
    | hcut_deep_0 l₀ r₀ l₁ r₁ c : only_copies ⟨l₀⟛r₀⟩ c → hcut_deep ⟨l₁⟞⟨l₀⟞⨸⟝r₀⟩⟝r₁⟩ ⟨l₁⟛c⟛r₁⟩
    | hcut_deep_1 l h h' r : hcut_deep h h' → hcut_deep ⟨l⟞h⟝r⟩ ⟨l⟞h'⟝r⟩.

  Inductive hcut : hydra → hydra → Prop :=
    | hcut_d1 l r : hcut ⟨l⟞⨸⟝r⟩ ⟨l⟛r⟩
    | hcut_d2 h h' : hcut_deep h h' → hcut h h'.

  Local Fact cut_mpo l r : mpo ⟨l⟛r⟩ ⟨l⟞⨸⟝r⟩.
  Proof.
    constructor.
    change r with ([]++r).
    now apply mso_ctx, mso_intro.
  Qed.

  Hint Resolve cut_mpo : core.

  Local Lemma hcut_deep_mpo g h : hcut_deep h g → mpo g h.
  Proof.
    induction 1 as [ l0 r0 l1 r1 c Hc | l h h' r H IH ].
    + constructor.
      rewrite app_ass.
      apply mso_ctx, mso_intro.
      intros ? <-%Hc; auto.
    + constructor.
      apply mso_ctx, mso_intro.
      now intros ? [ <- | [] ].
  Qed.

  Hint Resolve hcut_deep_mpo : core.

  Local Lemma hcut_mpo g h : hcut h g → mpo g h.
  Proof. induction 1; auto. Qed.

  Hint Resolve hcut_mpo : core.

  Theorem hydra_terminating h : terminating hcut h.
  Proof.  apply wf_incl with (2 := wf_mpo); red; eauto. Qed.

  (* Now we study a sequence of moves *)

  Fact hydra_ht_0_inv h : ⌊h⌋ = 0 → h = ⨸.
  Proof.
    destruct h as [ [ | x m ] ]; simpl; auto.
    now destruct (lmax (map (λ g, S ⌊g⌋) m)).
  Qed.

  Fact hydra_ht_S_inv h n : ⌊h⌋ = S n → { l : _ & { g : _ & { r | h = ⟨l⟞g⟝r⟩ /\ ⌊g⌋ = n } } }.
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

  Fact hydra_ht_SS_deep h n : ⌊h⌋ = S (S n) → sig (hcut_deep h).
  Proof.
    revert n; induction h as [ m IH ]; intros [ | n ] E.
    + apply hydra_ht_S_inv in E as (l1 & g & r1 & H1 & E).
      apply hydra_ht_S_inv in E as (l0 & g' & r0 & H2 & E).
      apply hydra_ht_0_inv in E; subst.
      rewrite H1.
      exists ⟨l1⟛[]⟛r1⟩.
      constructor 1; intros _ [].
    + apply hydra_ht_S_inv in E as (l & g & r & H1 & E).
      apply IH in E as (g' & E).
      * rewrite H1; exists ⟨l⟞g'⟝r⟩; now constructor.
      * inversion H1; auto.
  Qed.

  Fact hydra_ht_1_cut h : ⌊h⌋ = 1 → sig (hcut h).
  Proof.
    intros (l & ? & r & -> & ->%hydra_ht_0_inv)%hydra_ht_S_inv.
    exists ⟨l⟛r⟩; constructor.
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
            (Hp : ∀n, { hcut (p n) (p (S n)) } + { p n = ⨸ }).

  Hint Resolve hydra_terminating : core.

  Corollary hydra_steps : { n | p n = ⨸ }.
  Proof.
    destruct play_terminates with (2 := hydra_terminating (p 0))
      as (n & Hn).
    + intros n; destruct (Hp n); eauto; right; now apply hydra_terminal.
    + exists n; now apply hydra_terminal.
  Qed.

End hercules.

Print move.
Check hydra_steps.
Print Assumptions hydra_steps.


(*
Fact fold_right_conj {X} (P : rel₁ X) l :
   fold_right (λ x p, P x ∧ p) True l ↔ Forall P l.
Proof.
  induction l; simpl.
  + split; eauto.
  + now rewrite IHl, Forall_cons_iff.
Qed.

Section hydra_fall.

  Variable P : hydra → Prop.

  Fixpoint hydra_fall h : Prop :=
    match h with
    | ⟨l⟩ => P ⟨l⟩ ∧ fold_right (λ x p, hydra_fall x ∧ p) True l
    end.

  Fact hydra_fall_fix l :
      hydra_fall ⟨l⟩ ↔ P ⟨l⟩ ∧ ∀h, h ∈ l → hydra_fall h.
  Proof. now simpl; rewrite fold_right_conj, <- Forall_forall. Qed.

  Section hydra_fall_rect.

    Variables (Q : hydra → Type)
              (HQ : ∀l, P ⟨l⟩
                     → (∀h, h ∈ l → hydra_fall h)
                     → (∀h, h ∈ l → Q h)
                     → Q ⟨l⟩).

    Theorem hydra_fall_rect h : hydra_fall h → Q h.
    Proof.
      induction h as [ l IH ]; intros H.
      rewrite hydra_fall_fix in H; destruct H; auto.
    Qed.

  End hydra_fall_rect.

End hydra_fall.
*)

  

