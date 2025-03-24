(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import hydra ordered lex_list.

Import ListNotations hydra_notations.

Set Implicit Arguments.

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.
Arguments transitive {_}.

Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.

Unset Elimination Schemes.

Inductive E0 : Set :=
  | E0_cons : list (E0*nat) → E0.

Set Elimination Schemes.

Notation "'ω[' l ]" := (E0_cons l) (at level 1, no associativity, format "ω[ l ]").

Section E0_rect.

  Let E0_sub e f := match f with ω[l] => ∃n, (e,n) ∈ l end.

  Local Lemma E0_sub_wf : well_founded E0_sub.
  Proof.
    refine (fix loop f := _).
    destruct f as [ l ].
    constructor; intros e (n & Hn).
    induction l as [ | y l IHl ].
    + destruct Hn.
    + destruct Hn as [ Hn | Hn ]; [ | apply IHl; assumption ].
      generalize (loop (fst y)). (* be careful here on what loop is applied *)
      clear loop; now subst.
  Qed.

  Variables (P : E0 → Type)
            (HP : ∀l, (∀ e n, (e,n) ∈ l → P e) → P ω[l]).

  Theorem E0_rect e : P e.
  Proof.
    apply Fix_F with (2 := E0_sub_wf e).
    intros [l] Hl.
    apply HP.
    intros f n Hfn; apply Hl; simpl; eauto.
  Defined.

End E0_rect.

Definition E0_ind (P : _ → Prop) := E0_rect P.
Definition E0_rec (P : _ → Set) := E0_rect P.

Fixpoint E0_ht e :=
  match e with
  | ω[l] => lmax (map (λ '(f,_), 1+E0_ht f) l)
  end.

Definition E0_fall (P : list (E0*nat) → Prop) : E0 → Prop :=
  fix loop e :=
    match e with
    | ω[l] => P l ∧ fold_right (λ p, and (loop (fst p))) True l
    end.

Lemma E0_fall_fix P l : E0_fall P ω[l] ↔ P l ∧ ∀ x i, (x,i) ∈ l → E0_fall P x.
Proof.
  simpl; rewrite fold_right_conj.
  apply and_iff_compat_l.
  split.
  + intros H ? ?; apply (H (_,_)).
  + intros ? []; eauto.
Qed.

Section E0_fall_rect.

  Variables (P : list (E0*nat) → Prop)
            (Q : E0 → Type)
            (HQ : ∀l, P l 
                    → (∀ e i, (e,i) ∈ l → E0_fall P e)
                    → (∀ e i, (e,i) ∈ l → Q e)
                    → Q ω[l]).

  Theorem E0_fall_rect e : E0_fall P e → Q e.
  Proof. induction e; intros []%E0_fall_fix; eauto. Qed.

End E0_fall_rect.

Section lex2.

  Variables (X I : Type) (RX : X → X → Prop) (RI : I → I → Prop).

  Inductive lex2 : X*I → X*I → Prop :=
    | lex2_left x i y j : RX x y → lex2 (x,i) (y,j)
    | lex2_right x i j  : RI i j → lex2 (x,i) (x,j).

  Hint Constructors lex2 : core.

  Fact lex2_inv xi yj :
      lex2 xi yj
    → match xi, yj with
      | (x,i), (y,j) => RX x y ∨ x = y ∧ RI i j
      end.
  Proof. destruct 1; eauto. Qed.

  Lemma lex2_irrefl xi : lex2 xi xi → RX (fst xi) (fst xi) ∨ RI (snd xi) (snd xi).
  Proof. revert xi; intros []?%lex2_inv; simpl; tauto. Qed.

  Section lex2_trans.

    Variables (l m p : list (X*I))
              (RXtrans : ∀ x i y j z u, (x,i) ∈ l → (y,j) ∈ m → (z,u) ∈ p → RX x y → RX y z → RX x z)
              (RItrans : ∀ x i y j z u, (x,i) ∈ l → (y,j) ∈ m → (z,u) ∈ p → RI i j → RI j u → RI i u).

    Lemma lex2_trans xi yj zk : xi ∈ l → yj ∈ m → zk ∈ p → lex2 xi yj → lex2 yj zk → lex2 xi zk.
    Proof.
      revert xi yj zk.
      intros [] [] [] ? ? ? [ | (<- & ?) ]%lex2_inv [ | (<- & ?) ]%lex2_inv; eauto.
    Qed.

  End lex2_trans.

  Hint Constructors sdec : core.

  Section lex2_sdec.

    Variables (l m : list (X*I))
              (RX_sdec : ∀ x i y j, (x,i) ∈ l → (y,j) ∈ m → sdec RX x y)
              (RI_sdec : ∀ x i y j, (x,i) ∈ l → (y,j) ∈ m → sdec RI i j).

    Lemma lex2_sdec xi yj : xi ∈ l → yj ∈ m → sdec lex2 xi yj.
    Proof.
      revert xi yj; intros (x,i) (y,j) ? ?.
      destruct (RX_sdec x i y j) as [| x |]; eauto.
      destruct (RI_sdec x i x j); eauto.
    Qed.

  End lex2_sdec.

  Section Acc.

    Hypothesis RI_wf : well_founded RI.

    Fact Acc_lex2 x : Acc RX x → ∀i, Acc lex2 (x,i).
    Proof.
      induction 1 as [ x _ IHx ].
      intros i; induction i using (well_founded_induction RI_wf).
      constructor.
      intros [] [ | (<- & ?) ]%lex2_inv; eauto.
    Qed.

  End Acc.

End lex2.

Arguments lex2 {_ _}.

Unset Elimination Schemes.

Inductive E0_lt : E0 → E0 → Prop :=
  | E0_lt_intro l m : lex_list (lex2 E0_lt lt) l m → E0_lt ω[l] ω[m].

Set Elimination Schemes.

#[local] Hint Constructors E0_lt : core.

Notation "e '<E₀' f" := (E0_lt e f) (at level 70, format "e  <E₀  f").

#[local] Hint Constructors E0_lt : core.

(* This inversion principle is enough to reason about <ε₀, 
   proceeding by induction on arguments *)
Fact E0_lt_inv l m : ω[l] <E₀ ω[m] ↔ lex_list (lex2 E0_lt lt) l m.
Proof. split; auto; now inversion 1. Qed.

(** We show that <E₀ is a strict order (irreflexive and transitive)
    and computably total, ie either e <E₀ f or e = f or f <E₀ e *)

Fact lt_irrefl n : ¬ n < n.
Proof. lia. Qed.

Fact lt_trans a b c : a < b → b < c → a < c.
Proof. lia. Qed.

(* irreflexive *)
Lemma E0_lt_irrefl e : ¬ e <E₀ e.
Proof.
  induction e as [ l IH ].
  intros ((?,i) & ? & [ ?%(IH _ i) | ?%lt_irrefl ]%lex2_irrefl)%E0_lt_inv%lex_list_irrefl; auto.
Qed.

#[local] Hint Resolve lt_trans lex2_trans : core.

(* transitive *)
Lemma E0_lt_trans : transitive E0_lt.
Proof.
  intros e.
  induction e as [ l IH ]. 
  intros [] [] H1%E0_lt_inv H2%E0_lt_inv; constructor.
  revert H1 H2; apply lex_list_trans; eauto.
Qed.

#[local] Hint Constructors sdec : core.

Lemma lt_sdec i j : sdec lt i j.
Proof. destruct (lt_eq_lt_dec i j) as [ [ | []] | ]; eauto. Qed.

#[local] Hint Resolve lt_sdec lex2_sdec : core.

(* computably total *)
Lemma E0_lt_sdec e f : sdec E0_lt e f.
Proof.
  revert f; induction e as [l]; intros [m].
  destruct (@lex_list_sdec _ (lex2 E0_lt lt) l m); eauto.
Qed.

#[local] Hint Resolve E0_lt_trans E0_lt_irrefl : core.

(* Hence decidable *)
Corollary E0_lt_dec e f : { e <E₀ f } + { ¬ e <E₀ f }.
Proof.
  destruct (E0_lt_sdec e f) as [ | | e f ]; eauto.
  right; intro; apply (@E0_lt_irrefl e); eauto.
Qed.

#[local] Hint Resolve E0_lt_dec : core.

Corollary E0_lt_trans' e f : clos_trans E0_lt e f → e <E₀ f.
Proof. induction 1; eauto. Qed.

(** An ordinal of ε₀ is in CNF if, recursivelly, it is
   of the shape ω[(e₁,i₁);...;(eₙ,iₙ)] with
   0 < i₁,...,iₙ and e₁ >ε₀ ... >ε₀ eₙ *)

Definition E0_cnf_pred l :=
    (∀ e i, (e,i) ∈ l → 0 < i) ∧ ordered E0_lt⁻¹ (map fst l).

Definition E0_cnf := E0_fall E0_cnf_pred.

Fact E0_cnf_fix l : 
    E0_cnf ω[l]
  ↔ ordered E0_lt⁻¹ (map fst l) ∧ ∀ e i, (e,i) ∈ l → 0 < i ∧ E0_cnf e.
Proof. 
  unfold E0_cnf.
  rewrite E0_fall_fix.
  unfold E0_cnf_pred; firstorder.
Qed.

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

(* E0_cnf is a strongly decidable predicate *)
Theorem E0_cnf_dec e : { E0_cnf e } + { ¬ E0_cnf e }.
Proof.
  induction e as [ l IHl ].
  destruct (ordered_dec E0_lt⁻¹ (map fst l))
    as [ H1 | H1 ]; eauto.
  + destruct list_fall_choose
      with (P := fun xi => snd xi = 0 \/ ~ E0_cnf (fst xi))
           (Q := fun xi => 0 < snd xi /\ E0_cnf (fst xi))
           (l := l)
      as [ ((x,i) & H2 & H3) | H2 ].
    * intros (x,[|i]) [ H | H ]%IHl; simpl; try tauto.
      right; split; auto; lia.
    * right; rewrite E0_cnf_fix; intros (_ & G).
      simpl in H3; apply G in H2.
      destruct H2, H3; subst; tauto || lia.
    * left; rewrite E0_cnf_fix; split; auto.
      intros; apply (H2 (_,_)); auto.
  + right; rewrite E0_cnf_fix; tauto.
Qed.

Inductive E0_lpo : E0 → E0 → Prop :=
  | E0_lpo_intro l m : lo (lex2 E0_lpo lt) l m → E0_lpo ω[l] ω[m].

#[local] Hint Constructors E0_lpo : core.

Fact E0_lpo_inv l m : E0_lpo ω[l] ω[m] → lo (lex2 E0_lpo lt) l m.
Proof. now inversion 1. Qed.

#[local] Hint Resolve lt_wf : core.

Section wf_rel_morph.

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (f : X → Y → Prop)
            (f_surj : ∀y, ∃x, f x y)
            (f_morph : ∀ x₁ x₂ y₁ y₂, f x₁ y₁ → f x₂ y₂ → T y₁ y₂ → R x₁ x₂).

  Theorem Acc_rel_morph x y : f x y → Acc R x → Acc T y.
  Proof.
    intros H1 H2; revert H2 y H1.
    induction 1 as [ x _ IH ]; intros y ?.
    constructor; intros z ?.
    destruct (f_surj z); eauto.
  Qed.

  Hint Resolve Acc_rel_morph : core.

  Corollary wf_rel_morph : well_founded R → well_founded T.
  Proof. intros ? y; destruct (f_surj y); eauto. Qed.

End wf_rel_morph.

Lemma wf_E0_lpo : well_founded E0_lpo.
Proof.
  intros e.
  induction e as [ l IH ].
  assert (Acc (lo (lex2 E0_lpo lt)) l) as Hl.
  1:{ apply Acc_lo_iff.
      intros [] ?.
      apply Acc_lex2; eauto. }
  revert Hl.
  apply Acc_rel_morph with (f := fun l e => ω[l] = e); auto.
  + intros []; eauto.
  + now intros ? ? ? ? <- <- ?%E0_lpo_inv.
Qed.

Fact Acc_irrefl X (R : X → X → Prop) x : Acc R x → ~ R x x.
Proof. induction 1 as [ x _ IH ]; intros H; exact (IH _ H H). Qed.

Fact E0_lpo_irrefl e : ~ E0_lpo e e.
Proof. apply Acc_irrefl with (1 := wf_E0_lpo _). Qed.

Fact E0_lpo_trans : transitive E0_lpo.
Proof.
  intros [l] [m] [k] ?%E0_lpo_inv ?%E0_lpo_inv.
  constructor; econstructor 2; eauto.
Qed.

#[local] Hint Resolve E0_lpo_trans : core.

Fact E0_lpo_trans' e f : clos_trans E0_lpo e f → E0_lpo e f.
Proof. induction 1; eauto. Qed.

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

(* We convert E0_cnf into an equivalent proof irrelevant predicate *)
Definition cnf e := squash (E0_cnf_dec e).

Fact cnf_iff e : cnf e ↔ E0_cnf e.          Proof. apply squash_iff. Qed.
Fact cnf_pirr e (h1 h2 : cnf e) : h1 = h2.  Proof. apply squash_pirr. Qed.

Fact cnf_fix l : 
    cnf ω[l]
  ↔ ordered E0_lt⁻¹ (map fst l) ∧ ∀ e i, (e,i) ∈ l → 0 < i ∧ cnf e.
Proof.
  rewrite cnf_iff, E0_cnf_fix.
  apply and_iff_compat_l.
  split; intros H ? ? []%H; split; auto; apply cnf_iff; auto.
Qed.

(* We convert the recursor *)
Fact cnf_rect (P : E0 → Type) :
    (∀l, ordered E0_lt⁻¹ (map fst l) 
       → (∀ e i, (e,i) ∈ l → 0 < i)
       → (∀ e i, (e,i) ∈ l → cnf e)
       → (∀ e i, (e,i) ∈ l → P e)
       → P ω[l])
  → ∀e, cnf e → P e.
Proof. 
  intros HP h H%cnf_iff; revert h H.
  induction 1 as [ l [] H2 IH ] using E0_fall_rect.
  apply HP; auto.
  intros ? i ?.
  apply cnf_iff, (H2 _ i); auto.
Qed.

Fact lex2_E0_lpo_lt_trans : transitive (lex2 E0_lpo lt).
Proof. intros a b c; apply lex2_trans with [a] [b] [c]; eauto. Qed.

#[local] Hint Resolve lex2_E0_lpo_lt_trans : core.

Fact lex2_E0_lpo_lt_trans' xi yj : clos_trans (lex2 E0_lpo lt) xi yj → lex2 E0_lpo lt xi yj.
Proof. induction 1; eauto. Qed.

#[local] Hint Constructors lex2 : core.

#[local] Hint Resolve lex_list_mono : core.

(** The fundamental theorem: E0_lt is well-founded on CNF *)
Lemma cnf_lt_lpo e f : cnf e → cnf f → e <E₀ f → E0_lpo e f.
Proof.
  intros H1 H2; revert e H1 f H2.
  induction 1 as [ l He1 He2 He3 IH ] using cnf_rect.
  induction 1 as [ m Hf1 Hf2 Hf3 _   ] using cnf_rect.
  intros H%E0_lt_inv.
  constructor.
  apply lo_mono with (1 := lex2_E0_lpo_lt_trans').
  apply ordered_lex_list_lo; eauto.
  + revert He1.
    apply ordered_morphism with (f := fun x y => x = fst y).
    * intros ? ? [] [] ([] & ? & ?)%in_map_iff ([] & ? & ?)%in_map_iff -> ->; right; left; simpl in *; subst; eauto.
    * clear He2 He3 IH H; induction l; simpl; constructor; auto.
  + revert H; apply lex_list_mono.
    intros [] [] ? ? [| (<- & ?)]%lex2_inv; eauto.
Qed.

(** ε₀ is the sub-type of E0 composed of trees in nested lexigraphic order *)

Definition eps0 := { e | cnf e }.

Notation ε₀ := eps0.

Notation π₁ := proj1_sig.
Notation π₂ := proj2_sig.

(** ε₀ is itself equipped with the restriction of the nested lex. order
    denoted <ε₀ *)

Definition eps0_lt (e f : ε₀) := E0_lt (π₁ e) (π₁ f).

Notation "e '<ε₀' f" := (eps0_lt e f) (at level 70, format "e  <ε₀  f").

(** The nested lexicographic order <ε₀ is a strict total/decidable order *)

Theorem eps0_lt_irrefl e : ¬ e <ε₀ e.
Proof. destruct e; apply E0_lt_irrefl. Qed.

Theorem eps0_lt_trans : transitive eps0_lt.
Proof. intros [] [] []; apply E0_lt_trans. Qed.

Theorem eps0_lt_sdec e f : sdec eps0_lt e f.
Proof.
  revert e f; intros (e & He) (f & Hf).
  destruct (E0_lt_sdec e f) as []; eauto.
  rewrite (cnf_pirr _ He Hf); auto.
Qed.

#[local] Hint Resolve cnf_lt_lpo : core.

(* <ε₀ is well-founded *)
Theorem wf_eps0_lt : well_founded eps0_lt.
Proof.
  generalize wf_E0_lpo.
  apply wf_rel_morph with (f := fun x y => x = π₁ y).
  + intros []; eauto.
  + unfold eps0_lt; intros ? ? [] [] -> ->; simpl; eauto.
Qed.

Section epsilon0_rect.






