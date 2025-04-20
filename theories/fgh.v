(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils pos eps0 eps0_ltf eps0_fseq.

Set Implicit Arguments.

#[local] Notation π₁ := proj1_sig.
#[local] Notation π₂ := proj2_sig.

Section Fast_Growing_Hierarchy.

  (** Construction of the Grzegorczyk Fast Growing Hierarchy

      F : ε₀ → nat → nat

      F 0₀ n      := S n             for 0₀
      F (S₀ e) n  := (F e)^{S n} n   for a successor ordinal
      F λ n       := F λ[n] n        for a limit ordinal λ, using the fund. seq. λ[_]

      We specify it as a relation between the types ε₀ and (nat → nat)

  *)

  Inductive fgh_gr : ε₀ → (nat → nat) → Prop :=
    | fgh_gr_0       : fgh_gr 0₀ S
    | fgh_gr_1 e F   : fgh_gr e F
                     → fgh_gr (S₀ e) (λ n, iter F (S n) n)
    | fgh_gr_2 e l F : (∀n, fgh_gr (@eps0_fseq e l n) (F n))
                     → fgh_gr e (λ n, F n n).

  Hint Constructors fgh_gr : core.

  Hint Resolve eps0_is_succ_S : core.

  Lemma fgh_gr_fun e E f F : fgh_gr e E → fgh_gr f F → e = f → ∀n, E n = F n.
  Proof.
    intros H; revert H f F.
    induction 1 as [ | e E H1 IH1 | e l E H1 IH1 ];
      destruct 1 as [ | f F H2 | f m F H2 ]; auto.
    + now intros ?%eps0_zero_not_succ.
    + intros <-; destruct m as [ [] _ ]; auto.
    + symm; now intros ?%eps0_zero_not_succ.
    + intros ?%eps0_succ_inj ?; apply iter_ext; eauto.
    + intros <-; destruct m as [ ? [] ]; auto.
    + intros ->; destruct l as [ [] _ ]; auto.
    + intros ->; destruct l as [ ? [] ]; auto.
    + intros <- ?; eapply IH1; eauto.
      apply (@eps0_fseq_gr_fun e); apply eps0_fseq_spec.
  Qed.

  Inductive eps0_choice : ε₀ → Type :=
    | eps0_choice_0   : eps0_choice 0₀
    | eps0_choice_1 e : eps0_choice (S₀ e)
    | eps0_choice_2 e : eps0_is_limit e
                      → eps0_choice e.

  Hint Resolve eps0_lt_succ eps0_is_limit_omega eps0_is_limit_tf : core.

  Fact eps0_choose e : eps0_choice e.
  Proof. induction e using eps0_ltf_pos_rect; constructor; auto. Qed.

  (** This is the Grzegorczyk hierarchy *)
  Definition FGH_pwc e : { F | fgh_gr e F }.
  Proof.
    induction e as [ e IH ] using eps0_rect.
    destruct (eps0_choose e) as [ | e | e l ].
    + exists S; auto.
    + destruct (IH e) as (F & ?); auto.
      exists (λ n, iter F (S n) n); auto.
    + set (F i := π₁ (IH (eps0_fseq l i) (eps0_fseq_lt _ _))).
      exists (λ n, F n n).
      constructor 3 with l.
      intro; apply (π₂ (IH (eps0_fseq l n) (eps0_fseq_lt _ _))).
  Qed.

  (* The hierarchy is uniquely characterized, up to extensionality 
     provided the fundamental sequence is uniquely characterized 
     as well !! *)

  Definition FGH e := π₁ (FGH_pwc e). 

  Fact FGH_spec e : fgh_gr e (FGH e).
  Proof. apply (proj2_sig _). Qed.

  Hint Resolve FGH_spec : core.

  (** We establish the defining equations using the spec *)

  Tactic Notation "solve" "fgh" :=
    apply fgh_gr_fun with (1 := FGH_spec _) (3 := eq_refl); eauto.

  Theorem FGH_fix_zero n : FGH 0₀ n = S n.
  Proof. solve fgh. Qed. 

  Theorem FGH_fix_succ e n : FGH (S₀ e) n = iter (FGH e) (S n) n.
  Proof.
    change (FGH (S₀ e) n = (λ n, iter (FGH e) (S n) n) n).
    solve fgh.
  Qed.

  Theorem FGH_fix_limit e l n : FGH e n = FGH (@eps0_fseq e l n) n.
  Proof.
    change (FGH e n = (λ n, FGH (@eps0_fseq e l n) n) n).
    solve fgh.
    constructor 3 with l; auto.
  Qed.

  (* The fundamental sequence for ε₀ is increasing and unbounded in ε₀ *)

  Definition eps0_fseq_eps0 n := iter (λ e, ω^e) n 0₀.

  Fact eps0_fseq_eps0_incr n : eps0_fseq_eps0 n <ε₀ eps0_fseq_eps0 (S n).
  Proof. unfold eps0_fseq_eps0; rewrite iter_S; apply eps0_lt_omega. Qed.

  Theorem eps0_fseq_eps0_bound e : { n | e <ε₀ eps0_fseq_eps0 n }.
  Proof.
    unfold eps0_fseq_eps0.
    induction e as [ | e i f H (n & Hn) _ ] using eps0_hnf_rect.
    + exists 1; apply eps0_lt_omega.
    + exists (S n); rewrite iter_S.
      apply eps0_add_below_omega.
      * apply eps0_exp_mono_left; auto.
      * apply eps0_lt_le_trans with (1 := H).
        apply eps0_omega_mono_le, eps0_lt_le_weak; auto.
  Qed.

  (* This function grows faster than any function definable in HA/PA 
     A proof of this result would be very nice addition *)

  Definition FGH_eps0 n := FGH (eps0_fseq_eps0 n) n.

End Fast_Growing_Hierarchy.

Check FGH_fix_zero.
Check FGH_fix_succ.
Check FGH_fix_limit.