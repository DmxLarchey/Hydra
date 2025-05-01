(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils ordinal.

Set Implicit Arguments.

(** Construction of the Grzegorczyk Fast Growing Hierarchy for
    o : ord which has fundamental sequences 

    F : o → nat → nat

    F 0ₒ n         := S n             for 0ₒ
    F (e +ₒ 1ₒ) n  := (F e)^{S n} n   for a successor ordinal
    F λ n          := F λ[n] n        for a limit ordinal λ, using the fund. seq. λ[_]

    We specify it as a relation between the types 0ₒ and (nat → nat)

*)

Section Fast_Growing_Hierarchy.


  Variable (o : ord).

  Inductive fgh_gr : o → (nat → nat) → Prop :=
    | fgh_gr_0       : fgh_gr 0ₒ S
    | fgh_gr_1 e F   : fgh_gr e F
                     → fgh_gr (e +ₒ 1ₒ) (λ n, iter F (S n) n)
    | fgh_gr_2 e l F : (∀n, fgh_gr (@ord_fseq _ e l n) (F n))
                     → fgh_gr e (λ n, F n n).

  Hint Constructors fgh_gr : core.

  Lemma fgh_fun e E f F : fgh_gr e E → fgh_gr f F → e = f → ∀n, E n = F n.
  Proof.
    intros H; revert H f F.
    induction 1 as [ | e E H1 IH1 | e l E H1 IH1 ];
      destruct 1 as [ | f F H2 | f m F H2 ]; auto.
    + now intros ?%ord_zero_not_succ.
    + intros <-; destruct m as [ [] _ ]; auto.
    + symm; now intros ?%ord_zero_not_succ.
    + intros ?%ord_succ_inj ?; apply iter_ext; eauto.
    + intros <-; destruct m as [ ? [] ]; eauto.
    + intros ->; destruct l as [ [] _ ]; auto.
    + intros ->; destruct l as [ ? [] ]; eauto.
    + intros <- ?; eapply IH1; eauto.
      apply ord_fseq_pirr.
  Qed.

  Hint Resolve ord_lt_succ : core.

  (** This is the Grzegorczyk hierarchy *)
  Definition FGH_pwc e : { F | fgh_gr e F }.
  Proof.
    induction e as [ e IH ] using (well_founded_induction_type (@ord_lt_wf o)).
    destruct (@ord_zero_succ_limit_dec _ e) as [ [ -> | (f & ->) ] | l ].
    + exists S; auto.
    + destruct (IH f) as (F & ?); auto.
      exists (λ n, iter F (S n) n); auto.
    + set (F i := proj1_sig (IH (ord_fseq l i) (ord_fseq_lt _ _ _))).
      exists (λ n, F n n).
      constructor 3 with l.
      intro; apply (proj2_sig (IH (ord_fseq l n) (ord_fseq_lt _ _ _))).
  Qed.

  (* The hierarchy is uniquely characterized, up to extensionality 
     provided the fundamental sequence is uniquely characterized 
     as well !! *)

  Definition FGH e := proj1_sig (FGH_pwc e). 

  Fact FGH_spec e : fgh_gr e (FGH e).
  Proof. apply (proj2_sig _). Qed.

  Hint Resolve FGH_spec : core.

  (** We establish the defining equations using the spec *)

  Tactic Notation "solve" "fgh" :=
    apply fgh_fun with (1 := FGH_spec _) (3 := eq_refl); eauto.

  Theorem FGH_fix_zero n : FGH 0ₒ n = S n.
  Proof. solve fgh. Qed. 

  Theorem FGH_fix_succ e n : FGH (e +ₒ 1ₒ) n = iter (FGH e) (S n) n.
  Proof.
    change (FGH (e +ₒ 1ₒ) n = (λ n, iter (FGH e) (S n) n) n).
    solve fgh.
  Qed.

  Theorem FGH_fix_limit e l n : FGH e n = FGH (@ord_fseq _ e l n) n.
  Proof.
    change (FGH e n = (λ n, FGH (ord_fseq l n) n) n).
    solve fgh.
    constructor 3 with l; auto.
  Qed.

  (* The fundamental sequence for ε₀ is increasing and unbounded in ε₀ *)

  (* This function grows faster than any function definable in HA/PA 
     A proof of this result would be very nice addition *)

  Definition FGH_eps0 n := FGH (ord_mseq n) n.

End Fast_Growing_Hierarchy.

Print ord.
Check FGH_fix_zero.
Check FGH_fix_succ.
Check FGH_fix_limit.