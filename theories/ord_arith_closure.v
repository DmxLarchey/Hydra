(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.
From Hydra Require Import utils ordinal ordered eps0 eps0_mult eps0_fseq ord_omega.

Set Implicit Arguments.

Arguments eps0_le {_}.
Arguments eps0_lt {_}.
Arguments eps0_zero {_}.
Arguments eps0_one {_}.
Arguments eps0_add {_}.
Arguments eps0_mult {_}.
Arguments eps0_fseq {_}.
Arguments eps0_mseq {_}.

Definition ord_arith_closure (o : ord) : ord.
Proof.
  exists (eps0 o) eps0_lt eps0_le eps0_zero eps0_one eps0_add eps0_mult eps0_fseq eps0_mseq.
  + apply wf_eps0_lt.
  + apply eps0_lt_irrefl.
  + apply eps0_lt_trans.
  + apply eps0_le_lt_iff.
  + apply eps0_lt_sdec.
  + apply eps0_zero_least.
  + apply eps0_zero_lt_one.
  + apply eps0_zero_or_ge_one.
  + apply eps0_le_sub.
  + apply eps0_add_zero_left.
  + apply eps0_add_zero_right.
  + apply eps0_1add_le_succ_comm.
  + intros; apply eps0_lt_add_right; auto.
  + intros; apply eps0_le_add_left; auto.
  + apply eps0_add_assoc.
  + intros; now rewrite eps0_mult_assoc.
  + apply eps0_mult_zero_left.
  + apply eps0_mult_zero_right.
  + apply eps0_mult_one_left.
  + apply eps0_mult_one_right.
  + intros; apply eps0_mult_distr.
  + intros; now apply eps0_mult_mono.
  + apply eps0_is_succ_dec.
  + apply eps0_mult_is_succ_inv.
  + apply eps0_fseq_pirr.
  + apply eps0_fseq_incr.
  + apply eps0_fseq_lt.
  + apply eps0_fseq_limit.
  + apply eps0_fseq_add.
  + apply eps0_fseq_mult.
  + apply eps0_mseq_incr.
  + apply eps0_mseq_limit.
Defined.

Section embedding.

  Variable (o : ord).

  Definition oac_embed (e : o) : ord_arith_closure o. 
  Proof. 
    destruct (ord_zero_succ_limit_dec _ e) as [ [-> | (p & ->)] | ].
    + exact 0₀.
    + exact (@eps0_exp o 0₀ p).
    + exact (@eps0_exp o 0₀ e).
  Defined.

  Fact oac_lt_embed e f : e <ₒ f → oac_embed e <ₒ oac_embed f.
  Proof.
    intros Hef.
  Admitted.

  Definition oac_base : ord_arith_closure o := (@eps0_omega o 1₀).

  Fact oac_embed_lt e : oac_embed e <ₒ oac_base.
  Proof. 
    unfold oac_embed, oac_base.
    destruct (ord_zero_succ_limit_dec _ e) as [ [-> | (p & ->)] | He ].
    + apply eps0_zero_lt_omega.
    + apply eps0_lt_exp_left, eps0_zero_lt_one.
    + apply eps0_lt_exp_left, eps0_zero_lt_one.
 Qed.

  Fact oac_embed_limit g : g <ₒ oac_base → ∃e, g = oac_embed e.
  Proof.
    intros [-> | (e & He) ]%eps0_below_omega1_inv.
    + exists (ord_zero _).
      unfold oac_embed.
      admit.
    + exists e.
      unfold oac_embed. 

Fact oac_embed_correct o : 

Fixpoint epsilon n :=
  match n with
  | 0   => ord_omega
  | S n => ord_arith_closure (epsilon n)
  end.

Definition epsilon0 := epsilon 0.

