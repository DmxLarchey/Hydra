(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations (* Arith Lia *) Wellfounded Utf8.
From Hydra Require Import utils pos ordered eps0.

Import ListNotations.

Set Implicit Arguments.

#[local] Notation π₁ := proj1_sig.
#[local] Notation π₂ := proj2_sig.

#[local] Hint Resolve eps0_le_refl eps0_lt_succ
                      eps0_zero_least
                      eps0_add_incr
                      eps0_add_mono_right
                      eps0_lt_zero_exp 
                      eps0_zero_lt_omega 
                      eps0_lt_le_weak 
                      eps0_add_mono_left 
                      eps0_add_mono
                      eps0_add_incr_left
                      eps0_add_incr_right
: core.

Section eps0_mpos.

  (** pos := nat viewed as 1, 2, ... and not 0, 1, ... *)

  (** The operation (θ : ε₀) (n : pos) => θ.(1+n) *)
  Inductive eps0_mpos_gr n : ε₀ → ε₀ → Prop :=
    | eps0_mpos_gr_0 : eps0_mpos_gr n 0₀ 0₀
    | eps0_mpos_gr_1 α i β : β <ε₀ ω^α → eps0_mpos_gr n (ω^⟨α,i⟩ +₀ β) (ω^⟨α,i *ₚ n⟩ +₀ β).

  Fact eps0_mpos_fun n e1 f1 e2 f2 : eps0_mpos_gr n e1 f1 → eps0_mpos_gr n e2 f2 → e1 = e2 → f1 = f2.
  Proof.
    do 2 destruct 1; auto.
    + now intros ?%eps0_zero_neq_hnf.
    + symm; now intros ?%eps0_zero_neq_hnf.
    + intros (? & [])%eps0_eq_hnf_inv; subst; auto.
  Qed.

  Definition eps0_mpos_pwc e n : sig (eps0_mpos_gr n e).
  Proof.
    destruct e as [ | e i f ] using eps0_hnf_rect.
    + exists 0₀; constructor.
    + exists (ω^⟨e,i *ₚ n⟩ +₀ f); now constructor.
  Qed.

  Definition eps0_mpos e n := π₁ (eps0_mpos_pwc e n).

  Fact eps0_mpos_spec e n : eps0_mpos_gr n e (eps0_mpos e n).
  Proof. apply (proj2_sig _). Qed.

  Fact eps0_mpos_fix_0 n : eps0_mpos 0₀ n = 0₀.
  Proof. apply eps0_mpos_fun with (1 := eps0_mpos_spec _ _) (3 := eq_refl); constructor. Qed.

  Fact eps0_mpos_fix_1 n α i β : β <ε₀ ω^α → eps0_mpos (ω^⟨α,i⟩ +₀ β) n = ω^⟨α,i *ₚ n⟩ +₀ β.
  Proof. intros; apply eps0_mpos_fun with (1 := eps0_mpos_spec _ _) (3 := eq_refl); now constructor. Qed.

  Fact eps0_mpos_exp n α i : eps0_mpos ω^⟨α,i⟩ n = ω^⟨α,i *ₚ n⟩.
  Proof. 
    rewrite <- (eps0_add_zero_right ω^⟨_,i⟩), eps0_mpos_fix_1; auto.
    now rewrite eps0_add_zero_right.
  Qed.

  Fact eps0_mpos_one e : eps0_mpos e 1ₚ = e.
  Proof.
    destruct e using eps0_hnf_rect.
    + now rewrite eps0_mpos_fix_0.
    + rewrite eps0_mpos_fix_1, pos_mul_one_right; auto.
  Qed.

  Fact eps0_mpos_omega_add n α β : β <ε₀ ω^α → eps0_mpos (ω^α +₀ β) n = ω^⟨α,n⟩ +₀ β.
  Proof.
    intros; unfold eps0_omega.
    rewrite eps0_mpos_fix_1, pos_mul_one_left; auto.
  Qed.

  Fact eps0_mpos_omega n α : eps0_mpos ω^α n = ω^⟨α,n⟩.
  Proof.
    rewrite <- (eps0_add_zero_right ω^α), eps0_mpos_omega_add; auto.
    now rewrite eps0_add_zero_right.
  Qed.

  Fact eps0_mpos_add e i j : eps0_mpos e i +₀ eps0_mpos e j = eps0_mpos e (i +ₚ j).
  Proof.
    destruct e using eps0_hnf_rect.
    + now rewrite !eps0_mpos_fix_0, eps0_add_zero_left.
    + rewrite !eps0_mpos_fix_1; auto.
      rewrite eps0_add_hnf_eq, pos_mul_distr_right; auto.
  Qed.

  Fact eps0_mpos_comp e i j : eps0_mpos (eps0_mpos e i) j = eps0_mpos e (i *ₚ j).
  Proof.
    destruct e using eps0_hnf_rect.
    + now rewrite !eps0_mpos_fix_0.
    + rewrite !eps0_mpos_fix_1, pos_mul_assoc; auto.
  Qed.

  (** a.2 < b.2 *)
  Fact eps0_mpos_mono_left a b m n : a <ε₀ b → m ≤ n → eps0_mpos a m <ε₀ eps0_mpos b n.
  Proof.
    intros Hab Hmn.
    destruct a as [ | e i f H1 _ _ ] using eps0_hnf_rect;
      destruct b as [ | g j h H2 _ _ ] using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in Hab.
    + rewrite eps0_mpos_fix_0, eps0_mpos_fix_1; auto.
    + now apply eps0_zero_not_gt in Hab.
    + (* ε₀.(i.n) < ε₀.(j.m) *)
    apply eps0_lt_hnf_inv in Hab; auto.
      rewrite !eps0_mpos_fix_1; auto.
      apply eps0_lt_hnf_inv; auto.
      destruct Hab as [ | (<- & [ | (<- & ?) ]) ]; auto.
      * right; split; auto.
        admit.
(*        now apply pos_mul_mono_left. *)
      * apply pos_le_lt_iff in Hmn as [ -> | Hmn ]; auto.
        right; split; auto; left.
        now apply pos_mul_mono_right.
  Admitted.
  
  Fact eps0_mpos_mono_left_le a b m n : a <ε₀ b → m ≤ n → eps0_mpos a m ≤ε₀ eps0_mpos b n.
  Proof.
    intros Hab Hmn.
    destruct a as [ | e i f H1 _ _ ] using eps0_hnf_rect;
      destruct b as [ | g j h H2 _ _ ] using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in Hab.
    + rewrite eps0_mpos_fix_0, eps0_mpos_fix_1; auto.
    + now apply eps0_zero_not_gt in Hab.
    + (* ε₀.(i.n) < ε₀.(j.m) *)
      apply eps0_lt_hnf_inv in Hab; auto.
      rewrite !eps0_mpos_fix_1; auto.
      destruct Hab as [ | (<- & [ | (<- & ?) ]) ]; auto.
      * apply eps0_lt_le_weak, eps0_lt_hnf_inv; auto. 
      * (* (ε₀.ω²).k = (ε₀.ω).k ? 
           because then ε₀.ω + 2 < ε₀.ω² + 1
           but (ε₀.ω + 2).k
      
       *)
      
      apply pos_le_lt_iff in Hmn as [ -> | Hmn ]; auto.
        right; split; auto; left.
        now apply pos_mul_mono_right.
      
      rewrite !eps0_mpos_fix_1; auto.
      apply eps0_lt_hnf_inv; auto.
      destruct Hab as [ | (<- & [ | (<- & ?) ]) ]; auto.
      * right; split; auto.
        admit.
(*        now apply pos_mul_mono_left. *)
      * apply pos_le_lt_iff in Hmn as [ -> | Hmn ]; auto.
        right; split; auto; left.
        now apply pos_mul_mono_right.
  Admitted.

  Fact eps0_mpos_gt_zero a n : 0₀ <ε₀ a → 0₀ <ε₀ eps0_mpos a n.
  Proof.
    intros H.
    apply eps0_lt_le_trans with (1 := H).
    destruct (pos_one_or_next n) as [ -> | (k & ->) ].
    + rewrite eps0_mpos_one; auto.
    + rewrite <- eps0_mpos_add, eps0_mpos_one; auto.
  Qed.

  Hint Resolve eps0_mpos_mono_left eps0_mpos_gt_zero : core.

  Fact eps0_mpos_mono_right a n m : 0₀ <ε₀ a → n < m → eps0_mpos a n <ε₀ eps0_mpos a m.
  Proof.
    intros H1 H2.
    destruct a as [ | e i f H _ _ ] using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in H1.
    + rewrite !eps0_mpos_fix_1; auto.
      apply eps0_lt_hnf_inv; auto.
      right; split; auto; left.
      now apply pos_mul_mono_right.
  Qed.

  Fact eps0_mpos_mono_right_le a n m : n ≤ m → eps0_mpos a n ≤ε₀ eps0_mpos a m.
  Proof.
    destruct (eq_nat_dec n m) as [ <- | ]; auto; intro.
    destruct (eps0_zero_or_pos a) as [ -> | ].
    + rewrite !eps0_mpos_fix_0; auto.
    + apply eps0_le_iff_lt.
      left; apply eps0_mpos_mono_right; auto; lia.
  Qed.

  Fact eps0_mpos_mono a b m n : a ≤ε₀ b → m ≤ n → eps0_mpos a m ≤ε₀ eps0_mpos b n.
  Proof.
    rewrite eps0_le_iff_lt.
    intros [ H1 | -> ].
    + rewrite eps0_le_iff_lt; left; now apply eps0_mpos_mono_left.
    + apply eps0_mpos_mono_right_le.
  Qed.

  Fact eps0_mpos_below_omega a n e : a <ε₀ ω^e → eps0_mpos a n <ε₀ ω^e.
  Proof.
    intros [ -> | (f & i & H1 & H2) ]%eps0_below_omega_inv.
    + rewrite eps0_mpos_fix_0; auto.
    + apply eps0_mpos_mono_left with (n := n) (m := n) in H1; auto.
      apply eps0_lt_trans with (1 := H1).
      rewrite eps0_mpos_exp.
      apply eps0_lt_exp_inv; auto.
  Qed.

  Fact eps0_mpos_below_omega' a n e i : a <ε₀ ω^⟨e,i⟩ → eps0_mpos a n <ε₀ ω^(S₀ e).
  Proof.
    intros H.
    apply eps0_mpos_below_omega,
          eps0_lt_trans with (1 := H),
          eps0_exp_mono_left; auto.
  Qed.

End eps0_mpos.

#[local] Hint Resolve eps0_mpos_mono_left eps0_mpos_gt_zero : core.

Section eps0_momega.

  (** now the operation (θ α : ε₀) => θ.ω^α *)
  Inductive eps0_momega_gr α : ε₀ → ε₀ → Prop :=
    | eps0_momega_gr_0 : eps0_momega_gr α 0₀ 0₀
    | eps0_momega_gr_1 γ n β : β <ε₀ ω^γ → eps0_momega_gr α (ω^⟨γ,n⟩ +₀ β) ω^(γ+₀α).

  Fact eps0_momega_fun a e1 f1 e2 f2 : eps0_momega_gr a e1 f1 → eps0_momega_gr a e2 f2 → e1 = e2 → f1 = f2.
  Proof.
    do 2 destruct 1; auto.
    + now intros ?%eps0_zero_neq_hnf.
    + symm; now intros ?%eps0_zero_neq_hnf.
    + intros (? & [])%eps0_eq_hnf_inv; subst; auto.
  Qed.

  Definition eps0_momega_pwc e α : sig (eps0_momega_gr α e).
  Proof.
    destruct e as [ | e ] using eps0_hnf_rect.
    + exists 0₀; constructor.
    + exists ω^(e+₀α); now constructor.
  Qed.

  Definition eps0_momega e α := π₁ (eps0_momega_pwc e α).

  Fact eps0_momega_spec e α : eps0_momega_gr α e (eps0_momega e α).
  Proof. apply (proj2_sig _). Qed.

  Fact eps0_momega_fix_0 α : eps0_momega 0₀ α = 0₀.
  Proof. apply eps0_momega_fun with (1 := eps0_momega_spec _ _) (3 := eq_refl); constructor. Qed.

  Fact eps0_momega_fix_1 γ n β α : β <ε₀ ω^γ → eps0_momega (ω^⟨γ,n⟩ +₀ β) α = ω^(γ+₀α).
  Proof. intros; apply eps0_momega_fun with (1 := eps0_momega_spec _ _) (3 := eq_refl); now constructor. Qed.

  Fact eps0_momega_exp γ n α : eps0_momega ω^⟨γ,n⟩ α = ω^(γ+₀α).
  Proof. rewrite <- (eps0_add_zero_right ω^⟨_,_⟩), eps0_momega_fix_1; auto. Qed.

  Fact eps0_momega_mpos a i e :
      0₀ <ε₀ e → eps0_momega (eps0_mpos a i) e = eps0_momega a e.
  Proof.
    intros He.
    destruct a using eps0_hnf_rect.
    + now rewrite eps0_mpos_fix_0.
    + rewrite eps0_mpos_fix_1; auto.
      rewrite !eps0_momega_fix_1; auto.
  Qed.

  Fact eps0_add_mpos_momega n k e f :
      0₀ <ε₀ f
    → eps0_mpos e n +₀ eps0_mpos (eps0_momega e f) k
    = eps0_mpos (eps0_momega e f) k.
  Proof.
    intros Hf.
    destruct e using eps0_hnf_rect.
    + now rewrite !eps0_mpos_fix_0, eps0_add_zero_left.
    + rewrite !eps0_mpos_fix_1; auto.
      rewrite eps0_momega_fix_1; auto.
      rewrite !eps0_mpos_omega.
      rewrite <- (eps0_add_zero_right ω^⟨_,k⟩).
      rewrite eps0_add_hnf_lt; auto.
  Qed.

  Fact eps0_mpos_add_momega a e f i j :
      e <ε₀ f
    → eps0_mpos (eps0_momega a e) i +₀ eps0_mpos (eps0_momega a f) j
    = eps0_mpos (eps0_momega a f) j.
  Proof.
    intros Hef.
    destruct a using eps0_hnf_rect.
    + now rewrite !eps0_momega_fix_0, !eps0_mpos_fix_0, eps0_add_zero_left.
    + rewrite !eps0_momega_fix_1; auto.
      rewrite !eps0_mpos_omega, eps0_add_exp_lt; auto.
  Qed.

  Fact eps0_momega_mono_left a b c :
      a ≤ε₀ b
    → eps0_momega a c ≤ε₀ eps0_momega b c.
  Proof.
    intros [ Hab | <- ]%eps0_le_iff_lt; auto.
    destruct a as [ | e i f H1 _ _ ] using eps0_hnf_rect;
      destruct b as [ | g j h H2 _ _ ] using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in Hab.
    + rewrite eps0_momega_fix_0, eps0_momega_fix_1; auto.
    + now apply eps0_zero_not_gt in Hab.
    + rewrite !eps0_momega_fix_1; auto.
      apply eps0_lt_hnf_inv in Hab; auto.
      apply eps0_omega_mono_le.
      destruct Hab as [ | (<- & _) ]; auto.
  Qed.

  Fact eps0_momega_mono_right a b c :
      0₀ <ε₀ a
    → b <ε₀ c 
    → eps0_momega a b <ε₀ eps0_momega a c.
  Proof.
    intros H ?.
    destruct a using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in H.
    + rewrite !eps0_momega_fix_1; auto.
      apply eps0_omega_mono_lt; auto.
  Qed.

  Fact eps0_momega_lt_pos a e :
      0₀ <ε₀ a
    → 0₀ <ε₀ e
    → ω^e ≤ε₀ eps0_momega a e.
  Proof.
    intros Ha He.
    destruct a using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in Ha.
    + rewrite eps0_momega_fix_1; auto.
      apply eps0_omega_mono_le; auto.
  Qed.

  Fact eps0_lt_mpos_momega a n f :
      0₀ <ε₀ a
    → 0₀ <ε₀ f
    → eps0_mpos a n <ε₀ eps0_momega a f.
  Proof.
    intros Ha Hf.
    destruct a using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in Ha.
    + rewrite eps0_mpos_fix_1, eps0_momega_fix_1; auto.
      apply eps0_lt_hnf_exp_inv; auto.
  Qed.

  Fact eps0_momega_below_omega a b e f :
      a <ε₀ ω^e
    → b <ε₀ f
    → eps0_momega a b <ε₀ ω^(e +₀ f).
  Proof.
    intros [ -> | (g & i & H1 & H2) ]%eps0_below_omega_inv Hb.
    + rewrite eps0_momega_fix_0; auto.
    + apply eps0_le_lt_trans with (eps0_momega ω^⟨g,i⟩ b).
      * apply eps0_momega_mono_left; auto.
      * rewrite eps0_momega_exp.
        apply eps0_omega_mono_lt.
        apply eps0_lt_le_trans with (g +₀ f); auto.
  Qed.

  Fact eps0_momega_below_exp a b e n f :
      a <ε₀ ω^⟨e,n⟩
    → b <ε₀ f
    → eps0_momega a b <ε₀ ω^(e +₀ f).
  Proof.
    intros [ [ -> | (i & c & -> & ? & ?) ] | (g & i & H1 & ?) ]%eps0_below_exp_inv ?.
    + rewrite eps0_momega_fix_0; auto.
    + rewrite eps0_momega_fix_1; auto.
      apply eps0_omega_mono_lt; auto.
    + apply eps0_lt_le_weak, eps0_momega_mono_left with (c := b) in H1.
      apply eps0_le_lt_trans with (1 := H1).
      rewrite eps0_momega_exp; auto.
      apply eps0_omega_mono_lt.
      apply eps0_le_lt_trans with (e +₀ b); auto.
  Qed.

End eps0_momega.

Section eps0_mult.

  (* now the operation (γ α : ε₀) => γ.α *)
  Inductive eps0_mult_gr γ : ε₀ → ε₀ → Prop :=
    | eps0_mult_gr_0         : eps0_mult_gr γ 0₀ 0₀ 
    | eps0_mult_gr_1 n       : eps0_mult_gr γ ω^⟨0₀,n⟩ (eps0_mpos γ n)
    | eps0_mult_gr_2 α n β r : 0₀ <ε₀ α
                             → β <ε₀ ω^α
                             → eps0_mult_gr γ β r
                             → eps0_mult_gr γ (ω^⟨α,n⟩ +₀ β) (eps0_mpos (eps0_momega γ α) n +₀ r).

  Fact eps0_mult_fun a e1 f1 e2 f2 :
      eps0_mult_gr a e1 f1
    → eps0_mult_gr a e2 f2
    → e1 = e2
    → f1 = f2.
  Proof.
    intros H1; revert H1 e2 f2.
    induction 1 as [ | n1 | e1 n1 f1 r1 H1 G1 F1 IH1 ];
      induction 1 as [ | n2 | e2 n2 f2 r2 H2 G2 F2 _ ]; auto.
    + now intros ?%eps0_zero_neq_exp.
    + now intros ?%eps0_zero_neq_hnf.
    + symm; now intros ?%eps0_zero_neq_exp.
    + now intros (_ & ->)%eps0_exp_inj.
    + intros (<- & -> & ->)%eps0_eq_exp_hnf_inv; auto.
      contradict H2; apply eps0_lt_irrefl.
    + symm; now intros ?%eps0_zero_neq_hnf.
    + symm; intros (<- & -> & ->)%eps0_eq_exp_hnf_inv; auto.
      contradict H1; apply eps0_lt_irrefl.
    + intros (<- & <- & <-)%eps0_eq_hnf_inv; auto.
      f_equal; eauto.
  Qed.

  Hint Constructors eps0_mult_gr : core.

  Definition eps0_mult_pwc γ e : sig (eps0_mult_gr γ e).
  Proof.
    induction e as [ | n | e n f He Hf _ (r & Hr) ] using eps0_hnf_pos_rect.
    + exists 0₀; auto.
    + exists (eps0_mpos γ n); auto.
    + exists (eps0_mpos (eps0_momega γ e) n +₀ r); auto.
  Qed.

  Definition eps0_mult e f := π₁ (eps0_mult_pwc e f).

  Infix "*₀" := eps0_mult.

  Fact eps0_mult_spec e f : eps0_mult_gr e f (e *₀ f).
  Proof. apply (proj2_sig _). Qed.

  Hint Resolve eps0_mult_spec : core.

  Tactic Notation "solve" "mult" :=
    intros; apply eps0_mult_fun with (1 := eps0_mult_spec _ _) (3 := eq_refl); auto.

  Fact eps0_mult_zero_right a : a *₀ 0₀ = 0₀.
  Proof. solve mult. Qed.

  Fact eps0_mult_pos_right a n : a *₀ ω^⟨0₀,n⟩ = eps0_mpos a n.
  Proof. solve mult. Qed.

  Corollary eps0_mpos_eq a n : eps0_mpos a n = a *₀ ω^⟨0₀,n⟩.
  Proof. now rewrite eps0_mult_pos_right. Qed.

  Fact eps0_mult_hnf_right a e n f :
      0₀ <ε₀ e
    → f <ε₀ ω^e
    → a *₀ (ω^⟨e,n⟩ +₀ f)
    = eps0_mpos (eps0_momega a e) n +₀ a *₀ f.
  Proof. solve mult. Qed.

  (** This one is stronger because it does not need any relation between e and f *)
  Fact eps0_mult_right a e n f :
      0₀ <ε₀ e
    → a *₀ (ω^⟨e,n⟩ +₀ f)
    = eps0_mpos (eps0_momega a e) n +₀ a *₀ f.
  Proof.
    intros He.
    destruct f as [ | f i g H _ _ ] using eps0_hnf_rect.
    + rewrite eps0_mult_hnf_right; auto.
    + destruct (eps0_lt_sdec e f).
      * rewrite eps0_add_exp_hnf_lt, eps0_mult_hnf_right,
             <- eps0_add_assoc, eps0_mpos_add_momega; auto.
        eapply eps0_lt_trans; eassumption.
      * rewrite eps0_add_exp_hnf_eq, 
               !eps0_mult_hnf_right,
             <- eps0_add_assoc,
                eps0_mpos_add; auto.
      * rewrite eps0_mult_hnf_right; auto.
        apply eps0_add_below_omega.
        - now apply eps0_exp_mono_left.
        - apply eps0_lt_trans with (1 := H),
                eps0_omega_mono_lt; auto.
  Qed.

  Fact eps0_mpos_momega_eq a n e :
    0₀ <ε₀ e → eps0_mpos (eps0_momega a e) n = a *₀ ω^⟨e,n⟩.
  Proof.
    intro.
    rewrite <- (eps0_add_zero_right ω^⟨_,_⟩),
                eps0_mult_right,
                eps0_mult_zero_right,
                eps0_add_zero_right; auto.
  Qed.

  Fact eps0_momega_eq a e :
    0₀ <ε₀ e → eps0_momega a e = a *₀ ω^e.
  Proof.
    intro; unfold eps0_omega.
    rewrite <- eps0_mpos_momega_eq, eps0_mpos_one; auto.
  Qed.

  Fact eps0_mult_zero_left e : 0₀ *₀ e = 0₀.
  Proof.
    induction e as [ | n | e n f He Hf _ IHf ] using eps0_hnf_pos_rect.
    + now rewrite eps0_mult_zero_right.
    + now rewrite eps0_mult_pos_right, eps0_mpos_fix_0.
    + rewrite eps0_mult_hnf_right, IHf; auto.
      now rewrite eps0_momega_fix_0, eps0_mpos_fix_0, eps0_add_zero_left.
  Qed.

  Fact eps0_mult_distr a b c : a *₀ (b +₀ c) = a *₀ b +₀ a *₀ c.
  Proof.
    induction b as [ | n | e n f He Hf IHe IHf ] in a, c |- *
      using eps0_hnf_pos_rect.
    + now rewrite eps0_mult_zero_right, !eps0_add_zero_left.
    + destruct c as [ | k | c k g ? ? _ _ ] using eps0_hnf_pos_rect.
      * now rewrite eps0_mult_zero_right, !eps0_add_zero_right.
      * now rewrite eps0_add_exp, !eps0_mult_pos_right, eps0_mpos_add.
      * rewrite eps0_add_exp_hnf_lt,
                eps0_mult_hnf_right,
                eps0_mult_pos_right,
             <- eps0_add_assoc,
                eps0_add_mpos_momega; auto.
    + rewrite eps0_mult_right,
             !eps0_add_assoc,
           <- IHf, eps0_mult_right; auto.
  Qed.

  Fact eps0_mult_gt_zero a e : 0₀ <ε₀ a → 0₀ <ε₀ e → 0₀ <ε₀ a *₀ e.
  Proof.
    intros Ha He.
    induction e as [ | n | e n f H1 H2 IH1 IH2 ] using eps0_hnf_pos_rect.
    + now apply eps0_lt_irrefl in He.
    + rewrite eps0_mult_pos_right; now apply eps0_mpos_gt_zero.
    + rewrite eps0_mult_right; auto.
      destruct (eps0_zero_or_pos f) as [ -> | Hf ].
      * rewrite eps0_mult_zero_right, eps0_add_zero_right.
        apply eps0_mpos_gt_zero; auto.
        apply eps0_lt_le_trans with (2 := eps0_momega_lt_pos _ _ Ha H1); auto.
      * apply eps0_lt_le_trans with (1 := IH2 Hf); auto.
  Qed.

  (* Easy using substraction *)
  Fact eps0_mult_mono_right a e f :
    0₀ <ε₀ a → e <ε₀ f → a *₀ e <ε₀ a *₀ f.
  Proof.
    intros ? (? & -> & ?)%eps0_lt_inv_add.
    rewrite eps0_mult_distr.
    now apply eps0_add_incr, eps0_mult_gt_zero.
  Qed.

  Fact eps0_mult_mono_left a b e :
    a <ε₀ b → a *₀ e ≤ε₀ b *₀ e.
  Proof.
    intros Hab.
    induction e as [ | n | e n g H1 IH1 IH2 ] using eps0_hnf_pos_rect.
    + rewrite !eps0_mult_zero_right; auto.
    + rewrite !eps0_mult_pos_right, eps0_le_iff_lt.
      left; apply eps0_mpos_mono_left; auto.
    + rewrite !eps0_mult_right; auto.
      apply eps0_add_mono; auto.
      apply eps0_mpos_mono; auto.
      apply eps0_momega_mono_left; auto.
  Qed.

  Fact eps0_mult_mono a b e f :
    a ≤ε₀ b → e ≤ε₀ f → a *₀ e ≤ε₀ b *₀ f.
  Proof.
    destruct (eps0_zero_or_pos a) as [ -> | Ha ].
    1: rewrite eps0_mult_zero_left; auto.
    intros [ H1 | <- ]%eps0_le_iff_lt [ H2 | <- ]%eps0_le_iff_lt.
    + apply eps0_le_trans with (a *₀ f).
      * rewrite eps0_le_iff_lt; left; apply eps0_mult_mono_right; auto.
      * now apply eps0_mult_mono_left.
    + now apply eps0_mult_mono_left.
    + rewrite eps0_le_iff_lt; left; now apply eps0_mult_mono_right.
    + rewrite eps0_le_iff_lt; now right.
  Qed.

  Fact eps0_mult_hnf a i b e j f :
      0₀ <ε₀ e
    → b <ε₀ ω^a
    → f <ε₀ ω^e
    → (ω^⟨a,i⟩ +₀ b) *₀ (ω^⟨e,j⟩ +₀ f)
     = ω^⟨a+₀e,j⟩ +₀ (ω^⟨a,i⟩ +₀ b) *₀ f.
  Proof. intros; rewrite eps0_mult_right, eps0_momega_fix_1, eps0_mpos_omega; auto. Qed.

  Fact eps0_mult_hnf_exp a i b e j :
      0₀ <ε₀ e → b <ε₀ ω^a → (ω^⟨a,i⟩ +₀ b) *₀ ω^⟨e,j⟩ = ω^⟨a+₀e,j⟩.
  Proof.
    intros H1 H2.
    rewrite <- (eps0_add_zero_right ω^⟨_,j⟩), eps0_mult_hnf; auto.
    now rewrite eps0_mult_zero_right, eps0_add_zero_right.
  Qed.

  Fact eps0_mult_exp_hnf a i e j f : 
      0₀ <ε₀ e
    → f <ε₀ ω^e
    → ω^⟨a,i⟩ *₀ (ω^⟨e,j⟩ +₀ f)
    = ω^⟨a+₀e,j⟩ +₀ ω^⟨a,i⟩ *₀ f.
  Proof. intros; rewrite <- (eps0_add_zero_right ω^⟨_,i⟩), eps0_mult_hnf; auto. Qed.

  Fact eps0_mult_omega_hnf a e j f : 
      0₀ <ε₀ e
    → f <ε₀ ω^e
    → ω^a *₀ (ω^⟨e,j⟩ +₀ f)
    = ω^⟨a+₀e,j⟩ +₀ ω^a *₀ f.
  Proof. apply eps0_mult_exp_hnf. Qed.

  Fact eps0_mult_exp_pos e i j : ω^⟨e,i⟩ *₀ ω^⟨0₀,j⟩ = ω^⟨e,i *ₚ j⟩.
  Proof. now rewrite eps0_mult_pos_right, eps0_mpos_exp. Qed.

  Fact eps0_mult_exp e i f j : 0₀ <ε₀ f → ω^⟨e,i⟩ *₀ ω^⟨f,j⟩ = ω^⟨e+₀f,j⟩.
  Proof. intro; rewrite <- (eps0_add_zero_right ω^⟨e,i⟩), eps0_mult_hnf_exp; auto. Qed.

  Fact eps0_mult_exp_omega e i f : 0₀ <ε₀ f → ω^⟨e,i⟩ *₀ ω^f = ω^(e+₀f).
  Proof. intro; apply eps0_mult_exp; auto. Qed.

  Fact eps0_mult_omega_exp e f n: ω^e *₀ ω^⟨f,n⟩ = ω^⟨e+₀f,n⟩.
  Proof.
    unfold eps0_omega.
    destruct (eps0_zero_or_pos f) as [ -> | ].
    + now rewrite eps0_mult_exp_pos, eps0_add_zero_right.
    + rewrite eps0_mult_exp; auto.
  Qed.

  Fact eps0_mult_omega e f : ω^e *₀ ω^f = ω^(e+₀f).
  Proof. apply eps0_mult_omega_exp. Qed.

  (** From ω^e.n.ω^f = ω^(e+f) *)
  Fact eps0_mult_below_omega a b e n f : 
      a <ε₀ ω^⟨e,n⟩
    → b <ε₀ ω^f
    → a *₀ b <ε₀ ω^(e+₀f).
  Proof.
    intros H1 H2.
    apply eps0_le_lt_trans with (ω^⟨e,n⟩ *₀ b).
    + apply eps0_mult_mono; auto.
    + destruct (eps0_zero_or_pos f) as [ -> | ].
      * rewrite eps0_omega_zero in H2.
        apply eps0_lt_one in H2 as ->.
        rewrite eps0_mult_zero_right; auto.
      * rewrite <- eps0_mult_exp_omega with (i := n); auto.
        apply eps0_mult_mono_right; auto.
  Qed.

  Remark eps0_mult_below_omega' a b e f : 
      a <ε₀ ω^e → b <ε₀ ω^f → a *₀ b <ε₀ ω^(e+₀f).
  Proof. apply eps0_mult_below_omega. Qed.

  Fact eps0_mult_mpos a b n : eps0_mpos (a *₀ b) n = a *₀ eps0_mpos b n. 
  Proof.
    induction b using eps0_hnf_pos_rect in a, n |- *.
    + now rewrite eps0_mult_zero_right, eps0_mpos_fix_0, eps0_mult_zero_right.
    + now rewrite eps0_mpos_exp, !eps0_mult_pos_right, eps0_mpos_comp.
    + rewrite eps0_mult_distr.
      destruct a as [ | ] using eps0_hnf_rect.
      * now rewrite !eps0_mult_zero_left, eps0_add_zero_left, eps0_mpos_fix_0.
      * rewrite eps0_mult_hnf_exp, !eps0_mpos_fix_1; auto.
        - rewrite eps0_mult_distr, eps0_mult_hnf_exp; auto.
        - apply eps0_mult_below_omega with (n := i0 +ₚ 1ₚ); auto.
          rewrite <- eps0_add_exp; auto.
  Qed.

  (** This one was a long shot !! 
      induction on c and case analysis on b and a *)
  Theorem eps0_mult_assoc a b c : a *₀ (b *₀ c) = (a *₀ b) *₀ c.
  Proof.
    induction c as [ | n | e n f He Hf IHe IHf ]
      in a, b |- * using eps0_hnf_pos_rect.
    + now rewrite !eps0_mult_zero_right.
    + now rewrite !eps0_mult_pos_right, eps0_mult_mpos.
    + destruct b as [ | i | g i h Hg Hh _ ] using eps0_hnf_pos_rect.
      * rewrite eps0_mult_zero_left,
               !eps0_mult_zero_right,
                eps0_mult_zero_left; auto.
      * rewrite eps0_mult_exp_hnf,
                eps0_add_zero_left, 
               !eps0_mult_distr,
                IHf,
                eps0_mult_pos_right,
            <- !eps0_mpos_momega_eq,
                eps0_momega_mpos; auto.
      * rewrite eps0_mult_hnf, eps0_mult_distr, IHf; auto.
        destruct a as [ | u j v Hu _ _ ] using eps0_hnf_rect.
        - now rewrite !eps0_mult_zero_left, eps0_add_zero_left.
        - rewrite eps0_mult_hnf_exp; auto.
          2: apply eps0_lt_le_trans with (1 := He); auto.
          rewrite !eps0_mult_hnf, eps0_add_assoc; auto.
          apply eps0_mult_below_omega with (n := j +ₚ 1ₚ); auto.
          apply eps0_lt_le_trans with (ω^⟨u,j⟩ +₀ ω^u); auto.
          unfold eps0_omega; rewrite eps0_add_exp; auto.
  Qed.

  Fact eps0_mult_one_left e : 1₀ *₀ e = e.
  Proof.
    rewrite <- eps0_omega_zero.
    induction e using eps0_hnf_pos_rect.
    + now rewrite eps0_mult_zero_right.
    + now rewrite eps0_mult_pos_right, eps0_mpos_omega.
    + unfold eps0_omega.
      rewrite eps0_mult_exp_hnf, eps0_add_zero_left; auto.
      f_equal; auto.
  Qed.

  Fact eps0_mult_one_right e : e *₀ 1₀ = e.
  Proof.
    rewrite <- eps0_omega_zero; unfold eps0_omega.
    now rewrite eps0_mult_pos_right, eps0_mpos_one.
  Qed.

  Fact eps0_mult_zero_inv a e : a *₀ e = 0₀ → a = 0₀ ∨ e = 0₀.
  Proof.
    intros E.
    destruct (eps0_zero_or_pos a) as [ | Ha ]; auto.
    destruct (eps0_zero_or_pos e) as [ | He ]; auto.
    destruct (@eps0_lt_irrefl 0₀).
    rewrite <- E at 2.
    now apply eps0_mult_gt_zero.
  Qed.

  Fact eps0_mult_cancel a e f : 0₀ <ε₀ a → a *₀ e = a *₀ f → e = f.
  Proof.
    intros Ha H.
    destruct (eps0_lt_sdec e f) as [ e f C | | e f C ]; auto; exfalso;
      apply (@eps0_lt_irrefl (a *₀ e)).
    + rewrite H at 2; now apply eps0_mult_mono_right.
    + rewrite H at 1; now apply eps0_mult_mono_right.
  Qed.

  Fact eps0_mult_succ_right a e : a *₀ (S₀ e) = a *₀ e +₀ a.
  Proof. now rewrite <- eps0_add_one_right, eps0_mult_distr, eps0_mult_one_right. Qed.

End eps0_mult.

Infix "*₀" := eps0_mult.

(* 0.a = a.0 = 0 *)
Check eps0_mult_zero_left.
Check eps0_mult_zero_right.
(* 1.a = a.1 = 0 *)
Check eps0_mult_one_left.
Check eps0_mult_one_right.
(* a.b = 0 → a = 0 ∨ b = 0 *)
Check eps0_mult_zero_inv.
(* a.(b.c) = (a.b).c *)
Check eps0_mult_assoc.
(* 0 < e -> a < b -> e.a < e.b *)
Check eps0_mult_mono_right.
(* Continuity is missing e.(lub P) = lub e.P *)
Check eps0_mult_mono.
Check eps0_mult_distr.
Check eps0_mult_cancel.

(** Section expo *)

Fact eps0_omega_succ e : ω^(S₀ e) = ω^e *₀ ω^1₀.
Proof.
  now rewrite <- eps0_succ_zero_is_one,
                 eps0_mult_omega,
                 eps0_succ_zero_is_one,
                 eps0_add_one_right.
Qed.

Check eps0_omega_zero.
Check eps0_omega_succ.

Section eps0_exponentiation.

  (** Define exponentiation in CNF 
   
      The formula here: 

         https://proofwiki.org/wiki/Ordinal_Exponentiation_via_Cantor_Normal_Form/Limit_Exponents

      (w^a₁.n₁+...+w^aₚ.nₚ)^e = w^(a₁.e) when a₁ > ... > aₚ

      The spec here is probably wrong for α successor
  *)

  Inductive eps0_expo_gr α : ε₀ → ε₀ → Prop :=
    | eps0_expr_gr_0 : eps0_expo_gr α 0₀ 0₀
    | eps0_expr_gr_1 γ n β : β <ε₀ ω^γ → eps0_expo_gr α (ω^⟨γ,n⟩ +₀ β) ω^(γ*₀α).

  Fact eps0_expo_fun α e1 f1 e2 f2 :
    eps0_expo_gr α e1 f1 → eps0_expo_gr α e2 f2 → e1 = e2 → f1 = f2.
  Proof.
    intros [] []; auto.
    + now intros ?%eps0_zero_neq_hnf.
    + symm; now intros ?%eps0_zero_neq_hnf.
    + intros (<- & <- & <-)%eps0_eq_hnf_inv; auto.
  Qed. 

  Definition eps0_expo_pwc e α : sig (eps0_expo_gr α e).
  Proof.
    destruct e as [ | e ] using eps0_hnf_rect.
    + exists 0₀; constructor.
    + exists ω^(e*₀α); constructor; auto.
  Qed.

  Definition eps0_expo e α := proj1_sig (eps0_expo_pwc e α).

  Fact eps0_expo_spec e α : eps0_expo_gr α e (eps0_expo e α).
  Proof. apply (proj2_sig _). Qed.

  Hint Constructors eps0_expo_gr : core.
  Hint Resolve eps0_expo_spec : core.

  Tactic Notation "functionality" :=
    apply eps0_expo_fun with (1 := eps0_expo_spec _ _) (3 := eq_refl); auto.

  Fact eps0_expo_zero e : eps0_expo 0₀ e = 0₀.
  Proof. functionality; constructor. Qed.

  Fact eps0_expo_head a n b e : b <ε₀ ω^a → eps0_expo (ω^⟨a,n⟩ +₀ b) e = ω^(a*₀e).
  Proof. intros; functionality; constructor; auto. Qed.

  Fact eps0_expo_exp_S a n e : eps0_expo ω^⟨a,n⟩ e = ω^(a*₀e).
  Proof. rewrite <- (eps0_add_zero_right ω^⟨_,n⟩), eps0_expo_head; auto. Qed.

  Fact eps0_expo_omega_pos n e : eps0_expo ω^⟨1₀,n⟩ e = ω^e.
  Proof. now rewrite eps0_expo_exp_S, eps0_mult_one_left. Qed.

  Fact eps0_expo_omega a e : eps0_expo ω^a e = ω^(a*₀e).
  Proof. apply eps0_expo_exp_S. Qed.

  (** Need to check more equations *)

End eps0_exponentiation.


