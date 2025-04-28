(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils ord ordered eps0.

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

(** Multiplication rules for j < ε₀

    0._ = 0
    j.ε₀ = ε₀ if 0 < j (indeed ε₀ <= j.ε₀ = lub {j.k | k < ε₀} <= ε₀)
    
    j.ε₀^0 = j
    j.ε₀^(1+k) = j.ε₀.ε₀^k = ε₀.ε₀^k = ε₀^(1+k)
    
    a.(b+c) = a.b+a.c
    
    Decomp 
    
    0 < j then (ε₀^0.j + 0).ε₀ = ε₀
      (indeed ε₀ <= 1.ε₀ <= (ε₀^0.j).ε₀ = j.lub {k | k < ε₀} <= ε₀)
    
    Now we decomp ε₀^e.j + u with j < ε₀ and u < ε₀^e and 0 < e
    
    establish (ε₀^e.j+u).ε₀ = ε₀^(e+1)

    proof:    
      ε₀^e.j+f <= ε₀^e.j+ε₀^e.1 = ε₀^e.(j+1)
      (ε₀^e.j+f).ε₀ <= (ε₀^e.(j+1)).ε₀ = ε₀^e.((j+1).ε₀) = ε₀^(e+1)
      ε₀^(e+1) <= ε₀^e.ε₀ <= (ε₀^e.j+f).ε₀
    
    hence for f = 1+g,  (ε₀^e.i+u).ε₀^f = ε₀^(e+f)
    
    proof:
      (ε₀^e.i+u).ε₀^f = ((ε₀^e.i+u).ε₀).ε₀^g = ε₀^(e+1).ε₀^g = ε₀^(e+1+g) = ε₀^(e+f)
    
    for f = 0, (ε₀^e.i+u).ε₀^0 = ε₀^e.i+u
    
    hence
    for f₁ > ... > fₙ > 0, and j₁,...,jₙ all < ε₀
    
    (ε₀^e.i+u).(ε₀^f₁.j₁+...+ε₀^fₙ.jₙ) = ε₀^(e+f₁).j₁+...+ ε₀^(e+fₙ).jₙ
    
    for f₁ > ... > fₙ = 0, and j₁,...,jₙ all < ε₀
    
    (ε₀^e.i+u).(ε₀^f₁.j₁+...+ε₀^fₙ.jₙ) = ε₀^(e+f₁).j₁+...+ (ε₀^e.i+u).jₙ
    
    Missing is (ε₀^e.i+u).j where u < ε₀^e and i,j < ε₀
    
    if j = 0 then 0
    else j = n (nat) then   (ε₀^e.i+u).n = ε₀^e.(i.n) + u
    else j = λ (limit) then (ε₀^e.i+u).λ = ε₀^e.(i.λ) for a limit ordinal λ

    Proof:
    assume e and f with f <= e and f + e = e
    then for a nat n > 0 we have (e+f).n = e.n + f (by induction)
       -> (e+f).(n+1) = (e+f).n+e+f = e.n+(f+e)+f = e.n+e+f = e.(n+1)+f
    now considering the value of (e+f).ω, we have the bounds
        e.n <= (e+f).n = e.n.+f <= e.n+e = e.(n+1) <= e.ω
    hence (e+f).ω = e.ω (because lub { e.n | n < ω } = e.ω)

    Now let λ be a limit ordinal. Then there is α such that λ = ω.α
    (by euclidean division, λ = ω.α + r with r < ω hence r = 0 
    otherwise λ would be a successor)

    Then (e+f).λ = (e+f).(ω.α) = ((e+f).ω).α = (e.ω).α = e.(ω.α) = e.λ

    Qed.

    We now cover the case j = λ+n with n > 0 (case of successor ordinals)

    Then (ε₀^e.i+u).j = (ε₀^e.i+u).(λ+n)
                      = (ε₀^e.i+u).λ + (ε₀^e.i+u).n
                      = ε₀^e.i.λ + ε₀^e.i.n + u
                      = ε₀^e.i.(λ+n) + u
                      = ε₀^e.i.j + u

    So the computation rules for right multiplication with an ord:

         (ε₀^e.i+u).j = 0                if j = 0
         (ε₀^e.i+u).j = ε₀^e.(i.j) + u   if j is a successor ordinal
         (ε₀^e.i+u).j = ε₀^e.(i.j)       if j is a limit ordinal

    Hence we have all the rule to compute multiplication by an ord j
    provided we can discriminate whether j is 0, successor or limit.

*)

#[local] Notation "i '+ₚ' j" := (i +ₒ 1ₒ +ₒ j) (at level 31, left associativity).
#[local] Notation "i '*ₚ' j" := (i +ₒ (1ₒ +ₒ i) *ₒ j) (at level 29, left associativity).

Section ord_extra.

  Fact ord_not_is_succ_is_limit j : ord_is_succ (1 +ₒ j) → ord_is_limit j → False.
  Proof. intros H G%ord_is_limit_1add; now apply G in H. Qed.

  Fact ord_1add_choose j : { ord_is_succ (1ₒ +ₒ j) } + { ord_is_limit j }.
  Proof.
    destruct (ord_zero_succ_limit_dec j) as [ [ -> | (p & ->) ] | ]; auto; left.
    + apply ord_is_succ_10.
    + apply ord_is_succ_1add, ord_is_succ_succ.
  Qed. 

  Fact ord_mulp_distr k i j : k *ₚ (i +ₚ j) = (k *ₚ i) +ₚ (k *ₚ j).
  Proof.
    rewrite !ord_add_assoc, <-(ord_add_assoc 1ₒ).
    rewrite <-(ord_mul_one_right (1ₒ +ₒ k)) at 3.
    now rewrite <- !ord_mul_distr.
  Qed.

  Fact ord_mulp_1add i j : 1ₒ +ₒ i *ₚ j = (1ₒ +ₒ i) *ₒ (1ₒ +ₒ j).
  Proof. now rewrite <- ord_add_assoc, ord_mul_distr, ord_mul_one_right. Qed.

  Fact ord_mulp_is_succ i j : ord_is_succ (1ₒ +ₒ i)
                           -> ord_is_succ (1ₒ +ₒ j)
                           -> ord_is_succ (1ₒ +ₒ i *ₚ j).
  Proof. rewrite ord_mulp_1add; apply ord_mul_is_succ. Qed.

  Fact ord_mulp_assoc i j k : (i *ₚ j) *ₚ k = i *ₚ (j *ₚ k).
  Proof.
    rewrite ord_mul_distr, <- ord_mul_assoc, ord_mul_distr. 
    now rewrite <- !ord_add_assoc, ord_mul_one_right.
  Qed.
 
  Fact ord_mulp_is_limit_left i j : ord_is_limit i -> ord_is_limit (i *ₚ j).
  Proof.
    intros H.
    apply ord_is_limit_1add.
    rewrite ord_mulp_1add.
    apply ord_mul_is_limit_left.
    + apply ord_1add_not_zero.
    + now apply ord_is_limit_1add.
  Qed.

  Fact ord_mulp_is_limit_right i j : ord_is_limit j -> ord_is_limit (i *ₚ j).
  Proof.
   intros H.
   apply ord_is_limit_1add.
   rewrite ord_mulp_1add.
   apply ord_mul_is_limit_right.
   + apply ord_1add_not_zero.
   + now apply ord_is_limit_1add.
  Qed.

  Fact ord_mulp_zero_left n : 0ₒ *ₚ n = n.
  Proof. now rewrite ord_add_zero_right, ord_add_zero_left, ord_mul_one_left. Qed.

End ord_extra.

#[local] Hint Resolve ord_mulp_is_succ
               ord_mulp_is_limit_left
               ord_mulp_is_limit_right : core.

Section eps0_m1add.


  (** The operation (θ : ε₀) (j : ord) => θ.(1+j)
      remember (1+i)*(1+j) = 1+(i+(1+i)*j) *)
  Inductive eps0_m1add_gr j : ε₀ → ε₀ → Prop :=
    | eps0_m1add_gr_0 :       eps0_m1add_gr j 0₀ 0₀
    | eps0_m1add_gr_1 α i β : ord_is_succ (1 +ₒ j)
                            → β <ε₀ ω^α
                            → eps0_m1add_gr j (ω^⟨α,i⟩ +₀ β) (ω^⟨α,i *ₚ j⟩ +₀ β)
    | eps0_m1add_gr_2 α i β : ord_is_limit j
                            → β <ε₀ ω^α
                            → eps0_m1add_gr j (ω^⟨α,i⟩ +₀ β) ω^⟨α,i *ₚ j⟩.


  Fact eps0_m1add_fun j e1 f1 e2 f2 : eps0_m1add_gr j e1 f1 → eps0_m1add_gr j e2 f2 → e1 = e2 → f1 = f2.
  Proof.
    do 2 destruct 1; auto.
    1,2: now intros ?%eps0_zero_neq_hnf.
    1,4: symm; now intros ?%eps0_zero_neq_hnf.
    + intros (? & [])%eps0_eq_hnf_inv; subst; auto.
    + intros (? & [])%eps0_eq_hnf_inv; subst; auto.
      edestruct ord_not_is_succ_is_limit; eauto.
    + intros (? & [])%eps0_eq_hnf_inv; subst; auto.
      edestruct ord_not_is_succ_is_limit; eauto.
    + intros (? & [])%eps0_eq_hnf_inv; subst; auto.
  Qed.

  Definition eps0_m1add_pwc e j : sig (eps0_m1add_gr j e).
  Proof.
    destruct e as [ | e i f H _ _ ] using eps0_hnf_rect.
    + exists 0₀; constructor.
    + destruct (ord_1add_choose j) as [ G | G ].
      * exists (ω^⟨e,i *ₚ j⟩ +₀ f); now constructor.
      * exists (ω^⟨e,i *ₚ j⟩); now constructor.
  Qed.

  Definition eps0_m1add e j := π₁ (eps0_m1add_pwc e j).

  Fact eps0_m1add_spec e j : eps0_m1add_gr j e (eps0_m1add e j).
  Proof. apply (proj2_sig _). Qed.

  Tactic Notation "solve" "m1add" :=
    intros; apply eps0_m1add_fun with (1 := eps0_m1add_spec _ _) (3 := eq_refl); constructor; auto.

  Fact eps0_m1add_fix_0 j : eps0_m1add 0₀ j = 0₀.
  Proof. solve m1add. Qed.

  Fact eps0_m1add_fix_1 j α i β :
    ord_is_succ (1 +ₒ j) → β <ε₀ ω^α → eps0_m1add (ω^⟨α,i⟩ +₀ β) j = ω^⟨α,i *ₚ j⟩ +₀ β.
  Proof. solve m1add. Qed.

  Fact eps0_m1add_fix_2 j α i β :
    ord_is_limit j → β <ε₀ ω^α → eps0_m1add (ω^⟨α,i⟩ +₀ β) j = ω^⟨α,i *ₚ j⟩.
  Proof. solve m1add. Qed. 

  Fact eps0_m1add_exp j α i : eps0_m1add ω^⟨α,i⟩ j = ω^⟨α,i *ₚ j⟩.
  Proof. 
    rewrite <- (eps0_add_zero_right ω^⟨_,i⟩).
    destruct (ord_1add_choose j).
    + rewrite eps0_m1add_fix_1, eps0_add_zero_right; auto.
    + rewrite eps0_m1add_fix_2; auto.
  Qed.

  Hint Resolve ord_is_succ_10 : core.

  Fact eps0_m1add_one e : eps0_m1add e 0ₒ = e.
  Proof.
    destruct e using eps0_hnf_rect.
    + now rewrite eps0_m1add_fix_0.
    + rewrite eps0_m1add_fix_1; auto.
      now rewrite ord_mul_zero_right, ord_add_zero_right.
  Qed.

  Fact eps0_m1add_omega_add_succ j α β : 
    ord_is_succ (1 +ₒ j) → β <ε₀ ω^α → eps0_m1add (ω^α +₀ β) j = ω^⟨α,j⟩ +₀ β.
  Proof.
    intros; unfold eps0_omega.
    rewrite eps0_m1add_fix_1; auto; f_equal; trivial.
    now rewrite ord_add_zero_right, ord_add_zero_left, ord_mul_one_left.
  Qed.

  Fact eps0_m1add_omega_add_limit j α β : 
    ord_is_limit j → β <ε₀ ω^α → eps0_m1add (ω^α +₀ β) j = ω^⟨α,j⟩.
  Proof.
    intros; unfold eps0_omega.
    rewrite eps0_m1add_fix_2; trivial.
    now rewrite ord_add_zero_right, ord_add_zero_left, ord_mul_one_left.
  Qed.

  Fact eps0_m1add_omega j α : eps0_m1add ω^α j = ω^⟨α,j⟩.
  Proof.
    unfold eps0_omega.
    rewrite eps0_m1add_exp.
    now rewrite ord_add_zero_right, ord_add_zero_left, ord_mul_one_left.
  Qed.

  Fact eps0_m1add_add e i j : eps0_m1add e i +₀ eps0_m1add e j = eps0_m1add e (i +ₚ j).
  Proof.
    destruct e using eps0_hnf_rect.
    + now rewrite !eps0_m1add_fix_0, eps0_add_zero_left.
    + destruct (ord_1add_choose j) as [ Gj | Gj ];
      destruct (ord_1add_choose i) as [ Gi | Gi ].
      * do 3 (rewrite eps0_m1add_fix_1; auto).
        - rewrite eps0_add_hnf_eq, ord_mulp_distr; auto.
        - rewrite !ord_add_assoc, <- ord_add_assoc.
          apply ord_is_succ_add; auto.
      * rewrite eps0_m1add_fix_2; auto.
        do 2 (rewrite eps0_m1add_fix_1; auto).
        - rewrite eps0_add_exp_hnf_eq, ord_mulp_distr; auto.
        - rewrite !ord_add_assoc, <- ord_add_assoc.
          apply ord_is_succ_add; auto.
      * rewrite eps0_m1add_fix_1 with (j := i); auto.
        do 2 (rewrite eps0_m1add_fix_2; auto).
        - rewrite eps0_add_hnf_exp_eq, ord_mulp_distr; auto.
        - apply ord_is_limit_add; auto.
      * do 3 (rewrite eps0_m1add_fix_2; auto).
        - rewrite eps0_add_exp, ord_mulp_distr; auto.
        - apply ord_is_limit_add; auto.
  Qed.

  Fact eps0_m1add_comp e i j : eps0_m1add (eps0_m1add e i) j = eps0_m1add e (i *ₚ j).
  Proof.
    destruct e using eps0_hnf_rect.
    + now rewrite !eps0_m1add_fix_0.
    + destruct (ord_1add_choose j) as [ Gj | Gj ];
      destruct (ord_1add_choose i) as [ Gi | Gi ].
      * do 3 (rewrite eps0_m1add_fix_1; auto).
        now rewrite ord_mulp_assoc.
      * rewrite eps0_m1add_fix_2 with (j := i); auto.
        rewrite eps0_m1add_exp.
        rewrite eps0_m1add_fix_2; auto.
        now rewrite ord_mulp_assoc.
      * rewrite eps0_m1add_fix_1 with (j := i); auto.
        do 2 (rewrite eps0_m1add_fix_2; auto).
        now rewrite ord_mulp_assoc.
      * do 2 (rewrite eps0_m1add_fix_2; auto).
        rewrite eps0_m1add_exp, ord_mulp_assoc; auto.
  Qed.

  Hint Resolve ord_add_mono_le ord_mul_mono ord_le_refl ord_lt_le_weak 
               ord_add_mono_lt_right : core.

  (* This is incorrect for limit ordinals : 3.ω = 2.ω but not 3 < 2 *) 
  Fact eps0_m1add_mono_left_eq_succ a b n : 
    ord_is_succ (1ₒ +ₒ n) → a <ε₀ b → eps0_m1add a n <ε₀ eps0_m1add b n.
  Proof.
    intros Hn Hab.
    destruct a as [ | e i f H1 _ _ ] using eps0_hnf_rect;
      destruct b as [ | g j h H2 _ _ ] using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in Hab.
    + rewrite eps0_m1add_fix_0.
      destruct (ord_1add_choose n).
      * rewrite eps0_m1add_fix_1; auto.
      * rewrite eps0_m1add_fix_2; auto.
    + now apply eps0_zero_not_gt in Hab.
    + apply eps0_lt_hnf_inv in Hab; auto.
      rewrite !eps0_m1add_fix_1; auto.
      apply eps0_lt_hnf_inv; auto.
      destruct Hab as [ | (<- & [ | (<- & ?) ]) ]; auto.
      right; split; auto; left.
      apply ord_add_mono_lt_inv with 1ₒ.
      rewrite !ord_mulp_1add.
      destruct Hn as (k & ->).
      rewrite !ord_mul_distr, !ord_mul_one_right.
      apply ord_le_lt_trans with ((1ₒ +ₒ j) *ₒ k +ₒ (1ₒ +ₒ i)); auto.
  Qed.

  Fact eps0_m1add_mono_left_eq_limit a b n : 
    ord_is_limit n → a <ε₀ b → eps0_m1add a n ≤ε₀ eps0_m1add b n.
  Proof.
    intros Hn Hab.
    destruct a as [ | e i f H1 _ _ ] using eps0_hnf_rect;
      destruct b as [ | g j h H2 _ _ ] using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in Hab.
    + rewrite eps0_m1add_fix_0.
      destruct (ord_1add_choose n).
      * rewrite eps0_m1add_fix_1; auto.
      * rewrite eps0_m1add_fix_2; auto.
    + now apply eps0_zero_not_gt in Hab.
    + apply eps0_lt_hnf_inv in Hab; auto.
      rewrite !eps0_m1add_fix_2; auto.
      apply eps0_le_exp_inv; auto.
      destruct Hab as [ | (<- & [ | (<- & ?) ]) ]; auto.
      right; split; auto.
  Qed.

  Fact eps0_m1add_mono_left a b n : 
    a ≤ε₀ b → eps0_m1add a n ≤ε₀ eps0_m1add b n.
  Proof.
    intros [ | -> ]%eps0_le_iff_lt; auto.
    destruct (ord_1add_choose n).
    + apply eps0_le_iff_lt; left; apply eps0_m1add_mono_left_eq_succ; auto.
    + apply eps0_m1add_mono_left_eq_limit; auto.
  Qed.

  Fact eps0_m1add_mono_right_le a n m : n ≤ₒ m → eps0_m1add a n ≤ε₀ eps0_m1add a m.
  Proof.
    intros (k& ->)%ord_sub.
    destruct (ord_zero_or_1add k) as [ -> | (j & ->) ].
    + rewrite ord_add_zero_right; auto.
    + rewrite <- ord_add_assoc, <- eps0_m1add_add; auto.
  Qed.

  Hint Resolve ord_le_zero_least : core.

  Fact eps0_m1add_gt_zero a n : 0₀ <ε₀ a → 0₀ <ε₀ eps0_m1add a n.
  Proof.
    intros H.
    apply eps0_lt_le_trans with (1 := H).
    rewrite <- (eps0_m1add_one a) at 1.
    apply eps0_m1add_mono_right_le; auto.
  Qed.

  Hint Resolve eps0_m1add_mono_left eps0_m1add_gt_zero : core.

  Fact eps0_m1add_mono_right_lt a n m : 0₀ <ε₀ a → n <ₒ m → eps0_m1add a n <ε₀ eps0_m1add a m.
  Proof.
    intros H1 H2%ord_lt__succ_le_iff.
    apply eps0_lt_le_trans with (eps0_m1add a (n +ₒ 1ₒ)).
    2: apply eps0_m1add_mono_right_le; auto.
    replace (n +ₒ 1ₒ) with (n +ₚ 0ₒ).
    2: now rewrite ord_add_zero_right.
    rewrite <- eps0_m1add_add.
    rewrite <- (eps0_add_zero_right (eps0_m1add a n)) at 1.
    apply eps0_add_mono_right; auto.
  Qed.

  Hint Resolve eps0_m1add_mono_right_le : core.

  Fact eps0_m1add_mono a b m n : a ≤ε₀ b → m ≤ₒ n → eps0_m1add a m ≤ε₀ eps0_m1add b n.
  Proof. intros; apply eps0_le_trans with (eps0_m1add a n); auto. Qed.

  Fact eps0_m1add_below_omega a n e : a <ε₀ ω^e → eps0_m1add a n <ε₀ ω^e.
  Proof.
    intros [ -> | (f & i & H1 & H2) ]%eps0_below_omega_inv.
    + rewrite eps0_m1add_fix_0; auto.
    + apply eps0_lt_le_weak, eps0_m1add_mono_left with (n := n) in H1.
      apply eps0_le_lt_trans with (1 := H1).
      rewrite eps0_m1add_exp.
      apply eps0_lt_exp_inv; auto.
  Qed.

  Fact eps0_m1add_below_omega' a n e i : a <ε₀ ω^⟨e,i⟩ → eps0_m1add a n <ε₀ ω^(S₀ e).
  Proof.
    intros H.
    apply eps0_m1add_below_omega,
          eps0_lt_trans with (1 := H),
          eps0_exp_mono_left; auto.
  Qed.

End eps0_m1add.

#[local] Hint Resolve eps0_m1add_mono_left eps0_m1add_gt_zero : core.

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

  Fact eps0_momega_m1add a i e :
      0₀ <ε₀ e → eps0_momega (eps0_m1add a i) e = eps0_momega a e.
  Proof.
    intros He.
    destruct a using eps0_hnf_rect.
    + now rewrite eps0_m1add_fix_0.
    + destruct (ord_1add_choose i).
      * rewrite eps0_m1add_fix_1; auto.
        rewrite !eps0_momega_fix_1; auto.
      * rewrite eps0_m1add_fix_2; auto.
        rewrite eps0_momega_fix_1, eps0_momega_exp; auto.
  Qed.

  Fact eps0_add_m1add_momega n k e f :
      0₀ <ε₀ f
    → eps0_m1add e n +₀ eps0_m1add (eps0_momega e f) k
    = eps0_m1add (eps0_momega e f) k.
  Proof.
    intros Hf.
    destruct e using eps0_hnf_rect.
    + now rewrite !eps0_m1add_fix_0, eps0_add_zero_left.
    + rewrite eps0_momega_fix_1; auto.
      rewrite eps0_m1add_omega.
      destruct (ord_1add_choose n).
      * rewrite eps0_m1add_fix_1; auto.
        rewrite <- (eps0_add_zero_right ω^⟨_,k⟩).
        rewrite eps0_add_hnf_lt; auto.
      * rewrite eps0_m1add_fix_2; auto.
        rewrite eps0_add_exp_lt; auto.
  Qed.

  Fact eps0_m1add_add_momega a e f i j :
      e <ε₀ f
    → eps0_m1add (eps0_momega a e) i +₀ eps0_m1add (eps0_momega a f) j
    = eps0_m1add (eps0_momega a f) j.
  Proof.
    intros Hef.
    destruct a using eps0_hnf_rect.
    + now rewrite !eps0_momega_fix_0, !eps0_m1add_fix_0, eps0_add_zero_left.
    + rewrite !eps0_momega_fix_1; auto.
      rewrite !eps0_m1add_omega, eps0_add_exp_lt; auto.
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

  Fact eps0_lt_m1add_momega a n f :
      0₀ <ε₀ a
    → 0₀ <ε₀ f
    → eps0_m1add a n <ε₀ eps0_momega a f.
  Proof.
    intros Ha Hf.
    destruct a using eps0_hnf_rect.
    + now apply eps0_lt_irrefl in Ha.
    + rewrite eps0_momega_fix_1; auto.
      destruct (ord_1add_choose n).
      * rewrite eps0_m1add_fix_1; auto.
        apply eps0_lt_hnf_exp_inv; auto.
      * rewrite eps0_m1add_fix_2; auto.
        apply eps0_exp_mono_left; auto.
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
    | eps0_mult_gr_1 n       : eps0_mult_gr γ ω^⟨0₀,n⟩ (eps0_m1add γ n)
    | eps0_mult_gr_2 α n β r : 0₀ <ε₀ α
                             → β <ε₀ ω^α
                             → eps0_mult_gr γ β r
                             → eps0_mult_gr γ (ω^⟨α,n⟩ +₀ β) (eps0_m1add (eps0_momega γ α) n +₀ r).

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
    + exists (eps0_m1add γ n); auto.
    + exists (eps0_m1add (eps0_momega γ e) n +₀ r); auto.
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

  Fact eps0_mult_1add_right a n : a *₀ ω^⟨0₀,n⟩ = eps0_m1add a n.
  Proof. solve mult. Qed.

  Corollary eps0_m1add_eq a n : eps0_m1add a n = a *₀ ω^⟨0₀,n⟩.
  Proof. now rewrite eps0_mult_1add_right. Qed.

  Fact eps0_mult_hnf_right a e n f :
      0₀ <ε₀ e
    → f <ε₀ ω^e
    → a *₀ (ω^⟨e,n⟩ +₀ f)
    = eps0_m1add (eps0_momega a e) n +₀ a *₀ f.
  Proof. solve mult. Qed.

  (** This one is stronger because it does not need any relation between e and f *)
  Fact eps0_mult_right a e n f :
      0₀ <ε₀ e
    → a *₀ (ω^⟨e,n⟩ +₀ f)
    = eps0_m1add (eps0_momega a e) n +₀ a *₀ f.
  Proof.
    intros He.
    destruct f as [ | f i g H _ _ ] using eps0_hnf_rect.
    + rewrite eps0_mult_hnf_right; auto.
    + destruct (eps0_lt_sdec e f).
      * rewrite eps0_add_exp_hnf_lt, eps0_mult_hnf_right,
             <- eps0_add_assoc, eps0_m1add_add_momega; auto.
        eapply eps0_lt_trans; eassumption.
      * rewrite eps0_add_exp_hnf_eq, 
               !eps0_mult_hnf_right,
             <- eps0_add_assoc,
                eps0_m1add_add; auto.
      * rewrite eps0_mult_hnf_right; auto.
        apply eps0_add_below_omega.
        - now apply eps0_exp_mono_left.
        - apply eps0_lt_trans with (1 := H),
                eps0_omega_mono_lt; auto.
  Qed.

  Fact eps0_m1add_momega_eq a n e :
    0₀ <ε₀ e → eps0_m1add (eps0_momega a e) n = a *₀ ω^⟨e,n⟩.
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
    rewrite <- eps0_m1add_momega_eq, eps0_m1add_one; auto.
  Qed.

  Fact eps0_mult_zero_left e : 0₀ *₀ e = 0₀.
  Proof.
    induction e as [ | n | e n f He Hf _ IHf ] using eps0_hnf_pos_rect.
    + now rewrite eps0_mult_zero_right.
    + now rewrite eps0_mult_1add_right, eps0_m1add_fix_0.
    + rewrite eps0_mult_hnf_right, IHf; auto.
      now rewrite eps0_momega_fix_0, eps0_m1add_fix_0, eps0_add_zero_left.
  Qed.

  Fact eps0_mult_distr a b c : a *₀ (b +₀ c) = a *₀ b +₀ a *₀ c.
  Proof.
    induction b as [ | n | e n f He Hf IHe IHf ] in a, c |- *
      using eps0_hnf_pos_rect.
    + now rewrite eps0_mult_zero_right, !eps0_add_zero_left.
    + destruct c as [ | k | c k g ? ? _ _ ] using eps0_hnf_pos_rect.
      * now rewrite eps0_mult_zero_right, !eps0_add_zero_right.
      * now rewrite eps0_add_exp, !eps0_mult_1add_right, eps0_m1add_add.
      * rewrite eps0_add_exp_hnf_lt,
                eps0_mult_hnf_right,
                eps0_mult_1add_right,
             <- eps0_add_assoc,
                eps0_add_m1add_momega; auto.
    + rewrite eps0_mult_right,
             !eps0_add_assoc,
           <- IHf, eps0_mult_right; auto.
  Qed.

  Fact eps0_mult_gt_zero a e : 0₀ <ε₀ a → 0₀ <ε₀ e → 0₀ <ε₀ a *₀ e.
  Proof.
    intros Ha He.
    induction e as [ | n | e n f H1 H2 IH1 IH2 ] using eps0_hnf_pos_rect.
    + now apply eps0_lt_irrefl in He.
    + rewrite eps0_mult_1add_right; auto.
    + rewrite eps0_mult_right; auto.
      destruct (eps0_zero_or_pos f) as [ -> | Hf ].
      * rewrite eps0_mult_zero_right, eps0_add_zero_right.
        apply eps0_m1add_gt_zero; auto.
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
    + rewrite !eps0_mult_1add_right; auto.
    + rewrite !eps0_mult_right; auto.
      apply eps0_add_mono; auto.
      apply eps0_m1add_mono; auto.
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
  Proof. intros; rewrite eps0_mult_right, eps0_momega_fix_1, eps0_m1add_omega; auto. Qed.

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
  Proof. now rewrite eps0_mult_1add_right, eps0_m1add_exp. Qed.

  Fact eps0_mult_exp e i f j : 0₀ <ε₀ f → ω^⟨e,i⟩ *₀ ω^⟨f,j⟩ = ω^⟨e+₀f,j⟩.
  Proof. intro; rewrite <- (eps0_add_zero_right ω^⟨e,i⟩), eps0_mult_hnf_exp; auto. Qed.

  Fact eps0_mult_exp_omega e i f : 0₀ <ε₀ f → ω^⟨e,i⟩ *₀ ω^f = ω^(e+₀f).
  Proof. intro; apply eps0_mult_exp; auto. Qed.

  Fact eps0_mult_omega_exp e f n: ω^e *₀ ω^⟨f,n⟩ = ω^⟨e+₀f,n⟩.
  Proof.
    unfold eps0_omega.
    destruct (eps0_zero_or_pos f) as [ -> | ].
    + now rewrite eps0_mult_exp_pos, eps0_add_zero_right, ord_mulp_zero_left.
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

  Fact eps0_mult_m1add a b n : eps0_m1add (a *₀ b) n = a *₀ eps0_m1add b n. 
  Proof.
    induction b as [ | | b1 i b2 ] using eps0_hnf_pos_rect in a, n |- *.
    + now rewrite eps0_mult_zero_right, eps0_m1add_fix_0, eps0_mult_zero_right.
    + now rewrite eps0_m1add_exp, !eps0_mult_1add_right, eps0_m1add_comp.
    + rewrite eps0_mult_distr.
      destruct a as [ | a1 j a2 ] using eps0_hnf_rect.
      * now rewrite !eps0_mult_zero_left, eps0_add_zero_left, eps0_m1add_fix_0.
      * rewrite eps0_mult_hnf_exp; auto.
        destruct (ord_1add_choose n).
        - rewrite !eps0_m1add_fix_1; auto.
          ++ rewrite eps0_mult_distr, eps0_mult_hnf_exp; auto.
          ++ apply eps0_mult_below_omega with (n := j +ₚ 0ₒ); auto.
             rewrite <- eps0_add_exp; auto.
        - rewrite !eps0_m1add_fix_2; auto.
          ++ rewrite eps0_mult_hnf_exp; auto.
          ++ apply eps0_mult_below_omega with (n := j +ₚ 0ₒ); auto.
             rewrite <- eps0_add_exp; auto.
  Qed.

  (** This one was a long shot !! 
      induction on c and case analysis on b and a *)
  Theorem eps0_mult_assoc a b c : a *₀ (b *₀ c) = (a *₀ b) *₀ c.
  Proof.
    induction c as [ | n | e n f He Hf IHe IHf ]
      in a, b |- * using eps0_hnf_pos_rect.
    + now rewrite !eps0_mult_zero_right.
    + now rewrite !eps0_mult_1add_right, eps0_mult_m1add.
    + destruct b as [ | i | g i h Hg Hh _ ] using eps0_hnf_pos_rect.
      * rewrite eps0_mult_zero_left,
               !eps0_mult_zero_right,
                eps0_mult_zero_left; auto.
      * rewrite eps0_mult_exp_hnf,
                eps0_add_zero_left, 
               !eps0_mult_distr,
                IHf,
                eps0_mult_1add_right,
            <- !eps0_m1add_momega_eq,
                eps0_momega_m1add; auto.
      * rewrite eps0_mult_hnf, eps0_mult_distr, IHf; auto.
        destruct a as [ | u j v Hu _ _ ] using eps0_hnf_rect.
        - now rewrite !eps0_mult_zero_left, eps0_add_zero_left.
        - rewrite eps0_mult_hnf_exp; auto.
          2: apply eps0_lt_le_trans with (1 := He); auto.
          rewrite !eps0_mult_hnf, eps0_add_assoc; auto.
          apply eps0_mult_below_omega with (n := j +ₚ 0ₒ); auto.
          apply eps0_lt_le_trans with (ω^⟨u,j⟩ +₀ ω^u); auto.
          unfold eps0_omega; rewrite eps0_add_exp; auto.
  Qed.

  Fact eps0_mult_one_left e : 1₀ *₀ e = e.
  Proof.
    rewrite <- eps0_omega_zero.
    induction e using eps0_hnf_pos_rect.
    + now rewrite eps0_mult_zero_right.
    + now rewrite eps0_mult_1add_right, eps0_m1add_omega.
    + unfold eps0_omega.
      rewrite eps0_mult_exp_hnf, eps0_add_zero_left; auto.
      f_equal; auto.
  Qed.

  Fact eps0_mult_one_right e : e *₀ 1₀ = e.
  Proof.
    rewrite <- eps0_omega_zero; unfold eps0_omega.
    now rewrite eps0_mult_1add_right, eps0_m1add_one.
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
  
  (** See comment here for an algo. 
  
            https://math.stackexchange.com/a/4133983   *)

  (*
  
  Fact eps0_euclid a d : 0₀ <ε₀ d → ∃ q r, a = d *₀ q +₀ r ∧ r <ε₀ d.
  Proof.
    destruct d as [ | e j f Hf _ _ ] using eps0_hnf_rect.
    1: now intros ?%eps0_lt_irrefl.
    intros _.
    induction a as [ | a i b Hb IHa IHb ] using eps0_hnf_rect.
    + exists 0₀, 0₀; rewrite eps0_mult_zero_right, eps0_add_zero_left; auto.
    + destruct (eps0_lt_sdec a e) as [ a e H | a | a e H ].
      * exists 0₀, (ω^⟨a,i⟩ +₀ b); split.
        - rewrite eps0_mult_zero_right, eps0_add_zero_left; auto.
        - apply eps0_lt_hnf_inv; auto.
      * destruct (pos_lt_sdec i j) as [ i j H | i | i j H ].
        - exists 0₀, (ω^⟨a,i⟩ +₀ b); split.
          ++ rewrite eps0_mult_zero_right, eps0_add_zero_left; auto.
          ++ apply eps0_lt_hnf_inv; auto.
        - destruct IHb as (q' & r' & -> & Hb').
          destruct (eps0_zero_or_pos q') as [ -> | Hq' ].
          ++ apply eps0_lt_add_inv_add in Hb' as [ Hb' | (k & -> & Hk) ].
             ** exists 1₀, r'; rewrite eps0_mult_zero_right, eps0_add_zero_left, eps0_mult_one_right.
          exists (1₀ +₀ q'), r'.
        exists 
      destruct (IHb
        apply eps0_lt_le_trans with ω^e.
        Search eps0_lt eps0_exp.
          ++ apply eps0_add_below_omega.
             ** now apply eps0_exp_mono_left.
             ** now apply eps0_lt_trans with (1 := Hb), eps0_exp_mono_left.
          ++ admit.
      * destruct (eps0_le_lt
        apply eps0_lt_hnf.
    destruct (eps0_lt_sdec d a) as [ d a (b & -> & H)%eps0_lt_inv_add | d | d a H ].
    + destruct (IH b) as (q & r & -> & ?); auto.
      * admit.
      * exists (
      exists (
    
    Search eps0_lt eps0_add.

  *)

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

(*

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

*)


