(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils ord eps0 eps0_mult.

Set Implicit Arguments.

#[local] Notation π₁ := proj1_sig.
#[local] Notation π₂ := proj2_sig.

Section eps0_limit_dep_rect.

  Variables (P : ∀e, eps0_is_limit e → Type)
            (HP0 : ∀ j l, ord_is_limit j → @P ω^⟨0₀,j⟩ l)
            (HP1 : ∀ e j l, e ≠ 0₀ → @P ω^⟨e,j⟩ l)
            (HP2 : ∀ e j f l l', f <ε₀ ω^e → @P f l → @P (ω^⟨e,j⟩ +₀ f) l').

  Theorem eps0_limit_dep_rect e l : @P e l.
  Proof.
    induction e as [ | e j f H IH1 IH2 ] in l |- * using eps0_hnf_rect.
    + exfalso; now destruct l.
    + destruct (eps0_is_limit_dec f) as [ Hf | Hf ].
      * now apply HP2 with (2 := IH2 Hf).
      * assert (f = 0₀) as ->
          by (rewrite eps0_hnf_is_limit in l; tauto).
        revert l; rewrite eps0_add_zero_right; intros l.
        destruct (eps0_eq_dec e 0₀) as [ -> | He ].
        - apply HP0.
          apply eps0_is_limit_exp_iff in l; tauto.
        - now apply HP1.
  Qed.

End eps0_limit_dep_rect.

Section eps0_fseq_dep_rect.

  (* cases:
        ω^e.j         -> ω^e.λ              where λ ~> j
        ω^(e+1).(j+1) -> ω^(e+1).j + ω^e.λ  where λ ~> ω
        ω^e.(j+1)     -> ω^e.j + ω^e        where λ ~> e *)

  Variables (P : ∀e, eps0_is_limit e → Type)
            (HP0 : ∀ e j l, ord_is_limit j → @P ω^⟨e,j⟩ l)

            (HP1 : ∀ e l,   @P ω^(e +₀ 1₀) l)
            (HP2 : ∀ e j l, @P ω^⟨e +₀ 1₀,j +ₒ 1ₒ⟩ l)

            (HP3 : ∀ e l l', @P e l → @P ω^e l')
            (HP4 : ∀ e j l l', @P e l → @P ω^⟨e,j +ₒ 1ₒ⟩ l')
             
            (HP5 : ∀ e j f l l', f <ε₀ ω^e → @P f l → @P (ω^⟨e,j⟩ +₀ f) l').

  Hint Resolve ord_is_succ_succ : core.

  Theorem eps0_fseq_dep_rect e l : @P e l.
  Proof.
    induction e as [ | e j f H IH1 IH2 ] in l |- * using eps0_hnf_rect.
    + now destruct (proj1 l).
    + destruct (eps0_is_limit_dec f) as [ Hf | Hf ].
      * now apply HP5 with (2 := IH2 Hf).
      * assert (f = 0₀) as ->.
        1: apply eps0_hnf_is_limit in l as [ | [] ]; tauto.
        revert l; rewrite eps0_add_zero_right; clear H Hf; intros l.
        destruct (ord_zero_succ_limit_dec j) as [ [ -> | (i & ->) ] | lj ].
        - destruct (eps0_zero_succ_limit_dec e) as [ [ -> | (g & ->) ] | le ].
          ++ exfalso; apply eps0_is_limit_exp_iff in l as [ [] | (_ & []) ]; auto.
          ++ apply HP1.
          ++ apply HP3 with le, IH1.
        - destruct (eps0_zero_succ_limit_dec e) as [ [ -> | (g & ->) ] | le ].
          ++ exfalso; apply eps0_is_limit_exp_iff in l as [ [] | (_ & [_ []]) ]; auto.
          ++ apply HP2.
          ++ apply HP4 with le, IH1.
        - now apply HP0.
  Qed.

End eps0_fseq_dep_rect.

(*

   Fund sequence possible for limit ordinal a + ε₀^(e,1+n)
      - 1+n = 0 is not possible
      - if 1+n = m+1 then a + ε₀^(e,m) + ε₀^e
        - ε₀^e is limit so e <> 0
        - if e = f+1 then λ(i) := a + ε₀^(e,m) + ε₀^f.(1+i)
        - if e is limit λₑ then λ(i) := a + ε₀^(e,m) + ε₀^(λₑ(i))
      - if 1+n is limit λₙ then λ(i) := a + ε₀^(e,λₙ(i))

   Or fseq by hnf induction ?
    
    0 is not limit
    ε₀^e.g + f and f < ε₀^e and g < ε₀
     - e = 0, then f = 0 then g is limit
     - f = 0
       - e = 0
       - g = n+1
       - g is limit
     - f <> 0 then f is limit

    cases is_limit
      - ε₀^0.g + 0 with g is limit
      - ε₀^e.g + f with 0 < e and g < ε₀ and f < ε₀^e
        - f = 0 
           - g = n + 1
           - g is limit
        - 0 < f then f is limit

    *)

Section eps0_fseq.

  Inductive eps0_fseq_gr : ε₀ → (nat → ε₀) → Prop :=
    | eps0_fseq_gr_0 e j l   : eps0_fseq_gr ω^⟨e,j⟩ (λ n, ω^⟨e,@ord_fseq j l n⟩)
    | eps0_fseq_gr_1 e       : eps0_fseq_gr ω^(e +₀ 1₀) (λ n, ω^⟨e,ord_mseq n⟩)
    | eps0_fseq_gr_2 e j     : eps0_fseq_gr ω^⟨e +₀ 1₀,j +ₒ 1ₒ⟩ (λ n, ω^⟨e +₀ 1₀,j⟩ +₀ ω^⟨e,ord_mseq n⟩)
    | eps0_fseq_gr_3 e r     : eps0_is_limit e
                             → eps0_fseq_gr e r
                             → eps0_fseq_gr ω^e (λ n, ω^(r n))
    | eps0_fseq_gr_4 e j r   : eps0_is_limit e
                             → eps0_fseq_gr e r
                             → eps0_fseq_gr ω^⟨e,j +ₒ 1ₒ⟩ (λ n, ω^⟨e,j⟩ +₀ ω^(r n))
    | eps0_fseq_gr_5 e j f r : f <ε₀ ω^e
                             → eps0_is_limit f
                             → eps0_fseq_gr f r
                             → eps0_fseq_gr (ω^⟨e,j⟩ +₀ f) (λ n, ω^⟨e,j⟩ +₀ r n).

  Hint Resolve ord_is_succ_succ eps0_is_succ_add1 : core.

  Local Fact eps0_eq_absurd_1 e f i : ord_is_limit i → ω^⟨e,i⟩ = ω^f → False.
  Proof. intros H (_ & ->)%eps0_exp_inj; now destruct H. Qed.

  Local Fact eps0_eq_absurd_2 e f i j : ord_is_limit i → ω^⟨e,i⟩ = ω^⟨f,j +ₒ 1ₒ⟩ → False.
  Proof. intros H (_ & ->)%eps0_exp_inj; destruct H as [ ? [] ]; auto. Qed.

  Local Fact eps0_eq_absurd_3 e f i j g : g <ε₀ ω^f → eps0_is_limit g → ω^⟨e,i⟩ = ω^⟨f,j⟩ +₀ g → False.
  Proof. intros H1 H2 (-> & -> & ->)%eps0_eq_exp_hnf_inv; auto; now destruct H2. Qed.

  Local Fact eps0_eq_absurd_4 e f i : ω^e = ω^⟨f,i +ₒ 1ₒ⟩ → False.
  Proof. intros [_ H]%eps0_exp_inj; revert H; symm; apply ord_succ_not_zero. Qed.

  Local Fact eps0_eq_absurd_5 e f i j : eps0_is_limit f → ω^⟨e +₀ 1₀,i⟩ = ω^⟨f,j⟩ → False.
  Proof. intros H (<- & _)%eps0_exp_inj; destruct H as [ ? [] ]; auto. Qed. 

  Tactic Notation "elim" "one" :=
       (now intros ?%eps0_eq_absurd_1) 
    || (now intros ?%eps0_eq_absurd_2) 
    || (now intros ?%eps0_eq_absurd_3) 
    || (now intros ?%eps0_eq_absurd_4) 
    || (now intros ?%eps0_eq_absurd_5) 
    || (now intros ?%eps0_eq_absurd_5).

  Tactic Notation "elim" "absurd" := (elim one) || (symm; elim one) || idtac. 

  Local Lemma eps0_fseq_fun_rec e se f sf :
    eps0_fseq_gr e se → eps0_fseq_gr f sf → e = f → ∀n, se n = sf n.
  Proof.
    intros H; revert H f sf.
    induction 1 as [ e i l | e | e i | e r l H IH | e i r l H IH | e i f r H1 H2 ? IH ];
      induction 1 as [ g j m | g | g j | g s m G ? | g j s m G _ | g j h s G1 G2 ? _ ].
    all: elim absurd.
    + intros (-> & ->)%eps0_exp_inj; intro; f_equal; apply ord_fseq_pirr.
    + now intros (->%eps0_add1_inj & _)%eps0_exp_inj.
    + intros (->%eps0_add1_inj & ->%ord_succ_inj)%eps0_exp_inj; auto.
    + intros (-> & _)%eps0_exp_inj.
      intro; f_equal; now apply IH with (2 := eq_refl).
    + intros (-> & ->%ord_succ_inj)%eps0_exp_inj.
      intro; do 2 f_equal; now apply IH with (2 := eq_refl).
    + intros (-> & -> & ->)%eps0_eq_hnf_inv; auto.
      intro; f_equal; now apply IH with (2 := eq_refl).
  Qed.

  Lemma eps0_fseq_fun e r r' : eps0_fseq_gr e r → eps0_fseq_gr e r' → ∀n, r n = r' n.
  Proof. intros H1 H2; now apply (eps0_fseq_fun_rec H1 H2). Qed.

  Theorem eps0_fseq_pwc e : eps0_is_limit e → sig (eps0_fseq_gr e).
  Proof.
    induction 1 as [ e j _ l | e | e j | e l l' (r & Hr) | e j l l' (r & Hr) 
                   | e j f l l' H (r & Hr)] using eps0_fseq_dep_rect.
    + exists (λ n, ω^⟨e,@ord_fseq j l n⟩); constructor.
    + exists (λ n, ω^⟨e,ord_mseq n⟩); constructor.
    + exists (λ n, ω^⟨e +₀ 1₀,j⟩ +₀ ω^⟨e,ord_mseq n⟩); constructor.
    + exists (λ n, ω^(r n)); now constructor.
    + exists (λ n, ω^⟨e,j⟩ +₀ ω^(r n)); now constructor.
    + exists (λ n, ω^⟨e,j⟩ +₀ r n); now constructor.
  Qed.

  Definition eps0_fseq e l := π₁ (@eps0_fseq_pwc e l).

  Fact eps0_fseq_spec e l : eps0_fseq_gr e (@eps0_fseq e l).
  Proof. apply (proj2_sig _). Qed.

  Hint Resolve eps0_fseq_spec : core.

  Fact eps0_fseq_pirr e l1 l2 n : @eps0_fseq e l1 n = @eps0_fseq e l2 n.
  Proof. apply eps0_fseq_fun with e; auto. Qed.

  Tactic Notation "solve" "fix" :=
    intros; match goal with n : nat |- _ => revert n end; 
    apply eps0_fseq_fun with (1 := @eps0_fseq_spec _ _); constructor; auto.

  Fact eps0_fseq_fix_0 e j l l' n : @eps0_fseq ω^⟨e,j⟩ l n = ω^⟨e,@ord_fseq j l' n⟩.
  Proof. solve fix. Qed.

  Fact eps0_fseq_fix_1 e l n : @eps0_fseq ω^(e +₀ 1₀) l n = ω^⟨e,ord_mseq n⟩.
  Proof. solve fix. Qed.

  Fact eps0_fseq_fix_2 e j l n : @eps0_fseq ω^⟨e +₀ 1₀,j +ₒ 1ₒ⟩ l n = ω^⟨e +₀ 1₀,j⟩ +₀ ω^⟨e,ord_mseq n⟩.
  Proof. solve fix. Qed.

  Fact eps0_fseq_fix_3 e l l' n : @eps0_fseq ω^e l n = ω^(@eps0_fseq e l' n).
  Proof. solve fix. Qed.

  Fact eps0_fseq_fix_4 e j l l' n : @eps0_fseq ω^⟨e,j +ₒ 1ₒ⟩ l n = ω^⟨e,j⟩ +₀ ω^(@eps0_fseq e l' n).
  Proof. solve fix. Qed.

  Fact eps0_fseq_fix_5 e j f l l' n : f <ε₀ ω^e → @eps0_fseq (ω^⟨e,j⟩ +₀ f) l n = ω^⟨e,j⟩ +₀ @eps0_fseq f l' n.
  Proof. solve fix. Qed.
  
  Fact eps0_fseq_gt_zero e (l : eps0_is_limit e) : ∀n, 0₀ <ε₀ eps0_fseq l n.
  Proof.
    induction l as [ e j l l' | e | e j | e l l' IH | e j l l' IH 
                   | e j f l l' H IH ] using eps0_fseq_dep_rect; intros n.
    + rewrite !eps0_fseq_fix_0 with (l' := l'); auto.
    + rewrite !eps0_fseq_fix_1; auto.
    + rewrite !eps0_fseq_fix_2; auto.
    + rewrite !eps0_fseq_fix_3 with (l' := l); auto.
    + rewrite !eps0_fseq_fix_4 with (l' := l); auto.
    + rewrite !eps0_fseq_fix_5 with (l' := l); auto.
  Qed.

  Fact eps0_fseq_mono e (l : eps0_is_limit e) : ∀ n m, n < m → eps0_fseq l n <ε₀ eps0_fseq l m.
  Proof.
    induction l as [ e j l l' | e | e j | e l l' IH | e j l l' IH 
                   | e j f l l' H IH ] using eps0_fseq_dep_rect.
    + intros; rewrite !eps0_fseq_fix_0 with (l' := l'); auto.
      now apply eps0_exp_mono_right, ord_fseq_mono.
    + intros; rewrite !eps0_fseq_fix_1.
      now apply eps0_exp_mono_right, ord_mseq_mono.
    + intros; rewrite !eps0_fseq_fix_2.
      now apply eps0_add_mono_right, eps0_exp_mono_right, ord_mseq_mono.
    + intros; rewrite !eps0_fseq_fix_3 with (l' := l).
      now apply eps0_exp_mono_left, IH.
    + intros; rewrite !eps0_fseq_fix_4 with (l' := l).
      now apply eps0_add_mono_right, eps0_exp_mono_left, IH.
    + intros; rewrite !eps0_fseq_fix_5 with (l' := l); auto.
      now apply eps0_add_mono_right, IH.
  Qed.

  Local Fact eps0_zero_lt_one : 0₀ <ε₀ 1₀.
  Proof. rewrite <- eps0_succ_zero_is_one; apply eps0_zero_lt_succ. Qed.

  Hint Resolve eps0_lt_zero_exp eps0_add_below_exp eps0_exp_mono_right eps0_exp_mono_left 
               eps0_lt_trans eps0_exp_mono_le_lt eps0_exp_mono eps0_le_refl
               eps0_add_mono_le_lt eps0_lt_le_weak 
               eps0_add_incr_right
               eps0_add_incr eps0_zero_lt_one 
               eps0_omega_mono_lt : core.

  Local Fact eps0_lt_add1 e : e <ε₀ e +₀ 1₀.
  Proof. rewrite <- (eps0_add_zero_right e) at 1; auto. Qed.

  Hint Resolve eps0_lt_add1 ord_lt_succ : core.

  Fact eps0_lt_add1_inv e f : e <ε₀ f +₀ 1₀ → e ≤ε₀ f.
  Proof. rewrite eps0_add_one_right; apply eps0_succ_next_inv. Qed.

  Fact eps0_fseq_lt e l n : @eps0_fseq e l n <ε₀ e.
  Proof.
    revert n.
    induction l as [ e j l l' | e | e j | e l l' IH | e j l l' IH 
                   | e j g l l' H IH ] using eps0_fseq_dep_rect; intros n.
    + generalize (ord_fseq_lt _ l' n).
      rewrite eps0_fseq_fix_0 with (l' := l'); auto.
    + rewrite eps0_fseq_fix_1; apply eps0_exp_mono_left; auto.
    + rewrite eps0_fseq_fix_2; apply eps0_add_below_exp; auto.
      apply eps0_exp_mono_left; auto.
    + rewrite eps0_fseq_fix_3 with (l' := l); auto.
    + rewrite eps0_fseq_fix_4 with (l' := l).
      apply eps0_add_below_exp; auto.
    + rewrite eps0_fseq_fix_5 with (l' := l); auto.
  Qed.

  Fact eps0_fseq_limit e (l : eps0_is_limit e) f : f <ε₀ e → ∃n, f <ε₀ eps0_fseq l n.
  Proof.
    induction l as [ e j l l' | e | e j | e l l' IH | e j l l' IH 
                   | e j g l l' H IH ] in f |- * using eps0_fseq_dep_rect.
    + intros [ [-> | (i & b & -> & H1 & H2) ] | (g & i & H1 & H2) ]%eps0_below_exp_inv.
      * exists 0; rewrite eps0_fseq_fix_0 with (l' := l'); auto.
      * destruct (ord_fseq_limit _ l' _ H1) as (n & Hn).
        exists n; rewrite eps0_fseq_fix_0 with (l' := l'); auto.
      * exists 0; rewrite eps0_fseq_fix_0 with (l' := l'); eauto.
    + intros [ -> | (g & i & H1 & H2%eps0_lt_add1_inv) ]%eps0_below_omega_inv.
      * exists 0; rewrite eps0_fseq_fix_1; auto.
      * destruct (ord_mseq_limit i) as (n & Hn).
        exists n; rewrite eps0_fseq_fix_1; eauto.
    + intros [ [-> | (i & b & -> & H1%ord_lt_succ__le_iff & H2) ] | (g & i & H1 & H2) ]%eps0_below_exp_inv.
      * exists 0; rewrite eps0_fseq_fix_2; auto.
      * apply eps0_below_omega_inv in H2 as [ -> | (f & k & H3 & H4%eps0_lt_add1_inv) ].
        - exists 0; rewrite eps0_fseq_fix_2; auto.
        - destruct (ord_mseq_limit k) as (n & Hn).
          exists n; rewrite eps0_fseq_fix_2; eauto.
      * exists 0; rewrite eps0_fseq_fix_2; eauto.
    + intros [ -> | (g & i & H1 & H2) ]%eps0_below_omega_inv.
      * exists 0; rewrite eps0_fseq_fix_3 with (l' := l); auto.
      * destruct (IH _ H2) as (n & Hn).
        exists n; rewrite eps0_fseq_fix_3 with (l' := l).
        apply eps0_lt_trans with (1 := H1), eps0_exp_mono_left; auto.
    + intros [ [-> | (i & b & -> & H1%ord_lt_succ__le_iff & H2) ] | (g & i & H1 & H2) ]%eps0_below_exp_inv.
      * exists 0; rewrite eps0_fseq_fix_4 with (l' := l); auto.
      * apply eps0_below_omega_inv in H2 as [ -> | (f & k & H3 & H4) ].
        - exists 0; rewrite eps0_fseq_fix_4 with (l' := l); auto.
        - destruct (IH _ H4) as (n & Hn).
          exists n; rewrite eps0_fseq_fix_4 with (l' := l); auto.
          apply eps0_add_mono_le_lt; auto.
          now apply eps0_lt_trans with (1 := H3), eps0_exp_mono_left.
      * destruct (IH _ H2) as (n & Hn).
        exists n; rewrite eps0_fseq_fix_4 with (l' := l); auto.
        apply eps0_lt_le_trans with (1 := H1).
        rewrite <- (eps0_add_zero_right ω^⟨_,_⟩) at 1; auto.
    + intros [ H1 | (h & -> & H1) ]%eps0_lt_add_inv_add.
      * exists 0; rewrite eps0_fseq_fix_5 with (l' := l); auto.
        apply eps0_lt_le_trans with (1 := H1); auto.
      * destruct (IH _ H1) as (n & Hn).
        exists n; rewrite eps0_fseq_fix_5 with (l' := l); auto.
  Qed.

  Hint Resolve eps0_le_refl eps0_lt_le_weak : core.

  Fact eps0_max u v b : u <ε₀ b → v <ε₀ b → { w | u ≤ε₀ w ∧ v ≤ε₀ w ∧ w <ε₀ b }.
  Proof. intros ? ?; destruct (eps0_le_lt_dec u v); eauto. Qed.
  
  Hint Resolve eps0_is_succ_exp_zero : core.

  Local Fact eps0_not_zero_lt e : e ≠ 0₀ → 0₀ <ε₀ e.
  Proof. intros; destruct (eps0_zero_or_pos e); now auto. Qed.
  
  Local Fact eps0_zero_lt_succ e : 0₀ <ε₀ e +₀ 1₀.
  Proof. rewrite eps0_add_one_right; apply eps0_zero_lt_succ. Qed.

  Hint Resolve eps0_not_zero_lt eps0_zero_lt_succ : core.
  
  Hint Resolve eps0_add_incr_left 
     eps0_add_incr_right 
     eps0_lt_succ 
     eps0_add_is_limit eps0_is_limit_omega
     eps0_add_mono eps0_add_mono_right : core.

  (** Notice that there are examples where fseq (a+e) n < a + fseq e n
      for instance a = ω³+ω and e = ω²

      a+e = ω³+ω+ω² = ω³+ω²
      fseq e n = fseq ω² n = ω.(n+1)
      fseq (a+e) n = fseq (ω³+ω²) n = ω³+ω.(n+1)
      a+(fseq e n) = ω³+ω+ω.(n+1) = ω³+ω.(n+2)
      and hence fseq (a+e) n < fseq (a+e) n + ω = a+(fseq e n) *)
 
 (*     
  Fact eps0_is_limit_hnf_special e n f :
         f <ε₀ ω^e
         → eps0_is_limit (ω^⟨e,n⟩ +₀ f)
           ↔ e ≠ 0₀ ∧ eps0_is_limit f ∨ f = 0₀ ∧ (((∃g, e = g +₀ 1₀) \/ eps0_is_limit e) ∨ e = 0₀ ∧ ord_is_limit n).
  Proof.
    intros Hf.
    rewrite  eps0_is_limit_hnf; auto.
    apply or_iff_compat_l, and_iff_compat_l, or_iff_compat_r.
    split.
    + intro; destruct (eps0_zero_succ_limit_dec e) as [ [ -> | [] ] | ]; now eauto.
    + intros [ (g & ->) | H ].
      * intros [ _ H ]%eps0_add_eq_zero.
        generalize eps0_zero_lt_one; rewrite H; apply eps0_lt_irrefl.
      * apply (proj1 H).
  Qed.
  
  *)
  
  Theorem eps0_fseq_add a e (le : eps0_is_limit e) (lae : eps0_is_limit (a+₀e)) :
     ∀n, eps0_fseq lae n ≤ε₀ a +₀ eps0_fseq le n.
  Proof.
    revert e le lae.
    induction a as [ | b i c Hc _ IH ] using eps0_hnf_rect.
    + intro e; rewrite (eps0_add_zero_left e).
      intros; rewrite eps0_add_zero_left; auto.
      apply eps0_le_iff_lt.
      right; apply eps0_fseq_pirr.
    + intros e le.
      destruct le as
        [ e j l l' | e | e j | e l l' _ | e j l l' _ | e j g l l' H _ ]
        using eps0_fseq_dep_rect.
      * destruct (eps0_lt_sdec b e) as [ b e Hbe | e | b e Hbe ].
        - rewrite eps0_add_hnf_exp_lt; auto.
          intros lae m.
          rewrite !eps0_fseq_fix_0 with (l' := l'), eps0_add_hnf_exp_lt; auto.
        - rewrite eps0_add_hnf_exp_eq; auto.
          intros lae m.
          assert (ord_is_limit (i +ₒ 1 +ₒ j)) as l'' by now apply ord_is_limit_add_succ.
          rewrite !eps0_fseq_fix_0 with (l' := l'), eps0_add_hnf_exp_eq; auto.
          rewrite !eps0_fseq_fix_0 with (l' := l'').
          apply eps0_exp_mono; auto.
          apply ord_fseq_add.
        - rewrite eps0_add_assoc.
          intros lae m.
          rewrite eps0_add_assoc.
          assert (l'' : eps0_is_limit (c +₀ ω^⟨e,j⟩)).
          1: apply eps0_hnf_is_limit in lae as [ | (? & _) ]; auto.
          rewrite eps0_fseq_fix_5 with (l' := l''); auto.
          apply eps0_add_below_omega; auto.
          apply eps0_exp_mono_left; auto.
      * destruct (eps0_lt_eq_gt_dec b (e +₀ 1₀)) as [ [ Hbe | -> ] | Hbe ].
        - rewrite eps0_add_hnf_omega_lt; auto.
          intros; rewrite !eps0_fseq_fix_1; auto.
        - rewrite eps0_add_hnf_omega_eq; auto.
          intros lae m.
          rewrite eps0_fseq_fix_1, eps0_fseq_fix_2; auto.
        - rewrite eps0_add_assoc.
          intros lae m.
          rewrite eps0_add_assoc.
          assert (l'' : eps0_is_limit (c +₀ ω^(e +₀ 1₀))).
          1: apply eps0_hnf_is_limit in lae as [ | (? & _) ]; auto.
          rewrite !eps0_fseq_fix_5 with (l' := l''); auto.
          apply eps0_add_below_omega; auto.
      * destruct (eps0_lt_eq_gt_dec b (e +₀ 1₀)) as [ [ Hbe | -> ] | Hbe ].
        - rewrite eps0_add_hnf_exp_lt; auto.
          intros; rewrite !eps0_fseq_fix_2; auto.
        - rewrite eps0_add_hnf_exp_eq; auto.
          intros lae m.
          rewrite eps0_fseq_fix_2, eps0_add_hnf_eq; auto. 
          2: apply eps0_exp_mono_left; auto.
          revert lae; rewrite <- ord_add_assoc; intros lae.
          rewrite eps0_fseq_fix_2; auto.
        - rewrite eps0_add_assoc.
          intros lae m.
          rewrite eps0_add_assoc.
          assert (l'' : eps0_is_limit (c +₀ ω^⟨e +₀ 1₀,j +ₒ 1ₒ⟩)).
          1: apply eps0_hnf_is_limit in lae as [ | (? & _) ]; auto.
          rewrite !eps0_fseq_fix_5 with (l' := l''); auto.
          apply eps0_add_below_omega; auto.
          apply eps0_exp_mono_left; auto.
      * destruct (eps0_lt_sdec b e) as [ b e Hbe | e | b e Hbe ].
        - rewrite eps0_add_hnf_omega_lt; auto.
          intros.
          rewrite !eps0_fseq_fix_3 with (l' := l); auto.
        - rewrite eps0_add_hnf_omega_eq; auto.
          intros lae m.
          rewrite eps0_fseq_fix_3 with (l' := l),
                  eps0_fseq_fix_4 with (l' := l); auto.
        - rewrite eps0_add_assoc.
          intros lae m.
          rewrite eps0_add_assoc.
          assert (l'' : eps0_is_limit (c +₀ ω^e)).
          1: apply eps0_hnf_is_limit in lae as [ | (? & _) ]; auto.
          rewrite !eps0_fseq_fix_5 with (l' := l''); auto.
          apply eps0_add_below_omega; auto.
      * destruct (eps0_lt_sdec b e) as [ b e Hbe | e | b e Hbe ].
        - rewrite eps0_add_hnf_exp_lt; auto.
          intros; rewrite !eps0_fseq_fix_4 with (l' := l); auto.
        - rewrite eps0_add_hnf_exp_eq; auto.
          rewrite <- ord_add_assoc; intros lae m.
          rewrite !eps0_fseq_fix_4 with (l' := l).
          rewrite eps0_add_hnf_eq; auto.
          apply eps0_omega_mono_lt, eps0_fseq_lt.
        - rewrite eps0_add_assoc.
          intros lae m.
          rewrite eps0_add_assoc.
          assert (l'' : eps0_is_limit (c +₀ ω^⟨e,j +ₒ 1ₒ⟩)).
          1: apply eps0_hnf_is_limit in lae as [ | (? & _) ]; auto.
          rewrite !eps0_fseq_fix_5 with (l' := l''); auto.
          apply eps0_add_below_omega; auto.
          apply eps0_exp_mono_left; auto.
      * destruct (eps0_lt_sdec b e) as [ b e Hbe | e | b e Hbe ].
        - rewrite eps0_add_hnf_lt; auto.
          intros; rewrite !eps0_fseq_fix_5 with (l' := l); auto.
        - rewrite eps0_add_hnf_eq; auto.
          intros.
          rewrite !eps0_fseq_fix_5 with (l' := l); auto.
          rewrite eps0_add_hnf_eq; auto.
          apply eps0_lt_trans with (2 := H), eps0_fseq_lt.
        - rewrite eps0_add_assoc.
          intros lae m.
          rewrite !eps0_fseq_fix_5 with (l' := l); auto.
          assert (l'' : eps0_is_limit (c +₀ (ω^⟨e,j⟩ +₀ g))).
          1: apply eps0_hnf_is_limit in lae as [ | (? & _) ]; auto.
          rewrite !eps0_fseq_fix_5 with (l' := l''), eps0_add_assoc; auto.
          ++ apply eps0_add_mono; auto.
             apply eps0_le_trans with (1 := IH _ l' _ _).
             apply eps0_add_mono; auto.
             rewrite eps0_fseq_fix_5 with (l':= l); auto.
          ++ repeat (apply eps0_add_below_omega; auto).
             ** now apply eps0_exp_mono_left.
             ** apply eps0_lt_trans with (1 := H); auto.
  Qed.

  Hint Resolve eps0_zero_lt_succ eps0_is_limit_pos : core.
  
  Fact eps0_mult_omega_limit a e :
      eps0_is_limit e
    → eps0_is_limit (ω^a *₀ e).
  Proof.
    induction 1 as [ | | e j f l l' H ] using eps0_limit_dep_rect.
    + rewrite eps0_mult_omega_exp, eps0_add_zero_right, eps0_is_limit_exp_iff.
      destruct (eps0_eq_dec a 0₀); auto.
    + rewrite eps0_mult_omega_exp, eps0_is_limit_exp_iff.
      left; now intros (? & ->)%eps0_add_eq_zero.
    + rewrite eps0_mult_omega_hnf; auto.
      destruct (eps0_zero_or_pos e) as [ -> | ]; auto.
      rewrite eps0_omega_zero in H.
      apply eps0_lt_one in H as ->.
      now destruct l as [ [] ].
  Qed.
  
  (*
  
  (** We start with fseq (ω^a * e) *)
  Lemma eps0_fseq_mult_omega a e (le : eps0_is_limit e) (lae : eps0_is_limit (ω^a*₀e)) :
     ∀n, eps0_fseq lae n ≤ε₀ ω^a *₀ eps0_fseq le n.
  Proof.
    revert lae.
    induction le as
      [ e j l l' | e | e j | e l l' IH | e j l l' IH | e j g l l' H IH ]
      using eps0_fseq_dep_rect.
    + rewrite eps0_mult_omega_exp.
      intros.
      rewrite !eps0_fseq_fix_0 with (l' := l').
      rewrite eps0_mult_omega_exp; auto.
    + rewrite eps0_mult_omega.
      rewrite <- eps0_add_assoc.
      intros.
      rewrite !eps0_fseq_fix_1, eps0_mult_omega_exp; auto.
    + rewrite eps0_mult_omega_exp.
      rewrite <- eps0_add_assoc.
      intros.
      rewrite !eps0_fseq_fix_2, eps0_mult_distr,
              !eps0_mult_omega_exp, eps0_add_assoc; auto.
    + rewrite eps0_mult_omega.
      intros.
      assert (l'' : eps0_is_limit (a +₀ e)) by now apply eps0_add_is_limit.
      rewrite eps0_fseq_fix_3 with (l' := l),
              eps0_fseq_fix_3 with (l' := l''); auto.
      rewrite eps0_mult_omega.
      apply eps0_omega_mono_le, eps0_fseq_add.
    + rewrite eps0_mult_omega_exp.
      intros.
      assert (l'' : eps0_is_limit (a +₀ e)) by now apply eps0_add_is_limit.
      rewrite eps0_fseq_fix_4 with (l' := l),
              eps0_fseq_fix_4 with (l' := l''); auto.
      rewrite eps0_mult_distr, eps0_mult_omega_exp, eps0_mult_omega.
      apply eps0_add_mono; auto.
      apply eps0_omega_mono_le, eps0_fseq_add.
    + destruct (eps0_zero_or_pos e) as [ -> | He ].
      1:{ rewrite eps0_omega_zero in H.
          apply eps0_lt_one in H.
          destruct (proj1 l H). }
      rewrite eps0_mult_omega_hnf; auto.
      intros.
      assert (l'' : eps0_is_limit (ω^a *₀ g)) by now apply eps0_mult_omega_limit.
      rewrite eps0_fseq_fix_5 with (l' := l''),
              eps0_fseq_fix_5 with (l' := l); auto.
      * rewrite eps0_mult_distr, eps0_mult_omega_exp; auto.
      * rewrite <- eps0_mult_omega; auto.
        apply eps0_mult_mono_right; auto.
  Qed.
  
  *)
  
  Fact eps0_mult_exp_is_limit a e n :
    0₀ <ε₀ a → 0₀ <ε₀ e → eps0_is_limit (a *₀ ω^⟨e,n⟩).
  Proof.
    intros Ha He.
    destruct a as [ | b i c H1 H2 ] using eps0_hnf_rect.
    + contradict Ha; apply eps0_lt_irrefl.
    + rewrite eps0_mult_hnf_exp; auto.
      apply eps0_is_limit_exp_iff; left.
      intros (-> & ->)%eps0_add_eq_zero.
      revert He; apply eps0_lt_irrefl.
  Qed.

  (* Of course, if a is 0 then a*e = 0 is not a limit ordinal
     is the sense we use for the fundemental sequence *)
  Fact eps0_mult_is_limit a e :
    0₀ <ε₀ a → eps0_is_limit e → eps0_is_limit (a *₀ e).
  Proof.
    intros Ha.
    induction e as [ | | e n f He Hf IHe IHf ] using eps0_hnf_pos_rect.
    + now rewrite eps0_mult_zero_right.
    + intros [ [] | (_ & l) ]%eps0_is_limit_exp_iff; auto.
      rewrite eps0_mult_1add_right.
      destruct (eps0_m1add_is_limit a l) as [ -> | ]; auto.
      now apply eps0_lt_irrefl in Ha.
    + intros [ (-> & H) | H ]%eps0_add_is_limit_inv.
      * rewrite eps0_add_zero_right; apply eps0_mult_exp_is_limit; auto.
      * rewrite eps0_mult_distr; apply eps0_add_is_limit; auto.
  Qed.

  Fact eps0_mult_limit_limit a i b n :
      b <ε₀ ω^a
    → ord_is_limit n
    → (ω^⟨a,i⟩ +₀ b) *₀ ω^⟨0₀,n⟩ = ω^⟨a,i +ₒ (1ₒ +ₒ i) *ₒ n⟩.
  Proof.
    intros Hb Hn.
    rewrite <- eps0_m1add_eq, eps0_m1add_fix_2; auto.
  Qed.
  
  Fact eps0_mult_hnf_ord_le a i b n :
      b <ε₀ ω^a
    → ω^⟨a,i +ₒ (1ₒ +ₒ i) *ₒ n⟩ ≤ε₀ (ω^⟨a,i⟩ +₀ b) *₀ ω^⟨0₀,n⟩ .
  Proof.
    intros Hb.
    rewrite <- eps0_m1add_eq.
    destruct (ord_zero_succ_limit_dec n) as [ [ -> | (k & ->) ] | Hn ].
    + rewrite eps0_m1add_fix_1; auto.
      apply ord_is_succ_10.
    + rewrite eps0_m1add_fix_1; auto.
      apply ord_is_succ_1add; auto.
    + rewrite eps0_m1add_fix_2; auto.
  Qed.
  
  Hint Resolve ord_add_incr_right ord_add_incr_left : core.
  
  Fact ord_mult_le_special i j : j ≤ₒ i +ₒ (1ₒ +ₒ i) *ₒ j.
  Proof.
    apply ord_le_trans with (i +ₒ j); auto.
    apply ord_add_mono_le; auto.
    rewrite <- (ord_mul_one_left j) at 1.
    apply ord_mul_mono; auto.
  Qed.
 
  Hint Resolve ord_mult_le_special eps0_fseq_gt_zero : core.
  
  Theorem eps0_fseq_mult a e (le : eps0_is_limit e) (lae : eps0_is_limit (a*₀e)) :
     ∀n, eps0_fseq lae n ≤ε₀ a *₀ eps0_fseq le n.
  Proof.
    destruct a as [ | a i b Hb _ _ ] using eps0_hnf_rect.
    + exfalso.
      rewrite eps0_mult_zero_left in lae.
      now apply (proj1 lae).
    + revert lae.
      induction le as 
        [ e j l l' | e | e j | e l l' IH | e j l l' IH | e j g l l' H IH ]
        using eps0_fseq_dep_rect.
      * intros lae n; rewrite eps0_fseq_fix_0 with (l' := l'); revert lae.
        destruct (eps0_zero_or_pos e) as [ -> | He ].
        - rewrite eps0_mult_limit_limit; auto.
          intros lae.
          assert (l1 : ord_is_limit ((1ₒ +ₒ i) *ₒ j)).
          1:{ apply ord_mul_is_limit_right; auto. }
          assert (l2 : ord_is_limit (i +ₒ (1ₒ +ₒ i) *ₒ j)).
          1:{ apply ord_is_limit_add; auto. }
          rewrite eps0_fseq_fix_0 with (l' := l2).
          apply eps0_le_trans with (2 := eps0_mult_hnf_ord_le _ _ _ _ Hb).
          apply eps0_exp_mono; auto.
          apply ord_le_trans with (1 := ord_fseq_add _ _ l1 _ _).
          apply ord_add_mono_le; auto.
          apply ord_fseq_mul.
        - rewrite !eps0_mult_hnf_exp; auto.
          intros lae.
          rewrite eps0_fseq_fix_0 with (l' := l'); auto.
      * rewrite eps0_mult_hnf_omega, <- eps0_add_assoc; auto.
        intros lae n.
        rewrite !eps0_fseq_fix_1.
        destruct (eps0_zero_or_pos e) as [ -> | He ].
        - rewrite eps0_add_zero_right.
          apply eps0_le_trans with (2 := eps0_mult_hnf_ord_le _ _ _ _ Hb); auto.
        - rewrite eps0_mult_hnf_exp; auto.
      * rewrite eps0_mult_hnf_exp, <- eps0_add_assoc; auto.
        intros lae n.
        rewrite !eps0_fseq_fix_2, eps0_mult_distr,
                 eps0_mult_hnf_exp, <- eps0_add_assoc; auto.
        apply eps0_add_mono; auto.
        destruct (eps0_zero_or_pos e) as [ -> | He ].
        - rewrite eps0_add_zero_right.
          apply eps0_le_trans with (2 := eps0_mult_hnf_ord_le _ _ _ _ Hb); auto.
        - rewrite eps0_mult_hnf_exp; auto.
      * destruct (eps0_zero_or_pos e) as [ -> | He ].
        1: now destruct l as [ [] ].
        rewrite eps0_mult_hnf_omega; auto.
        intros lae n.
        assert (l1: eps0_is_limit (a +₀ e))
          by now apply eps0_add_is_limit.
        rewrite eps0_fseq_fix_3 with (l' := l),
                eps0_fseq_fix_3 with (l' := l1).
        rewrite eps0_mult_hnf_omega; auto.
        apply eps0_omega_mono_le, eps0_fseq_add.
      * destruct (eps0_zero_or_pos e) as [ -> | He ].
        1: now destruct l as [ [] ].
        rewrite eps0_mult_hnf_exp; auto.
        intros lae n.
        assert (l1: eps0_is_limit (a +₀ e))
          by now apply eps0_add_is_limit.
        rewrite eps0_fseq_fix_4 with (l' := l),
                eps0_fseq_fix_4 with (l' := l1).
        rewrite eps0_mult_distr, eps0_mult_hnf_omega, eps0_mult_hnf_exp; auto.
        apply eps0_add_mono, eps0_omega_mono_le, eps0_fseq_add; auto.
      * destruct (eps0_zero_or_pos e) as [ -> | He ].
        1:{ exfalso; rewrite eps0_omega_zero in H.
            apply eps0_lt_one in H as ->.
            now destruct l as [ [] ]. }
        rewrite eps0_mult_hnf; auto.
        intros lae n.
        assert (l1: eps0_is_limit ((ω^⟨a,i⟩ +₀ b) *₀ g)).
        1:{ apply eps0_add_is_limit_iff in lae as [ [C _] | ]; auto.
            apply eps0_mult_zero_inv in C as [ C | -> ].
            - destruct (eps0_lt_irrefl 0₀).
              rewrite <- C at 2; auto.
            - now destruct l as [ [] ]. }
        apply eps0_le_trans with (1 := eps0_fseq_add _ l1 _ _).
        rewrite eps0_fseq_fix_5 with (l' := l); auto.
        rewrite eps0_mult_hnf; auto.
        now apply eps0_lt_trans with (1 := eps0_fseq_lt _ _).
  Qed.

End eps0_fseq.

Check eps0_fseq.
Check eps0_fseq_pirr.
Check eps0_fseq_mono.
Check eps0_fseq_gt_zero.
Check eps0_fseq_lt.
Check eps0_fseq_limit.
Check eps0_fseq_add.
Check eps0_fseq_mult.


