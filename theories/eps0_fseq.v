(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils pos eps0 eps0_least_split.

Set Implicit Arguments.

#[local] Notation π₁ := proj1_sig.
#[local] Notation π₂ := proj2_sig.

Section eps0_tail_rect.

  (** Induction principle corresponding to the following building rules 
      for ordinals below ε₀:

                    e      g  e  e≠0₀  eps0_least_split g e
        ------   ------   ----------------------------------
          0₀      S₀ e             g +₀ ω^e
   *)

  Variables (P : ε₀ → Type)
            (HP0 : P 0₀)
            (HP1 : ∀ e, P e → P (S₀ e))
            (HP2 : ∀ g e, e ≠ 0₀ → eps0_least_split g e → P g → P e → P (g +₀ ω^e)).

  Theorem eps0_tail_rect e : P e.
  Proof.
    induction e as [ | e f H IH ] using eps0_least_split_rect; auto.
    destruct (eps0_zero_or_pos f) as [ -> | Hf ].
    + rewrite eps0_omega_zero, eps0_add_one_right; auto.
    + apply HP2; auto.
      intros ->; now apply eps0_lt_irrefl in Hf.
  Qed.

End eps0_tail_rect.

Corollary eps0_least_split_find e : eps0_is_limit e → { a : _ & { g | e = a+₀ω^g ∧ g ≠ 0₀ ∧ eps0_least_split a g } }.
Proof.
  destruct e as [ | | a g ] using eps0_tail_rect.
  + now intros [ [] _ ].
  + intros [ _ [] ]; auto.
  + exists a, g; auto.
Qed.

Section eps0_discriminate.

  Variables (P : ε₀ → Type)
            (HP0 : P 0₀)
            (HP1 : ∀ e, P (S₀ e))
            (HP2 : ∀ e, eps0_is_limit e → P e).

  Hint Resolve eps0_is_limit_add_omega : core.
            
  Theorem eps0_discriminate e : P e.
  Proof. destruct e using eps0_tail_rect; auto. Qed.

End eps0_discriminate.

(** Tailored induction principle for computing the fundemental sequence *)

Section eps0_fseq_rect.

  Variables (P : forall e, eps0_is_limit e → Type)
            (HP0 : ∀ g e l, eps0_least_split g (S₀ e) → @P (g +₀ ω^(S₀ e)) l)
            (HP1 : ∀ g e l l', eps0_least_split g e → @P e l → @P (g +₀ ω^e) l').

  Hint Resolve eps0_is_limit_add_omega : core.

  Theorem eps0_fseq_rect e (l : eps0_is_limit e) : P l.
  Proof.
    revert l.
    destruct e as [ | e | g e H1 H2 _ _ ]
      using eps0_tail_rect.
    + now intros [ [] _ ].
    + intros [ _ [] ]; eauto.
    + induction e as [ | e | h e H3 H4 _ IH ]
        in H1, g, H2 |- *
        using eps0_tail_rect; intros l.
      * now destruct H1.
      * now apply HP0.
      * assert (eps0_is_limit (h+₀ ω^(e))) as l' by auto.
        apply HP1 with l'; auto.
  Qed.

End eps0_fseq_rect.

(** We build the fundemental sequence *)

Inductive eps0_fseq_gr : ε₀ → (nat → ε₀) → Prop :=
  | eps0_fseq_gr_0 g b   : eps0_least_split g (S₀ b)
                         → eps0_fseq_gr (g +₀ ω^(S₀ b)) (λ n, g +₀ ω^⟨b,n⟩)
  | eps0_fseq_gr_1 g b r : eps0_is_limit b
                         → eps0_least_split g b
                         → eps0_fseq_gr b r
                         → eps0_fseq_gr (g +₀ ω^b) (λ n, g +₀ ω^(r n)).

Local Lemma eps0_fseq_gr_fun_rec e se f sf :
  eps0_fseq_gr e se → eps0_fseq_gr f sf → e = f → ∀n, se n = sf n.
Proof.
  intros H; revert H f sf.
  induction 1 as [ g b Hs | g b r H0 Hs H1 IH1 ].
  + induction 1 as [ g' b' Hs' | g' b' r' H0' Hs' H2 IH2 ].
    * intros (<- & <-%eps0_succ_inj)%eps0_split_least_uniq; auto.
    * intros <-%eps0_add_omega_fun_right; eauto.
      destruct H0' as (_ & []); eauto.
  + induction 1 as [ g' b' Hs' | g' b' r' H0' Hs' H2 IH2 ].
    * intros ->%eps0_add_omega_fun_right; eauto.
      destruct H0 as (_ & []); eauto.
    * intros (<- & <-)%eps0_split_least_uniq; auto.
      intro; now rewrite IH1 with (1 := H2).
Qed.

Lemma eps0_fseq_gr_fun e r r' : eps0_fseq_gr e r → eps0_fseq_gr e r' → ∀n, r n = r' n.
Proof. intros H1 H2; now apply (eps0_fseq_gr_fun_rec H1 H2). Qed.

(** By WF induction, we build the fundemental sequence of a limit
    ordinal, packed with conformity (pwc) as spec'd with eps0_fseq_gr *)
Theorem eps0_fseq_pwc e : eps0_is_limit e → sig (eps0_fseq_gr e).
Proof.
  induction 1 as [ g e l H | g e l l' H (lam & Hlam) ] using eps0_fseq_rect.
  + exists (λ n, g +₀ ω^⟨e,n⟩); now constructor.
  + exists (λ n, g +₀ ω^(lam n)); constructor; auto.
Qed.

Definition eps0_fseq {e} (l : eps0_is_limit e) := π₁ (@eps0_fseq_pwc e l).

Fact eps0_fseq_spec e l : eps0_fseq_gr e (@eps0_fseq e l).
Proof. apply (proj2_sig _). Qed.

Fact eps0_fseq_pirr e (l l' : eps0_is_limit e) n :
    eps0_fseq l n = eps0_fseq l' n.
Proof. revert n; apply eps0_fseq_gr_fun with e; apply eps0_fseq_spec. Qed.

Fact eps0_fseq_fix_0 g e (l : eps0_is_limit (g +₀ ω^(S₀ e))) n :
    eps0_least_split g (S₀ e)
  → eps0_fseq l n = g +₀ ω^⟨e,n⟩.
Proof.
  intro.
  revert n; apply eps0_fseq_gr_fun with (1 := eps0_fseq_spec _).
  constructor; auto.
Qed.

Fact eps0_fseq_fix_1 g e (l : eps0_is_limit (g +₀ ω^e))
                         (l' : eps0_is_limit e) n :
    eps0_least_split g e
  → eps0_fseq l n = g +₀ ω^(eps0_fseq l' n).
Proof.
  intros H.
  revert n; apply eps0_fseq_gr_fun with (1 := eps0_fseq_spec _).
  constructor; auto.
  apply eps0_fseq_spec.
Qed.

#[local] Hint Resolve
     eps0_least_split_zero 
     eps0_least_split_exp_S
     eps0_least_split_add_exp_S : core.

Fact eps0_fseq_omega_succ e (l : eps0_is_limit ω^(S₀ e)) n :
    eps0_fseq l n = ω^⟨e,n⟩.
Proof.
  revert l; rewrite <- (eps0_add_zero_left ω^_); intros l.
  rewrite eps0_fseq_fix_0; auto.
  now rewrite eps0_add_zero_left.
Qed.

Fact eps0_fseq_omega_is_limit e (l : eps0_is_limit ω^e) (l' : eps0_is_limit e) n :
    eps0_fseq l n = ω^(eps0_fseq l' n).
Proof.
  revert l; rewrite <- (eps0_add_zero_left ω^_); intros l.
  rewrite eps0_fseq_fix_1 with (l' := l'); auto.
  now rewrite eps0_add_zero_left.
Qed.

Fact eps0_head_least_split e g i f :
    g <ε₀ ω^e
  → ω^f <ε₀ ω^e
  → eps0_least_split g f
  → eps0_least_split (ω^⟨e,i⟩ +₀ g) f.
Proof.
  intros H1 H2 H3 b Hb.
  destruct (eps0_le_lt_dec (ω^⟨e,i⟩ +₀ g) b) as [ | C ]; auto.
  apply eps0_lt_add_inv_add in C as [ C | (k & -> & C) ].
  - assert (b +₀ eps0_omega f <ε₀ ω^⟨e,i⟩) as D.
    1:{ apply eps0_add_below_exp_S; auto. }
    rewrite <- Hb, eps0_add_assoc in D.
    now apply eps0_incr_not_lt in D.
  - rewrite !eps0_add_assoc in Hb.
    apply eps0_add_cancel, H3 in Hb.
    destruct (@eps0_lt_irrefl k).
    now apply eps0_lt_le_trans with (1 := C). 
Qed.

Fact eps0_exp_S_least_split e n : eps0_least_split ω^⟨e,n⟩ e.
Proof.
  intros b; rewrite eps0_add_exp_S_omega; intros Hb.
  destruct (eps0_le_lt_dec ω^⟨e,n⟩ b) as [ | C ]; auto.
  apply eps0_lt_exp_S_inv in C
    as [ [ -> | (i & c & -> & H1 & H2) ] | (f & i & H1 & H2) ].
  + rewrite eps0_add_zero_left in Hb.
    now apply eps0_exp_S_inj, proj2 in Hb.
  + rewrite eps0_add_assoc, eps0_add_lt_omega, eps0_add_exp_S_omega in Hb; auto.
    apply eps0_exp_S_inj, proj2, pos_succ_inj in Hb; lia.
  + rewrite eps0_add_lt_omega in Hb; auto.
    * now apply eps0_exp_S_inj, proj2 in Hb.
    * now apply eps0_lt_trans with (1 := H1),
                eps0_exp_S_mono_left.
Qed.

Fact eps0_fseq_exp_S_succ_one e (l : eps0_is_limit ω^⟨S₀ e,1ₚ⟩) n :
    eps0_fseq l n = ω^⟨e,n⟩.
Proof. apply eps0_fseq_omega_succ. Qed.

Fact eps0_fseq_exp_S_succ_succ e k (l : eps0_is_limit ω^⟨S₀ e,k +ₚ 1ₚ⟩) n :
    eps0_fseq l n = ω^⟨S₀ e,k⟩ +₀ ω^⟨e,n⟩.
Proof.
  revert l; rewrite <- eps0_add_exp_S_omega; intros l.
  rewrite eps0_fseq_fix_0; auto.
Qed.

Fact eps0_fseq_exp_S_one_is_limit e (l : eps0_is_limit ω^⟨e,1ₚ⟩) (l' : eps0_is_limit e) n :
    eps0_fseq l n = ω^(eps0_fseq l' n).
Proof. apply eps0_fseq_omega_is_limit. Qed.

Fact eps0_fseq_exp_S_succ_is_limit e i (l : eps0_is_limit ω^⟨e,i +ₚ 1ₚ⟩) (l' : eps0_is_limit e) n :
    eps0_fseq l n = ω^⟨e,i⟩ +₀ ω^(eps0_fseq l' n).
Proof.
  revert l; rewrite <- eps0_add_exp_S_omega; intros l.
  rewrite eps0_fseq_fix_1 with (l' := l'); auto.
Qed.

(* Another computation for fseq :
     fseq (ω^e.i +₀ f) n = ω^e.i + fseq f n
   when f < ω^e *)
Lemma eps0_fseq_head e i f (l : eps0_is_limit (ω^⟨e,i⟩ +₀ f)) (l' : eps0_is_limit f) n :
    f <ε₀ ω^e → eps0_fseq l n = ω^⟨e,i⟩ +₀ eps0_fseq l' n.
Proof.
  intros Hf; revert l.
  induction l' as [ g j h | ] using eps0_fseq_rect; rewrite <- eps0_add_assoc; intros l.
  + rewrite !eps0_fseq_fix_0, eps0_add_assoc; auto.
  + rewrite !eps0_fseq_fix_1 with (l' := l'1), eps0_add_assoc; auto.
Qed.

(** The fundemental sequence is monotonic *)
Fact eps0_fseq_mono e (l : eps0_is_limit e) : ∀ n m, n < m → eps0_fseq l n <ε₀ eps0_fseq l m.
Proof.
  induction l using eps0_fseq_rect; intros n m Hnm.
  + rewrite !eps0_fseq_fix_0; auto.
    apply eps0_add_mono_right, eps0_exp_S_mono_right; auto.
  + rewrite !eps0_fseq_fix_1 with (l' := l1); auto.
    apply eps0_add_mono_right, eps0_omega_mono_lt; auto.
Qed.

#[local] Hint Resolve eps0_le_refl eps0_lt_le_weak : core.

Fact eps0_max u v b : u <ε₀ b → v <ε₀ b → { w | u ≤ε₀ w ∧ v ≤ε₀ w ∧ w <ε₀ b }.
Proof. intros ? ?; destruct (eps0_le_lt_dec u v); eauto. Qed.

  (** Another inversion lemma, but this time
      for the limit of the fundemental sequence

      This is inversion of _ < e when e is a limit ordinal,
      w.r.t. the fundemental sequence of e 

      This has become a nice proof *)
Theorem eps0_lt_fseq_inv e (l : eps0_is_limit e) f : f <ε₀ e → ∃n, f <ε₀ eps0_fseq l n.
Proof.
  (* We capture the fundemental sequence via its inductive spec *)
  revert f; generalize (eps0_fseq l) (eps0_fseq_spec l).
  clear l.
  induction 1 as [ e b Hs | e b r Hr H0 Hs IH ]; intros f H.
  + (* e is _ + ω^{b+1} *)
    apply eps0_lt_add_inv_add in H as [ H | (g & -> & H) ]; auto.
    * exists 0.
      apply eps0_lt_trans with (1 := H).
      apply eps0_add_incr; auto.
    * apply eps0_lt_omega_succ_inv in H as (n & Hn).
      exists n.
      apply eps0_add_mono_right; auto.
  + apply eps0_lt_add_inv_add in H as [ H | (g & -> & H) ]; auto.
    * exists 0.
      apply eps0_lt_trans with (1 := H).
      apply eps0_add_incr, eps0_lt_zero_exp_S.
    * apply eps0_lt_omega_inv in H as [ -> | (a & n & Ha & H) ].
      - exists 0.
        apply eps0_add_mono_right, eps0_lt_zero_exp_S.
      - apply IH in H as (i & Hi).
        exists i.
        apply eps0_add_mono_right.
        apply eps0_lt_trans with (1 := Ha).
        now apply eps0_exp_S_mono_left.
Qed.

(** The fundemental sequence is lesser than its limit *)
Theorem eps0_fseq_lt e (l : eps0_is_limit e) n : eps0_fseq l n <ε₀ e.
Proof.
  generalize (eps0_fseq l) (eps0_fseq_spec l) n; clear n l.
  induction 1 as [ | g b r Hr IH ].
  + intros; apply eps0_add_mono_right; auto.
    apply eps0_exp_S_mono_left, eps0_lt_succ.
  + intros; apply eps0_add_mono_right, eps0_exp_S_mono_left; auto.
Qed.

Fact eps0_mult_exp_S_is_limit a e n :
    0₀ <ε₀ a → 0₀ <ε₀ e → eps0_is_limit (a *₀ ω^⟨e,n⟩).
Proof.
  intros Ha He.
  destruct a as [ | b i c H1 H2 ] using eps0_head_rect.
  + contradict Ha; apply eps0_lt_irrefl.
  + rewrite eps0_mult_head_exp_S; auto.
    apply eps0_is_limit_exp_S.
    intros (-> & ->)%eps0_add_eq_zero.
    revert He; apply eps0_lt_irrefl.
Qed.

(* Of course, if a is 0 then a*e = 0 is not a limit ordinal
   is the sense we use for the fundemental sequence *)
Fact eps0_mult_is_limit a e :
    0₀ <ε₀ a → eps0_is_limit e → eps0_is_limit (a *₀ e).
Proof.
  intros Ha.
  induction e as [ | | e n f He Hf IHe IHf ] using eps0_head_pos_rect.
  + now rewrite eps0_mult_zero_right.
  + intros [H1 H2].
    destruct H2; auto.
  + intros [ (-> & H) | H ]%eps0_add_is_limit_inv.
    * rewrite eps0_add_zero_right; apply eps0_mult_exp_S_is_limit; auto.
    * rewrite eps0_mult_distr.
      apply eps0_add_is_limit; auto.
Qed.

Fact eps0_mult_head_limit a i b e :
      b <ε₀ ω^a
    → eps0_is_limit e
    → (ω^⟨a,i⟩ +₀ b) *₀ e = ω^a *₀ e.
Proof.
  intros Hab.
  induction e as [ | e n f H _ IHf ] using eps0_head_rect.
  + now intros [ [] _ ].
  + intros He.
    unfold eps0_omega.
    assert (e ≠ 0₀) as He'.
    1:{ intros ->.
        rewrite eps0_omega_zero in H.
        apply eps0_lt_one in H as ->.
        rewrite eps0_add_zero_right in He.
        apply (proj2 He); auto. }
    assert (0₀ <ε₀ e) as He''.
    1:{ now destruct (eps0_zero_or_pos e) as [ -> | ]. }
    apply eps0_add_is_limit_inv in He as [ (-> & _) | Hf ].
    * rewrite !eps0_add_zero_right, eps0_mult_head_exp_S, eps0_mult_exp_S; auto.
    * rewrite eps0_mult_head, IHf, eps0_mult_exp_S_head; auto.
Qed.

#[local] Hint Resolve eps0_add_incr_left 
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
Theorem eps0_fseq_add a e (le : eps0_is_limit e) (lae : eps0_is_limit (a+₀e)) :
   ∀n, eps0_fseq lae n ≤ε₀ a +₀ eps0_fseq le n.
Proof.
  revert e le lae.
  induction a as [ | b i c Hc _ IH ] using eps0_head_rect.
  + intro e; rewrite (eps0_add_zero_left e).
    intros; rewrite eps0_add_zero_left; auto.
    right; apply eps0_fseq_pirr.
  + intros e; destruct e as [ | f n g Hg _ _ ] using eps0_head_rect.
    1: intros l; exfalso; now apply (proj1 l).
    intros le.
    destruct (eps0_lt_sdec b f) as [ b f Hbf | f | b f Hbf ].
    * rewrite eps0_add_head_lt; auto.
      intros lae j.
      rewrite (eps0_fseq_pirr le lae); auto.
    * rewrite eps0_add_head_eq; auto.
      generalize le.
      apply eps0_add_is_limit_iff in le
        as [ (-> & Hf%eps0_is_limit_exp_S_iff) | Hg' ].
      - rewrite !eps0_add_zero_right.
        destruct (pos_add_is_succ i n) as (k & Hk).
        rewrite Hk.
        intros le lae m.
        destruct f as [ | f | f Hf' ] using eps0_discriminate.
        ++ easy.
        ++ rewrite eps0_fseq_exp_S_succ_succ.
           destruct (pos_one_or_succ n) as [ -> | (z & ->) ].
           ** apply pos_succ_inj in Hk as <-.
              rewrite eps0_fseq_exp_S_succ_one; auto.
           ** rewrite <- pos_add_assoc in Hk.
              apply pos_succ_inj in Hk as <-.
              rewrite eps0_fseq_exp_S_succ_succ, eps0_add_head_eq; auto.
              apply eps0_exp_S_mono_left; auto.
        ++ rewrite eps0_fseq_exp_S_succ_is_limit with (l' := Hf').
           destruct (pos_one_or_succ n) as [ -> | (z & ->) ].
           ** apply pos_succ_inj in Hk as <-.
              rewrite eps0_fseq_exp_S_one_is_limit with (l' := Hf'); auto.
           ** rewrite <- pos_add_assoc in Hk.
              apply pos_succ_inj in Hk as <-.
              rewrite <- eps0_add_exp_S,
                         eps0_fseq_exp_S_succ_is_limit with (l' := Hf'),
                        !eps0_add_assoc; auto.
      - intros le lae m.
        rewrite !eps0_fseq_head with (l' := Hg'); auto.
        rewrite <- eps0_add_exp_S, !eps0_add_assoc; auto.
    * rewrite  eps0_add_assoc.
      intros lae m.
      generalize (eps0_add_is_limit_inv _ _ le); intros [ (-> & Hf) | Hg' ].
      - revert le lae; rewrite !eps0_add_zero_right; intros le lae.
        assert (eps0_is_limit (c+₀ω^⟨f,n⟩)) as l' by auto.
        rewrite eps0_fseq_head with (l' := l'), eps0_add_assoc; auto.
        apply eps0_add_below_omega; auto; apply eps0_exp_S_mono_left; auto.
      - revert lae; rewrite <- (eps0_add_assoc c); intros lae.
        assert (eps0_is_limit (c+₀ω^⟨f,n⟩+₀g)) as l' by auto.
        rewrite eps0_fseq_head with (l' := l'); auto.
        ++ rewrite eps0_add_assoc.
           apply eps0_add_mono; auto.
           revert l'; rewrite eps0_add_assoc; auto.
        ++ apply eps0_add_below_omega.
           ** apply eps0_add_below_omega; auto.
              apply eps0_exp_S_mono_left; auto.
           ** now apply eps0_lt_trans with (1 := Hg), eps0_omega_mono_lt.
Qed.

Hint Resolve eps0_zero_lt_succ : core.

(** We start with fseq (ω^a * e) *)
Lemma eps0_fseq_mult_omega a e (le : eps0_is_limit e) (lae : eps0_is_limit (ω^a*₀e)) :
   ∀n, eps0_fseq lae n ≤ε₀ ω^a *₀ eps0_fseq le n.
Proof.
  revert le lae.
  destruct e as [ | f n g H IHf IHg ] using eps0_head_rect.
  1: intros l; exfalso; now apply (proj1 l).
  destruct f as [ | f | f Hf ] using eps0_discriminate.
  + rewrite eps0_omega_zero in H.
    apply eps0_lt_one in H as ->.
    rewrite eps0_add_zero_right; auto.
    intros le; exfalso; apply (proj2 le); auto.
  + rewrite eps0_mult_omega_head; auto.
    intros le lae i.
    generalize (eps0_add_is_limit_inv _ _ le); intros [ (-> & Hf) | Hg ].
    * revert le lae. 
      rewrite eps0_mult_zero_right, !eps0_add_zero_right, eps0_add_succ_right.
      intros le lae.
      destruct (pos_one_or_succ n) as [ -> | (m & ->) ].
      - rewrite !eps0_fseq_exp_S_succ_one, eps0_mult_omega_exp_S; auto.
      - rewrite !eps0_fseq_exp_S_succ_succ, eps0_mult_distr, 
                !eps0_mult_omega_exp_S, eps0_add_succ_right; auto.
    * assert (eps0_is_limit (ω^(a) *₀ g)) as Hag.
      1:{ apply eps0_mult_is_limit; auto. }
      rewrite eps0_fseq_head with (l' := Hg); auto.
      rewrite eps0_fseq_head with (l' := Hag); auto.
      - rewrite eps0_mult_distr, eps0_mult_omega_exp_S.
        apply eps0_add_mono; auto.
      - apply eps0_mult_below_omega with (n := 1); auto.
        apply eps0_exp_S_mono_right; auto.
  + rewrite eps0_mult_omega_head; auto.
    intros le lae i.
    generalize (eps0_add_is_limit_inv _ _ le); intros [ (-> & Hf') | Hg ].
    * revert le lae.
      rewrite eps0_mult_zero_right, !eps0_add_zero_right.
      intros le lae.
      assert (eps0_is_limit (a +₀ f)) as Haf by auto.
      destruct (pos_one_or_succ n) as [ -> | (m & ->) ].
      - rewrite eps0_fseq_exp_S_one_is_limit with (l' := Hf),
                eps0_fseq_exp_S_one_is_limit with (l' := Haf),
                eps0_mult_omega. 
        apply eps0_omega_mono_le, eps0_fseq_add.
      - rewrite eps0_fseq_exp_S_succ_is_limit with (l' := Hf),
                eps0_fseq_exp_S_succ_is_limit with (l' := Haf),
                eps0_mult_distr, eps0_mult_omega_exp_S, 
                eps0_mult_omega.
        apply eps0_add_mono; auto.
        apply eps0_omega_mono_le, eps0_fseq_add.
    * assert (eps0_is_limit (ω^(a) *₀ g)) as Hag.
      1:{ apply eps0_mult_is_limit; auto. }
      rewrite eps0_fseq_head with (l' := Hg); auto.
      rewrite eps0_fseq_head with (l' := Hag); auto.
      - rewrite eps0_mult_distr, eps0_mult_omega_exp_S.
        apply eps0_add_mono; auto.
      - apply eps0_mult_below_omega with (n := 1); auto.
        apply eps0_exp_S_mono_right; auto.
Qed.

Theorem eps0_fseq_mult a e (le : eps0_is_limit e) (lae : eps0_is_limit (a*₀e)) :
   ∀n, eps0_fseq lae n ≤ε₀ a *₀ eps0_fseq le n.
Proof.
  destruct a as [ | a i b Hb _ _ ] using eps0_head_rect.
  + exfalso.
    rewrite eps0_mult_zero_left in lae.
    now apply (proj1 lae).
  + revert lae.
    rewrite eps0_mult_head_limit; auto.
    intros lae n.
    apply eps0_le_trans with (1 := eps0_fseq_mult_omega _ le lae n).
    apply eps0_mult_mono; auto.
    apply eps0_le_trans with ω^⟨a,i⟩; auto.
    apply eps0_exp_S_mono; auto.
    apply pos_one_least.
Qed.


