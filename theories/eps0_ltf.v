(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils ord eps0.

Import ListNotations.

Set Implicit Arguments.

(** The least tail form (ltf) of an ordinal is a decomposition
    of the form a + ω^e for with a is the least possible 

    least tail form is either
       0
       a + ε₀^e  with 0 < e
       a + 1
       a + λ     with λ < ε₀ limit ord

    ε₀ + ω³ + ω² can be decomposed
    into (ε₀ + ω³) + ω² or ε₀ + (ω³ + ω²)
    so how to choose uniquely ?

    a + ε₀^e + λ where 0 < e and λ < ε₀ and a minimal 
    is unique ?

    Limit ordinals are 

      1) a + ε₀^e with 0 < e
      2) a + λ    with λ < ε₀ limit ord

    In case of 1) with analyse e as
       - e = f + 1,  then λ(n) := a + ε₀^f.λ₀(n) (where λ₀(n) ~> ε₀ in ord)
       - λ'(n) ~> e  then λ(n) := a + λ'(n) (recursive call on e)
    In case of 2) we get
       - λ'(n) ~> λ  then λ(n) := a + λ'(n) (where λ'(n) ~> λ < ε₀ is ord)

    This gives us a fundemental sequence for base ε₀ !!

    For instance ε₀^ε₀ + ε₀^ω² has fundemental sequence
          λ(n) := ε₀^ε₀ + ε₀^(ω.n)

    Hence for instance:
     - 0 + ω is a ltf
     - ω³ + ω is a ltf
     - but (ω³+ω) + ω² is not a ltf  
     
    This does not work when using ε₀ as a basis instead of ω
    because ω is not of the form a + ε₀^_ 

    Fund sequence for a + λ where λ < ε₀ and is a limit
    ordinal
    
    So the fundemental sequence needs to be computed otherwise
    for ε₀. Btw, we will need the fundemental sequence of for
    limit ordinals in ord to get that of those of basis ε₀
    
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

Definition eps0_ltf a e := ∀b, a +₀ ω^e = b +₀ ω^e → a ≤ε₀ b.

#[local] Hint Resolve eps0_zero_least : core.

#[local] Hint Resolve eps0_le_antisym : core.

#[local] Hint Resolve eps0_le_refl eps0_le_trans eps0_lt_trans 
                      eps0_lt_le_weak : core.

#[local] Hint Resolve eps0_add_mono eps0_add_incr 
                      eps0_add_incr_left eps0_add_incr_right : core.

Fact eps0_ltf_zero e : eps0_ltf 0₀ e.
Proof. red; auto. Qed.

Fact eps0_eq_ltf_inv :
  ∀ a b e f,
      eps0_ltf a e
    → eps0_ltf b f
    → a +₀ ω^e = b +₀ ω^f
    → a = b ∧ e = f.
Proof.
  intros a b e f H1 H2 E.
  assert (e = f) as <-; auto.
  1: now apply eps0_tf_fun_right in E.
Qed.

#[local] Hint Resolve eps0_ltf_zero : core. 

Fact eps0_one_eq_ltf a e :
    eps0_ltf a e
  → 1₀ = a +₀ ω^e
  → a = 0₀ ∧ e = 0₀.
Proof.
  intros H1.
  replace 1₀ with (0₀ +₀ ω^0₀).
  + intros (<- & <-)%eps0_eq_ltf_inv; eauto.
  + now rewrite eps0_add_zero_left, eps0_omega_zero.
Qed.

Fact eps0_eq_omega_ltf_inv a b e :
    eps0_ltf b e
  → ω^a = b +₀ ω^e
  → b = 0₀ ∧ a = e.
Proof.
  intros H.
  rewrite <- (eps0_add_zero_left ω^a).
  intros (<- & <-)%eps0_eq_ltf_inv; auto.
Qed.

Fact eps0_ltf_exp e n : eps0_ltf ω^⟨e,n⟩ e.
Proof.
  intros b Hb.
  rewrite eps0_add_exp_omega in Hb.
  destruct b as [ | g i f Hf _ ] using eps0_hnf_rect.
  + rewrite eps0_add_zero_left in Hb.
    now apply eps0_exp_inj, proj2, ord_succ_not_zero in Hb.
  + rewrite <- (eps0_add_zero_right ω^e) in Hb; unfold eps0_omega in Hb.
    destruct (eps0_lt_sdec g e) as [ g e C | e | g e C ].
    * rewrite eps0_add_hnf_lt, eps0_add_zero_right in Hb; auto.
      now apply eps0_exp_inj, proj2, ord_succ_not_zero in Hb.
    * rewrite eps0_add_hnf_eq, eps0_add_zero_right in Hb; auto.
      apply eps0_exp_inj, proj2 in Hb.
      rewrite ord_add_zero_right, ord_eq_succ_iff in Hb; subst; auto.
    * apply eps0_le_trans with ω^⟨g,i⟩; auto.
      apply eps0_le_iff_lt.
      left; now apply eps0_exp_mono_left.
Qed.

Fact eps0_ltf_hnf e n g h : 
    g +₀ ω^(h) <ε₀ ω^(e)
  → eps0_ltf g h
  → eps0_ltf (ω^⟨e,n⟩ +₀ g) h.
Proof.
  intros Hg Hgh b Hb.
  destruct (eps0_le_lt_dec (ω^⟨e,n⟩ +₀ g) b) as [ | [C | (b' & -> & Hb2)]%eps0_lt_add_inv_add ]; auto.
  + assert (ω^h <ε₀ ω^e) as Hh. 
    1:{ apply eps0_le_lt_trans with (2 := Hg); auto. }
    destruct (@eps0_lt_irrefl ω^⟨e,n⟩).
    apply eps0_le_lt_trans with (2 := eps0_add_below_exp _ _ _ _ C Hh).
    rewrite <- Hb, eps0_add_assoc; auto.
  + apply eps0_add_mono; auto.
    apply Hgh.
    rewrite !eps0_add_assoc in Hb.
    apply eps0_eq_hnf_inv in Hb as (_ & _ & Hb); auto.
    apply eps0_le_lt_trans with (2 := Hg); auto.
Qed.

Fact eps0_ltf_hnf' e g i f :
      g <ε₀ ω^e
    → ω^f <ε₀ ω^e
    → eps0_ltf g f
    → eps0_ltf (ω^⟨e,i⟩ +₀ g) f.
Proof. intros ? ?; apply eps0_ltf_hnf, eps0_add_below_omega; auto. Qed.

Section eps0_ltf_rect.

  Inductive eps0_ltf_decomp : ε₀ → Type :=
    | eps0_ld_zero :    eps0_ltf_decomp 0₀
    | eps0_ld_ltf g e : eps0_ltf g e
                      → eps0_ltf_decomp (g +₀ ω^e).

  Hint Constructors eps0_ltf_decomp : core.
  Hint Resolve eps0_ltf_exp eps0_ltf_hnf : core.

  Local Fact eps0_ld_exp e n : eps0_ltf_decomp ω^⟨e,n⟩.
  Proof.
    destruct (pos_one_or_succ n) as [ -> | (m & ->) ].
    + rewrite <- eps0_add_zero_left; constructor 2; auto.
    + rewrite <- eps0_add_exp_omega; eauto.
  Qed.

  Hint Resolve eps0_ld_exp : core.

  Lemma eps0_ld_build e : eps0_ltf_decomp e.
  Proof.
    induction e as [ | e n f H _ IH ] using eps0_hnf_rect; auto.
    destruct IH as [ | g h IH ].
    + rewrite eps0_add_zero_right; auto.
    + rewrite <- eps0_add_assoc; auto.
  Qed.

  Section eps0_ltf_rect.

    (** Induction principle corresponding to the following building rules 
        for ordinals below ε₀:

                       g  e  eps0_ltf g e
            ------   ----------------------
              0₀          g +₀ ω^e
     *)

    Variables (P : ε₀ → Type)
            (HP0 : P 0₀)
            (HP2 : ∀ g e, eps0_ltf g e → P g → P e → P (g +₀ ω^e)).

    Hint Resolve eps0_lt_le_trans eps0_lt_omega : core.

    Theorem eps0_ltf_rect e : P e.
    Proof.
      induction e as [ e IH ] using eps0_rect.
      destruct (eps0_ld_build e); auto.
      apply HP2; eauto.
    Qed.

  End eps0_ltf_rect.

End eps0_ltf_rect.
