(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.
From Hydra Require Import utils ordinal ordered eps0 eps0_mult.

Import ListNotations.

Set Implicit Arguments.

#[local] Notation π₁ := proj1_sig.
#[local] Notation π₂ := proj2_sig.

#[local] Hint Resolve eps0_le_refl eps0_lt_succ
                      eps0_zero_least
                      eps0_lt_add_incr
                      eps0_lt_add_right
                      eps0_lt_zero_exp 
                      eps0_zero_lt_omega 
                      eps0_lt_le_weak 
                      eps0_le_add_left 
                      eps0_le_add
                      eps0_le_add_incr_left
                      eps0_le_add_incr_right
: core.

(** Section expo *)

Check eps0_omega_zero.

(** Define exponentiation in CNF 

    α * 0     = 0
    α * (β+1) = α*β + α
    α * γ     = sup { α*x | x < γ }
 
    and 

    α^0 = 1
    α^(β+1) = α^β.α
    α^γ = sup { α^x | x < γ }
    
    are isomorphic

    α^(x+y) = α^x.α^y
    (α^x)^y = α^(x.y)
    
    for the multiplication    
    start with the operation (θ : ε₀) (j : ord) => θ * (1+j)   (struct on θ)
   
         0 * (1+j) = 0
         (ω^⟨α,i⟩+β)) * (1+j) = ω^⟨α,i.j⟩+β  (if 1+j is succ)
         (ω^⟨α,i⟩+β)) * (1+j) = ω^⟨α,i.j⟩      (if j is limit)
   
         then the operation (θ α : ε₀)         => θ * ω^α     (struct on θ)
         
         0 * ω^α = 0
         (ω^⟨γ,n⟩+β) * ω^α = ω^(γ+α)
         
         and finally        (γ α : ε₀)         => γ * α       (struct on α)
   
         γ * 0           = 0
         γ * ω^⟨0,n⟩     = γ * (1+n⟩
         γ * (ω^⟨α,n⟩+β) = (γ*ω^α)*(1+n) + γ*β
         
    for the exponentiation
    start with the operation (θ : ε₀) (j : ord) => θ ^ (1+j)   (struct on θ)
   
         0 ^ (1+j) = 0
         (ω^⟨α,i⟩+β)) ^ (1+j) = ω^⟨α*(1+j),i⟩ + ω^(α*k)*β         (if 1+j = k+1, see below, 0 < α) 
         (ω^⟨α,i⟩+β)) ^ (1+j) = ω^⟨α*j⟩      (if j is limit)
   
         then the operation (θ α : ε₀)         => θ ^ ω^α     (struct on θ)
         
         0 ^ ω^α = 0
         (ω^⟨γ,n⟩+β) ^ ω^α = ω^(γ*ω^α)
         
         and finally        (γ α : ε₀)         => γ ^ α       (struct on α)
   
         γ ^ 0           = 1
         γ ^ ω^⟨0,n⟩     = γ ^ (1+n⟩
         γ ^ (ω^⟨α,n⟩+β) = (γ ^ ω^α) ^ (1+n) * γ^β
         
      The formula here: 

         https://proofwiki.org/wiki/Ordinal_Exponentiation_via_Cantor_Normal_Form/Limit_Exponents

      (α^a₁.n₁+...+α^aₚ.nₚ)^β = α^(a₁.β) when a₁ > ... > aₚ > 0 are ordinals 
                                              0 < n₁,...,nₚ < α are ordinals
          and α, β are limit ordinals !!
          
            The spec above is probably wrong for α or β successor

    α^a₁ <= α^a₁.n₁+...+α^aₚ.nₚ <= α^a₁.n₁ + α^a₁ = α^a₁.(n₁+1)
    (α^a₁)^β <= (α^a₁.n₁+...+α^aₚ.nₚ)^β
             <= (α^a₁.(n₁+1))^β
             <= (α^a₁)^β = α^(a₁.β)

   we only need (α^a.n)^β = (α^a)^β for 0 < n < α and 0 < a and α, β limit
   this holds because n.α = α (a property of a α which is arith-closed, see below
   
      Thm: Let ε, l, i be ordinals.
           If i.ε = ε and 0 < l then i.ε^l = ε^l.
      Proof.
        if l > 0 then 1 <= l so there exists m st l = 1 + m
        then i.ε^l = i.ε^(1+m) = (i.ε).ε^m = ε.ε^m = ε^(1+m) = ε^l
      Qed.

        Notice that ω.ω² = ω³ <> ω² is a counter example to i.ε = ε
        but this holds for ε in {ω,ε₀,ε₁,...} because in that case
        ε satisfies: forall x,y < ε, xy < ε (arithmetic closure)

      Thm: if ε is limit ordinal, 0 < i < ε and 0 < α
           Assume i.ε = ε. Then for any l, 
            if l = 0 or limit then (ε^α.i)^l = (ε^α)^l
            if l is succ then (ε^α.i)^l = (ε^α)^l.i
      Proof.
        We have i.ε^α = ε^α by the above theorem
        Proceed by induction on l.
        - 0: ok
        - l+1: (ε^α.i)^(l+1) = (ε^α.i)^l.ε^α.i
                             = (ε^α)^l.(i.ε^α).i
                             = (ε^α)^l.ε^α.i
                             =  (ε^α)^(l+1).i
        - l is limit: 
             the inequality (ε^α)^l <= (ε^α.i)^l is trivial
             for any k < l we have (ε^α.i)^k <= (ε^α)^k.i <= (ε^α)^k.ε <= (ε^α)^k.ε^α = (ε^α)^(k+1)
             but k+1 <= l (l is limit) hence (ε^α.i)^k <= (ε^α)^(k+1) <= (ε^α)^l
             so since (ε^α.i)^l = sup { (ε^α.i)^k | k < l } <= (ε^α)^l
      Qed.

      Thm: if ε, l are a limit ordinals, 0 < i < ε and β < ε^α and 0 < α and i.ε = ε
           then (ε^α.i+β))^l = ε^(α.l)
      Proof.
        Observe:  ε^α <= ε^α.i+β <= ε^α.i + ε^α.1 = ε^α.(i+1)
        then (ε^α)^l <= (ε^α.i+β)^l <= (ε^α.(i+1))^l = (ε^α)^l
        Hence (ε^α.i+β)^l = (ε^α)^l = ε^(α.l)
      Qed.
      
      Thm: if ε is a limit ordinal, 0 < i < ε and β < ω^α and 0 < α and n is nat
           then (ε^α.i+β)^(n+1) = ε^(α.(n+1)).i + ε^(α.n).β
      Proof.
      
        using equation:   (ε^a.i+b).(ε^e.j+f) = ε^(a+e).j + (ε^a.i+b).f
      
        by induction on n:
        n = 0. (ε^α.i+β)^(n+1) = ε^α.i+β
               ε^(α.(n+1)).i + ε^(α.n).β = ε^(α.1).i + ε^0.β = ε^α.i+β
        
        n = 1+k.
               (ε^α.i+β)^(n+1)
             = (ε^α.i+β)^(1+k+1)
             = (ε^α.i+β).(ε^α.i+β)^(k+1)
             = (ε^α.i+β).(ε^(α.(k+1)).i + ε^(α.k).β)
             = ε^(α+α.(k+1)).i + (ε^α.i+β).ε^(α.k).β
             = ε^(α.(1+k+1)).i + ((ε^α.i+β).ε^(α.k)).β
             = ε^(α.(n+1)).i + (ε^(α+α.k) + 0).β
             = ε^(α.(n+1)).i + ε^(α.n).β
      Qed.
      
      Thm: if ω, l are a limit ordinals, 0 < i < ω and β < ω^α and n is nat
              then (ω^α.i+β)^(l+n+1) = ω^(α.(l+n+1)).i + ω^(α.(l+n)).β
      Proof.
        (ω^α.i+β)^(l+n+1) = (ω^α.i+β)^l.(ω^α.i+β)^(n+1)
                          = ω^(α.l).(ω^(α.(n+1)).i + ω^(α.n).β)
                          = ω^(α.l+α.(n+1)).i + ω^(α.l).ω^(α.n).β
                          = ω^(α.(l+n+1)).i + ω^(α.(l+n)).β
      Qed.

*)

#[global] Reserved Notation "x '^ₒ' y" (at level 27, left associativity, format "x ^ₒ y").

Section eps0_power.

  Variables (o : ord).

  Notation ε₀ := (@eps0 o).

  Section eps0_pow1add.

  (** The operation (θ : ε₀) (j : ord) => θ ^ (1+j)
  
     (1ₒ +ₒ p) ^ₒ (1ₒ +ₒ j)
   *)
  
  Inductive eps0_pow1add_gr : ε₀ → o → ε₀ → Prop :=
    | eps0_pow1add_gr_0 j :       eps0_pow1add_gr 0₀ j 0₀
    | eps0_pow1add_gr_1 p j k :   (1ₒ +ₒ p) ^ₒ (1ₒ +ₒ j) = 1ₒ +ₒ k
                                → eps0_pow1add_gr ω^⟨0₀,p⟩ j ω^⟨0₀,k⟩
    | eps0_pow1add_gr_2 α i β :   0₀ <ε₀ α 
                                → β <ε₀ ω^α
                                → eps0_pow1add_gr (ω^⟨α,i⟩ +₀ β) 0ₒ (ω^⟨α,i⟩ +₀ β) 
    | eps0_pow1add_gr_3 α i β j : 0₀ <ε₀ α 
                                → β <ε₀ ω^α
                                → eps0_pow1add_gr (ω^⟨α,i⟩ +₀ β) (j +ₒ 1ₒ) 
                                    ( ω^⟨α *₀ ω^⟨0₀,1ₒ +ₒ j +ₒ 1ₒ⟩,i⟩ +₀ ω^⟨α *₀ ω^⟨0₀,1ₒ +ₒ j⟩,i⟩ *₀ β )
    | eps0_mpowadd_gr_4 α i β j : ord_is_limit j
                                → 0₀ <ε₀ α 
                                → β <ε₀ ω^α
                                → eps0_pow1add_gr (ω^⟨α,i⟩ +₀ β) j ω^(α *₀ ω^⟨0₀,j⟩).

  Fact eps0_pow1add_fun e1 j1 f1 e2 j2 f2 : eps0_pow1add_gr e1 j1 f1 → eps0_pow1add_gr e2 j2 f2 → e1 = e2 → j1 = j2 → f1 = f2.
  Proof.
    do 2 destruct 1; auto.
    2,3: now intros ?%eps0_zero_neq_hnf.
    1: now intros ?%eps0_zero_neq_exp.
    1: symm; now intros ?%eps0_zero_neq_exp.
    8,13: symm; now intros ?%eps0_zero_neq_hnf.
    
    (*
    1: now intros ? ?%ord_zero_not_succ.
    2: now intros ? ?%ord_succ_not_zero.
    + intros _ ?; subst.
      match goal with H : ord_is_limit _ |- _ => now apply ord_is_limit_zero_iff in H end.
    + intros (? & [])%eps0_eq_hnf_inv ?%ord_succ_inj; subst; auto.
    + intros (? & [])%eps0_eq_hnf_inv ?; subst; auto.
      match goal with H : ord_is_limit _ |- _ => now apply ord_is_limit_succ_iff in H end.
    + intros _ ?; subst.
      match goal with H : ord_is_limit _ |- _ => now apply ord_is_limit_zero_iff in H end.
    + intros (? & [])%eps0_eq_hnf_inv ?; subst; auto.
      match goal with H : ord_is_limit _ |- _ => now apply ord_is_limit_succ_iff in H end.
    + intros (? & [])%eps0_eq_hnf_inv ?; subst; auto. *)
  Admitted.
  
  Hint Resolve ord_le_refl ord_le_zero_least ord_le_add : core.
  
  Definition eps0_pow1add_pwc e j : sig (eps0_pow1add_gr e j).
  Proof.
    destruct e as [ | e i f H _ _ ] using eps0_hnf_rect.
    + exists 0₀; constructor.
    + destruct (eps0_zero_or_pos e) as [ -> | He ].
      * rewrite eps0_omega_zero in H.
        apply eps0_lt_one in H as ->.
        rewrite eps0_add_zero_right.
        destruct (ord_zero_or_1add ((1ₒ +ₒ i) ^ₒ (1ₒ +ₒ j))) as [ C | (k & Hk) ].
        - destruct (@ord_not_one_le_zero o).
          rewrite <- C.
          apply ord_one_le_pow.
          rewrite <- (ord_add_zero_right 1ₒ) at 1; auto.
        - exists ω^⟨0₀,k⟩; constructor; auto.
      * destruct (ord_zero_succ_limit_dec j) as [ [ -> | (p & ->) ] | G ].
        - exists (ω^⟨e,i⟩ +₀ f); now constructor.
        - exists  ( ω^⟨e *₀ ω^⟨0₀,1ₒ +ₒ p +ₒ 1ₒ⟩,i⟩ +₀ ω^⟨e *₀ ω^⟨0₀,1ₒ +ₒ p⟩,i⟩ *₀ f ); now constructor.
        - exists ω^(e *₀ ω^⟨0₀,j⟩); now constructor.
  Qed.

  Definition eps0_pow1add e j := π₁ (eps0_pow1add_pwc e j).

  Fact eps0_pow1add_spec e j : eps0_pow1add_gr e j (eps0_pow1add e j).
  Proof. apply (proj2_sig _). Qed.

  Tactic Notation "solve" "pow1add" :=
    intros; apply eps0_pow1add_fun with (1 := eps0_pow1add_spec _ _) (3 := eq_refl) (4 := eq_refl); constructor; auto.

  Fact eps0_pow1add_fix_0 j : eps0_pow1add 0₀ j = 0₀.
  Proof. solve pow1add. Qed.

  Fact eps0_pow1add_fix_1 α i β : β <ε₀ ω^α → eps0_pow1add (ω^⟨α,i⟩ +₀ β) 0ₒ = ω^⟨α,i⟩ +₀ β.
  Proof. solve pow1add. Qed.

  Fact eps0_pow1add_fix_2 α i β j : β <ε₀ ω^α → eps0_pow1add (ω^⟨α,i⟩ +₀ β) (j +ₒ 1ₒ) = ω^⟨α *₀ ω^⟨0₀,1ₒ +ₒ j +ₒ 1ₒ⟩,i⟩ +₀ ω^⟨α *₀ ω^⟨0₀,1ₒ +ₒ j⟩,i⟩ *₀ β.
  Proof. solve pow1add. Qed.

  Fact eps0_pow1add_fix_3 α i β j : ord_is_limit j → β <ε₀ ω^α → eps0_pow1add (ω^⟨α,i⟩ +₀ β) j = ω^(α *₀ ω^⟨0₀,j⟩).
  Proof. solve pow1add. Qed. 
  
  End eps0_pow1add.

  (** The operation  (θ α : ε₀)         => θ ^ ω^α     (struct on θ)
         
         0 ^ ω^α = 0
         (ω^⟨γ,n⟩+β) ^ ω^α = ω^(γ*ω^α) *)

  Inductive eps0_powomega_gr α : ε₀ → ε₀ → Prop :=
    | eps0_powomega_gr_0 : eps0_powomega_gr α 0₀ 0₀
    | eps0_powomega_gr_1 γ n β : β <ε₀ ω^γ → eps0_powomega_gr α (ω^⟨γ,n⟩ +₀ β) ω^(γ*₀ω^α).

  Fact eps0_powomega_fun a e1 f1 e2 f2 : eps0_powomega_gr a e1 f1 → eps0_powomega_gr a e2 f2 → e1 = e2 → f1 = f2.
  Proof.
    do 2 destruct 1; auto.
    + now intros ?%eps0_zero_neq_hnf.
    + symm; now intros ?%eps0_zero_neq_hnf.
    + intros (? & [])%eps0_eq_hnf_inv; subst; auto.
  Qed.

  Definition eps0_powomega_pwc e α : sig (eps0_powomega_gr α e).
  Proof.
    destruct e as [ | e ] using eps0_hnf_rect.
    + exists 0₀; constructor.
    + exists ω^(e*₀ω^α); now constructor.
  Qed.

  Definition eps0_powomega e α := π₁ (eps0_powomega_pwc e α).

  Fact eps0_powomega_spec e α : eps0_powomega_gr α e (eps0_powomega e α).
  Proof. apply (proj2_sig _). Qed.

  Fact eps0_powomega_fix_0 α : eps0_powomega 0₀ α = 0₀.
  Proof. apply eps0_powomega_fun with (1 := eps0_powomega_spec _ _) (3 := eq_refl); constructor. Qed.

  Fact eps0_powomega_fix_1 γ n β α : β <ε₀ ω^γ → eps0_powomega (ω^⟨γ,n⟩ +₀ β) α = ω^(γ*₀ω^α).
  Proof. intros; apply eps0_powomega_fun with (1 := eps0_powomega_spec _ _) (3 := eq_refl); now constructor. Qed.

  (** The operation   (γ α : ε₀)         => γ ^ α       (struct on α)
   
         γ ^ 0           = 1
         γ ^ ω^⟨0,n⟩     = γ ^ (1+n⟩
         γ ^ (ω^⟨α,n⟩+β) = (γ ^ ω^α) ^ (1+n) * γ^β *)

  Inductive eps0_pow_gr γ : ε₀ → ε₀ → Prop :=
    | eps0_pow_gr_0         : eps0_pow_gr γ 0₀ 1₀ 
    | eps0_pow_gr_1 n       : eps0_pow_gr γ ω^⟨0₀,n⟩ (eps0_pow1add γ n)
    | eps0_pow_gr_2 α n β r : 0₀ <ε₀ α
                            → β <ε₀ ω^α
                            → eps0_pow_gr γ β r
                            → eps0_pow_gr γ (ω^⟨α,n⟩ +₀ β) (eps0_pow1add (eps0_powomega γ α) n *₀ r).

  Fact eps0_pow_fun a e1 f1 e2 f2 :
      eps0_pow_gr a e1 f1
    → eps0_pow_gr a e2 f2
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

  Hint Constructors eps0_pow_gr : core.

  Definition eps0_pow_pwc γ e : sig (eps0_pow_gr γ e).
  Proof.
    induction e as [ | n | e n f He Hf _ (r & Hr) ] using eps0_hnf_pos_rect.
    + exists 1₀; auto.
    + exists (eps0_pow1add γ n); auto.
    + exists (eps0_pow1add (eps0_powomega γ e) n *₀ r); auto.
  Qed.

  Definition eps0_pow e f := π₁ (eps0_pow_pwc e f).

(*
  Infix "^₀" := eps0_mult.

  Fact eps0_pow_spec e f : eps0_mult_gr e f (e *₀ f).
  Proof. apply (proj2_sig _). Qed.

  Hint Resolve eps0_mult_spec : core.

  Tactic Notation "solve" "mult" :=
    intros; apply eps0_mult_fun with (1 := eps0_mult_spec _ _) (3 := eq_refl); auto.

  Fact eps0_mult_zero_right a : a *₀ 0₀ = 0₀.
  Proof. solve mult. Qed.

  Fact eps0_mult_1add_right a n : a *₀ ω^⟨0₀,n⟩ = eps0_m1add a n.
  Proof. solve mult. Qed.

*)

  (** Need to check more equations *)

End eps0_power.



