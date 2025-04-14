(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils ordered lex2 lex_list list_order wlist E0.

Import ListNotations.


(* LAWS:

   α.0 = 0.α = 0
   α.1 = 1.α = α
   (α.β).γ = α.(β.γ)
   0 < γ → α < β → γ.α < γ.β
   α ≤ β → α.γ ≤ β.γ
   α· S(β) = (α · β) + α
   α(β + γ) = αβ + αγ
   (ω^γ.a + β).n = ω^γ.(an) + β
   (ω^γ.a + β).ω^α = ω^(γ+α)

  a^0 = 1
     a^(S n) = a^n.a
     a^(ω^e+f) = a^(ω^e).a^f

     a^(ω^e) = ?
      0^_ = 0
      n^(ω^e) = 
      (ω^a+b)^(ω^e) = ?
      (ω^a)^(ω^e) = ω^(a.ω^e)

   
   
   θ.n
   
   θ.(ω^α.a) = [ 
               [
   
   θ.0 = 0
   0 < n → θ.n = { 0.n = 0
                 { (ω^γ.a + β).n = ω^γ.(an) + β
                 
   β' < α → θ.(ω^α.a + β') = 
   
   
   
   0 < n → (ω^γ.a + β).n = ω^γ.(an) + β
   0 < α → (ω^γ.g + β).(ω^α.a + β') = ω^(γ+α).a + (ω^γ.g + β).β'
   
   *)

Set Implicit Arguments.

#[local] Notation π₁ := proj1_sig.
#[local] Notation π₂ := proj2_sig.

#[global] Reserved Notation "e '<ε₀' f" (at level 70, format "e  <ε₀  f").
#[global] Reserved Notation "e '≤ε₀' f" (at level 70, format "e  ≤ε₀  f").

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.
#[local] Hint Resolve clos_trans_rev transitive_rev : core.
#[local] Hint Constructors lex2 : core.

(** ε₀ is the sub-type of E0 composed of trees in nested lexigraphic order *)

Definition eps0 := { e | cnf e }.

#[local] Notation ε₀ := eps0.

Fact eps0_eq_iff (e f : ε₀) : e = f ↔ π₁ e = π₁ f.
Proof.
  split; intro H; subst; auto.
  revert e f H; intros [e He] [f Hf] ?; simpl in *; subst.
  now rewrite (cnf_pirr _ He Hf).
Qed.

Local Fact eps0_pirr (P : ε₀ → Type) e f h1 h2 : e = f → P (exist _ e h1) → P (exist _ f h2).
Proof. intros <-; now rewrite (cnf_pirr _ h1 h2). Qed.

Section eps0_order.

  (** ε₀ is itself equipped with the restriction 
      of the nested lex. order denoted <ε₀ *)

  Definition eps0_lt (e f : ε₀) := E0_lt (π₁ e) (π₁ f).

  Arguments eps0_lt /.

  Infix "<ε₀" := eps0_lt.

  (** The nested lexicographic order <ε₀ is a strict total/decidable order *)

  Fact eps0_lt_irrefl e : ¬ e <ε₀ e.
  Proof. destruct e; apply E0_lt_irrefl. Qed.

  Fact eps0_lt_trans : transitive eps0_lt.
  Proof. intros [] [] []; apply E0_lt_trans. Qed.

  Hint Resolve eps0_lt_trans : core.
  Hint Constructors sdec : core.

  Fact eps0_lt_sdec e f : sdec eps0_lt e f.
  Proof.
    revert e f; intros (e & He) (f & Hf).
    destruct (E0_lt_sdec e f) as []; eauto.
    rewrite (cnf_pirr _ He Hf); auto.
  Qed.

  Fact eps0_lt_eq_gt_dec e f : { e <ε₀ f } + { e = f } + { f <ε₀ e }.
  Proof. destruct (eps0_lt_sdec e f); auto. Qed.

  Fact eps0_eq_dec (e f : ε₀) : { e = f } + { e ≠ f }.
  Proof. apply sdec_eq_dec with (1 := eps0_lt_sdec), eps0_lt_irrefl. Qed.

  Hint Resolve cnf_lt_lpo : core.

  (* <ε₀ is well-founded *)
  Fact wf_eps0_lt : well_founded eps0_lt.
  Proof.
    generalize E0_lt_wf.
    apply wf_rel_morph with (f := fun x y => x = π₁ y).
    + intros []; eauto.
    + unfold eps0_lt; intros ? ? [] [] -> ->; simpl; eauto.
  Qed.

  Hint Resolve cnf_zero cnf_one : core.

  Definition eps0_zero : ε₀.
  Proof. now exists E0_zero. Defined.

  Definition eps0_one : ε₀.
  Proof. now exists E0_one. Defined.

  Notation "0₀" := eps0_zero.
  Notation "1₀" := eps0_one.

  Fact eps0_zero_not_gt : ∀e, ¬ e <ε₀ 0₀.
  Proof. intros []; apply E0_zero_not_gt. Qed.

  Definition eps0_le e f := e <ε₀ f ∨ e = f.

  Infix "≤ε₀" := eps0_le.

  Fact eps0_le_iff e f : e ≤ε₀ f ↔ E0_le (π₁ e) (π₁ f).
  Proof.
    unfold eps0_le, E0_le; rewrite eps0_eq_iff.  
    revert e f; intros [ e He ] [ f Hf ]; simpl; tauto.
  Qed.

  Fact eps0_zero_least e : 0₀ ≤ε₀ e.
  Proof.
    apply eps0_le_iff.
    destruct e as [ [l] He ]; simpl.
    destruct l; [ right | left ]; auto.
    constructor; constructor.
  Qed.

  Fact eps0_lt_le_weak e f : e <ε₀ f → e ≤ε₀ f.
  Proof. now left. Qed. 

  Fact eps0_le_refl e : e ≤ε₀ e.
  Proof. now right. Qed.

  Fact eps0_le_antisym e f : e ≤ε₀ f → f ≤ε₀ e → e = f.
  Proof. rewrite !eps0_le_iff, eps0_eq_iff; apply E0_le_antisym. Qed.

  Fact eps0_le_trans e f g : e ≤ε₀ f → f ≤ε₀ g → e ≤ε₀ g.
  Proof. rewrite !eps0_le_iff; apply E0_le_trans. Qed.

  Fact eps0_lt_le_trans e f g : e <ε₀ f → f ≤ε₀ g → e <ε₀ g.
  Proof. rewrite eps0_le_iff; apply E0_lt_le_trans. Qed.

  Fact eps0_le_lt_trans e f g : e ≤ε₀ f → f <ε₀ g → e <ε₀ g.
  Proof. rewrite eps0_le_iff; apply E0_le_lt_trans. Qed.

  Hint Resolve eps0_zero_least eps0_lt_le_weak
             eps0_le_refl eps0_le_antisym
             eps0_le_trans eps0_le_lt_trans
             eps0_lt_le_trans : core.

  Fact eps0_zero_or_pos e : { e = 0₀ } + { 0₀ <ε₀ e }.
  Proof.
    destruct e as [ [ [ | x l ] ] Hl ].
    + left; apply eps0_eq_iff; auto.
    + right; cbv; repeat constructor.
  Qed.

  Fact eps0_le_lt_dec e f : { e ≤ε₀ f } + { f <ε₀ e }.
  Proof. destruct (eps0_lt_sdec e f); auto. Qed.
  
  Fact eps0_le_not_lt e f : e ≤ε₀ f → ~ f <ε₀ e.
  Proof. intros ? ?; apply (@eps0_lt_irrefl e); eauto. Qed.

  Fact eps0_le_zero e : e ≤ε₀ 0₀ → e = 0₀.
  Proof. intros []; auto. Qed.

  Hint Resolve E0_succ_cnf : core.

  Definition eps0_succ (e : ε₀) : ε₀.
  Proof.
    destruct e as [ e He ].
    exists (E0_succ e); apply E0_succ_cnf, He.
  Defined.

  Notation S₀ := eps0_succ.

  Hint Resolve E0_succ_zero E0_succ_lt : core.

  (** The successor of E0_zero is E0_one *) 
  Fact eps0_succ_zero_is_one : S₀ 0₀ = 1₀.
  Proof. apply eps0_eq_iff; simpl; auto. Qed.

  (** The successor is <ε₀-greater *)
  Fact eps0_lt_succ e : e <ε₀ S₀ e.
  Proof. destruct e; simpl; auto. Qed.

  Fact eps0_lt_one : ∀e, e <ε₀ 1₀ → e = 0₀.
  Proof. intros []; rewrite eps0_eq_iff; apply E0_lt_one; auto. Qed.

  Fact eps0_le_not_succ e : ¬ S₀ e ≤ε₀ e.
  Proof. intros H; apply (@eps0_lt_irrefl e), eps0_lt_le_trans with (2 := H), eps0_lt_succ. Qed.

  Fact eps0_zero_not_succ e : 0₀ ≠ S₀ e.
  Proof.
    intros H.
    apply (@eps0_lt_irrefl 0₀).
    rewrite H at 2.
    apply eps0_le_lt_trans with (2 := eps0_lt_succ _).
    apply eps0_zero_least.
  Qed.

  Fact eps0_lt_not_le e f : e <ε₀ f → ¬ f ≤ε₀ e.
  Proof. intros ? ?; apply (@eps0_lt_irrefl e); eauto. Qed.

End eps0_order.

Arguments eps0_lt /.

#[local] Hint Resolve eps0_zero_least eps0_lt_le_weak
             eps0_le_refl eps0_le_antisym
             eps0_lt_trans eps0_le_trans 
             eps0_le_lt_trans
             eps0_lt_le_trans : core.

Infix "<ε₀" := eps0_lt.
Infix "≤ε₀" := eps0_le.
Notation "0₀" := eps0_zero.
Notation "1₀" := eps0_one.
Notation S₀ := eps0_succ.

Section eps0_add.

  Hint Resolve E0_add_cnf : core.

  Definition eps0_add : ε₀ → ε₀ → ε₀.
  Proof. intros [e] [f]; exists (E0_add e f); eauto. Defined.

  Infix "+₀" := eps0_add.

  Fact eps0_add_zero_left : ∀e, 0₀ +₀ e = e.
  Proof. intros []; apply eps0_eq_iff, E0_add_zero_left. Qed.

  Fact eps0_add_zero_right : ∀e, e +₀ 0₀ = e.
  Proof. intros []; apply eps0_eq_iff, E0_add_zero_right. Qed.

  Fact eps0_add_assoc : ∀ e f g, (e +₀ f) +₀ g = e +₀ (f +₀ g).
  Proof. intros [] [] []; apply eps0_eq_iff; simpl; apply E0_add_assoc. Qed.

  Fact eps0_add_one_right : ∀e, e +₀ 1₀ = S₀ e.
  Proof. intros []; apply eps0_eq_iff, E0_add_one_right; auto. Qed.

  (** The defining equation for _ + S _ *)
  Fact eps0_add_succ_right e f : e +₀ S₀ f = S₀ (e +₀ f).
  Proof. now rewrite <- eps0_add_one_right, <- eps0_add_assoc, eps0_add_one_right. Qed.

  Fact eps0_lt_inv_add : ∀ e f, e <ε₀ f → ∃a, f = e +₀ a ∧ 0₀ <ε₀ a.
  Proof.
    intros [e] [f] (a & ? & ? & Ha)%E0_lt_inv_add; auto; simpl in *.
    exists (exist _ a Ha); rewrite eps0_eq_iff; simpl; auto.
  Qed.

  Fact eps0_add_mono_left : ∀ e f g, e ≤ε₀ f → e +₀ g ≤ε₀ f +₀ g.
  Proof. intros [] [] []; rewrite !eps0_le_iff; simpl; apply E0_add_mono_left; auto. Qed.

  Fact eps0_add_incr : ∀ e f, 0₀ <ε₀ f → e <ε₀ e +₀ f.
  Proof. intros [] []; apply E0_add_incr; auto. Qed.

  Fact eps0_add_mono_right : ∀ e f g, f <ε₀ g → e +₀ f <ε₀ e +₀ g.
  Proof. intros [] [] []; simpl; apply E0_add_mono_right; auto. Qed.

  Hint Resolve eps0_add_mono_left eps0_add_mono_right : core.

  Fact eps0_add_mono e e' f f' : e ≤ε₀ e' → f ≤ε₀ f' → e +₀ f ≤ε₀ e' +₀ f'.
  Proof. intros ? [ | <- ]; eauto. Qed.

  Hint Resolve eps0_add_mono : core.

  Fact eps0_add_incr_left e f : e ≤ε₀ f +₀ e.
  Proof. rewrite <- (eps0_add_zero_left e) at 1; auto. Qed.

  Fact eps0_add_incr_right e f : e ≤ε₀ e +₀ f.
  Proof. rewrite <- (eps0_add_zero_right e) at 1; auto. Qed.

  Hint Resolve eps0_add_incr_left eps0_add_incr_right : core.

  Fact eps0_add_lt_cancel e u v : e +₀ u <ε₀ e +₀ v → u <ε₀ v.
  Proof. 
    intros H.
    destruct (eps0_lt_sdec u v) as [ u v ? | u | u v G ]; auto.
    + now apply E0_lt_irrefl in H.
    + apply eps0_add_mono_right with (e := e) in G.
      destruct (@eps0_lt_irrefl (e +₀ v)); eauto.
  Qed.
  
  Fact eps0_incr_not_lt e f : ~ e +₀ f <ε₀ e.
  Proof. apply eps0_le_not_lt; auto. Qed.

  Fact eps0_add_eq_zero e f : e +₀ f = 0₀ → e = 0₀ ∧ f = 0₀.
  Proof.
    intros H.
    destruct (eps0_zero_or_pos f) as [ -> | Hf ].
    + now rewrite eps0_add_zero_right in H.
    + apply eps0_add_incr with (e := e) in Hf.
      rewrite H in Hf.
      now apply eps0_zero_not_gt in Hf.
  Qed.

  Lemma eps0_lt_add_inv_add e a f : e <ε₀ a +₀ f → e <ε₀ a ∨ ∃g, e = a +₀ g ∧ g <ε₀ f.
  Proof.
    intros H.
    destruct (eps0_lt_sdec e a) as [ e a G | e | e a G ]; auto.
    + right; exists 0₀.
      rewrite eps0_add_zero_right; split; auto.
      destruct (eps0_zero_or_pos f) as [ -> | ]; auto.
      exfalso; revert H; rewrite eps0_add_zero_right; apply eps0_lt_irrefl.
    + right.
      apply eps0_lt_inv_add in G as (b & -> & Hb).
      apply eps0_add_lt_cancel in H; eauto.
  Qed.

  Fact eps0_succ_next e f : e <ε₀ f → S₀ e ≤ε₀ f.
  Proof.
    intros H.
    destruct (eps0_le_lt_dec (S₀ e) f) as [ | C ]; auto; exfalso.
    rewrite <- eps0_add_one_right in C; auto.
    apply eps0_lt_add_inv_add in C as [ C | (g & -> & Hg) ]; eauto.
    + apply (@eps0_lt_irrefl e); eauto.
    + apply eps0_lt_one in Hg as ->; auto.
      revert H; rewrite eps0_add_zero_right; apply E0_lt_irrefl.
  Qed.

  Fact eps0_succ_next_inv e f : e <ε₀ S₀ f → e ≤ε₀ f.
  Proof.
    intros H.
    destruct (eps0_lt_sdec e f) as [ e f H1 | e | e f H1%eps0_succ_next ].
    + now left.
    + now right.
    + destruct (@eps0_lt_irrefl e).
      now apply eps0_lt_le_trans with (2 := H1).
  Qed.

  Hint Resolve eps0_le_lt_trans eps0_lt_succ eps0_le_not_succ : core.

  Fact eps0_succ_mono e f : e <ε₀ f ↔ S₀ e <ε₀ S₀ f.
  Proof.
    split.
    + intros H%eps0_succ_next; eauto.
    + intros H%eps0_succ_next_inv.
      destruct (eps0_le_lt_dec f e); auto.
      apply eps0_lt_le_trans with (2 := H); auto.
  Qed.

  Fact eps0_succ_inj e f : S₀ e = S₀ f → e = f.
  Proof.
    intros E.
    destruct (eps0_lt_sdec e f) as [ e f G | e | e f G ]; auto.
    all: apply eps0_succ_mono in G; auto; rewrite E in G; destruct (eps0_lt_irrefl G).
  Qed.

  (** There is no ordinal between e and (eps0_succ e) *)
  Corollary eps0_no_ordinal_between_n_and_succ e f :
      ¬ (e <ε₀ f ∧ f <ε₀ eps0_succ e).
  Proof.
    intros (H1 & H2).
    destruct eps0_succ_next with (1 := H1) as [ | <- ].
    + apply (@eps0_lt_irrefl f), eps0_lt_trans with (1 := H2); auto.
    + revert H2; apply eps0_lt_irrefl.
  Qed.

  Fact eps0_add_cancel e u v : e +₀ u = e +₀ v → u = v.
  Proof.
    intros H.
    destruct (eps0_lt_sdec u v) as [ u v G | u | u v G ]; auto;
      apply eps0_add_mono_right with (e := e) in G; rewrite H in G;
      edestruct eps0_lt_irrefl; eauto.
  Qed.

  Fact eps0_add_le_cancel e u v : e +₀ u ≤ε₀ e +₀ v → u ≤ε₀ v.
  Proof. now intros [ ?%eps0_add_lt_cancel | ?%eps0_add_cancel ]; [ left | right ]. Qed.

End eps0_add.

Infix "+₀" := eps0_add.

#[local] Hint Resolve eps0_le_lt_trans
                      eps0_lt_succ
                      eps0_le_not_succ : core.

#[local] Hint Resolve eps0_add_incr
                      eps0_add_incr_left
                      eps0_add_incr_right : core.

#[local] Hint Resolve eps0_add_mono_left
                      eps0_add_mono_right
                      eps0_add_mono : core.

Section eps0_omega.

  (* ω^{e.(S n)} *)
  Definition eps0_exp_S : ε₀ → nat → ε₀.
  Proof.
    intros (e & He) n.
    exists (E0_cons [(e,1+n)]).
    apply cnf_sg; auto; lia.
  Defined.

  (* Beware that this is for ωᵉ.(1+i) and NOT ωᵉ.i *)
  Notation "ω^⟨ e , i ⟩" := (eps0_exp_S e i).

  Fact eps0_succ_exp_S n : S₀ ω^⟨0₀,n⟩ = ω^⟨0₀,S n⟩.
  Proof. apply eps0_eq_iff; simpl; apply E0_succ_pos. Qed.

  Fact eps0_lt_exp_S e n : e <ε₀ ω^⟨e,n⟩.
  Proof.
    destruct e as [e]; unfold eps0_exp_S; cbn.
    apply E0_lt_sub with (1+n); auto.
    apply cnf_sg; auto; lia.
  Qed.

  Fact eps0_lt_zero_exp_S e n : 0₀ <ε₀ ω^⟨e,n⟩.
  Proof. apply eps0_le_lt_trans with (2 := eps0_lt_exp_S _ _); auto. Qed.

  Hint Resolve eps0_lt_zero_exp_S : core.

  Fact eps0_zero_neq_exp_S e n : 0₀ ≠ ω^⟨e,n⟩.
  Proof.
    intros E; apply (@eps0_lt_irrefl 0₀).
    rewrite E at 2; apply eps0_lt_zero_exp_S.
  Qed.

  Fact eps0_exp_S_mono_right : ∀ e n m, n < m → ω^⟨e,n⟩ <ε₀ ω^⟨e,m⟩.
  Proof. intros [] ? ?; simpl; constructor; constructor 2; right; lia. Qed.

  Fact eps0_exp_S_mono_left : ∀ e f n m, e <ε₀ f → ω^⟨e,n⟩ <ε₀ ω^⟨f,m⟩.
  Proof. intros [] [] ? ?; apply E0_lt_exp. Qed.

  Fact eps0_exp_S_mono e f n m : e ≤ε₀ f → n ≤ m → ω^⟨e,n⟩ ≤ε₀ ω^⟨f,m⟩.
  Proof.
    intros [ | <- ] H2.
    + now left; apply eps0_exp_S_mono_left.
    + destruct H2; auto.
      left; apply eps0_exp_S_mono_right; lia.
  Qed.

  Fact eps0_exp_S_mono_inv e f n m : ω^⟨e,n⟩ <ε₀ ω^⟨f,m⟩ → e <ε₀ f ∨ e = f ∧ n < m.
  Proof.
    intros H.
    destruct (eps0_lt_sdec e f) as [ | e | e f H1 ]; auto.
    + destruct (lt_sdec n m) as [ | n | n m H2 ]; auto.
      * contradict H; apply eps0_lt_irrefl.
      * destruct (@eps0_lt_irrefl ω^⟨e,n⟩).
        apply eps0_lt_trans with (1 := H).
        now apply eps0_exp_S_mono_right.
    + destruct (@eps0_lt_irrefl ω^⟨e,n⟩).
      apply eps0_lt_trans with (1 := H).
      now apply eps0_exp_S_mono_left.
  Qed.
  
  Fact eps0_exp_S_inj e f n m : ω^⟨e,n⟩ = ω^⟨f,m⟩ → e = f ∧ n = m.
  Proof.
    intros E.
    destruct (eps0_lt_sdec e f) as [ e f H | e | e f H ].
    + apply eps0_exp_S_mono_left with (n := n) (m := m) in H.
      rewrite E in H; now apply eps0_lt_irrefl in H.
    + destruct (lt_sdec n m) as [ n m H | | n m H ]; auto;
        apply eps0_exp_S_mono_right with (e := e) in H;
        rewrite E in H; now apply eps0_lt_irrefl in H.
    + apply eps0_exp_S_mono_left with (n := m) (m := n) in H.
      rewrite E in H; now apply eps0_lt_irrefl in H.
  Qed.

  Fact eps0_add_exp_S e i j : ω^⟨e,i⟩ +₀ ω^⟨e,j⟩ = ω^⟨e,i+j+1⟩.
  Proof.
    destruct e as (e & He); apply eps0_eq_iff; unfold eps0_add, eps0_exp_S, proj1_sig.
    rewrite E0_add_exp; do 3 f_equal; lia.
  Qed.

  Fact eps0_zero_neq_exp_S_add e n f: 0₀ ≠ ω^⟨e,n⟩ +₀ f.
  Proof.
    intros H.
    apply (@eps0_lt_irrefl 0₀).
    rewrite H at 2.
    apply eps0_lt_le_trans with (1 := eps0_lt_zero_exp_S e n).
    rewrite <- (eps0_add_zero_right ω^⟨e,n⟩) at 1.
    apply eps0_add_mono; auto.
  Qed.

  (* ωᵉ = ωᵉ.(1+0) *)
  Definition eps0_omega (e : ε₀) := ω^⟨e,0⟩.
  Notation "ω^ e" := (eps0_omega e).

  Fact eps0_omega_zero : ω^0₀ = 1₀.
  Proof. apply eps0_eq_iff; trivial. Qed.

  Fact eps0_lt_omega e : e <ε₀ ω^e.
  Proof. apply eps0_lt_exp_S. Qed.

  Hint Resolve eps0_lt_omega : core.

  Fact eps0_omega_mono_lt : ∀ e f, e <ε₀ f → ω^e <ε₀ ω^f.
  Proof. intros [] [] ?; constructor; constructor 2; left; auto. Qed.

  Fact eps0_omega_mono_le e f : e ≤ε₀ f → ω^e ≤ε₀ ω^f.
  Proof. intros [ | <- ]; auto; left; now apply eps0_omega_mono_lt. Qed.

  Fact eps0_omega_inj e f : ω^e = ω^f → e = f.
  Proof.
    intros E.
    destruct (eps0_lt_sdec e f) as [ e f H | | e f H ]; auto;
      apply eps0_omega_mono_lt in H; rewrite E in H; now apply eps0_lt_irrefl in H.
  Qed.
  
  Fact eps0_add_exp_S_omega e i : ω^⟨e,i⟩ +₀ ω^e = ω^⟨e,S i⟩.
  Proof. unfold eps0_omega; rewrite eps0_add_exp_S; f_equal; lia. Qed.

  Fact eps0_one_eq_omega e : 1₀ = ω^e → e = 0₀.
  Proof.
    rewrite <- eps0_omega_zero.
    now intros <-%eps0_omega_inj.
  Qed.

  Fact eps0_zero_lt_omega e : 0₀ <ε₀ ω^e.
  Proof. apply eps0_lt_zero_exp_S. Qed.

  Hint Resolve eps0_zero_lt_omega : core.

  Fact eps0_zero_neq_omega e : 0₀ ≠ ω^e.
  Proof. 
    intros H.
    apply (@eps0_lt_irrefl 0₀).
    rewrite H at 2.
    apply eps0_zero_lt_omega.
  Qed.

  Fact eps0_add_below_omega e f g : e <ε₀ ω^g → f <ε₀ ω^g → e +₀ f <ε₀ ω^g.
  Proof. revert e f g; intros [[] ] [[] ] []; apply E0_add_below_omega. Qed.

  Fact eps0_lt_head_split_inv e₁ i₁ f₁ e₂ i₂ f₂ :
      f₁ <ε₀ ω^e₁
    → f₂ <ε₀ ω^e₂
    → ω^⟨e₁,i₁⟩ +₀ f₁ <ε₀ ω^⟨e₂,i₂⟩ +₀ f₂
    ↔ e₁ <ε₀ e₂ ∨ e₁ = e₂ ∧ (i₁ < i₂ ∨ i₁ = i₂ ∧ f₁ <ε₀ f₂).
  Proof.
    rewrite !eps0_eq_iff.
    revert e₁ i₁ f₁ e₂ i₂ f₂.
    intros (e & He) i ([l] & Hl) (f & Hf) j ([m] & Hm) H1 H2; simpl in *.
    rewrite !E0_add_head_normal in *; auto.
    split; intros H3.
    + apply E0_lt_inv, lex_list_cons_inv in H3
        as [ [ | (<- & ?)]%lex2_inv | ([=] & ?)  ]; auto.
      * right; split; auto; left; lia.
      * subst; do 2 (right; split; auto).
        now constructor.
    + constructor.
      destruct H3 as [ | (<- & [ | (<- & ?%E0_lt_inv) ]) ].
      * constructor 2; now left.
      * constructor 2; right; lia.
      * now constructor 3.
  Qed.

  Fact eps0_lt_head_split_inv_left e₁ i₁ e₂ i₂ f₂ :
      f₂ <ε₀ ω^e₂
    → ω^⟨e₁,i₁⟩ <ε₀ ω^⟨e₂,i₂⟩ +₀ f₂
    ↔ e₁ <ε₀ e₂ ∨ e₁ = e₂ ∧ (i₁ < i₂ ∨ i₁ = i₂ ∧ 0₀ <ε₀ f₂).
  Proof.
    intro.
    rewrite <- (eps0_add_zero_right ω^⟨e₁,_⟩), eps0_lt_head_split_inv; auto.
    firstorder.
  Qed.

  Fact eps0_lt_head_split_inv_right e₁ i₁ f₁ e₂ i₂ :
      f₁ <ε₀ ω^e₁
    → ω^⟨e₁,i₁⟩ +₀ f₁ <ε₀ ω^⟨e₂,i₂⟩
    ↔ e₁ <ε₀ e₂ ∨ e₁ = e₂ ∧ i₁ < i₂.
  Proof.
    intro.
    rewrite <- (eps0_add_zero_right ω^⟨e₂,_⟩), eps0_lt_head_split_inv; auto.
    apply or_iff_compat_l, and_iff_compat_l.
    split; auto.
    intros [ | (_ & ?%eps0_zero_not_gt) ]; now auto.
  Qed.

  Fact eps0_lt_head_split_inv_both e₁ i₁ e₂ i₂ :
      ω^⟨e₁,i₁⟩ <ε₀ ω^⟨e₂,i₂⟩
    ↔ e₁ <ε₀ e₂ ∨ e₁ = e₂ ∧ i₁ < i₂.
  Proof.
    rewrite <- (eps0_add_zero_right ω^⟨e₁,_⟩).
    apply eps0_lt_head_split_inv_right; auto.
  Qed.

  Fact eps0_lt_zero_head e i f : 0₀ <ε₀ ω^⟨e,i⟩ +₀ f.
  Proof. apply eps0_lt_le_trans with ω^⟨e,i⟩; auto. Qed.

  Hint Resolve eps0_lt_zero_head : core.

  Fact eps0_not_head_split_lt_zero e i f : ¬ ω^⟨e,i⟩ +₀ f <ε₀ 0₀.
  Proof. apply eps0_zero_not_gt. Qed.

  Fact eps0_not_eps_S_lt_zero e i : ¬ ω^⟨e,i⟩ <ε₀ 0₀.
  Proof. apply eps0_zero_not_gt. Qed.

  Fact eps0_head_split_uniq e₁ i₁ f₁ e₂ i₂ f₂ :
      ω^⟨e₁,i₁⟩ +₀ f₁ = ω^⟨e₂,i₂⟩ +₀ f₂
    → f₁ <ε₀ ω^e₁
    → f₂ <ε₀ ω^e₂
    → e₁ = e₂ ∧ i₁ = i₂ ∧ f₁ = f₂.
  Proof.
    revert e₁ i₁ f₁ e₂ i₂ f₂.
    intros (e & He) i ([l] & Hl) (f & Hf) j ([m] & Hm)
           E%eps0_eq_iff H1 H2.
    rewrite !eps0_eq_iff; simpl in *.
    rewrite !E0_add_head_normal in E; auto.
    now inversion E.
  Qed.

  Fact eps0_head_split_uniq' e₁ i₁ e₂ i₂ f₂ :
      ω^⟨e₁,i₁⟩ = ω^⟨e₂,i₂⟩ +₀ f₂
    → f₂ <ε₀ ω^e₂
    → e₁ = e₂ ∧ i₁ = i₂ ∧ f₂ = 0₀.
  Proof.
    rewrite <- (eps0_add_zero_right ω^⟨e₁,i₁⟩).
    intros H1 H2; revert H1.
    intros (-> & -> & <-)%eps0_head_split_uniq; auto.
  Qed.

  Fact eps0_eps_S_uniq e₁ i₁ e₂ i₂ :
    ω^⟨e₁,i₁⟩ = ω^⟨e₂,i₂⟩ → e₁ = e₂ ∧ i₁ = i₂.
  Proof.
     rewrite <- (eps0_add_zero_right ω^⟨_,i₁⟩),
             <- (eps0_add_zero_right ω^⟨_,i₂⟩).
     intros (-> & -> & _)%eps0_head_split_uniq; auto.
  Qed.

  Fact eps0_zero_neq_head e i f : 0₀ ≠ ω^⟨e,i⟩ +₀ f.
  Proof.
    intros E.
    apply (@eps0_lt_irrefl 0₀).
    rewrite E at 2.
    apply eps0_lt_le_trans with (1 := eps0_lt_zero_exp_S e i).
    rewrite <- (eps0_add_zero_right ω^⟨_,i⟩) at 1.
    apply eps0_add_mono; auto.
  Qed.

  Fact eps0_add_head_lt e₁ i₁ f₁ e₂ i₂ f₂ :
      e₁ <ε₀ e₂
    → f₁ <ε₀ ω^e₁
    → f₂ <ε₀ ω^e₂
    → (ω^⟨e₁,i₁⟩ +₀ f₁) +₀ (ω^⟨e₂,i₂⟩ +₀ f₂) = ω^⟨e₂,i₂⟩ +₀ f₂.
  Proof.
    revert e₁ i₁ f₁ e₂ i₂ f₂.
    intros (e1 & He1) i ([l] & Hf1) (e2 & He2) j ([m] & Hf2) H1 H2 H3.
    apply eps0_eq_iff; simpl in *.
    rewrite !E0_add_head_normal; auto.
    rewrite E0_add_head_lt; auto.
  Qed.

  Fact eps0_add_head_lt' e₁ i₁ e₂ i₂ f₂ :
      e₁ <ε₀ e₂
    → f₂ <ε₀ ω^e₂
    → ω^⟨e₁,i₁⟩ +₀ (ω^⟨e₂,i₂⟩ +₀ f₂) = ω^⟨e₂,i₂⟩ +₀ f₂.
  Proof.
    intros H1 H2.
    rewrite <- (eps0_add_zero_right ω^⟨e₁,i₁⟩).
    apply eps0_add_head_lt; auto.
  Qed.

  Fact eps0_add_head_lt'' e₁ i₁ e₂ i₂ :
      e₁ <ε₀ e₂ → ω^⟨e₁,i₁⟩ +₀ ω^⟨e₂,i₂⟩ = ω^⟨e₂,i₂⟩.
  Proof.
    intros H.
    rewrite <- (eps0_add_zero_right ω^⟨_,i₂⟩).
    apply eps0_add_head_lt'; auto.
  Qed.

  Fact eps0_add_head_eq e i₁ f₁ i₂ f₂ :
      f₁ <ε₀ ω^e
    → f₂ <ε₀ ω^e
    → (ω^⟨e,i₁⟩ +₀ f₁) +₀ (ω^⟨e,i₂⟩ +₀ f₂) = ω^⟨e,i₁+i₂+1⟩ +₀ f₂.
  Proof.
    revert e i₁ f₁ i₂ f₂.
    intros (e & He) i ([l] & Hf1) j ([m] & Hf2) H1 H2.
    apply eps0_eq_iff; simpl in *.
    rewrite !E0_add_head_normal; auto.
    rewrite E0_add_head_eq; auto.
    do 3 f_equal; lia.
  Qed.

  Fact eps0_add_head_eq' e i₁ i₂ f₂ :
      f₂ <ε₀ ω^e
    → ω^⟨e,i₁⟩ +₀ (ω^⟨e,i₂⟩ +₀ f₂) = ω^⟨e,i₁+i₂+1⟩ +₀ f₂.
  Proof.
    intros.
    rewrite <- (eps0_add_zero_right ω^⟨e,i₁⟩).
    rewrite eps0_add_head_eq; auto.
  Qed.

  Fact eps0_add_head_gt e₁ i₁ f₁ e₂ i₂ f₂ :
      e₂ <ε₀ e₁
    → f₁ <ε₀ ω^e₁
    → f₂ <ε₀ ω^e₂
    → (ω^⟨e₁,i₁⟩ +₀ f₁) +₀ (ω^⟨e₂,i₂⟩ +₀ f₂) = ω^⟨e₁,i₁⟩ +₀ (f₁ +₀ (ω^⟨e₂,i₂⟩ +₀ f₂))
     ∧ f₁ +₀ (ω^⟨e₂,i₂⟩ +₀ f₂) <ε₀ ω^e₁.
  Proof.
    revert e₁ i₁ f₁ e₂ i₂ f₂.
    intros (e1 & He1) i ([l] & Hf1) (e2 & He2) j ([m] & Hf2) H1 H2 H3.
    rewrite eps0_eq_iff; simpl in *.
    rewrite !E0_add_head_normal; auto.
    apply E0_add_head_gt; auto; lia.
  Qed.

  Section eps0_head_rect.

    Variables (P : ε₀ → Type)
              (HP0 : P 0₀)
              (HP1 : ∀ e i f, f <ε₀ ω^e → P e → P f → P (ω^⟨e,i⟩ +₀ f)).

    Theorem eps0_head_rect : ∀e, P e.
    Proof.
      intros (e & he); revert e he.
      apply cnf_head_rect.
      + intros; revert HP0; apply eps0_pirr with (1 := eq_refl).
      + intros e he i f hf h hi H Hf He.
        refine (@eps0_pirr P _ _ _ _ _ (@HP1 _ (pred i) _ _ He Hf)).
        * do 4 f_equal; lia.
        * simpl; trivial.
    Qed.

  End eps0_head_rect.

  Lemma eps0_lt_exp_S_inv a e n :
      a <ε₀ ω^⟨e,n⟩
    → (a = 0₀)
    + { i : _ & { b | a = ω^⟨e,i⟩ +₀ b ∧ i < n ∧ b <ε₀ ω^e } }
    + { f : _ & { i | a <ε₀ ω^⟨f,i⟩ ∧ f <ε₀ e } }.
  Proof.
    destruct a as [ | g i h H _ _ ] using eps0_head_rect.
    + now do 2 left.
    + intros H1.
      destruct n as [ | n ].
      * right.
        exists g, (S i).
        apply eps0_lt_head_split_inv_right in H1
          as [ H1 | (_ & ?) ]; lia || auto.
        split; auto.
        apply eps0_lt_head_split_inv_right; auto.
      * apply eps0_lt_head_split_inv_right in H1; auto.
        destruct (eps0_le_lt_dec e g) as [ C | C ].
        - left; right; exists i, h.
          destruct H1 as [ H1 | (-> & H1) ]; eauto.
          destruct (@eps0_lt_irrefl e); eauto.
        - right; exists g, (S i); split; auto.
          apply eps0_lt_head_split_inv_right; auto.
  Qed.

  (** inversion for _ <ε₀ ω^_ *)
  Lemma eps0_lt_omega_inv a e : a <ε₀ ω^e → (a = 0₀) + { f : ε₀ & { n | a <ε₀ ω^⟨f,n⟩ ∧ f <ε₀ e } }.
  Proof. intros [[ -> | (i & ? & ? & ? & _) ] | ]%eps0_lt_exp_S_inv; auto; lia. Qed.

  (** inversion for _ < ω^(_+1) *)
  Lemma eps0_lt_omega_succ_inv f e : f <ε₀ ω^(S₀ e) → { n | f <ε₀ ω^⟨e,n⟩ }.
  Proof.
    intros [ -> | (a & n & H1 & H2%eps0_succ_next_inv) ]%eps0_lt_omega_inv.
    + exists 0; auto.
    + exists n; apply eps0_lt_le_trans with (1 := H1), eps0_exp_S_mono; auto.
  Qed.
  
  Hint Resolve eps0_exp_S_mono_left eps0_exp_S_mono : core.
  
  Fact eps0_add_exp_S_omega_le e n m : n < m → ω^⟨e,n⟩ +₀ ω^e ≤ε₀ ω^⟨e,m⟩.
  Proof.
    intro H; unfold eps0_omega.
    rewrite eps0_add_exp_S.
    apply eps0_exp_S_mono; auto; lia.
  Qed.
  
  Lemma eps0_add_below_exp_S b c e n : b <ε₀ ω^⟨e,n⟩ → c <ε₀ ω^e → b+₀c <ε₀ ω^⟨e,n⟩.
  Proof.
    intros [ [ -> | (u & i & -> & []) ] | (u & i & []) ]%eps0_lt_exp_S_inv [ -> | (v & j & H2 & H3) ]%eps0_lt_omega_inv.
    + rewrite eps0_add_zero_left; auto.
    + rewrite eps0_add_zero_left; apply eps0_lt_trans with (1 := H2); auto.
    + rewrite eps0_add_zero_right.
      apply eps0_lt_le_trans with (2 := eps0_add_exp_S_omega_le _ H); auto.
    + rewrite eps0_add_assoc.
      apply eps0_lt_le_trans with (2 := eps0_add_exp_S_omega_le _ H); auto.
      apply eps0_add_mono_right, eps0_add_below_omega; auto.
      now apply eps0_lt_trans with (1 := H2), eps0_exp_S_mono_left.
    + rewrite eps0_add_zero_right.
      now apply eps0_lt_trans with (1 := H), eps0_exp_S_mono_left.
    + apply eps0_lt_le_trans with ω^e.
      * apply eps0_add_below_omega; auto.
        - now apply eps0_lt_trans with (1 := H), eps0_exp_S_mono_left.
        - now apply eps0_lt_trans with (1 := H2), eps0_exp_S_mono_left.
      * apply eps0_exp_S_mono; auto; lia.
  Qed.
  
  Section eps0_head_pos_rect.

    Variables (P : ε₀ → Type)
              (HP0 : P 0₀)
              (HP1 : ∀i, P ω^⟨0₀,i⟩) 
              (HP2 : ∀ e i f, 0₀ <ε₀ e → f <ε₀ ω^e → P e → P f → P (ω^⟨e,i⟩ +₀ f)).

    Theorem eps0_head_pos_rect : ∀e, P e.
    Proof.
      induction e as [ | e n f H ] using eps0_head_rect; trivial.
      destruct (eps0_zero_or_pos e) as [ -> | G ].
      + assert (f = 0₀) as ->.
        1:{ rewrite eps0_omega_zero in H.
            now apply eps0_lt_one in H. }
        rewrite eps0_add_zero_right; trivial.
      + now apply HP2.
    Qed.

  End eps0_head_pos_rect.

End eps0_omega.

Hint Resolve eps0_lt_omega 
             eps0_lt_zero_exp_S
             eps0_zero_lt_omega 
             eps0_lt_zero_head : core.

#[local] Notation "ω^⟨ e , i ⟩" := (eps0_exp_S e i).
#[local] Notation "ω^ e" := (eps0_omega e).

Section eps0_mpos.

  (** pos := nat viewed as 1, 2, ... and not 0, 1, ... *)

  (** The operation (θ : ε₀) (n : pos) => θ.(1+n) *)
  Inductive eps0_mpos_gr n : ε₀ → ε₀ → Prop :=
    | eps0_mpos_gr_0 : eps0_mpos_gr n 0₀ 0₀
    | eps0_mpos_gr_1 α i β : β <ε₀ ω^α → eps0_mpos_gr n (ω^⟨α,i⟩ +₀ β) (ω^⟨α,i*n+i+n⟩ +₀ β).

  Fact eps0_mpos_fun n e1 f1 e2 f2 : eps0_mpos_gr n e1 f1 → eps0_mpos_gr n e2 f2 → e1 = e2 → f1 = f2.
  Proof.
    do 2 destruct 1; auto.
    + now intros ?%eps0_zero_neq_exp_S_add.
    + symm; now intros ?%eps0_zero_neq_exp_S_add.
    + intros (? & [])%eps0_head_split_uniq; subst; auto.
  Qed.

  Definition eps0_mpos_pwc e n : sig (eps0_mpos_gr n e).
  Proof.
    destruct e as [ | e i f H ] using eps0_head_rect.
    + exists 0₀; constructor.
    + exists (ω^⟨e,i*n+i+n⟩ +₀ f); now constructor.
  Qed.

  Definition eps0_mpos e n := π₁ (eps0_mpos_pwc e n).

  Fact eps0_mpos_spec e n : eps0_mpos_gr n e (eps0_mpos e n).
  Proof. apply (proj2_sig _). Qed.

  Fact eps0_mpos_fix_0 n : eps0_mpos 0₀ n = 0₀.
  Proof. apply eps0_mpos_fun with (1 := eps0_mpos_spec _ _) (3 := eq_refl); constructor. Qed.

  Fact eps0_mpos_fix_1 n α i β : β <ε₀ ω^α → eps0_mpos (ω^⟨α,i⟩ +₀ β) n = ω^⟨α,i*n+i+n⟩ +₀ β.
  Proof. intros; apply eps0_mpos_fun with (1 := eps0_mpos_spec _ _) (3 := eq_refl); now constructor. Qed.

  Fact eps0_mpos_exp_S n α i : eps0_mpos ω^⟨α,i⟩ n = ω^⟨α,i*n+i+n⟩.
  Proof. 
    rewrite <- (eps0_add_zero_right ω^⟨_,i⟩), eps0_mpos_fix_1; auto.
    now rewrite eps0_add_zero_right.
  Qed.

  Fact eps0_mpos_O e : eps0_mpos e 0 = e.
  Proof.
    destruct e using eps0_head_rect.
    + now rewrite eps0_mpos_fix_0.
    + rewrite eps0_mpos_fix_1; auto.
      do 2 f_equal; lia.
  Qed.

  Fact eps0_mpos_omega_add n α β : β <ε₀ ω^α → eps0_mpos (ω^α +₀ β) n = ω^⟨α,n⟩ +₀ β.
  Proof.
    intros; unfold eps0_omega.
    rewrite eps0_mpos_fix_1; auto.
  Qed.

  Fact eps0_mpos_omega n α : eps0_mpos ω^α n = ω^⟨α,n⟩.
  Proof.
    rewrite <- (eps0_add_zero_right ω^α), eps0_mpos_omega_add; auto.
    now rewrite eps0_add_zero_right.
  Qed.

  Fact eps0_mpos_plus e i j : eps0_mpos e i +₀ eps0_mpos e j = eps0_mpos e (i+j+1).
  Proof.
    destruct e using eps0_head_rect.
    + now rewrite !eps0_mpos_fix_0, eps0_add_zero_left.
    + rewrite !eps0_mpos_fix_1; auto.
      rewrite eps0_add_head_eq; auto.
      do 2 f_equal; ring.
  Qed.

  Fact eps0_mpos_mult e i j : eps0_mpos (eps0_mpos e i) j = eps0_mpos e (i*j+i+j).
  Proof.
    destruct e using eps0_head_rect.
    + now rewrite !eps0_mpos_fix_0.
    + rewrite !eps0_mpos_fix_1; auto.
      do 2 f_equal; ring.
  Qed.

  Fact eps0_mpos_mono_left a b m n : a <ε₀ b → m ≤ n → eps0_mpos a m <ε₀ eps0_mpos b n.
  Proof.
    intros Hab Hmn.
    destruct a as [ | e i f H1 _ _ ] using eps0_head_rect;
      destruct b as [ | g j h H2 _ _ ] using eps0_head_rect.
    + now apply eps0_lt_irrefl in Hab.
    + rewrite eps0_mpos_fix_0, eps0_mpos_fix_1; auto.
    + now apply eps0_not_head_split_lt_zero in Hab.
    + apply eps0_lt_head_split_inv in Hab; auto.
      rewrite !eps0_mpos_fix_1; auto.
      apply eps0_lt_head_split_inv; auto.
      destruct Hab as [ | (<- & [ | (<- & ?) ]) ]; auto.
      * right; split; auto; left.
        assert (i*m <= j*n); [ | lia ].
        apply Nat.mul_le_mono; lia.
      * destruct (eq_nat_dec m n) as [ -> | ? ]; auto.
        right; split; auto; left.
        assert (i*m <= i*n); [ | lia ].
        apply Nat.mul_le_mono; lia.
  Qed.

  Fact eps0_mpos_gt_zero a n : 0₀ <ε₀ a → 0₀ <ε₀ eps0_mpos a n.
  Proof.
    intros H.
    apply eps0_mpos_mono_left with (n := n) (m := n) in H; auto.
    now rewrite eps0_mpos_fix_0 in H.
  Qed.

  Hint Resolve eps0_mpos_mono_left eps0_mpos_gt_zero : core.

  Fact eps0_mpos_mono_right a n m : 0₀ <ε₀ a → n < m → eps0_mpos a n <ε₀ eps0_mpos a m.
  Proof.
    intros H1 H2.
    destruct a as [ | e i f H _ _ ] using eps0_head_rect.
    + now apply eps0_lt_irrefl in H1.
    + rewrite !eps0_mpos_fix_1; auto.
      apply eps0_lt_head_split_inv; auto.
      right; split; auto; left.
      assert (i*n <= i*m); [ | lia ].
      apply Nat.mul_le_mono_l; lia.
  Qed.

  Fact eps0_mpos_mono_right_le a n m : n ≤ m → eps0_mpos a n ≤ε₀ eps0_mpos a m.
  Proof.
    destruct (eq_nat_dec n m) as [ <- | ]; auto; intro.
    destruct (eps0_zero_or_pos a) as [ -> | ].
    + rewrite !eps0_mpos_fix_0; auto.
    + left; apply eps0_mpos_mono_right; auto; lia.
  Qed.

  Fact eps0_mpos_mono a b m n : a ≤ε₀ b → m ≤ n → eps0_mpos a m ≤ε₀ eps0_mpos b n.
  Proof.
    intros [ H1 | -> ].
    + left; now apply eps0_mpos_mono_left.
    + apply eps0_mpos_mono_right_le.
  Qed.

  Fact eps0_mpos_below_omega a n e : a <ε₀ ω^e → eps0_mpos a n <ε₀ ω^e.
  Proof.
    intros [ -> | (f & i & H1 & H2) ] %eps0_lt_omega_inv.
    + rewrite eps0_mpos_fix_0; auto.
    + apply eps0_mpos_mono_left with (n := n) (m := n) in H1; auto.
      apply eps0_lt_trans with (1 := H1).
      rewrite eps0_mpos_exp_S.
      apply eps0_lt_head_split_inv_both; auto.
  Qed.

  Fact eps0_mpos_below_omega' a n e i : a <ε₀ ω^⟨e,i⟩ → eps0_mpos a n <ε₀ ω^(S₀ e).
  Proof.
    intros H.
    apply eps0_mpos_below_omega,
          eps0_lt_trans with (1 := H),
          eps0_exp_S_mono_left; auto.
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
    + now intros ?%eps0_zero_neq_exp_S_add.
    + symm; now intros ?%eps0_zero_neq_exp_S_add.
    + intros (? & [])%eps0_head_split_uniq; subst; auto.
  Qed.

  Definition eps0_momega_pwc e α : sig (eps0_momega_gr α e).
  Proof.
    destruct e as [ | e ] using eps0_head_rect.
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

  Fact eps0_momega_exp_S γ n α : eps0_momega ω^⟨γ,n⟩ α = ω^(γ+₀α).
  Proof. rewrite <- (eps0_add_zero_right ω^⟨_,_⟩), eps0_momega_fix_1; auto. Qed.

  Fact eps0_momega_mpos a i e :
      0₀ <ε₀ e → eps0_momega (eps0_mpos a i) e = eps0_momega a e.
  Proof.
    intros He.
    destruct a using eps0_head_rect.
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
    destruct e using eps0_head_rect.
    + now rewrite !eps0_mpos_fix_0, eps0_add_zero_left.
    + rewrite !eps0_mpos_fix_1; auto.
      rewrite eps0_momega_fix_1; auto.
      rewrite !eps0_mpos_omega.
      rewrite <- (eps0_add_zero_right ω^⟨_,k⟩).
      rewrite eps0_add_head_lt; auto.
  Qed.

  Fact eps0_mpos_add_momega a e f i j :
      e <ε₀ f
    → eps0_mpos (eps0_momega a e) i +₀ eps0_mpos (eps0_momega a f) j
    = eps0_mpos (eps0_momega a f) j.
  Proof.
    intros Hef.
    destruct a using eps0_head_rect.
    + now rewrite !eps0_momega_fix_0, !eps0_mpos_fix_0, eps0_add_zero_left.
    + rewrite !eps0_momega_fix_1; auto.
      rewrite !eps0_mpos_omega, eps0_add_head_lt''; auto.
  Qed.

  Fact eps0_momega_mono_left a b c :
      a ≤ε₀ b
    → eps0_momega a c ≤ε₀ eps0_momega b c.
  Proof.
    intros [ Hab | <- ]; auto.
    destruct a as [ | e i f H1 _ _ ] using eps0_head_rect;
      destruct b as [ | g j h H2 _ _ ] using eps0_head_rect.
    + now apply eps0_lt_irrefl in Hab.
    + rewrite eps0_momega_fix_0, eps0_momega_fix_1; auto.
    + now apply eps0_zero_not_gt in Hab.
    + rewrite !eps0_momega_fix_1; auto.
      apply eps0_lt_head_split_inv in Hab; auto.
      apply eps0_omega_mono_le.
      destruct Hab as [ | (<- & _) ]; auto.
  Qed.

  Fact eps0_momega_mono_right a b c :
      0₀ <ε₀ a
    → b <ε₀ c 
    → eps0_momega a b <ε₀ eps0_momega a c.
  Proof.
    intros H ?.
    destruct a using eps0_head_rect.
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
    destruct a using eps0_head_rect.
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
    destruct a using eps0_head_rect.
    + now apply eps0_lt_irrefl in Ha.
    + rewrite eps0_mpos_fix_1, eps0_momega_fix_1; auto.
      apply eps0_lt_head_split_inv_right; auto.
  Qed.

  Fact eps0_momega_below_omega a b e f :
      a <ε₀ ω^e
    → b <ε₀ f
    → eps0_momega a b <ε₀ ω^(e +₀ f).
  Proof.
    intros [ -> | (g & i & H1 & H2) ]%eps0_lt_omega_inv Hb.
    + rewrite eps0_momega_fix_0; auto.
    + apply eps0_le_lt_trans with (eps0_momega ω^⟨g,i⟩ b).
      * apply eps0_momega_mono_left; auto.
      * rewrite eps0_momega_exp_S.
        apply eps0_omega_mono_lt.
        apply eps0_lt_le_trans with (g +₀ f); auto.
  Qed.

  Fact eps0_momega_below_exp_S a b e n f :
      a <ε₀ ω^⟨e,n⟩
    → b <ε₀ f
    → eps0_momega a b <ε₀ ω^(e +₀ f).
  Proof.
    intros [ [ -> | (i & c & -> & ? & ?) ] | (g & i & H1 & ?) ]%eps0_lt_exp_S_inv ?.
    + rewrite eps0_momega_fix_0; auto.
    + rewrite eps0_momega_fix_1; auto.
      apply eps0_omega_mono_lt; auto.
    + apply eps0_lt_le_weak, eps0_momega_mono_left with (c := b) in H1.
      apply eps0_le_lt_trans with (1 := H1).
      rewrite eps0_momega_exp_S; auto.
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
    + now intros ?%eps0_zero_neq_exp_S.
    + now intros ?%eps0_zero_neq_exp_S_add.
    + symm; now intros ?%eps0_zero_neq_exp_S.
    + now intros (_ & ->)%eps0_eps_S_uniq.
    + intros (<- & -> & ->)%eps0_head_split_uniq'; auto.
      contradict H2; apply eps0_lt_irrefl.
    + symm; now intros ?%eps0_zero_neq_head.
    + symm; intros (<- & -> & ->)%eps0_head_split_uniq'; auto.
      contradict H1; apply eps0_lt_irrefl.
    + intros (<- & <- & <-)%eps0_head_split_uniq; auto.
      f_equal; eauto.
  Qed.

  Definition eps0_mult_pwc γ e : sig (eps0_mult_gr γ e).
  Proof.
    induction e as [ | n | e n f He Hf _ (r & Hr) ] using eps0_head_pos_rect.
    + exists 0₀; constructor.
    + exists (eps0_mpos γ n); constructor.
    + exists (eps0_mpos (eps0_momega γ e) n +₀ r).
      now constructor.
  Qed.

  Definition eps0_mult e f := π₁ (eps0_mult_pwc e f).

  Infix "*₀" := eps0_mult.

  Fact eps0_mult_spec e f : eps0_mult_gr e f (e *₀ f).
  Proof. apply (proj2_sig _). Qed.

  Fact eps0_mult_zero_right a : a *₀ 0₀ = 0₀.
  Proof. apply eps0_mult_fun with (1 := eps0_mult_spec _ _) (3 := eq_refl); now constructor. Qed.

  Fact eps0_mult_pos_right a n : a *₀ ω^⟨0₀,n⟩ = eps0_mpos a n.
  Proof. apply eps0_mult_fun with (1 := eps0_mult_spec _ _) (3 := eq_refl); now constructor. Qed.

  Corollary eps0_mpos_eq a n : eps0_mpos a n = a *₀ ω^⟨0₀,n⟩.
  Proof. now rewrite eps0_mult_pos_right. Qed.

  Fact eps0_mult_head_right a e n f :
      0₀ <ε₀ e
    → f <ε₀ ω^e
    → a *₀ (ω^⟨e,n⟩ +₀ f)
    = eps0_mpos (eps0_momega a e) n +₀ a *₀ f.
  Proof.
    intros.
    apply eps0_mult_fun with (1 := eps0_mult_spec _ _) (3 := eq_refl); constructor; auto.
    apply eps0_mult_spec.
  Qed.

  (** This one is stronger because it does not need any relation between e and f *)
  Fact eps0_mult_right a e n f :
      0₀ <ε₀ e
    → a *₀ (ω^⟨e,n⟩ +₀ f)
    = eps0_mpos (eps0_momega a e) n +₀ a *₀ f.
  Proof.
    intros He.
    destruct f as [ | f i g H _ _ ] using eps0_head_rect.
    + rewrite eps0_mult_head_right; auto.
    + destruct (eps0_lt_sdec e f).
      * rewrite eps0_add_head_lt', eps0_mult_head_right,
             <- eps0_add_assoc, eps0_mpos_add_momega; auto.
        eapply eps0_lt_trans; eassumption.
      * rewrite eps0_add_head_eq', 
               !eps0_mult_head_right,
             <- eps0_add_assoc,
                eps0_mpos_plus; auto.
      * rewrite eps0_mult_head_right; auto.
        apply eps0_add_below_omega.
        - now apply eps0_exp_S_mono_left.
        - apply eps0_lt_trans with (1 := H),
                eps0_omega_mono_lt; auto.
  Qed.

  Fact eps0_mpos_momega_eq a n e :
      0₀ <ε₀ e
    → eps0_mpos (eps0_momega a e) n = a *₀ ω^⟨e,n⟩.
  Proof.
    intro.
    rewrite <- (eps0_add_zero_right ω^⟨_,_⟩),
                eps0_mult_right,
                eps0_mult_zero_right,
                eps0_add_zero_right; auto.
  Qed.

  Fact eps0_momega_eq a e :
      0₀ <ε₀ e
    → eps0_momega a e = a *₀ ω^e.
  Proof.
    intro; unfold eps0_omega.
    rewrite <- eps0_mpos_momega_eq, eps0_mpos_O; auto.
  Qed.

  Fact eps0_mult_zero_left e : 0₀ *₀ e = 0₀.
  Proof.
    induction e as [ | n | e n f He Hf _ IHf ] using eps0_head_pos_rect.
    + now rewrite eps0_mult_zero_right.
    + now rewrite eps0_mult_pos_right, eps0_mpos_fix_0.
    + rewrite eps0_mult_head_right, IHf; auto.
      now rewrite eps0_momega_fix_0, eps0_mpos_fix_0, eps0_add_zero_left.
  Qed.

  Fact eps0_mult_distr a b c : a *₀ (b +₀ c) = a *₀ b +₀ a *₀ c.
  Proof.
    induction b as [ | n | e n f He Hf IHe IHf ] in a, c |- *
      using eps0_head_pos_rect.
    + now rewrite  eps0_mult_zero_right, !eps0_add_zero_left.
    + destruct c as [ | k | c k g ? ? _ _ ] using eps0_head_pos_rect.
      * now rewrite eps0_mult_zero_right, !eps0_add_zero_right.
      * now rewrite eps0_add_exp_S, !eps0_mult_pos_right, eps0_mpos_plus.
      * rewrite eps0_add_head_lt',
                eps0_mult_head_right,
                eps0_mult_pos_right,
             <- eps0_add_assoc,
                eps0_add_mpos_momega; auto.
    + rewrite eps0_mult_right,
             !eps0_add_assoc,
           <- IHf, eps0_mult_right; auto.
  Qed.

  Fact eps0_mult_gt_zero a e :
      0₀ <ε₀ a → 0₀ <ε₀ e → 0₀ <ε₀ a *₀ e.
  Proof.
    intros Ha He.
    induction e as [ | n | e n f H1 H2 IH1 IH2 ] using eps0_head_pos_rect.
    + now apply eps0_lt_irrefl in He.
    + rewrite eps0_mult_pos_right; now apply eps0_mpos_gt_zero.
    + rewrite eps0_mult_right; auto.
      destruct (eps0_zero_or_pos f) as [ -> | Hf ].
      * rewrite eps0_mult_zero_right, eps0_add_zero_right.
        apply eps0_mpos_gt_zero.
        apply eps0_lt_le_trans with (2 := eps0_momega_lt_pos Ha H1); auto.
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
    induction e as [ | n | e n g H1 IH1 IH2 ] using eps0_head_pos_rect.
    + rewrite !eps0_mult_zero_right; auto.
    + rewrite !eps0_mult_pos_right.
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
    intros [ H1 | <- ] [ H2 | <- ].
    + apply eps0_le_trans with (a *₀ f).
      * left; apply eps0_mult_mono_right; auto.
      * now apply eps0_mult_mono_left.
    + now apply eps0_mult_mono_left.
    + left; now apply eps0_mult_mono_right.
    + now right.
  Qed.

  Fact eps0_mult_head a i b e j f :
      0₀ <ε₀ e
    → b <ε₀ ω^a
    → f <ε₀ ω^e
    → (ω^⟨a,i⟩ +₀ b) *₀ (ω^⟨e,j⟩ +₀ f)
     = ω^⟨a+₀e,j⟩ +₀ (ω^⟨a,i⟩ +₀ b) *₀ f.
  Proof.
    intros; rewrite eps0_mult_right, eps0_momega_fix_1, eps0_mpos_omega; auto.
  Qed.

  Fact eps0_mult_head_exp_S a i b e j :
      0₀ <ε₀ e → b <ε₀ ω^a → (ω^⟨a,i⟩ +₀ b) *₀ ω^⟨e,j⟩ = ω^⟨a+₀e,j⟩.
  Proof.
    intros H1 H2.
    rewrite <- (eps0_add_zero_right ω^⟨_,j⟩), eps0_mult_head; auto.
    now rewrite eps0_mult_zero_right, eps0_add_zero_right.
  Qed.

  Fact eps0_mult_exp_S_head a i e j f : 
      0₀ <ε₀ e
    → f <ε₀ ω^e
    → ω^⟨a,i⟩ *₀ (ω^⟨e,j⟩ +₀ f)
    = ω^⟨a+₀e,j⟩ +₀ ω^⟨a,i⟩ *₀ f.
  Proof. intros; rewrite <- (eps0_add_zero_right ω^⟨_,i⟩), eps0_mult_head; auto. Qed.

  Fact eps0_mult_exp_S_pos e i j : ω^⟨e,i⟩ *₀ ω^⟨0₀,j⟩ = ω^⟨e,i*j+i+j⟩.
  Proof. now rewrite eps0_mult_pos_right, eps0_mpos_exp_S. Qed.

  Fact eps0_mult_exp_S e i f j : 0₀ <ε₀ f → ω^⟨e,i⟩ *₀ ω^⟨f,j⟩ = ω^⟨e+₀f,j⟩.
  Proof. intro; rewrite <- (eps0_add_zero_right ω^⟨e,i⟩), eps0_mult_head_exp_S; auto. Qed.

  Fact eps0_mult_exp_S_omega e i f : 0₀ <ε₀ f → ω^⟨e,i⟩ *₀ ω^f = ω^(e+₀f).
  Proof. intro; apply eps0_mult_exp_S; auto. Qed.

  Fact eps0_mult_omega_exp_S e f n: ω^e *₀ ω^⟨f,n⟩ = ω^⟨e+₀f,n⟩.
  Proof.
    unfold eps0_omega.
    destruct (eps0_zero_or_pos f) as [ -> | ].
    + now rewrite eps0_mult_exp_S_pos, eps0_add_zero_right.
    + rewrite eps0_mult_exp_S; auto.
  Qed.

  Fact eps0_mult_omega e f : ω^e *₀ ω^f = ω^(e+₀f).
  Proof. apply eps0_mult_omega_exp_S. Qed.

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
      * apply eps0_lt_one in H2 as ->.
        rewrite eps0_mult_zero_right; auto.
      * rewrite <- eps0_mult_exp_S_omega with (i := n); auto.
        apply eps0_mult_mono_right; auto.
  Qed.

  Remark eps0_mult_below_omega_1 a b e f : 
      a <ε₀ ω^e → b <ε₀ ω^f → a *₀ b <ε₀ ω^(e+₀f).
  Proof. apply eps0_mult_below_omega. Qed.

  Fact eps0_mult_mpos a b n : eps0_mpos (a *₀ b) n = a *₀ eps0_mpos b n. 
  Proof.
    induction b using eps0_head_pos_rect in a, n |- *.
    + now rewrite eps0_mult_zero_right, eps0_mpos_fix_0, eps0_mult_zero_right.
    + now rewrite eps0_mpos_exp_S, !eps0_mult_pos_right, eps0_mpos_mult.
    + rewrite eps0_mult_distr.
      destruct a as [ | ] using eps0_head_rect.
      * now rewrite !eps0_mult_zero_left, eps0_add_zero_left, eps0_mpos_fix_0.
      * rewrite eps0_mult_head_exp_S, !eps0_mpos_fix_1; auto.
        - rewrite eps0_mult_distr, eps0_mult_head_exp_S; auto.
        - apply eps0_mult_below_omega with (n := i0+0+1); auto.
          rewrite <- eps0_add_exp_S; auto.
  Qed.

  (** This one was a long shot !! 
      induction on c and case analysis on b and a *)
  Theorem eps0_mult_assoc a b c : a *₀ (b *₀ c) = (a *₀ b) *₀ c.
  Proof.
    induction c as [ | n | e n f He Hf IHe IHf ]
      in a, b |- * using eps0_head_pos_rect.
    + now rewrite !eps0_mult_zero_right.
    + now rewrite !eps0_mult_pos_right, eps0_mult_mpos.
    + destruct b as [ | i | g i h Hg Hh _ ] using eps0_head_pos_rect.
      * rewrite eps0_mult_zero_left,
               !eps0_mult_zero_right,
                eps0_mult_zero_left; auto.
      * rewrite eps0_mult_exp_S_head,
                eps0_add_zero_left, 
               !eps0_mult_distr,
                IHf,
                eps0_mult_pos_right,
            <- !eps0_mpos_momega_eq,
                eps0_momega_mpos; auto.
      * rewrite eps0_mult_head, eps0_mult_distr, IHf; auto.
        destruct a as [ | u j v Hu _ _ ] using eps0_head_rect.
        - now rewrite !eps0_mult_zero_left, eps0_add_zero_left.
        - rewrite eps0_mult_head_exp_S; auto.
          2: apply eps0_lt_le_trans with (1 := He); auto.
          rewrite !eps0_mult_head, eps0_add_assoc; auto.
          apply eps0_mult_below_omega with (n := S j); auto.
          apply eps0_lt_le_trans with (ω^⟨u,j⟩ +₀ ω^u); auto.
          unfold eps0_omega; rewrite eps0_add_exp_S.
          right; f_equal; lia.
  Qed.

  Fact eps0_mult_one_left e : 1₀ *₀ e = e.
  Proof.
    rewrite <- eps0_omega_zero.
    induction e using eps0_head_pos_rect.
    + now rewrite eps0_mult_zero_right.
    + now rewrite eps0_mult_pos_right, eps0_mpos_omega.
    + unfold eps0_omega.
      rewrite eps0_mult_exp_S_head, eps0_add_zero_left; auto.
      f_equal; auto.
  Qed.

  Fact eps0_mult_one_right e : e *₀ 1₀ = e.
  Proof.
    rewrite <- eps0_omega_zero; unfold eps0_omega.
    now rewrite eps0_mult_pos_right, eps0_mpos_O.
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
  *)

  Inductive eps0_expo_gr α : ε₀ → ε₀ → Prop :=
    | eps0_expr_gr_0 : eps0_expo_gr α 0₀ 0₀
    | eps0_expr_gr_1 γ n β : β <ε₀ ω^γ → eps0_expo_gr α (ω^⟨γ,n⟩ +₀ β) ω^(γ*₀α).

  Fact eps0_expo_fun α e1 f1 e2 f2 :
    eps0_expo_gr α e1 f1 → eps0_expo_gr α e2 f2 → e1 = e2 → f1 = f2.
  Proof.
    intros [] []; auto.
    + now intros ?%eps0_zero_neq_head.
    + symm; now intros ?%eps0_zero_neq_head.
    + intros (<- & <- & <-)%eps0_head_split_uniq; auto.
  Qed. 

  Definition eps0_expo_pwc e α : sig (eps0_expo_gr α e).
  Proof.
    destruct e as [ | e ] using eps0_head_rect.
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

(** For the fundemental sequence *)

Fact eps0_add_lt_omega : ∀ a e, a <ε₀ ω^e → a +₀ ω^e = ω^e.
Proof.
  intros a e.
  destruct (eps0_zero_or_pos e) as [ -> | He ].
  + intros Ha.
    rewrite eps0_omega_zero in Ha.
    apply eps0_lt_one in Ha as ->.
    now rewrite eps0_add_zero_left.
  + revert a e He.
    intros [a Ha] [e He] He' H.
    apply eps0_eq_iff; simpl in H |- *.
    revert H; apply E0_add_lt_omega; auto.
    intros ->.
    revert He'; apply E0_lt_irrefl.
Qed.

Lemma eps0_add_omega_fun_right : ∀ a b e f, a +₀ ω^e = b +₀ ω^f → e = f.
Proof.
  intros [] [] [] []; rewrite !eps0_eq_iff; simpl.
  apply E0_add_omega_fun_right.
Qed.

(* a +₀ ω^e is the limit decomposition of that ordinal
 - e is unique 
 - but a is not and we choose the least one *)
Definition eps0_least_split a e  :=
    ∀b, a +₀ ω^e = b +₀ ω^e → a ≤ε₀ b.
    
Fact eps0_split_least_uniq :
  ∀ a b e f,
      eps0_least_split a e
    → eps0_least_split b f
    → a +₀ ω^e = b +₀ ω^f
    → a = b ∧ e = f.
Proof.
  intros a b e f H1 H2 E.
  assert (e = f) as <-; auto.
  1: now apply eps0_add_omega_fun_right in E.
Qed.

Fact eps0_one_eq_least_split a e :
    eps0_least_split a e
  → 1₀ = a +₀ ω^e
  → a = 0₀ ∧ e = 0₀.
Proof.
  intros H1.
  replace 1₀ with (0₀ +₀ ω^0₀).
  + intros (<- & <-)%eps0_split_least_uniq; eauto.
    red; eauto.
  + now rewrite eps0_add_zero_left, eps0_omega_zero.
Qed.

Fact eps0_omega_eq_least_split a b e :
    eps0_least_split b e
  → ω^a = b +₀ ω^e
  → b = 0₀ ∧ a = e.
Proof.
  intros H.
  rewrite <- (eps0_add_zero_left ω^a).
  intros (<- & <-)%eps0_split_least_uniq; auto.
  red; auto.
Qed.

(* Hence a successor is not a limit ordinal 

   Successor is of shape ω[_++[(ω[[]],1+i)]]
   Limit is either ω[[]] or ω[_++[(x,i)]] with 0 < i and x <> ω[[]] *)

Definition eps0_is_succ e := ∃f, e = S₀ f.

Fact eps0_is_succ_S e : eps0_is_succ (S₀ e).
Proof. now exists e. Qed.

Hint Resolve eps0_is_succ_S : core.

Fact eps0_is_succ_iff e : eps0_is_succ e ↔ E0_is_succ (π₁ e).
Proof.
  split.
  + intros ((f & ?) & ->); exists f; auto.
  + intros (f & H1 & H2); exists (exist _ f H2).
    apply eps0_eq_iff; now rewrite H1.
Qed.

Fact eps0_is_succ_exp_S n : eps0_is_succ ω^⟨0₀,n⟩.
Proof.
  destruct n as [ | n ].
  + exists 0₀. rewrite eps0_succ_zero_is_one; apply eps0_omega_zero.
  + exists ω^⟨0₀,n⟩; now rewrite eps0_succ_exp_S.
Qed.

Hint Resolve eps0_is_succ_exp_S : core.

Definition eps0_is_limit e := e ≠ 0₀ ∧ ¬ eps0_is_succ e.

Fact eps0_is_limit_iff e : eps0_is_limit e ↔ E0_is_limit (π₁ e).
Proof.
  split; intros (H1 & H2); split.
  + contradict H1; subst; now apply eps0_eq_iff.
  + contradict H2; destruct H2 as (f & H2 & H3).
    exists (exist _ f H3); now apply eps0_eq_iff.
  + contradict H1; now apply eps0_eq_iff in H1.
  + contradict H2; destruct H2 as ((f & Hf) & ->); now exists f.
Qed.

Fact eps0_add_is_limit a e : eps0_is_limit e → eps0_is_limit (a +₀ e).
Proof.
  rewrite !eps0_is_limit_iff.
  destruct a; destruct e; apply E0_add_is_limit; auto.
Qed.

Fact eps0_add_is_limit_inv a e :
    eps0_is_limit (a +₀ e)
  → e = 0₀ ∧ eps0_is_limit a ∨ eps0_is_limit e.
Proof.
  rewrite !eps0_is_limit_iff.
  revert a e; intros (a & Ha) (e & He); simpl; intros H.
  destruct E0_add_is_limit_inv with (3 := H)
    as [ -> | ]; auto.
  left; rewrite eps0_eq_iff; split; auto.
  now rewrite E0_add_zero_right in H.
Qed.

Fact eps0_add_is_limit_lt_inv a e :
    eps0_is_limit (a +₀ e)
  → 0₀ <ε₀ e
  → eps0_is_limit e.
Proof.
  intros [(-> & _) | ]%eps0_add_is_limit_inv; auto.
  now intros ?%eps0_lt_irrefl.
Qed.

Fact eps0_is_limit_exp_S e n : e ≠ 0₀ → eps0_is_limit ω^⟨e,n⟩.
Proof.
  intros H.
  apply eps0_is_limit_iff.
  destruct e; simpl.
  apply E0_exp_is_limit; auto.
  + contradict H; now apply eps0_eq_iff.
  + lia.
Qed.

Fact eps0_is_limit_omega e : e ≠ 0₀ → eps0_is_limit ω^e.
Proof. apply eps0_is_limit_exp_S. Qed.

Fact eps0_is_limit_add_omega a e : e ≠ 0₀ → eps0_is_limit (a +₀ ω^e).
Proof. intro; apply eps0_add_is_limit, eps0_is_limit_omega; auto. Qed.

Fact eps0_add_omega_not_zero a e : 0₀ ≠ a +₀ ω^e.
Proof.
  intros H.
  apply (@eps0_lt_irrefl (a+₀ω^e)).
  rewrite <- H at 1.
  apply eps0_lt_le_trans with (1 := eps0_zero_lt_omega e).
  rewrite <- (eps0_add_zero_left ω^e) at 1.
  apply eps0_add_mono_left, eps0_zero_least.
Qed.
Fact eps0_add_omega_not_succ a b e : e ≠ 0₀ → S₀ a ≠ b +₀ ω^e.
Proof.
  intros E H.
  assert (eps0_is_limit (S₀ a)) as [ _ [] ]; eauto.
  rewrite H.
  now apply eps0_is_limit_add_omega.
Qed.

Fact eps0_succ_eq_add_omega a b e : S₀ a = b +₀ ω^e → e = 0₀.
Proof.
  intros H.
  destruct (eps0_eq_dec e 0₀); auto.
  now apply eps0_add_omega_not_succ in H.
Qed.

Fact eps0_succ_eq_omega a e : S₀ a = ω^e → e = 0₀.
Proof.
  rewrite <- (eps0_add_zero_left ω^e).
  apply eps0_succ_eq_add_omega.
Qed.

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
    destruct e as (e & He); revert e He; apply cnf_add_rect.
    + intro; eapply eps0_pirr with (1 := eq_refl), HP0.
    + intros e he h H; eapply eps0_pirr with (1 := eq_refl), (HP1 H).
    + intros g e hg he h H1 H2 H3 H4.
      eapply eps0_pirr with (1 := eq_refl).
      apply HP2 with (3 := H3) (4 := H4).
      * now intros ?%eps0_eq_iff.
      * intros []; rewrite !eps0_eq_iff, eps0_le_iff; simpl; auto.
  Qed.

End eps0_tail_rect.

Section eps0_discriminate.

  Variables (P : ε₀ → Type)
            (HP0 : P 0₀)
            (HP1 : ∀ e, P (S₀ e))
            (HP2 : ∀ e, eps0_is_limit e → P e).
            
  Theorem eps0_discriminate e : P e.
  Proof.
    destruct e as [ | | g e H1 H2 _ _] using eps0_tail_rect; auto.
    apply HP2, eps0_is_limit_add_omega; auto.
  Qed.
  
End eps0_discriminate.

Fact eps0_least_split_find e : eps0_is_limit e → { a : _ & { g | e = a+₀ω^g ∧ g ≠ 0₀ ∧ eps0_least_split a g } }.
Proof.
  destruct e as [ | | a g H1 H2 _ _ ] using eps0_tail_rect.
  + now intros [ [] _ ].
  + intros [ _ [] ]; auto.
  + exists a, g; auto.
Qed.

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

Hint Resolve eps0_is_limit_exp_S eps0_is_limit_omega 
             eps0_add_is_limit : core.

Lemma eps0_fseq_gr_fun e r r' : eps0_fseq_gr e r → eps0_fseq_gr e r' → ∀n, r n = r' n.
Proof. intros H1 H2; now apply (eps0_fseq_gr_fun_rec H1 H2). Qed.

Section eps0_fseq_rect.

  Variables (P : forall e, eps0_is_limit e → Type)
            (HP0 : ∀ g e l, eps0_least_split g (S₀ e) → @P (g +₀ ω^(S₀ e)) l)
            (HP1 : ∀ g e l l', eps0_least_split g e → @P e l → @P (g +₀ ω^e) l').

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

Fact eps0_fseq_omega_succ e (l : eps0_is_limit ω^(S₀ e)) n :
    eps0_fseq l n = ω^⟨e,n⟩.
Proof.
  revert l; rewrite <- (eps0_add_zero_left ω^_); intros l.
  rewrite eps0_fseq_fix_0.
  + now rewrite eps0_add_zero_left.
  + red; auto.
Qed.

Fact eps0_fseq_omega_limit e (l : eps0_is_limit ω^e) (l' : eps0_is_limit e) n :
    eps0_fseq l n = ω^(eps0_fseq l' n).
Proof.
  revert l; rewrite <- (eps0_add_zero_left ω^_); intros l.
  rewrite eps0_fseq_fix_1 with (l' := l').
  + now rewrite eps0_add_zero_left.
  + red; auto.
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
    apply eps0_exp_S_inj, proj2 in Hb; lia.
  + rewrite eps0_add_lt_omega in Hb; auto.
    * now apply eps0_exp_S_inj, proj2 in Hb.
    * now apply eps0_lt_trans with (1 := H1),
                eps0_exp_S_mono_left.
Qed.

Fact eps0_fseq_exp_S_succ e k (l : eps0_is_limit ω^⟨S₀ e,S k⟩) n :
    eps0_fseq l n = ω^⟨S₀ e,k⟩ +₀ ω^⟨e,n⟩.
Proof.
  revert l; rewrite <- eps0_add_exp_S_omega; intros l.
  rewrite eps0_fseq_fix_0; auto.
  apply eps0_exp_S_least_split.
Qed.

Fact eps0_fseq_exp_S_limit e i (l : eps0_is_limit ω^⟨e,S i⟩) (l' : eps0_is_limit e) n :
    eps0_fseq l n = ω^⟨e,i⟩ +₀ ω^(eps0_fseq l' n).
Proof.
  revert l; rewrite <- eps0_add_exp_S_omega; intros l.
  rewrite eps0_fseq_fix_1 with (l' := l'); auto.
  apply eps0_exp_S_least_split.
Qed.

(* Another computation for fseq :
     fseq (ω^e.i +₀ f) n = ω^e.i + fseq f n
   when f < ω^e *)
Lemma eps0_fseq_head e i f (l : eps0_is_limit (ω^⟨e,i⟩ +₀ f)) (l' : eps0_is_limit f) n :
    f <ε₀ ω^e → eps0_fseq l n = ω^⟨e,i⟩ +₀ eps0_fseq l' n.
Proof.
  intros Hf; revert l.
  induction l' as [ g j h | ] using eps0_fseq_rect; rewrite <- eps0_add_assoc; intros l.
  + rewrite !eps0_fseq_fix_0; auto.
    * now rewrite eps0_add_assoc.
    * apply eps0_head_least_split; auto;
        apply eps0_le_lt_trans with (2 := Hf); auto.
  + rewrite !eps0_fseq_fix_1 with (l' := l'1); auto.
    * now rewrite eps0_add_assoc.
    * apply eps0_head_least_split; auto;
        apply eps0_le_lt_trans with (2 := Hf); auto.
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

Section upper_bound.

  Variables (X : Type) (R : X → X → Prop).
  
  Implicit Type (P : X → Prop).

  Definition ub P u := ∀x, P x → R x u.
  Definition lub P u := ub P u ∧ ∀v, ub P v → R u v.
  
  Fact ub_mono P Q : (∀x, P x → Q x) → ∀u, ub Q u → ub P u.
  Proof. intros H ? ? ? ?%H; auto. Qed.
  
  Fact lub_uniq P u v : lub P u → lub P v → R u v ∧ R v u.
  Proof.
    intros H1 H2; split.
    + apply H1, H2.
    + apply H2, H1.
  Qed.

  Hypothesis (R_refl : reflexive _ R)
             (R_trans : transitive R).

  Fact lub_iff P u : lub P u ↔ ∀v, ub P v ↔ R u v.
  Proof.
    split.
    + intros Hu v; split.
      * apply Hu.
      * intros Huv x Hx.
        now apply R_trans with (2 := Huv), Hu.
    + intros Hu; split.
      * apply Hu, R_refl.
      * intro; apply Hu.
  Qed.
  
End upper_bound.

(* for a limit ordinal e, it is the ≤ε₀-lub of its fundemental sequence *) 
Theorem eps0_fseq_lub e l : lub eps0_le (λ x, ∃n, x = @eps0_fseq e l n) e.
Proof.
  split.
  + intros x (n & ->); left; apply eps0_fseq_lt.
  + intros u Hu.
    destruct (eps0_lt_sdec u e) as [ x e H | | ].
    2,3: red; auto.
    apply eps0_lt_fseq_inv with (l := l) in H as (n & Hn); auto.
    exfalso.
    apply (@eps0_lt_irrefl x).
    apply eps0_lt_le_trans with (1 := Hn); eauto.
Qed.

(* A limit ordinal is the ≤ε₀-lub of <ε₀-smaller ordinals.
   This is also the case of 0₀. But of course, this is not
   the case for successor ordinals *)
Theorem eps0_is_limit_lub e : eps0_is_limit e → lub eps0_le (λ x, x <ε₀ e) e.
Proof.
  intros l; split.
  + now left.
  + intros v Hv.
    destruct (eps0_le_lt_dec e v) as [ | C ]; auto; exfalso.
    apply eps0_lt_fseq_inv with (l := l) in C as (n & Hn).
    apply (@eps0_lt_irrefl v).
    apply eps0_lt_le_trans with (1 := Hn), Hv.
    apply eps0_fseq_lt.
Qed.

(* For a successor ordinal S₀ e, the lub of its <ε₀-smaller ordinals
   is e (and not S₀ e). *)
Theorem eps0_is_succ_lub e : lub eps0_le (λ x, x <ε₀ S₀ e) e.
Proof.
  split.
  + now intros ? ?%eps0_succ_next_inv.
  + intros v Hv; apply Hv, eps0_lt_succ.
Qed.

(** Addition respects the limit *)
Theorem eps0_add_lub e u :
    eps0_is_limit u
  → lub eps0_le (λ x, ∃v, x = e +₀ v ∧ v <ε₀ u) (e +₀ u).
Proof.
  intros l.
  split.
  + intros ? (v & -> & Hv).
    left; now apply eps0_add_mono_right.
  + intros v Hv.
    red in Hv.
    destruct (eps0_le_lt_dec (e +₀ u) v) as [ |H1]; auto; exfalso.
    apply eps0_lt_add_inv_add in H1 as [ H1 | (g & -> & Hg) ].
    * apply (@eps0_lt_irrefl v).
      apply eps0_lt_le_trans with (1 := H1), Hv.
      exists 0₀; split.
      - now rewrite eps0_add_zero_right.
      - destruct (eps0_zero_or_pos u) as [ C%l | ]; now auto.
    * apply eps0_lt_fseq_inv with (l := l) in Hg as (n & Hn).
      destruct (@eps0_lt_irrefl g).
      apply eps0_lt_le_trans with (1 := Hn).
      apply eps0_add_le_cancel with e, Hv.
      exists (eps0_fseq l n); split; auto.
      apply eps0_fseq_lt.
Qed.

(** a.0 = 0
    a.(w^e.n+b) = (a.w^e).n + a.b

    a.w^0. *)

Check eps0_mpos_fix_1.

(** mpos does not respects limits 
    (w.2).2 = w.4
    but ordinals below w.2 are below some w.1+n
    and (w.1+n).2 = w.2+n < w.3 hence
    lub {v.2 | v < w.2 } = w.3 < w.4 *)

(** does eps0_momega e f = e.w^f respect limits *)

(** e*0 = e
    e*n = eps0_mpos e n but n is not limit
    e*(w^f.n+b) = (e.w^f).n + e*b

    if b is not zero then b is limit
    and we can approach b from below 
    and continuity applies recursively to e*b.

    otherwise if b is zero
   
    e.w^⟨f,n⟩ with 0 < f
    how can we approach w^⟨f,n⟩ ?
    if n = 0


    (ω^⟨a,i⟩ +₀ b) *₀ ω^⟨f,n⟩ = ω^⟨a+₀f,n⟩

     (ω^⟨a,i⟩ +₀ b) *₀ (ω^⟨f,n⟩ +₀ g)
       = ω^⟨a+₀f,n⟩ +₀ (ω^⟨a,i⟩ +₀ b) *₀ g


    Check forall n, exists m > n,
         fseq (a*e) m = a*(fseq e m) 

    Let u < a*e
    then exists n, u < fseq (a*e) n < a*e
    then exists m > n, u < a*fseq e m < e*e

 .

    w.w.1 = w² *)

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


Check eps0_least_split_find.

(* We need to show a strong property of the fundemental sequence wrt. mult 
   maybe even identity ? 

   Since (ω^⟨a,i⟩ +₀ b) *₀ e = ω^a *₀ e when e is a limit ordinal,

   we just need to show that lim ω^a *₀ fseq e n = ω^a *₀ e

   e = w^i₁.n1 + ... + w^iₓ.nₓ  i1 > ... > ix > 0
   

   w^a.e = w^(a+i₁).n1 + ... + w^(a+iₓ).nₓ

*)

(* g + w^e is a least split if g is minimal for this value 
   meaning g is either 
       of the form _ + w^e 
       or the form _ + w^f with f > e
       or 0 *)

Fact eps0_least_split_iff g e :
    eps0_least_split g e
  <-> g = 0₀ \/ exists a f, e ≤ε₀ f /\ g = a +₀ ω^f.
Proof.
Admitted.

Fact eps0_least_split_add a g e :
    g ≠ 0₀
 -> eps0_least_split g e 
 -> eps0_least_split (a +₀ g) e.
Proof.
  rewrite !eps0_least_split_iff.
  intros Hg [ -> | (b & f & H & ->) ].
  + easy.
  + right.
    exists (a+₀b), f; split; auto.
    now rewrite eps0_add_assoc.
Qed.

(*
Section eps0_is_limit_rect.

  Variables (P : ∀ e, eps0_is_limit e → Type)
            (HP0 : ∀ e l, @P ω^(S₀ e) l)
            (HP1 : ∀ e l l', @P e l → @P ω^e l')
            (HP2 : ∀ e n g l l', 0₀ <ε₀ g → g <ε₀ ω^e → @P g l → @P (ω^⟨e,n⟩ +₀ g) l').
  
  Theorem eps0_is_limit_rect e l : @P e l.
  Proof.
    revert l.
    induction e as [ e IH ] using (well_founded_induction_type wf_eps0_lt).
    destruct e as [ | e n f H _ _ ] using eps0_head_rect.
    + intros l; exfalso; now apply (proj1 l).
    + destruct (eps0_zero_or_pos f) as [ -> | ].
      * rewrite eps0_add_zero_right.
        destruct e as [ | e | e He ] using eps0_discriminate.
        - intros l; exfalso; apply (proj2 l); auto.
        - intros l. apply HP0.

*)

Check eps0_discriminate.

(** fseq (a+e) n <= a+fseq e n < a + e 
    is enough to show that a+fseq e n ~~> a+e 
    
    fseq (a+e) 
    
      e = 0 non
      e = S _ no
      e = w^f.n (0 < f)
      e = w^f.n + g with is_limit g and g < w^f
      
      a = 0
      a = w^b.i + c with c < w^b
      
      a = w^b.i + c with c < w^b,
      e = w^f.n
      
      -> if b < f then a + e = e
         if b = f then a + e = w^f(i+n)
         if b > f then a + e = w^b.i + (c+w^f.n) with c+b < w^b
      
      a = w^b.i + c with c < w^b,
      e = w^f.n + g with g < w^f and is_limit g
      
      -> if b < f then a + e = e
         if b = f then a + e = w^f.(i+n) + g
         if b > f then a + e = w^b.i + (c+e) with c+e < w^b

    *)

(** Notice that fseq (w³+w) n FIND COUNTER EXAMPLE of identity *) 
Theorem eps0_fseq_add a e (le : eps0_is_limit e) (lae : eps0_is_limit (a+₀e)) :
   ∀n, eps0_fseq lae n ≤ε₀ a +₀ eps0_fseq le n.
Proof.
  revert e le lae.
  induction a as [ | b i c Hc _ IH1 ] using eps0_head_rect.
  + intro e; rewrite (eps0_add_zero_left e).
    intros; rewrite eps0_add_zero_left; auto.
    right; apply eps0_fseq_pirr.
  + intros e; destruct e as [ | f n g Hg IH2 IH3 ] using eps0_head_rect.
    1: intros l; exfalso; now apply (proj1 l).
    intros le.
    destruct (eps0_lt_sdec b f) as [ b f Hbf | f | b f Hbf ].
    * rewrite eps0_add_head_lt; auto.
      intros lae j.
      rewrite (eps0_fseq_pirr le lae); auto.
    * rewrite eps0_add_head_eq; auto.
      replace (i+n+1) with (S (i+n)) by lia.
      revert le.
      destruct (eps0_zero_or_pos g) as [ -> | Hg' ].
      - rewrite !eps0_add_zero_right.
        intros le lae m.
        destruct f as [ | f | f Hf ] using eps0_discriminate.
        ++ exfalso; apply (proj2 le); auto.
        ++ rewrite eps0_fseq_exp_S_succ.
           destruct n.
           ** fold ω^(S₀ f) in le |- *.
              rewrite eps0_fseq_omega_succ.
              replace (i+0) with i by lia; auto.
           ** rewrite eps0_fseq_exp_S_succ.
              replace (i+S n) with (i+n+1) by lia.
              rewrite <- eps0_add_exp_S, eps0_add_assoc; auto.
        ++ rewrite eps0_fseq_exp_S_limit with (l' := Hf).
           destruct n as [ | n ].
           ** fold ω^f in le |- *.
              rewrite eps0_fseq_omega_limit with (l' := Hf).
              replace (i+0) with i by lia; auto.
           ** rewrite eps0_fseq_exp_S_limit with (l' := Hf).
              replace (i+S n) with (i+n+1) by lia.
              rewrite <- eps0_add_exp_S, eps0_add_assoc; auto.
      - intros.
        generalize (eps0_add_is_limit_lt_inv _ le Hg'); intros Hg''.
        rewrite !eps0_fseq_head with (l' := Hg''); auto.
        replace (S (i+n)) with (i+n+1) by lia.
        rewrite <- eps0_add_assoc, <- eps0_add_exp_S; auto.
    * rewrite  eps0_add_assoc.
      intros lae m.
      (* case f = 0 then g = 0 then ω^⟨f,n⟩ is not limit
         case f > 0 and g = 0 *)
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

(** fseq (a*e) n <= a*fseq e n < a*e 
    is enough to show that a*fseq e n ~~> a*e *)

Theorem eps0_fseq_mult a e (le : eps0_is_limit e) (lae : eps0_is_limit (ω^a*₀e)) :
   ∀n, eps0_fseq lae n = ω^a *₀ eps0_fseq le n.
Proof.
  revert lae.
  induction le as [ g e le H | g e le l' H IH ]using eps0_fseq_rect.
  + rewrite eps0_mult_distr, eps0_mult_omega, eps0_add_succ_right.
    intros lae n.
    rewrite !eps0_fseq_fix_0, eps0_mult_distr, eps0_mult_omega_exp_S; auto.
    admit.
  + rewrite eps0_mult_distr, eps0_mult_omega.
    intros lae n.
    rewrite eps0_fseq_fix_1 with (l' := le); auto.
    assert (l'' : eps0_is_limit (a+₀e)) by auto.
    rewrite eps0_fseq_fix_1 with (l' := l''); auto.
    * rewrite eps0_mult_distr; f_equal.
      rewrite eps0_mult_omega.
      f_equal.
      apply eps0_fseq_add.
    *
    unfold eps0_omega; rewrite eps0_mult_exp_S; auto.
    
    rewrite eps0_fseq_fix_1.
    


Check eps0_mult_exp_S_head.
Theorem eps0_fseq_mult a e (le : eps0_is_limit e) (lae : eps0_is_limit (a*₀e)) :
   ∀n, ∃m, n ≤ m ∧ eps0_fseq lae m = a*₀eps0_fseq le m.
Proof.
  (* tail induction on e is what we want to do here to be able to use
     fixpoint equations for fseq, that we need to show anyway !! *)
Admitted.
  



Definition is_lub {X} (R : X → X → Prop) (P : X → Prop) u := ∀v, (∀x, P x → R x v) ↔ R u v.

(* for a limit ordinal e, it is the ≤ε₀-lub of its fundemental sequence *) 
Theorem eps0_fseq_is_lub e l : is_lub eps0_le (λ x, ∃n, x = @eps0_fseq e l n) e.
Proof.
  intros x; split.
  + intros Hx.
    destruct (eps0_lt_sdec x e) as [ x e H | | ].
    2,3: red; auto.
    apply eps0_lt_fseq_inv with (l := l) in H as (n & Hn); auto.
    exfalso.
    apply (@eps0_lt_irrefl x).
    apply eps0_lt_le_trans with (1 := Hn), Hx; eauto.
  + intros H y (n & ->); left.
    apply eps0_lt_le_trans with (2 := H), eps0_fseq_lt.
Qed.

Section Fast_Growing_Hierarchy.

  (** Construction of the Grzegorczyk Fast Growing Hierarchy 

      F 0₀ n      := S n             for 0₀
      F (S₀ e) n  := (F e)^{S n} n   for a successor ordinal
      F λ n       := F λ[n] n        for a limit ordinal, using the fund. seq. λ[_]

      We specify it as a relation between ε₀ and nat → nat

  *)

  Inductive fgh_gr : ε₀ → (nat → nat) → Prop :=
    | fgh_gr_0       : fgh_gr 0₀ S
    | fgh_gr_1 e F   : fgh_gr e F
                     → fgh_gr (S₀ e) (λ n, iter F (S n) n)
    | fgh_gr_2 e l F : (∀n, fgh_gr (@eps0_fseq e l n) (F n))
                     → fgh_gr e (λ n, F n n).

  Hint Constructors fgh_gr : core.

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

  Hint Resolve eps0_lt_succ eps0_is_limit_omega eps0_is_limit_add_omega : core.

  Fact eps0_choose e : eps0_choice e.
  Proof. induction e using eps0_tail_rect; constructor; auto. Qed.

  (** This is the Grzegorczyk hierarchy *)
  Definition FGH_pwc e : { F | fgh_gr e F }.
  Proof.
    induction e as [ e IH ] using (well_founded_induction_type wf_eps0_lt).
    destruct (eps0_choose e) as [ | e | e l ].
    + exists S; auto.
    + destruct (IH e) as (F & ?); auto.
      exists (λ n, iter F (S n) n); auto.
    + set (F i := π₁ (IH (eps0_fseq l i) (eps0_fseq_lt _ _))).
      exists (λ n, F n n).
      constructor 3 with l.
      intro; apply (proj2_sig (IH (eps0_fseq l n) (eps0_fseq_lt _ _))).
  Qed.

  (* The hierarchy is uniquely characterized, up to extensionality 
     provided the fundemental sequence is uniquely characterized 
     as well !! *)

  Definition FGH e := π₁ (FGH_pwc e). 

  Fact FGH_spec e : fgh_gr e (FGH e).
  Proof. apply (proj2_sig _). Qed.

  Hint Resolve FGH_spec : core.

  (** We establish the defining equations using the spec *)

  Tactic Notation "functionality" :=
    apply fgh_gr_fun with (1 := FGH_spec _) (3 := eq_refl); eauto.

  Theorem FGH_fix_zero n : FGH 0₀ n = S n.
  Proof. functionality. Qed. 

  Theorem FGH_fix_succ e n : FGH (S₀ e) n = iter (FGH e) (S n) n.
  Proof.
    change (FGH (S₀ e) n = (λ n, iter (FGH e) (S n) n) n).
    functionality.
  Qed.

  Theorem FGH_fix_limit e l n : FGH e n = FGH (@eps0_fseq e l n) n.
  Proof.
    change (FGH e n = (λ n, FGH (@eps0_fseq e l n) n) n).
    functionality.
    constructor 3 with l; auto.
  Qed.

End Fast_Growing_Hierarchy.

