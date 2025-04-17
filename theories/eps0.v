(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils pos ordered lex2 lex_list list_order wlist E0.

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

#[global] Notation ε₀ := eps0.

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

  Fact eps0_zero_lt_succ e : 0₀ <ε₀ S₀ e.
  Proof. apply eps0_le_lt_trans with (2 := eps0_lt_succ _); auto. Qed.

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

#[global] Infix "<ε₀" := eps0_lt.
#[global] Infix "≤ε₀" := eps0_le.
#[global] Notation "0₀" := eps0_zero.
#[global] Notation "1₀" := eps0_one.
#[global] Notation S₀ := eps0_succ.

Theorem eps0_rect (P : ε₀ → Type) : (∀f, (∀e, e <ε₀ f → P e) → P f) → ∀e, P e.
Proof. apply (well_founded_induction_type wf_eps0_lt). Qed.

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

#[global] Infix "+₀" := eps0_add.

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
  Definition eps0_exp_S : ε₀ → pos → ε₀.
  Proof.
    intros (e & He) n.
    exists (E0_cons [(e,n)]).
    now apply cnf_sg.
  Defined.

  (* Beware that this is for ωᵉ.(1+i) and NOT ωᵉ.i *)
  Notation "ω^⟨ e , i ⟩" := (eps0_exp_S e i).

  Fact eps0_succ_exp_S n : S₀ ω^⟨0₀,n⟩ = ω^⟨0₀,n +ₚ 1ₚ⟩.
  Proof. apply eps0_eq_iff; simpl; apply E0_succ_pos. Qed.

  Fact eps0_lt_exp_S e n : e <ε₀ ω^⟨e,n⟩.
  Proof.
    destruct e as [e]; unfold eps0_exp_S; cbn.
    apply E0_lt_sub with n; auto.
    apply cnf_sg; auto.
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
  Proof. intros [] ? ?; simpl; constructor; constructor 2; right; auto. Qed.

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

  Fact eps0_add_exp_S e i j : ω^⟨e,i⟩ +₀ ω^⟨e,j⟩ = ω^⟨e,i +ₚ j⟩.
  Proof.
    destruct e as (e & He).
    apply eps0_eq_iff; unfold eps0_add, eps0_exp_S, proj1_sig.
    rewrite E0_add_exp; do 3 f_equal.
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
  Definition eps0_omega (e : ε₀) := ω^⟨e,1ₚ⟩.
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
  
  Fact eps0_add_exp_S_omega e i : ω^⟨e,i⟩ +₀ ω^e = ω^⟨e,i +ₚ 1ₚ⟩.
  Proof. unfold eps0_omega; rewrite eps0_add_exp_S; auto. Qed.

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
      subst; do 2 (right; split; auto).
      now constructor.
    + constructor.
      destruct H3 as [ | (<- & [ | (<- & ?%E0_lt_inv) ]) ].
      * constructor 2; now left.
      * constructor 2; right; auto.
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
    → (ω^⟨e,i₁⟩ +₀ f₁) +₀ (ω^⟨e,i₂⟩ +₀ f₂) = ω^⟨e,i₁ +ₚ i₂⟩ +₀ f₂.
  Proof.
    revert e i₁ f₁ i₂ f₂.
    intros (e & He) i ([l] & Hf1) j ([m] & Hf2) H1 H2.
    apply eps0_eq_iff; simpl in *.
    rewrite !E0_add_head_normal; auto.
    rewrite E0_add_head_eq; auto.
  Qed.

  Fact eps0_add_head_eq' e i₁ i₂ f₂ :
      f₂ <ε₀ ω^e
    → ω^⟨e,i₁⟩ +₀ (ω^⟨e,i₂⟩ +₀ f₂) = ω^⟨e,i₁ +ₚ i₂⟩ +₀ f₂.
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
    apply E0_add_head_gt; auto.
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
      + intros e he i f hf h H Hf He.
        refine (@eps0_pirr P _ _ _ _ _ (@HP1 _ i _ _ He Hf)); auto.
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
  Proof. intros [[ -> | (i & ? & ? & []%pos_not_lt_one & _) ] | ]%eps0_lt_exp_S_inv; auto. Qed.

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
    apply eps0_exp_S_mono; auto.
    unfold pos_one, pos_add; lia.
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
      * apply eps0_exp_S_mono; auto.
        unfold pos_one; lia.
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

#[global] Notation "ω^⟨ e , i ⟩" := (eps0_exp_S e i).
#[global] Notation "ω^ e" := (eps0_omega e).

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

Section eps0_mpos.

  (** pos := nat viewed as 1, 2, ... and not 0, 1, ... *)

  (** The operation (θ : ε₀) (n : pos) => θ.(1+n) *)
  Inductive eps0_mpos_gr n : ε₀ → ε₀ → Prop :=
    | eps0_mpos_gr_0 : eps0_mpos_gr n 0₀ 0₀
    | eps0_mpos_gr_1 α i β : β <ε₀ ω^α → eps0_mpos_gr n (ω^⟨α,i⟩ +₀ β) (ω^⟨α,i *ₚ n⟩ +₀ β).

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
    + exists (ω^⟨e,i *ₚ n⟩ +₀ f); now constructor.
  Qed.

  Definition eps0_mpos e n := π₁ (eps0_mpos_pwc e n).

  Fact eps0_mpos_spec e n : eps0_mpos_gr n e (eps0_mpos e n).
  Proof. apply (proj2_sig _). Qed.

  Fact eps0_mpos_fix_0 n : eps0_mpos 0₀ n = 0₀.
  Proof. apply eps0_mpos_fun with (1 := eps0_mpos_spec _ _) (3 := eq_refl); constructor. Qed.

  Fact eps0_mpos_fix_1 n α i β : β <ε₀ ω^α → eps0_mpos (ω^⟨α,i⟩ +₀ β) n = ω^⟨α,i *ₚ n⟩ +₀ β.
  Proof. intros; apply eps0_mpos_fun with (1 := eps0_mpos_spec _ _) (3 := eq_refl); now constructor. Qed.

  Fact eps0_mpos_exp_S n α i : eps0_mpos ω^⟨α,i⟩ n = ω^⟨α,i *ₚ n⟩.
  Proof. 
    rewrite <- (eps0_add_zero_right ω^⟨_,i⟩), eps0_mpos_fix_1; auto.
    now rewrite eps0_add_zero_right.
  Qed.

  Fact eps0_mpos_O e : eps0_mpos e 1ₚ = e.
  Proof.
    destruct e using eps0_head_rect.
    + now rewrite eps0_mpos_fix_0.
    + rewrite eps0_mpos_fix_1, pos_mul_one_right; auto.
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

  Fact eps0_mpos_plus e i j : eps0_mpos e i +₀ eps0_mpos e j = eps0_mpos e (i +ₚ j).
  Proof.
    destruct e using eps0_head_rect.
    + now rewrite !eps0_mpos_fix_0, eps0_add_zero_left.
    + rewrite !eps0_mpos_fix_1; auto.
      rewrite eps0_add_head_eq, pos_mul_distr_right; auto.
  Qed.

  Fact eps0_mpos_mult e i j : eps0_mpos (eps0_mpos e i) j = eps0_mpos e (i *ₚ j).
  Proof.
    destruct e using eps0_head_rect.
    + now rewrite !eps0_mpos_fix_0.
    + rewrite !eps0_mpos_fix_1, pos_mul_assoc; auto.
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
        now apply pos_mul_mono_left.
      * apply pos_le_lt_iff in Hmn as [ -> | Hmn ]; auto.
        right; split; auto; left.
        now apply pos_mul_mono_right.
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
      now apply pos_mul_mono_right.
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

  Fact eps0_mult_omega_head a e j f : 
      0₀ <ε₀ e
    → f <ε₀ ω^e
    → ω^a *₀ (ω^⟨e,j⟩ +₀ f)
    = ω^⟨a+₀e,j⟩ +₀ ω^a *₀ f.
  Proof. apply eps0_mult_exp_S_head. Qed.

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
        - apply eps0_mult_below_omega with (n := i0 +ₚ 1ₚ); auto.
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
          apply eps0_mult_below_omega with (n := j +ₚ 1ₚ); auto.
          apply eps0_lt_le_trans with (ω^⟨u,j⟩ +₀ ω^u); auto.
          unfold eps0_omega; rewrite eps0_add_exp_S; auto.
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
  destruct (pos_one_or_succ n) as [ -> | (m & ->) ].
  + exists 0₀.
    rewrite eps0_succ_zero_is_one; apply eps0_omega_zero.
  + exists ω^⟨0₀,m⟩. 
    now rewrite eps0_succ_exp_S.
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

Fact eps0_is_limit_pos e : eps0_is_limit e → 0₀ <ε₀ e.
Proof.
  destruct (eps0_zero_or_pos e) as [ -> | ]; auto.
  now intros [ [] _ ].
Qed.

Hint Resolve eps0_is_limit_pos : core.

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

Fact eps0_add_is_limit_iff a e :
    eps0_is_limit (a +₀ e)
  ↔ e = 0₀ ∧ eps0_is_limit a ∨ eps0_is_limit e.
Proof.
  split.
  + apply eps0_add_is_limit_inv.
  + intros [ (-> & ?) | ? ].
    * now rewrite eps0_add_zero_right.
    * now apply eps0_add_is_limit.
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
  contradict H; now apply eps0_eq_iff.
Qed.

Fact eps0_is_limit_exp_S_iff e n : eps0_is_limit ω^⟨e,n⟩ ↔ e ≠ 0₀.
Proof.
  split.
  + intros [ _ H1 ] ->; apply H1; auto.
  + apply eps0_is_limit_exp_S.
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

