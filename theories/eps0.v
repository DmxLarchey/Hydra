(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations (* Arith Lia *) Wellfounded Utf8.
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

#[global] Reserved Notation "a '+₀' b"  (at level 31, left associativity, format "a  +₀  b" ).
#[global] Reserved Notation "a '*₀' b"  (at level 29, left associativity, format "a  *₀  b" ).
#[global] Reserved Notation "'ω^' e" (at level 1, format "ω^ e").
#[global] Reserved Notation "'ω^⟨' e , i '⟩'" (at level 0, format "ω^⟨ e , i ⟩").

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve clos_trans_rev transitive_rev : core.
#[local] Hint Resolve in_cons in_eq in_elt in_or_app : core.
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
      of the nested lex. order denoted <ε₀ and ≤ε₀

      We make them proof irrelevant *)

  Let e0_lt (e f : ε₀) := E0_lt (π₁ e) (π₁ f).
  Let e0_le (e f : ε₀) := E0_le (π₁ e) (π₁ f).

  Local Fact e0_lt_dec : ∀ e f, { e0_lt e f } + { ~ e0_lt e f}.
  Proof. intros [] []; unfold e0_lt; simpl; apply E0_lt_dec. Qed.

  Definition eps0_lt e f := squash (e0_lt_dec e f).

  Fact eps0_lt_iff e f : eps0_lt e f ↔ E0_lt (π₁ e) (π₁ f).
  Proof. apply squash_iff. Qed.

  Fact eps0_lt_pirr e f (p q : eps0_lt e f) : p = q.
  Proof. apply squash_pirr. Qed.

  Local Fact e0_le_dec : ∀ e f, { e0_le e f } + { ~ e0_le e f}.
  Proof. intros [] []; unfold e0_le; simpl; apply E0_le_dec. Qed.

  Definition eps0_le e f := squash (e0_le_dec e f).

  Fact eps0_le_iff e f : eps0_le e f ↔ E0_le (π₁ e) (π₁ f).
  Proof. apply squash_iff. Qed.

  Fact eps0_le_pirr e f (p q : eps0_le e f) : p = q.
  Proof. apply squash_pirr. Qed.

End eps0_order.

(* Arguments eps0_lt /.
Arguments eps0_le /. *)

#[global] Infix "<ε₀" := eps0_lt.
#[global] Infix "≤ε₀" := eps0_le.

Section eps0_order.

  (** The nested lexicographic order <ε₀ is a strict total/decidable order *)

  Fact eps0_lt_irrefl e : ¬ e <ε₀ e.
  Proof. rewrite eps0_lt_iff; apply E0_lt_irrefl. Qed.

  Fact eps0_lt_trans : transitive eps0_lt.
  Proof. intros ? ? ?; rewrite !eps0_lt_iff; apply E0_lt_trans. Qed.

  Hint Resolve eps0_lt_trans : core.
  Hint Constructors sdec : core.

  Fact eps0_lt_sdec e f : sdec eps0_lt e f.
  Proof.
    revert e f; intros (e & He) (f & Hf).
    destruct (E0_lt_sdec e f) as []; [ constructor 1 | | constructor 3 ].
    1,3 : now apply eps0_lt_iff.
    rewrite (cnf_pirr _ He Hf); constructor 2.
  Qed.

  Fact eps0_lt_eq_gt_dec e f : { e <ε₀ f } + { e = f } + { f <ε₀ e }.
  Proof. destruct (eps0_lt_sdec e f); auto. Qed.

  Fact eps0_eq_dec (e f : ε₀) : { e = f } + { e ≠ f }.
  Proof. apply sdec_eq_dec with (1 := eps0_lt_sdec), eps0_lt_irrefl. Qed.

  (* <ε₀ is well-founded *)
  Fact wf_eps0_lt : well_founded eps0_lt.
  Proof.
    generalize wf_lt_cnf.
    apply wf_rel_morph with (f := λ x y, x = π₁ y).
    + intros []; eauto.
    + intros ? ? [] [] -> ->; rewrite eps0_lt_iff; simpl; auto.
  Qed.

  Hint Resolve cnf_zero cnf_one : core.

  Definition eps0_zero : ε₀.
  Proof. now exists E0_zero. Defined.

  Definition eps0_one : ε₀.
  Proof. now exists E0_one. Defined.

  Notation "0₀" := eps0_zero.
  Notation "1₀" := eps0_one.

  Fact eps0_zero_not_gt : ∀e, ¬ e <ε₀ 0₀.
  Proof. intro; rewrite eps0_lt_iff; apply E0_zero_not_gt. Qed.

  Fact eps0_le_iff_lt e f : e ≤ε₀ f ↔ e <ε₀ f ∨ e = f.
  Proof.
    rewrite eps0_lt_iff, eps0_le_iff, eps0_eq_iff.
    destruct e; destruct f; simpl.
    unfold E0_le; tauto.
  Qed.

  Fact eps0_zero_least e : 0₀ ≤ε₀ e.
  Proof.
    apply eps0_le_iff.
    destruct e as [ [l] He ]; simpl.
    destruct l; [ right | left ]; auto.
    constructor; constructor.
  Qed.

  Fact eps0_lt_le_weak e f : e <ε₀ f → e ≤ε₀ f.
  Proof. rewrite eps0_le_iff_lt; now left. Qed. 

  Fact eps0_le_refl e : e ≤ε₀ e.
  Proof. rewrite eps0_le_iff_lt; now right. Qed.

  Fact eps0_le_antisym e f : e ≤ε₀ f → f ≤ε₀ e → e = f.
  Proof. rewrite !eps0_le_iff, eps0_eq_iff; apply E0_le_antisym. Qed.

  Fact eps0_le_trans e f g : e ≤ε₀ f → f ≤ε₀ g → e ≤ε₀ g.
  Proof. rewrite !eps0_le_iff; apply E0_le_trans. Qed.

  Fact eps0_lt_le_trans e f g : e <ε₀ f → f ≤ε₀ g → e <ε₀ g.
  Proof. rewrite !eps0_lt_iff, !eps0_le_iff; apply E0_lt_le_trans. Qed.

  Fact eps0_le_lt_trans e f g : e ≤ε₀ f → f <ε₀ g → e <ε₀ g.
  Proof. rewrite !eps0_lt_iff, !eps0_le_iff; apply E0_le_lt_trans. Qed.

  Hint Resolve eps0_zero_least eps0_lt_le_weak
             eps0_le_refl eps0_le_antisym
             eps0_le_trans eps0_le_lt_trans
             eps0_lt_le_trans : core.

  Fact eps0_zero_or_pos e : { e = 0₀ } + { 0₀ <ε₀ e }.
  Proof. destruct (eps0_lt_eq_gt_dec 0₀ e) as [ [] | ]; auto. Qed.

  Fact eps0_le_lt_dec e f : { e ≤ε₀ f } + { f <ε₀ e }.
  Proof. destruct (eps0_lt_sdec e f); auto. Qed.
  
  Fact eps0_le_not_lt e f : e ≤ε₀ f → ~ f <ε₀ e.
  Proof. intros ? ?; apply (@eps0_lt_irrefl e); eauto. Qed.

  Fact eps0_le_zero e : e ≤ε₀ 0₀ → e = 0₀.
  Proof. intros []%eps0_le_iff_lt; auto. Qed.

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
  Proof. apply eps0_lt_iff; destruct e; simpl; auto. Qed.

  Fact eps0_zero_lt_succ e : 0₀ <ε₀ S₀ e.
  Proof. apply eps0_le_lt_trans with (2 := eps0_lt_succ _); auto. Qed.

  Fact eps0_lt_one : ∀e, e <ε₀ 1₀ → e = 0₀.
  Proof. intros []; rewrite eps0_lt_iff, eps0_eq_iff; apply E0_lt_one; auto. Qed.

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

#[local] Hint Resolve eps0_zero_least eps0_lt_le_weak
             eps0_le_refl eps0_le_antisym
             eps0_lt_trans eps0_le_trans 
             eps0_le_lt_trans
             eps0_lt_le_trans
             eps0_lt_succ
             eps0_le_not_succ : core.

#[global] Notation "0₀" := eps0_zero.
#[global] Notation "1₀" := eps0_one.
#[global] Notation S₀ := eps0_succ.

Theorem eps0_rect (P : ε₀ → Type) : (∀f, (∀e, e <ε₀ f → P e) → P f) → ∀e, P e.
Proof. apply (well_founded_induction_type wf_eps0_lt). Qed.

Section eps0_add_base.

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
    intros [e] [f] (a & ? & ? & Ha)%eps0_lt_iff%E0_lt_inv_add; auto; simpl in *.
    exists (exist _ a Ha); rewrite eps0_eq_iff, eps0_lt_iff; simpl; auto.
  Qed.

  Fact eps0_add_mono_left : ∀ e f g, e ≤ε₀ f → e +₀ g ≤ε₀ f +₀ g.
  Proof. intros [] [] []; rewrite !eps0_le_iff; simpl; apply E0_add_mono_left; auto. Qed.

  Fact eps0_add_incr : ∀ e f, 0₀ <ε₀ f → e <ε₀ e +₀ f.
  Proof. intros [] []; rewrite !eps0_lt_iff; apply E0_add_incr; auto. Qed.

  Fact eps0_add_mono_right : ∀ e f g, f <ε₀ g → e +₀ f <ε₀ e +₀ g.
  Proof. intros [] [] []; rewrite !eps0_lt_iff; apply E0_add_mono_right; auto. Qed.

End eps0_add_base.

#[global] Infix "+₀" := eps0_add.

#[local] Hint Resolve eps0_add_mono_left eps0_add_mono_right : core.

Section eps0_add_extra.

  Fact eps0_add_mono e e' f f' : e ≤ε₀ e' → f ≤ε₀ f' → e +₀ f ≤ε₀ e' +₀ f'.
  Proof. intros ? [ | <- ]%eps0_le_iff_lt; eauto. Qed.

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
    + now apply eps0_lt_irrefl in H.
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
      revert H; rewrite eps0_add_zero_right; apply eps0_lt_irrefl.
  Qed.

  Fact eps0_succ_next_inv e f : e <ε₀ S₀ f → e ≤ε₀ f.
  Proof.
    intros H.
    destruct (eps0_lt_sdec e f) as [ e f H1 | e | e f H1%eps0_succ_next ]; auto.
    destruct (@eps0_lt_irrefl e).
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
    all: apply eps0_succ_mono in G; auto; rewrite E in G; destruct (eps0_lt_irrefl _ G).
  Qed.

  (** There is no ordinal between e and (eps0_succ e) *)
  Corollary eps0_no_ordinal_between_n_and_succ e f :
      ¬ (e <ε₀ f ∧ f <ε₀ eps0_succ e).
  Proof.
    intros (H1 & H2).
    generalize (eps0_succ_next _ _ H1).
    intros [ | <- ]%eps0_le_iff_lt.
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
  Proof. rewrite !eps0_le_iff_lt; now intros [ ?%eps0_add_lt_cancel | ?%eps0_add_cancel ]; [ left | right ]. Qed.

End eps0_add_extra.

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

  Hint Resolve cnf_sg : core.

  (* ω^e.p where p is positive *)
  Definition eps0_exp : ε₀ → pos → ε₀.
  Proof.
    intros (e & He) p.
    exists (E0_cons [(e,p)]); auto.
  Defined.

  Notation "ω^⟨ e , i ⟩" := (eps0_exp e i).

  Fact eps0_succ_exp n : S₀ ω^⟨0₀,n⟩ = ω^⟨0₀,n +ₚ 1ₚ⟩.
  Proof. apply eps0_eq_iff; simpl; apply E0_succ_pos. Qed.

  Fact eps0_lt_exp : ∀ e n, e <ε₀ ω^⟨e,n⟩.
  Proof.
    intros [] n; apply eps0_lt_iff; unfold eps0_exp; cbn.
    apply E0_lt_sub with n; auto.
  Qed.

  Fact eps0_exp_mono_right : ∀ e n m, n < m → ω^⟨e,n⟩ <ε₀ ω^⟨e,m⟩.
  Proof. intros [] ? ?; rewrite eps0_lt_iff; simpl; constructor; constructor 2; right; auto. Qed.

  Fact eps0_exp_mono_left : ∀ e f n m, e <ε₀ f → ω^⟨e,n⟩ <ε₀ ω^⟨f,m⟩.
  Proof. intros [] [] ? N; rewrite !eps0_lt_iff; apply E0_lt_exp. Qed.

  Fact eps0_add_exp : ∀ e i j, ω^⟨e,i⟩ +₀ ω^⟨e,j⟩ = ω^⟨e,i +ₚ j⟩.
  Proof.
    intros [] ? ?.
    apply eps0_eq_iff; unfold eps0_add, eps0_exp, proj1_sig.
    rewrite E0_add_exp; do 3 f_equal.
  Qed.

  (***********************)

  Fact eps0_lt_zero_exp e n : 0₀ <ε₀ ω^⟨e,n⟩.
  Proof. apply eps0_le_lt_trans with (2 := eps0_lt_exp _ _); auto. Qed.

  Hint Resolve eps0_lt_zero_exp : core.

  Fact eps0_zero_neq_exp e n : 0₀ ≠ ω^⟨e,n⟩.
  Proof.
    intros E; apply (@eps0_lt_irrefl 0₀).
    rewrite E at 2; apply eps0_lt_zero_exp.
  Qed.

  Hint Resolve eps0_exp_mono_left eps0_exp_mono_right : core.

  Fact eps0_exp_mono e f n m : e ≤ε₀ f → n ≤ m → ω^⟨e,n⟩ ≤ε₀ ω^⟨f,m⟩.
  Proof.
    intros [ H1 | <- ]%eps0_le_iff_lt H2; auto.
    apply pos_le_lt_iff in H2 as [ <- | ]; auto.
  Qed.

  Hint Resolve eps0_exp_mono : core.

  Fact eps0_exp_mono_inv e f n m : ω^⟨e,n⟩ <ε₀ ω^⟨f,m⟩ → e <ε₀ f ∨ e = f ∧ n < m.
  Proof.
    intros H.
    destruct (eps0_lt_sdec e f) as [ | e | e f H1 ]; auto.
    + destruct (pos_lt_sdec n m) as [ | n | n m H2 ]; auto.
      * contradict H; apply eps0_lt_irrefl.
      * destruct (@eps0_lt_irrefl ω^⟨e,n⟩).
        apply eps0_lt_trans with (1 := H); auto.
    + destruct (@eps0_lt_irrefl ω^⟨e,n⟩).
      apply eps0_lt_trans with (1 := H); auto.
  Qed.
  
  Fact eps0_exp_inj e f n m : ω^⟨e,n⟩ = ω^⟨f,m⟩ → e = f ∧ n = m.
  Proof.
    intros E.
    destruct (eps0_lt_sdec e f) as [ e f H | e | e f H ].
    + apply eps0_exp_mono_left with (n := n) (m := m) in H.
      rewrite E in H; now apply eps0_lt_irrefl in H.
    + destruct (pos_lt_sdec n m) as [ n m H | | n m H ]; auto;
        apply eps0_exp_mono_right with (e := e) in H;
        rewrite E in H; now apply eps0_lt_irrefl in H.
    + apply eps0_exp_mono_left with (n := m) (m := n) in H.
      rewrite E in H; now apply eps0_lt_irrefl in H.
  Qed.

  (* ωᵉ = ωᵉ.(1+0) *)
  Definition eps0_omega (e : ε₀) := ω^⟨e,1ₚ⟩.
  Notation "ω^ e" := (eps0_omega e).
  
  Fact eps0_omega_eq_exp e : ω^e = ω^⟨e,1ₚ⟩.
  Proof. trivial. Qed.

  Fact eps0_omega_zero : ω^0₀ = 1₀.
  Proof. apply eps0_eq_iff; trivial. Qed.

  Fact eps0_add_below_omega : ∀ e f g, e <ε₀ ω^g → f <ε₀ ω^g → e +₀ f <ε₀ ω^g.
  Proof. intros [[] ] [[] ] []; rewrite !eps0_lt_iff; apply E0_add_below_omega. Qed.

  (* A "tail form" is a +₀ ω^e but it is not unique unless a is chosen
     the least possible for this value, see eps0_least_split *)

  Fact eps0_tf_fun_right : ∀ a b e f, a +₀ ω^e = b +₀ ω^f → e = f.
  Proof.
    intros [] [] [] []; rewrite !eps0_eq_iff; simpl.
    apply E0_add_omega_fun_right.
  Qed.

  (** A "head normal form" is ω^⟨e,i⟩ +₀ f with f <ε₀ ω^e 
      and it is unique (for non-zero ordinals) *)

  Fact eps0_eq_hnf_inv : ∀ e₁ i₁ f₁ e₂ i₂ f₂,
      ω^⟨e₁,i₁⟩ +₀ f₁ = ω^⟨e₂,i₂⟩ +₀ f₂
    → f₁ <ε₀ ω^e₁
    → f₂ <ε₀ ω^e₂
    → e₁ = e₂ ∧ i₁ = i₂ ∧ f₁ = f₂.
  Proof.
    intros (e & He) i ([l] & Hl) (f & Hf) j ([m] & Hm)
           E%eps0_eq_iff H1%eps0_lt_iff H2%eps0_lt_iff.
    rewrite !eps0_eq_iff; simpl in *.
    rewrite !E0_add_head_normal in E; auto.
    now inversion E.
  Qed.

  Fact eps0_lt_hnf_inv : ∀ e₁ i₁ f₁ e₂ i₂ f₂,
      f₁ <ε₀ ω^e₁
    → f₂ <ε₀ ω^e₂
    → ω^⟨e₁,i₁⟩ +₀ f₁ <ε₀ ω^⟨e₂,i₂⟩ +₀ f₂
    ↔ e₁ <ε₀ e₂ ∨ e₁ = e₂ ∧ (i₁ < i₂ ∨ i₁ = i₂ ∧ f₁ <ε₀ f₂).
  Proof.
    intros (e & He) i ([l] & Hl) (f & Hf) j ([m] & Hm) H1 H2;
    rewrite !eps0_lt_iff, eps0_eq_iff in *; simpl in *.
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

  Fact eps0_add_hnf_lt e₁ i₁ f₁ e₂ i₂ f₂ :
      e₁ <ε₀ e₂
    → f₁ <ε₀ ω^e₁
    → f₂ <ε₀ ω^e₂
    → (ω^⟨e₁,i₁⟩ +₀ f₁) +₀ (ω^⟨e₂,i₂⟩ +₀ f₂) = ω^⟨e₂,i₂⟩ +₀ f₂.
  Proof.
    revert e₁ i₁ f₁ e₂ i₂ f₂.
    intros (e1 & He1) i ([l] & Hf1) (e2 & He2) j ([m] & Hf2).
    rewrite !eps0_lt_iff, !eps0_eq_iff; simpl; intros.
    rewrite !E0_add_head_normal; auto.
    rewrite E0_add_head_lt; auto.
  Qed.

  Fact eps0_add_hnf_eq e i₁ f₁ i₂ f₂ :
      f₁ <ε₀ ω^e
    → f₂ <ε₀ ω^e
    → (ω^⟨e,i₁⟩ +₀ f₁) +₀ (ω^⟨e,i₂⟩ +₀ f₂) = ω^⟨e,i₁ +ₚ i₂⟩ +₀ f₂.
  Proof.
    revert e i₁ f₁ i₂ f₂.
    intros (e & He) i ([l] & Hf1) j ([m] & Hf2).
    rewrite !eps0_lt_iff, !eps0_eq_iff; simpl; intros.
    rewrite !E0_add_head_normal; auto.
    rewrite E0_add_head_eq; auto.
  Qed.

  Fact eps0_add_hnf_gt e₁ i₁ f₁ e₂ i₂ f₂ :
      e₂ <ε₀ e₁
    → f₁ <ε₀ ω^e₁
    → f₂ <ε₀ ω^e₂
    → (ω^⟨e₁,i₁⟩ +₀ f₁) +₀ (ω^⟨e₂,i₂⟩ +₀ f₂) = ω^⟨e₁,i₁⟩ +₀ (f₁ +₀ (ω^⟨e₂,i₂⟩ +₀ f₂))
     ∧ f₁ +₀ (ω^⟨e₂,i₂⟩ +₀ f₂) <ε₀ ω^e₁.
  Proof.
    revert e₁ i₁ f₁ e₂ i₂ f₂.
    intros (e1 & He1) i ([l] & Hf1) (e2 & He2) j ([m] & Hf2).
    rewrite !eps0_lt_iff, !eps0_eq_iff; simpl; intros.
    rewrite !E0_add_head_normal; auto.
    apply E0_add_head_gt; auto.
  Qed.

  Section eps0_hnf_rect.

    Variables (P : ε₀ → Type)
              (HP0 : P 0₀)
              (HP1 : ∀ e i f, f <ε₀ ω^e → P e → P f → P (ω^⟨e,i⟩ +₀ f)).

    Theorem eps0_hnf_rect : ∀e, P e.
    Proof.
      intros (e & he); revert e he.
      apply cnf_head_dep_rect.
      + intros; revert HP0; apply eps0_pirr with (1 := eq_refl).
      + intros e he i f hf h H Hf He.
        refine (@eps0_pirr P _ _ _ _ _ (@HP1 _ i _ _ He Hf)); auto.
        now apply eps0_lt_iff.
    Qed.

  End eps0_hnf_rect.

  (**********************)

  Fact eps0_lt_omega e : e <ε₀ ω^e.
  Proof. apply eps0_lt_exp. Qed.

  Hint Resolve eps0_lt_omega : core.

  Fact eps0_omega_mono_lt : ∀ e f, e <ε₀ f → ω^e <ε₀ ω^f.
  Proof. unfold eps0_omega; auto. Qed.

  Fact eps0_omega_mono_le e f : e ≤ε₀ f → ω^e ≤ε₀ ω^f.
  Proof. rewrite !eps0_le_iff_lt; intros [ | <- ]; auto; left; now apply eps0_omega_mono_lt. Qed.

  Fact eps0_omega_inj e f : ω^e = ω^f → e = f.
  Proof. now intros []%eps0_exp_inj. Qed.

  Fact eps0_add_exp_omega e i : ω^⟨e,i⟩ +₀ ω^e = ω^⟨e,i +ₚ 1ₚ⟩.
  Proof. unfold eps0_omega; rewrite eps0_add_exp; auto. Qed.

  Fact eps0_one_eq_omega e : 1₀ = ω^e → e = 0₀.
  Proof. rewrite <- eps0_omega_zero; now intros <-%eps0_omega_inj. Qed.

  Fact eps0_zero_lt_omega e : 0₀ <ε₀ ω^e.
  Proof. apply eps0_lt_zero_exp. Qed.

  Hint Resolve eps0_zero_lt_omega : core.

  Fact eps0_zero_neq_omega e : 0₀ ≠ ω^e.
  Proof. apply eps0_zero_neq_exp. Qed.

  (** head_normal_forms *)

  Fact eps0_lt_exp_hnf_inv e₁ i₁ e₂ i₂ f₂ :
      f₂ <ε₀ ω^e₂
    → ω^⟨e₁,i₁⟩ <ε₀ ω^⟨e₂,i₂⟩ +₀ f₂
    ↔ e₁ <ε₀ e₂ ∨ e₁ = e₂ ∧ (i₁ < i₂ ∨ i₁ = i₂ ∧ 0₀ <ε₀ f₂).
  Proof.
    intro.
    rewrite <- (eps0_add_zero_right ω^⟨e₁,_⟩),
                eps0_lt_hnf_inv; auto.
    firstorder.
  Qed.

  Fact eps0_lt_hnf_exp_inv e₁ i₁ f₁ e₂ i₂ :
      f₁ <ε₀ ω^e₁
    → ω^⟨e₁,i₁⟩ +₀ f₁ <ε₀ ω^⟨e₂,i₂⟩
    ↔ e₁ <ε₀ e₂ ∨ e₁ = e₂ ∧ i₁ < i₂.
  Proof.
    intro.
    rewrite <- (eps0_add_zero_right ω^⟨e₂,_⟩),
                eps0_lt_hnf_inv; auto.
    apply or_iff_compat_l, and_iff_compat_l.
    split; auto.
    intros [ | (_ & ?%eps0_zero_not_gt) ]; now auto.
  Qed.

  Fact eps0_lt_exp_inv e₁ i₁ e₂ i₂ :
      ω^⟨e₁,i₁⟩ <ε₀ ω^⟨e₂,i₂⟩
    ↔ e₁ <ε₀ e₂ ∨ e₁ = e₂ ∧ i₁ < i₂.
  Proof.
    rewrite <- (eps0_add_zero_right ω^⟨e₁,_⟩).
    apply eps0_lt_hnf_exp_inv; auto.
  Qed.

  Fact eps0_lt_zero_hnf e i f : 0₀ <ε₀ ω^⟨e,i⟩ +₀ f.
  Proof. apply eps0_lt_le_trans with ω^⟨e,i⟩; auto. Qed.

  Hint Resolve eps0_lt_zero_hnf : core.

  Fact eps0_eq_exp_hnf_inv e₁ i₁ e₂ i₂ f₂ :
      ω^⟨e₁,i₁⟩ = ω^⟨e₂,i₂⟩ +₀ f₂
    → f₂ <ε₀ ω^e₂
    → e₁ = e₂ ∧ i₁ = i₂ ∧ f₂ = 0₀.
  Proof.
    rewrite <- (eps0_add_zero_right ω^⟨e₁,i₁⟩).
    intros H1 H2; revert H1.
    intros (-> & -> & <-)%eps0_eq_hnf_inv; auto.
  Qed.

  Fact eps0_zero_neq_hnf e i f : 0₀ ≠ ω^⟨e,i⟩ +₀ f.
  Proof. intro E; apply (@eps0_lt_irrefl 0₀); rewrite E at 2; auto. Qed.

  Fact eps0_add_exp_hnf_lt e₁ i₁ e₂ i₂ f₂ :
      e₁ <ε₀ e₂
    → f₂ <ε₀ ω^e₂
    → ω^⟨e₁,i₁⟩ +₀ (ω^⟨e₂,i₂⟩ +₀ f₂) = ω^⟨e₂,i₂⟩ +₀ f₂.
  Proof.
    intros H1 H2.
    rewrite <- (eps0_add_zero_right ω^⟨e₁,i₁⟩).
    apply eps0_add_hnf_lt; auto.
  Qed.

  Fact eps0_add_exp_lt e₁ i₁ e₂ i₂ :
      e₁ <ε₀ e₂ → ω^⟨e₁,i₁⟩ +₀ ω^⟨e₂,i₂⟩ = ω^⟨e₂,i₂⟩.
  Proof.
    intro.
    rewrite <- (eps0_add_zero_right ω^⟨_,i₂⟩).
    apply eps0_add_exp_hnf_lt; auto.
  Qed.

  Fact eps0_add_exp_hnf_eq e i₁ i₂ f₂ :
      f₂ <ε₀ ω^e
    → ω^⟨e,i₁⟩ +₀ (ω^⟨e,i₂⟩ +₀ f₂) = ω^⟨e,i₁ +ₚ i₂⟩ +₀ f₂.
  Proof.
    intro.
    rewrite <- (eps0_add_zero_right ω^⟨e,i₁⟩).
    rewrite eps0_add_hnf_eq; auto.
  Qed.

  (* Ordinals below ω^e.n are of the form
        - 0
        - ω^e.i +₀ b with i < n and b < ω^e
        - or < ω^f.i with f <ε₀ e  *)

  Lemma eps0_below_exp_inv a e n :
      a <ε₀ ω^⟨e,n⟩
    → (a = 0₀)
    + {i : _ & {b | a = ω^⟨e,i⟩ +₀ b ∧ i < n ∧ b <ε₀ ω^e}}
    + {f : _ & {i | a <ε₀ ω^⟨f,i⟩ ∧ f <ε₀ e}}.
  Proof.
    destruct a as [ | g i h H _ _ ] using eps0_hnf_rect.
    + now do 2 left.
    + intros H1%eps0_lt_hnf_exp_inv; auto.
      destruct (pos_one_or_succ n) as [ -> | (j & ->) ].
      * right.
        exists g, (i +ₚ 1ₚ).
        rewrite eps0_lt_hnf_exp_inv; auto.
        destruct H1 as [ | (-> & []%pos_not_lt_one) ]; auto.
      * destruct (eps0_le_lt_dec e g) as [ C | C ].
        - left; right; exists i, h.
          destruct H1 as [ | (-> & ?) ]; eauto.
          destruct (@eps0_lt_irrefl e); eauto.
        - right; exists g, (i +ₚ 1ₚ); split; auto.
          rewrite eps0_lt_hnf_exp_inv; auto.
  Qed.

  (** inversion for _ <ε₀ ω^_ *)
  Lemma eps0_below_omega_inv a e :
      a <ε₀ ω^e
    → (a = 0₀) 
    + {f : ε₀ & {n | a <ε₀ ω^⟨f,n⟩ ∧ f <ε₀ e}}.
  Proof. intros [[ -> | (i & ? & ? & []%pos_not_lt_one & _) ] | ]%eps0_below_exp_inv; auto. Qed.

  Fact eps0_add_lt_omega a e : a <ε₀ ω^e → a +₀ ω^e = ω^e.
  Proof.
    intros [ -> | (f & n & []) ]%eps0_below_omega_inv.
    + now rewrite eps0_add_zero_left.
    + apply eps0_le_antisym; auto.
      apply eps0_le_trans with (ω^⟨f,n⟩ +₀ ω^e); auto.
      unfold eps0_omega; rewrite eps0_add_exp_lt; auto.
  Qed.

  (** inversion for _ < ω^(_+1) *)
  Lemma eps0_below_omega_succ_inv f e : f <ε₀ ω^(S₀ e) → { n | f <ε₀ ω^⟨e,n⟩ }.
  Proof.
    intros [ -> | (a & n & H1 & H2%eps0_succ_next_inv) ]%eps0_below_omega_inv.
    + exists 0; auto.
    + exists n; apply eps0_lt_le_trans with (1 := H1); auto.
  Qed.

  Fact eps0_le_add_exp_omega e n m : n < m → ω^⟨e,n⟩ +₀ ω^e ≤ε₀ ω^⟨e,m⟩.
  Proof.
    intros H%pos_lt_iff_le_succ; unfold eps0_omega.
    rewrite eps0_add_exp; auto.
  Qed.
  
  Lemma eps0_add_below_exp b c e n : b <ε₀ ω^⟨e,n⟩ → c <ε₀ ω^e → b+₀c <ε₀ ω^⟨e,n⟩.
  Proof.
    intros [ [ -> | (u & i & -> & []) ] | (u & i & []) ]%eps0_below_exp_inv
           [ -> | (v & j & H2 & H3) ]%eps0_below_omega_inv.
    + rewrite eps0_add_zero_left; auto.
    + rewrite eps0_add_zero_left; apply eps0_lt_trans with (1 := H2); auto.
    + rewrite eps0_add_zero_right.
      apply eps0_lt_le_trans with (2 := eps0_le_add_exp_omega _ H); auto.
    + rewrite eps0_add_assoc.
      apply eps0_lt_le_trans with (2 := eps0_le_add_exp_omega _ H); auto.
      apply eps0_add_mono_right, eps0_add_below_omega; auto.
      now apply eps0_lt_trans with (1 := H2), eps0_exp_mono_left.
    + rewrite eps0_add_zero_right; apply eps0_lt_trans with (1 := H); auto.
    + apply eps0_lt_le_trans with ω^e.
      * apply eps0_add_below_omega; auto.
        - now apply eps0_lt_trans with (1 := H), eps0_exp_mono_left.
        - now apply eps0_lt_trans with (1 := H2), eps0_exp_mono_left.
      * apply eps0_exp_mono; auto.
  Qed.

  Section eps0_hnf_pos_rect.

    Variables (P : ε₀ → Type)
              (HP0 : P 0₀)
              (HP1 : ∀i, P ω^⟨0₀,i⟩) 
              (HP2 : ∀ e i f, 0₀ <ε₀ e → f <ε₀ ω^e → P e → P f → P (ω^⟨e,i⟩ +₀ f)).

    Theorem eps0_hnf_pos_rect : ∀e, P e.
    Proof.
      induction e as [ | e n f H ] using eps0_hnf_rect; trivial.
      destruct (eps0_zero_or_pos e) as [ -> | G ].
      + assert (f = 0₀) as ->.
        1:{ rewrite eps0_omega_zero in H.
            now apply eps0_lt_one in H. }
        now rewrite eps0_add_zero_right.
      + now apply HP2.
    Qed.

  End eps0_hnf_pos_rect.

End eps0_omega.

Hint Resolve eps0_lt_omega 
             eps0_lt_zero_exp
             eps0_zero_lt_omega 
             eps0_lt_zero_hnf : core.

#[global] Notation "ω^⟨ e , i ⟩" := (eps0_exp e i).
#[global] Notation "ω^ e" := (eps0_omega e).

(* Hence a successor is not a limit ordinal 

   Successor is of shape ω[_++[(ω[[]],1+i)]]
   Limit is either ω[[]] or ω[_++[(x,i)]] with 0 < i and x <> ω[[]] *)

Definition eps0_is_succ e := ∃f, e = S₀ f.

Fact eps0_is_succ_S e : eps0_is_succ (S₀ e).
Proof. now exists e. Qed.

#[local] Hint Resolve eps0_is_succ_S : core.

Fact eps0_is_succ_iff e : eps0_is_succ e ↔ E0_is_succ (π₁ e).
Proof.
  split.
  + intros ((f & ?) & ->); exists f; auto.
  + intros (f & H1 & H2); exists (exist _ f H2).
    apply eps0_eq_iff; now rewrite H1.
Qed.

Fact eps0_is_succ_exp_zero n : eps0_is_succ ω^⟨0₀,n⟩.
Proof.
  destruct (pos_one_or_succ n) as [ -> | (m & ->) ].
  + exists 0₀; rewrite eps0_succ_zero_is_one; apply eps0_omega_zero.
  + exists ω^⟨0₀,m⟩; now rewrite eps0_succ_exp.
Qed.

#[local] Hint Resolve eps0_is_succ_exp_zero : core.

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

#[local] Hint Resolve eps0_is_limit_pos : core.

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

Fact eps0_is_limit_exp e n : e ≠ 0₀ → eps0_is_limit ω^⟨e,n⟩.
Proof.
  intros H.
  apply eps0_is_limit_iff.
  destruct e; simpl.
  apply E0_exp_is_limit; auto.
  contradict H; now apply eps0_eq_iff.
Qed.

Fact eps0_is_limit_exp_iff e n : eps0_is_limit ω^⟨e,n⟩ ↔ e ≠ 0₀.
Proof.
  split.
  + intros [ _ H1 ] ->; apply H1; auto.
  + apply eps0_is_limit_exp.
Qed.

Fact eps0_is_limit_omega e : e ≠ 0₀ → eps0_is_limit ω^e.
Proof. apply eps0_is_limit_exp. Qed.

Fact eps0_is_limit_tf a e : e ≠ 0₀ → eps0_is_limit (a +₀ ω^e).
Proof. intro; apply eps0_add_is_limit, eps0_is_limit_omega; auto. Qed.

Fact eps0_tf_not_zero a e : 0₀ ≠ a +₀ ω^e.
Proof.
  intros H.
  apply (@eps0_lt_irrefl (a+₀ω^e)).
  rewrite <- H at 1.
  apply eps0_lt_le_trans with (1 := eps0_zero_lt_omega e); auto.
Qed.

Fact eps0_succ_eq_tf a b e : S₀ a = b +₀ ω^e → e = 0₀ ∧ a = b.
Proof.
  rewrite <- eps0_add_one_right, <- eps0_omega_zero; intros H.
  destruct eps0_tf_fun_right with (1 := H); split; auto.
  rewrite eps0_omega_zero, !eps0_add_one_right in H.
  now apply eps0_succ_inj.
Qed.

Fact eps0_add_omega_not_succ a b e : e ≠ 0₀ → S₀ a ≠ b +₀ ω^e.
Proof. intros H; contradict H; now apply eps0_succ_eq_tf in H. Qed.

Fact eps0_succ_eq_omega a e : S₀ a = ω^e → e = 0₀ ∧ a = 0₀.
Proof. rewrite <- (eps0_add_zero_left ω^e); apply eps0_succ_eq_tf. Qed.

Fact eps0_add_one_left_choice e : (e = 0₀) + { f | e = 1₀ +₀ f }.
Proof.
  induction e as [ | n | e i f ? ? _ _ ] using eps0_hnf_pos_rect.
  + now left.
  + right.
    (* In case n is not in nat* but in eps0*, then n can be above
       eg (ε₀)⁰.ω then we write (ε₀)⁰.ω = 1 + (ε₀)⁰.ω *)
    (* 1+n is either 1 or 1+i *)
    destruct (pos_one_or_next n) as [ -> | (k & ->) ].
    * (*  ω⁰.1 = 1+0 *)
      exists 0₀; now rewrite eps0_add_zero_right, <- eps0_omega_zero.
    * (* ω⁰.(1+(1+i)) = ω⁰.1 + ω⁰.(1+i) *)
      exists ω^⟨0₀,k⟩; now rewrite <- eps0_omega_zero, eps0_omega_eq_exp, eps0_add_exp.
  + right.
    exists (ω^⟨e,i⟩ +₀ f).
    rewrite <- eps0_add_assoc, <- eps0_omega_zero, eps0_omega_eq_exp, eps0_add_exp_lt; auto.
Qed.

Fact eps0_add_one_left_inj e f : 1₀ +₀ e = 1₀ +₀ f → e = f.
Proof. apply eps0_add_cancel. Qed.

    

