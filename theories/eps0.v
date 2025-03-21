(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import hydra ordered lex_list.

Import ListNotations hydra_notations.

Set Implicit Arguments.

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.
Arguments transitive {_}.

Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.

Unset Elimination Schemes.

Inductive E0 : Set :=
  | E0_cons : list (nat*E0) → E0.

Set Elimination Schemes.

Notation "'ω[' l ]" := (E0_cons l) (at level 1, no associativity, format "ω[ l ]").

Section E0_rect.

  Let E0_sub e f := match f with ω[l] => ∃n, (n,e) ∈ l end.

  Local Lemma E0_sub_wf : well_founded E0_sub.
  Proof.
    refine (fix loop f := _).
    destruct f as [ l ].
    constructor; intros e (n & Hn).
    induction l as [ | y l IHl ].
    + destruct Hn.
    + destruct Hn as [ Hn | Hn ]; [ | apply IHl; assumption ].
      generalize (loop (snd y)). (* be careful here on what loop is applied *)
      clear loop; now subst.
  Qed.

  Variables (P : E0 → Type)
            (HP : ∀l, (∀ n e, (n,e) ∈ l → P e) → P ω[l]).

  Theorem E0_rect e : P e.
  Proof.
    apply Fix_F with (2 := E0_sub_wf e).
    intros [l] Hl.
    apply HP.
    intros n f Hnf; apply Hl; simpl; eauto.
  Defined.

End E0_rect.

Definition E0_ind (P : _ → Prop) := E0_rect P.
Definition E0_rec (P : _ → Set) := E0_rect P.

Fixpoint E0_ht e :=
  match e with
  | ω[l] => lmax (map (λ '(_,f), 1+E0_ht f) l)
  end.

Definition E0_fall (P : list (nat*E0) → Prop) : E0 → Prop :=
  fix loop e :=
    match e with
    | ω[l] => P l ∧ fold_right (λ p, and (loop (snd p))) True l
    end.

Lemma E0_fall_fix P l : E0_fall P ω[l] ↔ P l ∧ ∀ i x, (i,x) ∈ l → E0_fall P x.
Proof.
  simpl; rewrite fold_right_conj.
  apply and_iff_compat_l.
  split.
  + intros H ? ?; apply (H (_,_)).
  + intros ? []; eauto.
Qed.

Section E0_fall_rect.

  Variables (P : list (nat*E0) → Prop)
            (Q : E0 → Type)
            (HQ : ∀l, P l 
                    → (∀ i e, (i,e) ∈ l → E0_fall P e)
                    → (∀ i e, (i,e) ∈ l → Q e)
                    → Q ω[l]).

  Theorem E0_fall_rect e : E0_fall P e → Q e.
  Proof. induction e; intros []%E0_fall_fix; eauto. Qed.

End E0_fall_rect.

Section lex_ilist.

  Variables (I X : Type) (R : I → I → Prop) (T : X → X → Prop).

  (* lexicographic order on lists, head is most significant *)
  Inductive lex_ilist : list (I*X) → list (I*X) → Prop :=
    | lex_ilist_nil ix m      : lex_ilist [] (ix::m)
    | lex_ilist_T i j x y l m : T x y → lex_ilist ((i,x)::l) ((j,y)::m)
    | lex_ilist_R i j x l m   : R i j → lex_ilist ((i,x)::l) ((j,x)::m)
    | lex_ilist_cons ix l m   : lex_ilist l m → lex_ilist (ix::l) (ix::m).

  Hint Constructors lex_ilist : core.

  (* introduction lemmas *)

  Fact lex_ilist_app_head c l m : lex_ilist l m → lex_ilist (c++l) (c++m).
  Proof. induction c; simpl; eauto. Qed.

  Hint Resolve lex_ilist_app_head : core.

  Fact lex_ilist_prefix' p x l : lex_ilist p (p++x::l).
  Proof. rewrite (app_nil_end p) at 1; auto. Qed.

  Hint Resolve lex_ilist_prefix' : core.

  Fact lex_ilist_prefix p l : l ≠ [] → lex_ilist p (p++l).
  Proof. destruct l; [ easy | auto ]. Qed. 

  Fact lex_ilist_snoc h l : lex_ilist l (l++[h]).
  Proof. now apply lex_ilist_prefix. Qed.

  (* inversion lemmas *)

  Inductive lex_ilist_inv_shape l m j y : I → X → Prop :=
    | in_lex_ilist_inv_shape2 i x : T x y → lex_ilist_inv_shape l m j y i x
    | in_lex_ilist_inv_shape3 i : R i j → lex_ilist_inv_shape l m j y i y
    | in_lex_ilist_inv_shape4 : lex_ilist l m → lex_ilist_inv_shape l m j y j y.

  Hint Constructors lex_ilist_inv_shape : core.

  Fact lex_ilist_inv l m :
         lex_ilist l m 
       ↔ match l, m with 
         | _, []      => False
         | [], _      => True
         | (i,x)::l, (j,y)::m => lex_ilist_inv_shape l m j y i x
         end.
  Proof. 
    split.
    + intros [ | | | [] ]; eauto.
    + revert l m; intros [|[]] [|[]] []; eauto.
  Qed.

  Section lex_ilist_irrefl.

    Let ll_irrefl_rec l m : lex_ilist l m → l = m → ∃ i x, (i,x) ∈ l ∧ (T x x ∨ R i i).
    Proof.
      induction 1 as [ | | | [i x] l m H IH ]; try easy.
      * inversion 1; subst; eauto.
      * inversion 1; subst; eauto.
      * injection 1; intros (? & ? & [])%IH; eauto.
    Qed.

    Lemma lex_ilist_irrefl l : lex_ilist l l → ∃ i x, (i,x) ∈ l ∧ (T x x ∨ R i i).
    Proof. intros ?%ll_irrefl_rec; auto. Qed.

  End lex_ilist_irrefl.

  Section lex_ilist_trans.

    Variables (l m k : list (I*X))
              (Rtrans : ∀ i x j y u z, (i,x) ∈ l → (j,y) ∈ m → (u,z) ∈ k → R i j → R j u → R i u)
              (Ttrans : ∀ i x j y u z, (i,x) ∈ l → (j,y) ∈ m → (u,z) ∈ k → T x y → T y z → T x z).

    Lemma lex_ilist_trans : lex_ilist l m → lex_ilist m k → lex_ilist l k.
    Proof.
      intros H1 H2; revert H1 k H2 Rtrans Ttrans.
      induction 1 as [ [] m | i j x y l m H1 | i j x l m H1 | [] l m H1 IH1 ];
        intros [|[]] Hk%lex_ilist_inv; try destruct Hk; eauto.
      constructor 4; apply IH1; eauto.
    Qed.

  End lex_ilist_trans.

  Hint Constructors sdec : core.

  Section lex_list_total.

    Variables (l m : list (I*X))
              (R_sdec : ∀ i x j y, (i,x) ∈ l → (j,y) ∈ m → sdec R i j)
              (T_sdec : ∀ i x j y, (i,x) ∈ l → (j,y) ∈ m → sdec T x y).

    Theorem lex_ilist_sdec : sdec lex_ilist l m.
    Proof.
      revert m R_sdec T_sdec.
      rename l into l'.
      induction l' as [ | [i x] l IHl ]; intros [ | [j y] m ] R_sdec T_sdec; eauto.
      destruct (T_sdec i x j y) as [ x y H | x | x y H ]; eauto.
      destruct (R_sdec i x j x) as [ i j H | i | i j H ]; eauto.
      destruct (IHl m); eauto.
    Qed.

  End lex_list_total.

End lex_ilist.

Arguments lex_ilist {I X}.

#[local] Hint Constructors lex_ilist : core.

Unset Elimination Schemes.

Inductive E0_lt : E0 → E0 → Prop :=
  | E0_lt_intro l m : lex_ilist lt E0_lt l m → E0_lt ω[l] ω[m].

Set Elimination Schemes.

Notation "e '<E₀' f" := (E0_lt e f) (at level 70, format "e  <E₀  f").

#[local] Hint Constructors E0_lt : core.

(* This inversion principle is enough to reason about <ε₀, 
   proceeding by induction on arguments *)
Fact E0_lt_inv l m : ω[l] <E₀ ω[m] ↔ lex_ilist lt E0_lt l m.
Proof. split; auto; now inversion 1. Qed.

(** We show that <E₀ is a strict order (irreflexive and transitive)
    and computably total, ie either e <E₀ f or e = f or f <E₀ e *)

(* irreflexive *)
Lemma E0_lt_irrefl e : ¬ e <E₀ e.
Proof.
  induction e as [ l IH ].
  intros (i & ? & ? & [ ?%(IH i) | ?%lt_irrefl ])%E0_lt_inv%lex_ilist_irrefl; auto.
Qed.

#[local] Hint Resolve lt_trans : core.

(* transitive *)
Lemma E0_lt_trans : transitive E0_lt.
Proof.
  intros e.
  induction e as [ l IH ]. 
  intros [] [] H1%E0_lt_inv H2%E0_lt_inv; constructor.
  revert H1 H2; apply lex_ilist_trans; eauto.
Qed.

#[local] Hint Constructors sdec : core.

Lemma lt_sdec i j : sdec lt i j.
Proof. destruct (lt_eq_lt_dec i j) as [ [ | []] | ]; eauto. Qed.

#[local] Hint Resolve lt_sdec : core.

(* computably total *)
Lemma E0_lt_sdec e f : sdec E0_lt e f.
Proof.
  revert f; induction e as [l]; intros [m].
  destruct (@lex_ilist_sdec _ _ lt E0_lt l m); eauto.
Qed.

#[local] Hint Resolve E0_lt_trans E0_lt_irrefl : core.

(* Hence decidable *)
Corollary E0_lt_dec e f : { e <E₀ f } + { ¬ e <E₀ f }.
Proof.
  destruct (E0_lt_sdec e f) as [ | | e f ]; eauto.
  right; intro; apply (@E0_lt_irrefl e); eauto.
Qed.

#[local] Hint Resolve E0_lt_dec : core.

Corollary E0_lt_trans' e f : clos_trans E0_lt e f → e <E₀ f.
Proof. induction 1; eauto. Qed.

(** An ordinal of ε₀ is in CNF if, recursivelly, it is
   of the shape ω[(i₁,e₁);...;(iₙ,eₙ)] with
   0 < i₁,...,iₙ and e₁ >ε₀ ... >ε₀ eₙ *)

Definition E0_cnf_pred l :=
    (∀ i e, (i,e) ∈ l → 0 < i) ∧ ordered E0_lt⁻¹ (map snd l).

Definition E0_cnf := E0_fall E0_cnf_pred.

Fact E0_cnf_fix l : 
    E0_cnf ω[l]
  ↔ ordered E0_lt⁻¹ (map snd l) ∧ ∀ i x, (i,x) ∈ l → 0 < i ∧ E0_cnf x.
Proof. 
  unfold E0_cnf.
  rewrite E0_fall_fix.
  unfold E0_cnf_pred; firstorder.
Qed.

Fact list_nil_choose X (l : list X) : {l = []} + {l ≠ []}.
Proof. destruct l; eauto; now right. Qed.

Fact list_fall_choose X (P Q : X → Prop) l :
        (∀x, x ∈ l → {P x} + {Q x})
      → { x | x ∈ l ∧ P x } + { ∀x, x ∈ l → Q x }.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + now right.
  + destruct (Hl x); eauto.
    destruct IHl as [ (? & []) | ]; eauto.
    right; intros ? [<- |]; eauto.
Qed.

(* E0_cnf is a strongly decidable predicate *)
Theorem E0_cnf_dec e : { E0_cnf e } + { ¬ E0_cnf e }.
Proof.
  induction e as [ l IHl ].
  destruct (ordered_dec E0_lt⁻¹ (map snd l))
    as [ H1 | H1 ]; eauto.
  + destruct list_fall_choose
      with (P := fun ix => fst ix = 0 \/ ~ E0_cnf (snd ix))
           (Q := fun ix => 0 < fst ix /\ E0_cnf (snd ix))
           (l := l)
      as [ ((i,x) & H2 & H3) | H2 ].
    * intros ([|i],x) [ H | H ]%IHl; simpl; try tauto.
      right; split; auto; lia.
    * right; rewrite E0_cnf_fix; intros (_ & G).
      simpl in H3; apply G in H2.
      destruct H2, H3; subst; tauto || lia.
    * left; rewrite E0_cnf_fix; split; auto.
      intros; apply (H2 (_,_)); auto.
  + right; rewrite E0_cnf_fix; tauto.
Qed.

Section squash.

  (* Squashing map a (strongly) decidable predicate into
     an equivalent proof irrelevant one *)

  Variables (P : Prop) (d : {P}+{~P}).

  Definition squash := if d then True else False.

  Fact squash_iff : squash ↔ P.
  Proof. unfold squash; destruct d; tauto. Qed.

  Fact squash_pirr : ∀ p1 p2 : squash, p1 = p2.
  Proof. unfold squash; destruct d; now intros [] []. Qed.

End squash.

(* We convert E0_cnf into an equivalent proof irrelevant predicate *)
Definition cnf e := squash (E0_cnf_dec e).

Fact cnf_iff e : cnf e ↔ E0_cnf e.          Proof. apply squash_iff. Qed.
Fact cnf_pirr e (h1 h2 : cnf e) : h1 = h2.  Proof. apply squash_pirr. Qed.

Fact cnf_fix l : 
    cnf ω[l]
  ↔ ordered E0_lt⁻¹ (map snd l) ∧ ∀ i x, (i,x) ∈ l → 0 < i ∧ cnf x.
Proof.
  rewrite cnf_iff, E0_cnf_fix.
  apply and_iff_compat_l.
  split; intros H ? ? []%H; split; auto; apply cnf_iff; auto.
Qed.

(* We convert the recursor *)
Fact cnf_rect (P : E0 → Type) :
    (∀l, ordered E0_lt⁻¹ (map snd l) 
       → (∀i x, (i,x) ∈ l → 0 < i ∧ cnf x)
       → (∀i x, (i,x) ∈ l → P x)
       → P ω[l])
  → ∀e, cnf e → P e.
Proof. 
  intros HP h H%cnf_iff; revert h H.
  induction 1 as [ l [] H2 IH ] using E0_fall_rect.
  apply HP; auto.
  split; eauto.
  apply cnf_iff, (H2 i); auto.
Qed.

(* We now show that E0_lt is well_founded on cnf because 
   on this subtype, it is equivalent to the nested list ordering lpo
   which is itself well_founded. To Check because this does
   not take multiplicities into account. *)

Definition epsilon0 := { e | cnf e }.

Notation ε₀ := epsilon0.

Section epsilon0_rect.






