(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Arith Lia Wellfounded Utf8.
From Hydra Require Import utils ordered.

Import ListNotations.

Set Implicit Arguments.

Section lex2.

  Variables (X I : Type) (RX : X → X → Prop) (RI : I → I → Prop).

  Inductive lex2 : X*I → X*I → Prop :=
    | lex2_left x i y j : RX x y → lex2 (x,i) (y,j)
    | lex2_right x i j  : RI i j → lex2 (x,i) (x,j).

  Hint Constructors lex2 : core.

  Fact lex2_inv xi yj :
      lex2 xi yj
    → match xi, yj with
      | (x,i), (y,j) => RX x y ∨ x = y ∧ RI i j
      end.
  Proof. destruct 1; eauto. Qed.

  Lemma lex2_irrefl xi : lex2 xi xi → RX (fst xi) (fst xi) ∨ RI (snd xi) (snd xi).
  Proof. revert xi; intros []?%lex2_inv; simpl; tauto. Qed.

  Section lex2_trans.

    Variables (l m p : list (X*I))
              (RXtrans : ∀ x i y j z u, (x,i) ∈ l → (y,j) ∈ m → (z,u) ∈ p → RX x y → RX y z → RX x z)
              (RItrans : ∀ x i y j z u, (x,i) ∈ l → (y,j) ∈ m → (z,u) ∈ p → RI i j → RI j u → RI i u).

    Lemma lex2_trans xi yj zk : xi ∈ l → yj ∈ m → zk ∈ p → lex2 xi yj → lex2 yj zk → lex2 xi zk.
    Proof.
      revert xi yj zk.
      intros [] [] [] ? ? ? [ | (<- & ?) ]%lex2_inv
                            [ | (<- & ?) ]%lex2_inv; eauto.
    Qed.

  End lex2_trans.

  Hint Constructors sdec : core.

  Section lex2_sdec.

    Variables (l m : list (X*I))
              (RX_sdec : ∀ x i y j, (x,i) ∈ l → (y,j) ∈ m → sdec RX x y)
              (RI_sdec : ∀ x i y j, (x,i) ∈ l → (y,j) ∈ m → sdec RI i j).

    Lemma lex2_sdec : ∀ xi yj, xi ∈ l → yj ∈ m → sdec lex2 xi yj.
    Proof.
      intros (x,i) (y,j) ? ?.
      destruct (RX_sdec x i y j) as [| x |]; eauto.
      destruct (RI_sdec x i x j); eauto.
    Qed.

  End lex2_sdec.

  Section Acc.

    Hypothesis RI_wf : well_founded RI.

    Fact Acc_lex2 x : Acc RX x → ∀i, Acc lex2 (x,i).
    Proof.
      induction 1 as [ x _ IHx ]; intros i.
      induction i using (well_founded_induction RI_wf).
      constructor.
      intros [] [ | (<- & ?) ]%lex2_inv; eauto.
    Qed.

  End Acc.

End lex2.

Arguments lex2 {_ _}.

Fact lex2_mono X I (R R' : X → X → Prop) (T T' : I → I → Prop) p q :
    (R (fst p) (fst q) → R' (fst p) (fst q))
  → (T (snd p) (snd q) → T' (snd p) (snd q))
  → lex2 R  T  p q 
  → lex2 R' T' p q.
Proof. induction 3; [ constructor 1 | constructor 2 ]; auto. Qed.


