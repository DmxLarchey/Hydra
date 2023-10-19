(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Utf8.
From Hydra Require Import hydra.

Import ListNotations hydra_notations.

Set Implicit Arguments.

#[local] Hint Resolve in_cons in_eq in_elt in_or_app : core.

Section Hydrae.

  Inductive Hydra :=
    | Hydra_node  : Hydrae → Hydra
  with Hydrae :=
    | Hydrae_nil  : Hydrae
    | Hydrae_cons : Hydra → Hydrae → Hydrae.

  Inductive Fall2_Hl {X} (R : Hydra → X → Prop) : Hydrae → list X → Prop :=
    | Fall2_Hl_nil : Fall2_Hl R Hydrae_nil []
    | Fall2_Hl_cons H HH x l : R H x → Fall2_Hl R HH l → Fall2_Hl R (Hydrae_cons H HH) (x::l).

  Fact Fall2_Hl_inv X R HH l :
        @Fall2_Hl X R HH l
      → match HH, l with
        | Hydrae_nil,       []   => True
        | Hydrae_cons H HH, x::l => R H x ∧ Fall2_Hl R HH l
        | _,                _    => False
        end.
  Proof. intros []; eauto. Qed.

  Inductive Hydra_hydra_eq : Hydra → hydra → Prop :=
    | Hh_eq HH m : Fall2_Hl Hydra_hydra_eq HH m → Hydra_hydra_eq (Hydra_node HH) ⟨m⟩.

  Hint Constructors Hydra Hydrae Fall2_Hl Hydra_hydra_eq : core.

  Fact Hydra_hydra_eq_inv HH m : Hydra_hydra_eq (Hydra_node HH) ⟨m⟩ → Fall2_Hl Hydra_hydra_eq HH m.
  Proof. now inversion 1. Qed.

  (* The relation Hydra_hydra_eq is functional and injective *)

  Fixpoint Hydra_hydra_eq_fun H h (e : Hydra_hydra_eq H h) { struct e } : ∀g, Hydra_hydra_eq H g → h = g.
  Proof.
    destruct e as [ HH m E1 ].
    intros [ l ] E2%Hydra_hydra_eq_inv.
    revert l E2.
    induction E1 as [ | H HH x m E1 E2 IHE2 ].
    + intros [] ?%Fall2_Hl_inv; now auto.
    + intros [ | y l ] E3%Fall2_Hl_inv; [ easy | ].
      destruct E3 as [ E3 E4 ].
      do 2 f_equal.
      * apply (Hydra_hydra_eq_fun _ _ E1 _ E3).
      * specialize (IHE2 _ E4); now inversion IHE2.
  Qed.

  Fixpoint Hydra_hydra_eq_inj H h (e : Hydra_hydra_eq H h) { struct e } : ∀G, Hydra_hydra_eq G h → H = G.
  Proof.
    destruct e as [ HH m E1 ].
    intros [ GG ] E2%Hydra_hydra_eq_inv.
    revert GG E2.
    induction E1 as [ | H HH x m E1 E2 IHE2 ].
    + intros [] ?%Fall2_Hl_inv; now auto.
    + intros [ | G GG ] E3%Fall2_Hl_inv; [ easy | ].
      destruct E3 as [ E3 E4 ].
      do 2 f_equal.
      * apply (Hydra_hydra_eq_inj _ _ E1 _ E3).
      * specialize (IHE2 _ E4); now inversion IHE2.
  Qed.

  (* The relation Hydra_hydra_eq can be realized by a function in both directions.
     This is a mutual fixpoint.*)

  Fixpoint Hydra2hydra_pwc H : { h | Hydra_hydra_eq H h }
  with Hydrae2list_hydra_pwc HH : { m | Fall2_Hl Hydra_hydra_eq HH m }.
  Proof.
    + destruct H as [ HH ].
      destruct (Hydrae2list_hydra_pwc HH) as (m & Hm).
      exists ⟨m⟩; eauto.
    + destruct HH as [ | H HH ].
      * exists []; eauto.
      * destruct (Hydra2hydra_pwc H) as (h & ?).
        destruct (Hydrae2list_hydra_pwc HH) as (m & ?).
        exists (h::m); eauto.
  Qed.

  (* We use that hydra_rect recursor above here, which contains a 
     fixpoint itself *)
  Definition hydra2Hydra_pwc (h : hydra) : { H | Hydra_hydra_eq H h }.
  Proof.
    induction h as [ m IHm ] using hydra_rect.
    assert { HH | Fall2_Hl Hydra_hydra_eq HH m } as (HH & ?); eauto.
    revert IHm.
    induction m as [ | h m IHm ]; intros Hm; eauto.
    destruct (Hm h) as (H & ?); auto.
    destruct IHm as (HH & ?); eauto.
  Qed.

  (* hydra2Hydra/Hydra2hydra form a bijection *)

  Definition Hydra2hydra H := proj1_sig (Hydra2hydra_pwc H).
  Definition hydra2Hydra h := proj1_sig (hydra2Hydra_pwc h).

  Fact Hydra2hydra_spec H : Hydra_hydra_eq H (Hydra2hydra H).    Proof. apply (proj2_sig _). Qed.
  Fact hydra2Hydra_spec h : Hydra_hydra_eq (hydra2Hydra h) h.    Proof. exact (proj2_sig (hydra2Hydra_pwc _)). Qed.

  Hint Resolve hydra2Hydra_spec Hydra2hydra_spec : core.

  Theorem hydra2Hydra2hydra H : hydra2Hydra (Hydra2hydra H) = H.
  Proof. apply Hydra_hydra_eq_inj with (1 := hydra2Hydra_spec _); auto. Qed.

  Theorem Hydra2hydra2Hydra h : Hydra2hydra (hydra2Hydra h) = h.
  Proof. apply Hydra_hydra_eq_fun with (1 := Hydra2hydra_spec _); auto. Qed.

  (* We can derive fixpont equations for hydra2Hydra_fix and Hydra2hydra_fix *)

  Fixpoint fold_Hydrae {X} (f : Hydra → X → X) x HH :=
    match HH with
    | Hydrae_nil       => x
    | Hydrae_cons H HH => f H (fold_Hydrae f x HH)
    end.

  Lemma hydra2Hydra_fix l : hydra2Hydra ⟨l⟩ = Hydra_node (fold_right (λ x HH, Hydrae_cons (hydra2Hydra x) HH) Hydrae_nil l).
  Proof.
    apply Hydra_hydra_eq_inj with (1 := hydra2Hydra_spec _).
    constructor.
    induction l; simpl; eauto.
  Qed.

  Lemma Hydra2hydra_fix HH : Hydra2hydra (Hydra_node HH) = ⟨fold_Hydrae (λ H l, (Hydra2hydra H)::l) [] HH⟩.
  Proof.
    apply Hydra_hydra_eq_fun with (1 := Hydra2hydra_spec _).
    constructor.
    induction HH; simpl; eauto.
  Qed.

End Hydrae.