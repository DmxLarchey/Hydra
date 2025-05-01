(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Euclid Utf8.

From Hydra Require Import ordered ordinal.

Section ord_omega.

  Local Definition nat_is_limit n := n ≠ 0 ∧ ¬ ∃j, n = j+1.

  Local Fact nat_no_limit n : nat_is_limit n → False.
  Proof.
    destruct n; intros (? & H); [ easy | ].
    apply H; exists n; lia.
  Qed.
  
  Local Definition nat_no_limit_any [X] n : nat_is_limit n → X.
  Proof. intros []%nat_no_limit. Qed.

  Definition ord_omega : ord.
  Proof.
    exists nat lt le 0 1 plus mult (@nat_no_limit_any _) (fun n => n); try (intros; lia).
    + apply lt_wf.
    + apply lt_sdec.
    + intros i j; exists (j-i); lia.
    + intros; now apply Nat.mul_le_mono.
    + destruct i as [ | i ].
      * right; intros []; lia.
      * left; exists i; lia.
    + destruct i as [ | i ].
      * intros []; lia.
      * exists i; lia.
    + intros ? l; exfalso; now apply nat_no_limit in l.
    + intros ? l; exfalso; now apply nat_no_limit in l.
    + intros ? l; exfalso; now apply nat_no_limit in l.
    + intros ? l; exfalso; now apply nat_no_limit in l.
    + intros ? ? l; exfalso; now apply nat_no_limit in l.
    + intros ? ? l; exfalso; now apply nat_no_limit in l.
    + intros n; exists (S n); lia.
  Defined.

End ord_omega.

