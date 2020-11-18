From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality.

Ltac inv H := inversion H; clear H; subst.

Lemma Zge_refl: forall (n: Z), (n >= n)%Z.
intros. lia. Qed.

Lemma ge_refl: forall (n: nat), n >= n.
intros. lia. Qed.

Lemma ge_diff: forall {n m : nat}, n >= m -> exists k, n = m + k.
Proof.
  induction 1.
  - exists 0. lia.
  - destruct IHle. exists (S x). lia.
Qed.

Example ge_diff_example1: exists k, 7 = 3 + k.
Proof.
  assert (Hge: 7 >= 3) by omega.
  destruct (ge_diff Hge) as [k Hk].
  exists k; assumption.
Qed.
