Require Import Coq.Arith.PeanoNat.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.
Require Import FreeMonoid.MonoidExampleBoolOr.
Require Import FreeMonoid.MonoidExampleNatMax1.

(* Define a function mapping bool to nat *)
Definition bool_to_nat (b : bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.

Instance BoolToNatHomomorphism : MonoidHomomorphism BoolOrMonoid NatMax1Monoid bool_to_nat.
Proof.
  split.
  - intros x y.
    destruct x, y; simpl; try reflexivity.
  - reflexivity.
Defined.
