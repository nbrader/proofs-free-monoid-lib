Require Import FreeMonoid.MonoidFree.
Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.
Require Import Coq.Arith.Plus.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import ArithRing Ring.

Instance nat_Magma : Magma nat := {
  m_op := plus
}.

Instance nat_Semigroup : Semigroup nat := {
  sg_assoc := Nat.add_assoc
}.

Instance nat_Monoid : Monoid nat := {
  mn_id := 0;
  mn_left_id := Nat.add_0_l;
  mn_right_id := Nat.add_0_r
}.

Axiom Basis_to_nat : MonoidFree.Basis -> nat.

(* Define example_function using the Basis from MonoidFree directly *)
Definition example_function (b : MonoidFree.Basis) : nat := Basis_to_nat b * 2.

(* Define a proposition that asserts something about lifted_function *)
Theorem lifted_function_correct : forall x y z : MonoidFree.Basis,
  (MonoidFree.extend example_function) [x; y; z] = 2 * Basis_to_nat x + 2 * Basis_to_nat y + 2 * Basis_to_nat z.
Proof.
  intros x y z.
  unfold MonoidFree.extend, example_function.
  simpl.
  rewrite !Nat.add_assoc.  (* Use associativity of addition to simplify the nested additions *)
  ring.
Qed.


Axiom b0 : MonoidFree.Basis.
Axiom b1 : MonoidFree.Basis.
Axiom b2 : MonoidFree.Basis.
Axiom b3 : MonoidFree.Basis.
Axiom basis_b0 : Basis_to_nat b0 = 0.
Axiom basis_b1 : Basis_to_nat b1 = 1.
Axiom basis_b2 : Basis_to_nat b2 = 2.
Axiom basis_b3 : Basis_to_nat b3 = 3.

Theorem example_theorem : (MonoidFree.extend example_function) [b0; b1; b2] = 2*(0+1+2).
Proof.
  rewrite lifted_function_correct.
  rewrite basis_b0.
  rewrite basis_b1.
  rewrite basis_b2.
  simpl.
  reflexivity.
Qed.
