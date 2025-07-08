Require Import FreeMonoid.MonoidFree.
Require Import FreeMonoid.StructMonoid.
Require Import Coq.Arith.Plus.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import ArithRing Ring.
Require Import MonoidConcat.

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

Module NatBasis.
  Definition Basis := nat.
End NatBasis.

Module NatFreeMonoid := FreeMonoidModule NatBasis.

(* Define a proposition that asserts something about lifted_function *)
Theorem lifted_function_correct : forall x y z : nat,
  NatFreeMonoid.foldMap nat_Monoid (fun (b : nat) => 2 * b) [x; y; z] = 2 * x + 2 * y + 2 * z.
Proof.
  intros x y z.
  unfold NatFreeMonoid.foldMap.
  simpl.
  rewrite !Nat.add_assoc.  (* Use associativity of addition to simplify the nested additions *)
  ring.
Qed.

Theorem foldMap_mconcat_comparison_1 : forall (A : Type), forall (A_magma : Magma A), forall (A_semigroup : Semigroup A), forall (A_monoid : Monoid A), forall P : (nat -> A), forall n : nat,
  NatFreeMonoid.foldMap A_monoid P (@mconcat _ _ _ NatFreeMonoid.FreeMonoid_Monoid (fun x => [x]) n) = mconcat A P n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

(* Compute (NatFreeMonoid.foldMap nat_Monoid (fun b => 2*b) [0; 1; 2]). *)