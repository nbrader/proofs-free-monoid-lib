Require Import FreeMonoid.StructMonoid. Export FreeMonoid.StructMonoid.

(* Semiring structure - two monoids with distributivity *)
(* A semiring consists of:
   - An additive commutative monoid (S, ⊕, 𝟎)
   - A multiplicative monoid (S, ⊗, 𝟏)
   - Distributivity of multiplication over addition
   - Zero annihilation *)

Class Semiring (A : Type) := {
  (* Addition operation and structure *)
  add_op : A -> A -> A;
  add_zero : A;
  add_assoc : forall x y z : A, add_op x (add_op y z) = add_op (add_op x y) z;
  add_left_id : forall x : A, add_op add_zero x = x;
  add_right_id : forall x : A, add_op x add_zero = x;
  add_comm : forall x y : A, add_op x y = add_op y x;

  (* Multiplication operation and structure *)
  mul_op : A -> A -> A;
  mul_one : A;
  mul_assoc : forall x y z : A, mul_op x (mul_op y z) = mul_op (mul_op x y) z;
  mul_left_id : forall x : A, mul_op mul_one x = x;
  mul_right_id : forall x : A, mul_op x mul_one = x;

  (* Distributivity *)
  mul_add_distr_l : forall x y z : A, mul_op x (add_op y z) = add_op (mul_op x y) (mul_op x z);
  mul_add_distr_r : forall x y z : A, mul_op (add_op x y) z = add_op (mul_op x z) (mul_op y z);

  (* Zero annihilates *)
  mul_zero_l : forall x : A, mul_op add_zero x = add_zero;
  mul_zero_r : forall x : A, mul_op x add_zero = add_zero;
}.

(* Notation for semiring operations *)
Notation "x ⊕ y" := (add_op x y) (at level 50, left associativity).
Notation "x ⊗ y" := (mul_op x y) (at level 40, left associativity).
Notation "𝟎" := add_zero.
Notation "𝟏" := mul_one.

(* Convenience lemmas for semiring properties *)
Lemma semiring_add_assoc (A : Type) `{Semiring A} : forall x y z : A, x ⊕ (y ⊕ z) = (x ⊕ y) ⊕ z.
Proof. apply add_assoc. Qed.

Lemma semiring_mul_assoc (A : Type) `{Semiring A} : forall x y z : A, x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z.
Proof. apply mul_assoc. Qed.

Lemma semiring_add_comm (A : Type) `{Semiring A} : forall x y : A, x ⊕ y = y ⊕ x.
Proof. apply add_comm. Qed.

Lemma semiring_distr_l (A : Type) `{Semiring A} : forall x y z : A, x ⊗ (y ⊕ z) = (x ⊗ y) ⊕ (x ⊗ z).
Proof. apply mul_add_distr_l. Qed.

Lemma semiring_distr_r (A : Type) `{Semiring A} : forall x y z : A, (x ⊕ y) ⊗ z = (x ⊗ z) ⊕ (y ⊗ z).
Proof. apply mul_add_distr_r. Qed.