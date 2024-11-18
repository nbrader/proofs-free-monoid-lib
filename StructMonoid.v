Require Import FreeMonoid.StructSemigroup. Export FreeMonoid.StructSemigroup.

Definition is_left_id (A : Type) (m_op : A -> A -> A) (mn_id : A) := forall x : A, m_op mn_id x = x.
Definition is_right_id (A : Type) (m_op : A -> A -> A) (mn_id : A) := forall x : A, m_op x mn_id = x.
Definition is_id (A : Type) (m_op : A -> A -> A) (mn_id : A) := (is_left_id A m_op mn_id) /\ (is_right_id A m_op mn_id).

Class Monoid (A : Type) `{Semigroup A} := {
  mn_id : A;
  mn_left_id : is_left_id A m_op mn_id;
  mn_right_id : is_right_id A m_op mn_id;
}.
