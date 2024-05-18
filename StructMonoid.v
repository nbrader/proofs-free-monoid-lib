Require Import FreeMonoid.StructSemigroup. Export FreeMonoid.StructSemigroup.

Class Monoid (A : Type) `{Semigroup A} := {
  mn_id : A;
  mn_left_id : forall x : A, m_op mn_id x = x;
  mn_right_id : forall x : A, m_op x mn_id = x
}.
