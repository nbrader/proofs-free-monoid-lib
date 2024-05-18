Require Import FreeMonoid.StructMagma. Export FreeMonoid.StructMagma.

Class Semigroup (A : Type) `{Magma A} := {
  sg_assoc : forall x y z : A, m_op x (m_op y z) = m_op (m_op x y) z
}.
