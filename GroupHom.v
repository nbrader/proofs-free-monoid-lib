Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.StructGroup. Export FreeMonoid.StructGroup.

Section GroupHomomorphisms.

Class GroupHomomorphism {A B : Type} `{Group A} `{Group B} (f : A -> B) := {
  g_hom_preserves_op : forall x y : A, f (m_op x y) = m_op (f x) (f y);
}.

Theorem g_hom_preserves_id {A B : Type} `{Group A} `{Group B} (f : A -> B) (fHom : GroupHomomorphism f) : f (mn_id) = mn_id.
Proof.
  pose proof (@g_hom_preserves_op A B H H0 H1 H2 H3 H4 H5 H6 f fHom mn_id mn_id).
  rewrite mn_left_id in H7.
  rewrite H7. clear H7.
  pose proof (g_inv_right (f mn_id)).
  rewrite <- H7. clear H7.
  f_equal.
  pose proof (id_unique B).
  admit.
Admitted.

Theorem g_hom_preserves_inv {A B : Type} `{Group A} `{Group B} (f : A -> B) : forall x : A, f (g_inv x) = g_inv (f x).
  admit.
Admitted.

End GroupHomomorphisms.
