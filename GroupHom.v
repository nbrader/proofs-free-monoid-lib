Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.StructGroup. Export FreeMonoid.StructGroup.

Section GroupHomomorphisms.

Class GroupHomomorphism {A B : Type} `{Group A} `{Group B} (f : A -> B) := {
  g_hom_preserves_op : forall x y : A, f (m_op x y) = m_op (f x) (f y);
}.

Theorem g_hom_preserves_id {A B : Type} `{Group A} `{Group B} (f : A -> B) (fHom : GroupHomomorphism f) : f (mn_id) = mn_id.
Proof.
  pose proof (@g_hom_preserves_op A B H H0 H1 H2 H3 H4 H5 H6 f fHom).
  assert (forall x : A, f (m_op x mn_id) = m_op (f x) (f mn_id)) by (intros; apply H7; rewrite mn_right_id).
  assert (forall x : A, f (m_op mn_id x) = m_op (f mn_id) (f x)) by (intros; apply H7; rewrite mn_right_id).
  assert (forall x : A, f x = m_op (f x) (f mn_id)).
  {
    intros.
    specialize (H8 x).
    rewrite mn_right_id in H8.
    apply H8.
  }
  apply (id_unique B).
  - unfold is_id.
    split.
    + unfold is_left_id.
      intros.
      admit.
    + unfold is_right_id.
      admit.
  - unfold is_id.
    split.
    + apply mn_left_id.
    + apply mn_right_id.
Admitted.

Theorem g_hom_preserves_inv {A B : Type} `{Group A} `{Group B} (f : A -> B) : forall x : A, f (g_inv x) = g_inv (f x).
  admit.
Admitted.

End GroupHomomorphisms.
