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
  assert (forall x : A, f x = m_op (f x) (f mn_id)).
  {
    intros.
    specialize (H8 x).
    rewrite mn_right_id in H8.
    apply H8.
  }
  specialize (H9 (mn_id)).
  assert (@is_left_partial_id B m_op (f mn_id)).
  {
    unfold is_left_partial_id.
    exists (f mn_id).
    apply eq_sym.
    exact H9.
  }
  apply (@partial_id_unique B H3 H4 H5 H6 (f mn_id)).
  exact H10.
Qed.

Theorem g_hom_preserves_inv {A B : Type} `{Group A} `{Group B} (f : A -> B) (fHom : GroupHomomorphism f) : forall x : A, f (g_inv x) = g_inv (f x).
  intros.
  pose proof (@g_hom_preserves_id A B H H0 H1 H2 H3 H4 H5 H6 f fHom).
  rewrite <- (g_inv_left x) in H7.
  rewrite g_hom_preserves_op in H7.
  pose proof (inv_unique_3 B (f (g_inv x)) (f x) H7). clear H7.
  exact H8.
Qed.

End GroupHomomorphisms.
