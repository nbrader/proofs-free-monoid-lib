Require Import FreeMonoid.StructMonoid. Export FreeMonoid.StructSemigroup.
Require Import Setoid.

Definition is_left_inv (A : Type) (m_op : A -> A -> A) (mn_id : A) (g_inv : A -> A) := forall x : A, m_op (g_inv x) x = mn_id.
Definition is_right_inv (A : Type) (m_op : A -> A -> A) (mn_id : A) (g_inv : A -> A) := forall x : A, m_op x (g_inv x) = mn_id.
Definition is_inv (A : Type) (m_op : A -> A -> A) (mn_id : A) (g_inv : A -> A) := (is_left_inv A m_op mn_id g_inv) /\ (is_right_inv A m_op mn_id g_inv).

Class Group (A : Type) `{Monoid A} := {
  g_inv : A -> A;
  g_inv_left : is_left_inv A m_op mn_id g_inv;
  g_inv_right : is_right_inv A m_op mn_id g_inv;
}.

Theorem id_unique (A : Type) `{Group A} (x y : A) (x_id : is_id A m_op x) (y_id : is_id A m_op y) : x = y.
Proof.
  unfold is_id in *.
  destruct x_id.
  destruct y_id.
  unfold is_left_id in *.
  unfold is_right_id in *.
  assert (x = x) by reflexivity.
  rewrite <- H5 in H7.
  rewrite H4 in H7.
  apply H7.
Qed.

Definition is_left_partial_id (A : Type) (m_op : A -> A -> A) (partial_id : A) := exists x : A, m_op partial_id x = x.
Definition is_right_partial_id (A : Type) (m_op : A -> A -> A) (partial_id : A) := exists x : A, m_op x partial_id = x.
Definition is_partial_id (A : Type) (m_op : A -> A -> A) (partial_id : A) := (is_left_partial_id A m_op partial_id) /\ (is_right_partial_id A m_op partial_id).

Theorem id_unique_strong (A : Type) `{Group A} (x y : A) (x_id : is_partial_id A m_op x) (y_id : is_id A m_op y) : x = mn_id.
Proof.
  unfold is_id in *.
  destruct x_id as [temp01 temp02]. clear temp02.
  unfold is_left_id in *.
  unfold is_right_id in *.
  unfold is_left_partial_id in *.
  destruct temp01 as [x0 temp02].
  pose proof (@g_inv_right A H H0 H1 H2 x0) as temp03.
  rewrite <- temp02 in temp03 at 1.
  rewrite <- sg_assoc in temp03.
  rewrite g_inv_right in temp03.
  rewrite mn_right_id in temp03.
  apply temp03.
Qed.