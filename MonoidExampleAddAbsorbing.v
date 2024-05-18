Require Import Coq.Init.Datatypes.
Require Import FreeMonoid.StructMonoid.

Definition absorbing_op (A : Type) `{Hmon : Monoid A} (x y : option A) : option A := 
  match x, y with
  | None, None => None
  | None, Some y' => None
  | Some x', None => None
  | Some x', Some y' => Some (m_op x' y')
  end.

Instance AddAbsorbingMagma (A : Type) `{Hmon : Monoid A} : Magma (option A) := {
  m_op := absorbing_op A
}.

Lemma absorbing_op_assoc (A : Type) `{Hmon : Monoid A} : 
  forall x y z : option A, m_op x (m_op y z) = m_op (m_op x y) z.
Proof.
  intros [x|] [y|] [z|]; unfold m_op, absorbing_op; simpl; try reflexivity.
  - (* Case: Some x, Some y, Some z *)
    rewrite sg_assoc. reflexivity.
Qed.

Instance AddAbsorbingSemigroup (A : Type) `{Hmon : Monoid A} : Semigroup (option A) := {
  sg_assoc := absorbing_op_assoc A
}.

Lemma absorbing_op_left_id (A : Type) `{Hmon : Monoid A} : 
  forall x : option A, m_op (Some mn_id) x = x.
Proof.
  intros [x|]; unfold m_op, absorbing_op; simpl.
  - f_equal.
    apply mn_left_id.
  - reflexivity.
Qed.

Lemma absorbing_op_right_id (A : Type) `{Hmon : Monoid A} : 
  forall x : option A, m_op x (Some mn_id) = x.
Proof.
  intros [x|]; unfold m_op, absorbing_op; simpl.
  - f_equal.
    apply mn_right_id.
  - reflexivity.
Qed.

Instance AddAbsorbingMonoid (A : Type) `{Hmon : Monoid A} : Monoid (option A) := {
  mn_id := Some mn_id;
  mn_left_id := absorbing_op_left_id A;
  mn_right_id := absorbing_op_right_id A
}.
