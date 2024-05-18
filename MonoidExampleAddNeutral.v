Require Import Coq.Init.Datatypes.
Require Import FreeMonoid.StructMonoid.

Definition neutral_op (A : Type) `{Hmon : Monoid A} (x y : option A) : option A := 
  match x, y with
  | None, None => None
  | None, Some y' => Some y'
  | Some x', None => Some x'
  | Some x', Some y' => Some (m_op x' y')
  end.

Instance AddNeutralMagma (A : Type) `{Hmon : Monoid A} : Magma (option A) := {
  m_op := neutral_op A
}.

Lemma neutral_op_assoc (A : Type) `{Hmon : Monoid A} : 
  forall x y z : option A, m_op x (m_op y z) = m_op (m_op x y) z.
Proof.
  intros [x|] [y|] [z|]; unfold m_op, neutral_op; simpl; try reflexivity.
  - (* Case: Some x, Some y, Some z *)
    rewrite sg_assoc. reflexivity.
Qed.

Instance AddNeutralSemigroup (A : Type) `{Hmon : Monoid A} : Semigroup (option A) := {
  sg_assoc := neutral_op_assoc A
}.

Lemma neutral_op_left_id (A : Type) `{Hmon : Monoid A} : 
  forall x : option A, m_op None x = x.
Proof.
  intros [x|]; unfold m_op, neutral_op; simpl; reflexivity.
Qed.

Lemma neutral_op_right_id (A : Type) `{Hmon : Monoid A} : 
  forall x : option A, m_op x None = x.
Proof.
  intros [x|]; unfold m_op, neutral_op; simpl; reflexivity.
Qed.

Instance AddNeutralMonoid (A : Type) `{Hmon : Monoid A} : Monoid (option A) := {
  mn_id := None;
  mn_left_id := neutral_op_left_id A;
  mn_right_id := neutral_op_right_id A
}.
