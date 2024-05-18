Require Import Coq.Init.Datatypes.
Require Import FreeMonoid.StructMonoid.

Definition first_op (A : Type) (x y : option A) : option A := 
  match x, y with
  | None, None => None
  | None, Some y' => Some y'
  | Some x', None => Some x'
  | Some x', Some y' => Some x'
  end.

Instance FirstMagma (A : Type) : Magma (option A) := {
  m_op := first_op A
}.

Lemma first_op_assoc (A : Type) : 
  forall x y z : option A, m_op x (m_op y z) = m_op (m_op x y) z.
Proof.
  intros [x|] [y|] [z|]; unfold m_op, first_op; simpl; try reflexivity.
Qed.

Instance FirstSemigroup (A : Type) : Semigroup (option A) := {
  sg_assoc := first_op_assoc A
}.

Lemma first_op_left_id (A : Type) : 
  forall x : option A, m_op None x = x.
Proof.
  intros [x|]; unfold m_op, first_op; simpl; try reflexivity.
Qed.

Lemma first_op_right_id (A : Type) : 
  forall x : option A, m_op x None = x.
Proof.
  intros [x|]; unfold m_op, first_op; simpl; try reflexivity.
Qed.

Instance FirstMonoid (A : Type) : Monoid (option A) := {
  mn_id := None;
  mn_left_id := first_op_left_id A;
  mn_right_id := first_op_right_id A
}.
