Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import FreeMonoid.StructMonoid.

Instance EndoMagma (A : Type) : Magma (A -> A) := {
  m_op := compose
}.

Lemma compose_assoc (A : Type) : forall x y z : A -> A, m_op x (m_op y z) = m_op (m_op x y) z.
Proof.
  intros x y z.
  unfold m_op, compose.
  reflexivity.
Qed.

Instance EndoSemigroup (A : Type) : Semigroup (A -> A) := {
  sg_assoc := compose_assoc A
}.

Lemma id_left (A : Type) : forall f : A -> A, id ∘ f = f.
Proof.
  intros f.
  unfold compose.
  reflexivity.
Qed.

Lemma id_right (A : Type) : forall f : A -> A, f ∘ id = f.
Proof.
  intros f.
  unfold compose.
  reflexivity.
Qed.

Instance EndoMonoid (A : Type) : Monoid (A -> A) := {
  mn_id := id;
  mn_left_id := id_left A;
  mn_right_id := id_right A
}.
