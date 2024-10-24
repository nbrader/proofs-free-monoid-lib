Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import FreeMonoid.StructMonoid.

Definition app_op (A B : Type) `{Hmon : Monoid B} (f g : A -> B) : A -> B := fun x => m_op (f x) (g x).

Instance ExtendToFunctionMagma (A B : Type) `{Hmon : Monoid B} : Magma (A -> B) := {
  m_op := app_op A B
}.

Lemma app_op_assoc (A B : Type) `{Hmon : Monoid B} : 
  forall f g h : A -> B, m_op f (m_op g h) = m_op (m_op f g) h.
Proof.
  intros f g h.
   unfold m_op; simpl.
   unfold app_op; simpl.
   apply functional_extensionality.
   intros.
   rewrite sg_assoc.
   reflexivity.
Qed.

Instance ExtendToFunctionSemigroup (A B : Type) `{Hmon : Monoid B} : Semigroup (A -> B) := {
  sg_assoc := app_op_assoc A B
}.

Lemma app_op_left_id (A B : Type) `{Hmon : Monoid B} : 
  forall x : A -> B, m_op (fun _ => mn_id) x = x.
Proof.
  intros x.
  unfold m_op; simpl.
  unfold app_op.
  apply functional_extensionality.
  intros.
  apply mn_left_id.
Qed.

Lemma app_op_right_id (A B : Type) `{Hmon : Monoid B} : 
  forall x : A -> B, m_op x (fun _ => mn_id) = x.
Proof.
  intros x.
  unfold m_op; simpl.
  unfold app_op.
  apply functional_extensionality.
  intros.
  apply mn_right_id.
Qed.

Instance ExtendToFunctionMonoid (A B : Type) `{Hmon : Monoid B} : Monoid (A -> B) := {
  mn_id := fun _ => mn_id;
  mn_left_id := app_op_left_id A B;
  mn_right_id := app_op_right_id A B
}.
