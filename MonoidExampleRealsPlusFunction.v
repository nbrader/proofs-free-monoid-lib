Require Import Coq.Reals.Reals.
Open Scope R_scope.

Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.
Require Import FreeMonoid.MonoidExampleRealsMult.
Require Import FreeMonoid.MonoidExampleRealsPlus.
Require Import FreeMonoid.MonoidExampleExtendToFunction.
Require Import Coq.Lists.List.
Import ListNotations.

Definition FunctionToRealsMagma (A : Type) := @ExtendToFunctionMagma A R RplusMagma RplusSemigroup RplusMonoid.
Definition FunctionToRealsSemigroup (A : Type) := @ExtendToFunctionSemigroup A R RplusMagma RplusSemigroup RplusMonoid.
Definition FunctionToRealsMonoid (A : Type) := @ExtendToFunctionMonoid A R RplusMagma RplusSemigroup RplusMonoid.

Theorem function_left_identity (A : Type) :
  forall (f : A -> R), (@m_op (A -> R) (FunctionToRealsMagma A)) (fun _ => mn_id) f = f.
Proof.
  intros f.
  apply app_op_left_id.
Qed.

Fixpoint monoid_fold {A : Type} `{Monoid A} (l : list A) : A :=
  match l with
  | [] => mn_id
  | x :: xs => m_op x (monoid_fold xs)
  end.

Theorem fold_example (A : Type) (l : list (A -> R)) :
  monoid_fold l = fun x => monoid_fold (map (fun f => f x) l).
Proof.
  (* Coq will automatically resolve that we're using FunctionToRealsMonoid *)
  simpl.
  induction l as [| f fs IH].
  - (* Base case: empty list *)
    reflexivity.
  - (* Inductive step: f :: fs *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.