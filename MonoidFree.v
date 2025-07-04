Require Import Coq.Lists.List.
Import ListNotations.
Require Import FreeMonoid.StructMonoid. Export FreeMonoid.StructSemigroup.
Require Import FreeMonoid.MonoidHom.
Require Import Coq.Arith.Mult.

Module Type BasisType.
  Parameter Basis : Type.
End BasisType.

Module FreeMonoidModule (X : BasisType).
Definition Basis := X.Basis.

(* The type of lists over the Basis, representing the free monoid on Basis *)
Definition FreeMonoid := list Basis.

Instance FreeMonoid_Magma : Magma FreeMonoid := {
  m_op := @app Basis
}.

Instance FreeMonoid_Semigroup : Semigroup FreeMonoid := {
  sg_assoc := @app_assoc Basis
}.

Instance FreeMonoid_Monoid : Monoid FreeMonoid := {
  mn_id := [];
  mn_left_id := @app_nil_l Basis;
  mn_right_id := @app_nil_r Basis
}.

Definition canonical_inj (b : Basis) : FreeMonoid := [b].

(* Universal property definitions *)
Section UniversalProperty.

(*
        (Set)               (Mon)

      i
    X ⟶ U(A)                A
      ↘   ↓ U(foldMap f)     ↓ foldMap f
     f   U(B)                B
    
    
    Please note: The forgetful functor U is left implicit and X is called "Basis" in the code below. *)

(*
  For any monoid B, foldMap extends a function f : A -> B to a monoid homomorphism [A] -> B

  As the name suggests, this is equal to the following:
    fold_right m_op mn_id ∘ map f.

  The above form is valid syntax with the following imports:
    Require Import Coq.Program.Basics.
    Require Import Coq.Program.Combinators.
  
  I've chosen not to use this form to reduce dependencies and allow the simpl tactic to reduce further.
*)
Definition foldMap {B : Type} `{Semigroup B} (mb : Monoid B) (f : Basis -> B) : FreeMonoid -> B :=
  fold_right (fun b acc => m_op (f b) acc) mn_id.

(* Proof that foldMap f is a monoid homomorphism *)
Lemma foldMap_mor {B : Type} `{Semigroup B} (mb : Monoid B) (f : Basis -> B) : MonoidHomomorphism FreeMonoid_Monoid mb (foldMap mb f).
Proof.
  split.
  - intros x y. unfold foldMap.
    induction x as [|b bs IH].
    + simpl. rewrite mn_left_id. reflexivity.
    + simpl. rewrite <- sg_assoc. f_equal. apply IH.
  - simpl. reflexivity.
Qed.

Lemma foldMap_universal {B : Type} `{Semigroup B} (mb : Monoid B) (f : Basis -> B) (x : Basis) :
  foldMap mb f (canonical_inj x) = f x.
Proof.
  unfold foldMap, canonical_inj. simpl.
  simpl. rewrite mn_right_id. reflexivity.
Qed.

(* Proof that foldMap is unique *)
Lemma foldMap_unique {B : Type} `{Semigroup B} (mb : Monoid B) (f : Basis -> B) (g : FreeMonoid -> B)
  (gHom : MonoidHomomorphism FreeMonoid_Monoid mb g) :
  (forall x, g (canonical_inj x) = f x) -> forall y, g y = foldMap mb f y.
Proof.
  unfold foldMap.
  intros.
  induction y as [|b bs IHbs].
  - (* Base case for the empty list *)
    unfold foldMap. simpl.
    assert (H_mn_id: g [] = mn_id).
    { 
      destruct gHom.
      apply homo_preserves_id.
    }
    exact H_mn_id.
  - (* Inductive step for non-empty lists *)
    simpl.
    specialize (H1 b).  (* Utilize the fact that g (canonical_inj b) = f b *)
    simpl. rewrite <- H1.
    assert (H_cons: g (b :: bs) = m_op (g [b]) (g bs)).
    {
      destruct gHom.
      rewrite <- homo_preserves_op.
      - f_equal.
    }
    rewrite H_cons.
    f_equal.
    + apply IHbs.
Qed.

End UniversalProperty.

End FreeMonoidModule.
