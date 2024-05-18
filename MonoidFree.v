Require Import Coq.Lists.List.
Import ListNotations.
Require Import FreeMonoid.StructMonoid. Export FreeMonoid.StructSemigroup.
Require Import FreeMonoid.MonoidHom.
Require Import Coq.Arith.Mult.

Module Type BasisType.
  Parameter Basis : Type.
End BasisType.

Module FreeMonoidModule (B : BasisType).
Definition Basis := B.Basis.

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


Class UniversalProperty (B : Type) `{Monoid B} := {
  (*
          (Set)               (Mon)

        i
      X ⟶ U(A)                A
        ↘   ↓ U(extend f)      ↓ extend f
       f   U(B)                B
      
      
      Please note: The forgetful functor U is left implicit in the code below. *)
  
  (* extend : (X -> B) -> (A -> B); *)
  extend : (Basis -> B) -> (FreeMonoid -> B);
  
  (* extend_mor : forall (f : X -> B), MonoidHomomorphism (extend f); *)
  extend_mor : forall (f : Basis -> B), MonoidHomomorphism (extend f);

  (* extend_universal : forall (f : X -> B) (x : X), extend f (i x) = f x *)
  extend_universal : forall (f : Basis -> B) (x : Basis), extend f (canonical_inj x) = f x;

  (* extend_unique : forall (f : X -> B) (g : A -> B), MonoidHomomorphism g ->
                   (forall (x : X), g (i x) = f x) -> forall a, g a = extend f a *)
  extend_unique : forall (f : Basis -> B) (g : FreeMonoid -> B), MonoidHomomorphism g ->
                   (forall (x : Basis), g (canonical_inj x) = f x) -> forall a, g a = extend f a
}.


Section UniversalPropertyProof.

Context {A : Type} (HmagmaA : Magma A) (HsemigroupA : Semigroup A) (HmonoidA : Monoid A).

(* Extends a function f : Basis -> A to a function FreeMonoid -> A *)
Definition extend_monoid `{Monoid A} (f : Basis -> A) : FreeMonoid -> A :=
  fold_right (fun b acc => m_op (f b) acc) mn_id.

(* Proof that extend_monoid f is a monoid homomorphism *)
Lemma extend_monoid_homomorphism `{Monoid A} (f : Basis -> A) : MonoidHomomorphism (extend_monoid f).
Proof.
  split.
  - intros x y. unfold extend_monoid.
    induction x as [|b bs IH].
    + simpl. rewrite mn_left_id. reflexivity.
    + simpl in *. rewrite <- sg_assoc. f_equal. apply IH.
  - simpl. reflexivity.
Qed.


Lemma extend_monoid_universal `{Monoid A} (f : Basis -> A) (x : Basis) : extend_monoid f (canonical_inj x) = f x.
Proof.
  unfold extend_monoid, canonical_inj. simpl.
  rewrite mn_right_id. reflexivity.
Qed.


(* Proof that extend_monoid is the unique such extension *)
Lemma extend_monoid_unique (f : Basis -> A) (g : FreeMonoid -> A) (gHom : MonoidHomomorphism g) :
  (forall x, g (canonical_inj x) = f x) -> forall y, g y = extend_monoid f y.
Proof.
  unfold extend_monoid.
  intros.
  induction y as [|b bs IHbs].
  - (* Base case for the empty list *)
    unfold extend_monoid. simpl.
    assert (H_mn_id: g [] = mn_id).
    { 
      destruct gHom.
      apply homo_preserves_id.
    }
    exact H_mn_id.
  - (* Inductive step for non-empty lists *)
    simpl.
    specialize (H b).  (* Utilize the fact that g (canonical_inj b) = f b *)
    rewrite <- H.
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

End UniversalPropertyProof.


Instance FreeMonoid_UniversalProperty {A : Type} `{Monoid A} : UniversalProperty A :=
{
  extend := fun f => extend_monoid f;
  extend_mor := extend_monoid_homomorphism;
  extend_universal := extend_monoid_universal;  (* Correctly assign the lemma proving the universal property *)
  extend_unique := @extend_monoid_unique A _ _ _;
}.

End FreeMonoidModule.