Require Import Coq.Lists.List.
Import ListNotations.
Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.
Require Import Coq.Arith.Mult.

Variable Basis : Type.

(* The type of lists over the Basis, representing the free monoid on Basis *)
Definition FreeMonoid := list Basis.


Instance FreeMonoid_Magma : Magma FreeMonoid := {
  m_op := @app Basis
}.

Instance FreeMonoid_Semigroup : Semigroup FreeMonoid := {
  sg_assoc := fun x y z => app_assoc x y z  (* Correctly applying associativity of list concatenation *)
}.

Instance FreeMonoid_Monoid : Monoid FreeMonoid := {
  mn_id := [];
  mn_left_id := fun x => eq_refl : m_op [] x = x;  (* This works because [] ++ x is textually x in Coq's list concatenation *)
  mn_right_id := fun x => app_nil_r x   (* Correctly applying the lemma for list concatenation *)
}.

Definition canonical_inj (b : Basis) : FreeMonoid := [b].

Class UniversalProperty (A : Type) `{Monoid A} := {
  extend : (Basis -> A) -> (FreeMonoid -> A);
  extend_mor : forall (f : Basis -> A), MonoidHomomorphism (extend f);
  extend_unique : forall (f : Basis -> A) (g : FreeMonoid -> A),
                    MonoidHomomorphism g ->
                    (forall x, g (canonical_inj x) = f x) -> forall y, g y = extend f y
}.


Section UniversalPropertyProof.

Context {A : Type} (Hmagma : Magma A) (Hsemigroup : Semigroup A) (Hmonoid : Monoid A).

(* Extends a function f : Basis -> A to a function FreeMonoid -> A *)
Definition extend_monoid (f : Basis -> A) : FreeMonoid -> A :=
  fold_right (fun b acc => m_op (f b) acc) mn_id.

(* Proof that extend_monoid f is a monoid homomorphism *)
Lemma extend_monoid_homomorphism (f : Basis -> A) : MonoidHomomorphism (extend_monoid f).
Proof.
  split.
  - intros x y. unfold extend_monoid.
    induction x as [|b bs IH].
    + simpl. rewrite mn_left_id. reflexivity.
    + simpl in *. rewrite <- sg_assoc. f_equal. apply IH.
  - simpl. reflexivity.
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
    extend := fun f => @extend_monoid A _ _ _ f;
    extend_mor := @extend_monoid_homomorphism A _ _ _;
    extend_unique := fun (f : Basis -> A) (g : FreeMonoid -> A) (Hg : MonoidHomomorphism g)
                      (H : forall x, g (canonical_inj x) = f x) => 
                     @extend_monoid_unique A _ _ _ _ g Hg H
  }.
