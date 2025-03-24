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

(* Universal property definitions *)
Section UniversalProperty.

Context {A : Type} `{Monoid A}.

(*
        (Set)               (Mon)

      i
    X ⟶ U(A)                A
      ↘   ↓ U(extend f)      ↓ extend f
     f   U(B)                B
    
    
    Please note: The forgetful functor U is left implicit in the code below. *)

(* Extends a function f : Basis -> A to a function FreeMonoid -> A *)
Definition extend (f : Basis -> A) : FreeMonoid -> A :=
  fold_right (fun b acc => m_op (f b) acc) mn_id.

(* Proof that extend f is a monoid homomorphism *)
Lemma extend_mor (f : Basis -> A) : MonoidHomomorphism (extend f).
Proof.
  split.
  - intros x y. unfold extend.
    induction x as [|b bs IH].
    + simpl. rewrite mn_left_id. reflexivity.
    + simpl in *. rewrite <- sg_assoc. f_equal. apply IH.
  - simpl. reflexivity.
Qed.

Lemma extend_universal (f : Basis -> A) (x : Basis) :
  extend f (canonical_inj x) = f x.
Proof.
  unfold extend, canonical_inj. simpl.
  rewrite mn_right_id. reflexivity.
Qed.

(* Proof that extend is the unique such extension *)
Lemma extend_unique (f : Basis -> A) (g : FreeMonoid -> A)
  (gHom : MonoidHomomorphism g) :
  (forall x, g (canonical_inj x) = f x) -> forall y, g y = extend f y.
Proof.
  unfold extend.
  intros.
  induction y as [|b bs IHbs].
  - (* Base case for the empty list *)
    unfold extend. simpl.
    assert (H_mn_id: g [] = mn_id).
    { 
      destruct gHom.
      apply homo_preserves_id.
    }
    exact H_mn_id.
  - (* Inductive step for non-empty lists *)
    simpl.
    specialize (H2 b).  (* Utilize the fact that g (canonical_inj b) = f b *)
    rewrite <- H2.
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
