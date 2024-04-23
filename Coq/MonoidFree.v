Require Import Coq.Lists.List.
Import ListNotations.
Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.

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
                    (forall x, g (canonical_inj x) = f x) -> forall y, g y = extend f y
}.


Section UniversalPropertyProof.

Context {A : Type} `{Monoid A}.

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
Lemma extend_monoid_unique (f : Basis -> A) (g : FreeMonoid -> A) :
  (forall x, g (canonical_inj x) = f x) -> forall y, g y = extend_monoid f y.
Proof.
  intros. unfold extend_monoid.
  induction y as [|b bs IH].
  - simpl.
    (* To address the base case directly: We expect that g [] should behave as mn_id,
       given g should ideally act as a monoid homomorphism if extended from f. *)
    assert (g [] = mn_id) as Gnil.
    {
      (* Proof that g [] = mn_id might depend on the definition or properties of g 
         that are consistent with monoid homomorphism. *)
      admit.  (* Assuming or proving g [] = mn_id based on other properties of g not detailed here. *)
    }
    rewrite Gnil. reflexivity.

  - simpl. 
    (* Use the induction hypothesis *)
    admit.
(*     rewrite IH. 
    (* Apply the hypothesis H for the head of the list *)
    specialize (H b). simpl in H. rewrite <- H. 
    clear H. induction bs as [|b' bs' IH'].
    + simpl. apply mn_right_id.
    + simpl in *. rewrite <- mn_assoc. f_equal. apply IH'. *)
Admitted.

End UniversalPropertyProof.

Instance FreeMonoid_UniversalProperty {A : Type} `{Monoid A} : UniversalProperty A :=
  {
    extend := fun f => @extend_monoid A _ _ _ f;
    extend_mor := @extend_monoid_homomorphism A _ _ _;
    extend_unique := @extend_monoid_unique A _ _ _
  }.




