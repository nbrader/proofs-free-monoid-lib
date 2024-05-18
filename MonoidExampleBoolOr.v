Require Import Coq.Arith.PeanoNat.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.

Instance BoolOrMagma : Magma bool := { m_op := orb }.

Lemma orb_assoc : forall x y z : bool, orb x (orb y z) = orb (orb x y) z.
Proof.
  intros x y z.
  repeat (destruct x; destruct y; destruct z); reflexivity.
Qed.

Instance BoolOrSemigroup : Semigroup bool := { sg_assoc := orb_assoc }.

Lemma orb_left_id : forall x : bool, orb false x = x.
Proof. destruct x; reflexivity. Qed.

Lemma orb_right_id : forall x : bool, orb x false = x.
Proof. destruct x; reflexivity. Qed.

Instance BoolOrMonoid : Monoid bool := {
  mn_id := false;
  mn_left_id := orb_left_id;
  mn_right_id := orb_right_id
}.
