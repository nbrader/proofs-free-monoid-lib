Require Import Coq.Reals.Reals.
Open Scope R_scope.

Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.

(* Instance of Magma for this operation *)
Instance NatRmultMagma : Magma R := {
  m_op := Rmult
}.

(* Instance of Semigroup for this operation *)
Instance NatRmultSemigroup : Semigroup R := {
  sg_assoc := SYM3 Rmult_assoc
}.

(* Define the identity element as 0 and prove identity laws *)
Instance NatRmultMonoid : Monoid R := {
  mn_id := 1;
  mn_left_id := Rmult_1_l;
  mn_right_id := Rmult_1_r
}.
