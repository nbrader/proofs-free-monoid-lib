Require Import Coq.Reals.Reals.
Open Scope R_scope.

Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.

(* Instance of Magma for this operation *)
Instance RplusMagma : Magma R := {
  m_op := Rplus
}.

(* Instance of Semigroup for this operation *)
Instance RplusSemigroup : Semigroup R := {
  sg_assoc := SYM3 Rplus_assoc
}.

(* Define the identity element as 0 and prove identity laws *)
Instance RplusMonoid : Monoid R := {
  mn_id := 0;
  mn_left_id := Rplus_0_l;
  mn_right_id := Rplus_0_r
}.
