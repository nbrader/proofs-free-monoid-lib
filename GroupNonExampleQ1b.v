Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.StructGroup.

Require Import QArith.
Require Import Qcanon.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Classes.RelationClasses.

Open Scope Q_scope.

(* ******************************************************* *)
(*                    Set Definition                       *)
(* ******************************************************* *)

Definition Qnonzero := { q : Q | ~(q == 0%Q) }.

(* ******************************************************* *)
(*                 Operation on Qnonzero                   *)
(* ******************************************************* *)

Definition one_nonzero : Qnonzero.
Proof.
  exists (1 # 1).
  discriminate.
Defined.

Definition two_nonzero : Qnonzero.
Proof.
  exists (2 # 1).
  discriminate.
Defined.

Definition three_nonzero : Qnonzero.
Proof.
  exists (3 # 1).
  discriminate.
Defined.

Definition one_half_nonzero : Qnonzero.
Proof.
  exists (1 # 2).
  discriminate.
Defined.

Ltac nonzero :=
  intros H; apply Qeq_bool_neq in H; discriminate.

Definition get_rational (q : Qnonzero) : Q := proj1_sig q.

Compute get_rational one_half_nonzero. (* Outputs: 1/2 *)

Coercion get_rational : Qnonzero >-> Q.

Compute one_half_nonzero + (1 # 3). (* Uses the coercion to add a Qnonzero and a Q *)

Definition Qnonzero_mult (a b : Qnonzero) : Qnonzero.
Proof.
  destruct a as [a Hq1].
  destruct b as [b Hq2].
  exists (a * b).
  intro H.
  assert (a * b == 0) by (rewrite H; apply Qeq_refl).
  apply (Qmult_integral a b) in H0.
  destruct H0 as [H0 | H0].
  - contradiction Hq1.
  - contradiction Hq2.
Defined.

(* ******************************************************* *)
(*                 Qnonzero_mult Properties                *)
(* ******************************************************* *)

Require Import Coq.Setoids.Setoid.

(* Declare the equivalence relation for rational numbers *)
Global Instance Qeq_Equivalence : Equivalence Qeq.
Proof.
  constructor.
  - intro x; reflexivity.
  - intros x y H; symmetry; assumption.
  - intros x y z Hxy Hyz; transitivity y; assumption.
Qed.

(* Now you can use rewrite with == *)
Lemma example_rewrite (a b c : Q) : 
  a == b -> a + c == b + c.
Proof.
  intros Heq.
  rewrite Heq.
  reflexivity.
Qed.

Theorem Qnonzero_id_left : forall a : Qnonzero, Qnonzero_mult one_nonzero a = a.
Proof.
  admit.
Admitted.

Theorem Qnonzero_id_right : forall a : Qnonzero, Qnonzero_mult a one_nonzero = a.
Proof.
  admit.
Admitted.

Theorem Qnonzero_mult_assoc : forall n m p : Qnonzero, Qnonzero_mult n (Qnonzero_mult m p) = Qnonzero_mult (Qnonzero_mult n m) p.
Proof.
  admit.
Admitted.

Theorem Qnonzero_mult_comm (a b : Qnonzero) : Qnonzero_mult a b = Qnonzero_mult b a.
Proof.
  destruct a as [a Hq1].
  destruct b as [b Hq2].
  unfold Qnonzero_mult.
  assert (Qmult a b == Qmult b a) by apply (Qmult_comm a b).
  apply eq_dep_eq_sig.
  (* rewrite H. *)
  (* apply Q_dec. *)
  admit.
Admitted.

(* ******************************************************* *)
(*                        Magma Proof                      *)
(* ******************************************************* *)

Notation "a * b" := (Qnonzero_mult a b) : Q_scope.

Definition q1b_op (a b : Qnonzero) : Qnonzero := (a * a) * (b * b).

Instance Q1b_Magma : Magma Qnonzero := {
  m_op := q1b_op
}.

(* ******************************************************* *)
(*                    Semigroup Disproof                   *)
(* ******************************************************* *)

Lemma q1b_op_assoc :
  ~ (forall x y z : Qnonzero, q1b_op x (q1b_op y z) = q1b_op (q1b_op x y) z).
Proof.
  intro.
  specialize (H two_nonzero one_nonzero one_nonzero).
  unfold q1b_op in H.
  rewrite Qnonzero_id_right in H.
  rewrite Qnonzero_id_right in H.
  rewrite Qnonzero_id_right in H.
  rewrite Qnonzero_id_right in H.
  rewrite Qnonzero_id_right in H.
  discriminate.
Qed.
