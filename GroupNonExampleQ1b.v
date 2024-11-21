Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.StructGroup.

Require Import QArith.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

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

(* First, let's prove the identity laws *)
Theorem Qnonzero_id_left : forall a : Qnonzero, Qnonzero_mult one_nonzero a == a.
Proof.
  intros a.
  unfold Qnonzero_mult.
  destruct a as [a Ha].
  simpl.
  rewrite Qmult_1_l.
  apply Qeq_refl.
Qed.

Theorem Qnonzero_id_right : forall a : Qnonzero, Qnonzero_mult a one_nonzero == a.
Proof.
  intros a.
  unfold Qnonzero_mult.
  destruct a as [a Ha].
  simpl.
  rewrite Qmult_1_r.
  apply Qeq_refl.
Qed.

(* Prove associativity *)
Theorem Qnonzero_mult_assoc : forall a b c : Qnonzero, 
  Qnonzero_mult a (Qnonzero_mult b c) == Qnonzero_mult (Qnonzero_mult a b) c.
Proof.
  intros a b c.
  unfold Qnonzero_mult.
  destruct a as [a Ha].
  destruct b as [b Hb].
  destruct c as [c Hc].
  simpl.
  rewrite Qmult_assoc.
  apply Qeq_refl.
Qed.

(* Prove commutativity *)
Theorem Qnonzero_mult_comm (a b : Qnonzero) : Qnonzero_mult a b == Qnonzero_mult b a.
Proof.
  unfold Qnonzero_mult.
  destruct a as [a Ha].
  destruct b as [b Hb].
  simpl.
  rewrite Qmult_comm.
  apply Qeq_refl.
Qed.

(* ******************************************************* *)
(*                        Magma Proof                      *)
(* ******************************************************* *)

Notation "a * b" := (Qnonzero_mult a b) : Q_scope.

Definition q1b_op (a b : Qnonzero) : Qnonzero := (a * b) * (a * b).

Instance Q1b_Magma : Magma Qnonzero := {
  m_op := q1b_op
}.

(* ******************************************************* *)
(*                    Semigroup Disproof                   *)
(* ******************************************************* *)

Lemma q1b_op_assoc :
  ~ (forall x y z : Qnonzero, q1b_op x (q1b_op y z) == q1b_op (q1b_op x y) z).
Proof.
  intro.
  specialize (H two_nonzero one_nonzero one_nonzero).
  unfold q1b_op in H.
  simpl in H.
  rewrite Qmult_1_r in H.
  rewrite Qmult_1_r in H.
  rewrite Qmult_1_r in H.
  rewrite Qmult_1_r in H.
  discriminate.
Qed.
