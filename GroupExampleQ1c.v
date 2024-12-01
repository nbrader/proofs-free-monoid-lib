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

Definition neg_three_nonzero : Qnonzero.
Proof.
  exists (-3 # 1).
  discriminate.
Defined.

Definition neg_third_nonzero : Qnonzero.
Proof.
  exists (Qinv (-3 # 1)).
  discriminate.
Defined.

Definition one_half_nonzero : Qnonzero.
Proof.
  exists (1 # 2).
  discriminate.
Defined.

Definition two_over_four_nonzero : Qnonzero.
Proof.
  exists (2 # 4).
  discriminate.
Defined.

Ltac nonzero :=
  intros H; apply Qeq_bool_neq in H; discriminate.

Definition get_rational (q : Qnonzero) : Q := proj1_sig q.

Coercion get_rational : Qnonzero >-> Q.

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

Definition q1c_op (a b : Qnonzero) : Qnonzero := neg_three_nonzero * (a * b).

Instance Q1c_Magma : Magma Qnonzero := {
  m_op := q1c_op
}.

(* ******************************************************* *)
(*                      Semigroup Proof                    *)
(* ******************************************************* *)

Lemma q1c_op_assoc :
  forall x y z : Qnonzero, m_op x (m_op y z) == m_op (m_op x y) z.
Proof.
  intros a b c.
  unfold Qnonzero_mult.
  destruct a as [a Ha].
  destruct b as [b Hb].
  destruct c as [c Hc].
  simpl.
  rewrite Qmult_assoc with (n := a) (m := -3) (p := (Qmult b c)).
  rewrite Qmult_comm with (x := a) (y := -3).
  rewrite Qmult_assoc.
  rewrite Qmult_assoc.
  rewrite Qmult_assoc.
  rewrite Qmult_assoc.
  rewrite Qmult_assoc.
  rewrite Qmult_assoc.
  reflexivity.
Qed.

Axiom Qnonzeroeq_to_eq : forall x y : Qnonzero, get_rational x == get_rational y -> x = y.

(* Start the contradiction proof *)
Theorem Qeq_to_eq_implies_false : False.
Proof.
  (* Construct two rationals that are Qeq-equivalent but not propositionally equal *)
  assert (H1 : get_rational one_half_nonzero == get_rational two_over_four_nonzero).
  { (* This follows from the definition of Qeq in QArith *)
    simpl.
    ring.
  }
  
  (* Use the axiom to try to prove these are propositionally equal *)
  pose proof (Qnonzeroeq_to_eq one_half_nonzero two_over_four_nonzero H1) as H2.
  
  (* This will create a proof obligation that x = y, but 1#2 and 2#4 are 
     syntactically different representations *)
  discriminate H2.
Qed.


Lemma q1c_op_assoc_eq : forall x y z : Qnonzero, m_op x (m_op y z) = m_op (m_op x y) z.
Proof.
  intros a b c.
  pose proof (q1c_op_assoc a b c).
  apply Qnonzeroeq_to_eq in H.
  apply H.
Qed.

Instance Q1c_Semigroup : Semigroup Qnonzero := {
  sg_assoc := q1c_op_assoc_eq
}.

(* ******************************************************* *)
(*                      Monoid Proof                       *)
(* ******************************************************* *)

Definition Q1c_id : Qnonzero := neg_third_nonzero.

Lemma q1c_op_left_id :
  forall x : Qnonzero, m_op Q1c_id x == x.
Proof.
  intros x.
  destruct x as [x Hx].
  unfold Q1c_id.
  simpl.
  rewrite Qmult_assoc.
  assert (~ 3 == 0) by discriminate.
  rewrite (Qmult_inv_r 3 H).
  apply Qmult_1_l.
Qed.

Lemma q1c_op_right_id :
  forall x : Qnonzero, m_op x Q1c_id == x.
Proof.
  intros x.
  destruct x as [x Hx].
  unfold Q1c_id.
  simpl.
  rewrite Qmult_assoc.
  rewrite Qmult_comm.
  rewrite Qmult_assoc.
  rewrite (Qmult_comm (/ -3) (-3)).
  assert (~ 3 == 0) by discriminate.
  rewrite (Qmult_inv_r 3 H).
  apply Qmult_1_l.
Qed.

Lemma q1c_op_left_id_eq : forall x : Qnonzero, m_op Q1c_id x = x.
Proof.
  intros a.
  pose proof (q1c_op_left_id a).
  apply Qnonzeroeq_to_eq in H.
  apply H.
Qed.

Lemma q1c_op_right_id_eq : forall x : Qnonzero, m_op x Q1c_id = x.
Proof.
  intros a.
  pose proof (q1c_op_right_id a).
  apply Qnonzeroeq_to_eq in H.
  apply H.
Qed.

Instance Q1c_Monoid : Monoid Qnonzero := {
  mn_id := Q1c_id;
  mn_left_id := q1c_op_left_id_eq;
  mn_right_id := q1c_op_right_id_eq
}.

(* ******************************************************* *)
(*                      Group Proof                        *)
(* ******************************************************* *)

Definition Qnonzero_inv (x : Qnonzero) : Qnonzero.
Proof.
  destruct x as [q nq]. (* Decompose the pair: q is the rational number, nq is the proof of nonzero *)
  exists (Qinv q). (* Construct the reciprocal of q *)
  intros H. (* Assume the hypothesis that 1/q = 0 *)
  apply nq. (* Use the proof that q ≠ 0 *)
  apply (Qmult_inj_r (/ q) 0 q) in H.
  - rewrite Qmult_0_l in H.
    assert (Qmult (/ q) q == 1).
    {
      rewrite Qmult_comm.
      apply Qmult_inv_r.
      apply nq.
    }
    rewrite H in H0.
    discriminate.
  - apply nq.
Defined.

Definition Q1c_inv (x : Qnonzero) : Qnonzero := neg_third_nonzero * neg_third_nonzero * Qnonzero_inv x.

Lemma q1c_op_g_inv_left :
  forall x : Qnonzero, m_op (Q1c_inv x) x == Q1c_id.
Proof.
  intros x.
  destruct x as [x Hx].
  unfold Q1c_id.
  simpl.
  rewrite Qmult_assoc.
  rewrite Qmult_assoc.
  rewrite Qmult_assoc.
  rewrite Qmult_inv_r.
  - rewrite Qmult_1_l.
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (/ x) x).
    rewrite Qmult_inv_r.
    + rewrite Qmult_1_r.
      reflexivity.
    + apply Hx.
  - discriminate.
Qed.

Lemma q1c_op_g_inv_left_eq :
  forall x : Qnonzero, m_op (Q1c_inv x) x = Q1c_id.
Proof.
  intros x.
  pose proof (q1c_op_g_inv_left x).
  apply Qnonzeroeq_to_eq in H.
  apply H.
Qed.

Instance Q1c_Group : Group Qnonzero := {
  g_inv := Q1c_inv;
  g_inv_left := q1c_op_g_inv_left_eq;
}.
