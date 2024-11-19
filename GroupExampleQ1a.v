Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.StructGroup.

(* ******************************************************* *)
(*                    Set Definition                       *)
(* ******************************************************* *)

Inductive Q1a_Set : Type :=
  | Q1a_3
  | Q1a_9
  | Q1a_21
  | Q1a_27.

(* ******************************************************* *)
(*                 Operation on Q1a_Set                    *)
(* ******************************************************* *)

Definition q1a_op (x y : Q1a_Set) : Q1a_Set :=
  match x, y with
  | Q1a_3, Q1a_3 => Q1a_9
  | Q1a_3, Q1a_9 => Q1a_27
  | Q1a_3, Q1a_21 => Q1a_3
  | Q1a_3, Q1a_27 => Q1a_21
  | Q1a_9, Q1a_3 => Q1a_27
  | Q1a_9, Q1a_9 => Q1a_21
  | Q1a_9, Q1a_21 => Q1a_9
  | Q1a_9, Q1a_27 => Q1a_3
  | Q1a_21, Q1a_3 => Q1a_3
  | Q1a_21, Q1a_9 => Q1a_9
  | Q1a_21, Q1a_21 => Q1a_21
  | Q1a_21, Q1a_27 => Q1a_27
  | Q1a_27, Q1a_3 => Q1a_21
  | Q1a_27, Q1a_9 => Q1a_3
  | Q1a_27, Q1a_21 => Q1a_27
  | Q1a_27, Q1a_27 => Q1a_9
  end.

Instance Q1a_Magma : Magma Q1a_Set := {
  m_op := q1a_op
}.

(* ******************************************************* *)
(*      Proving Correspondence with Modular Arithmetic     *)
(* ******************************************************* *)

Definition Q1a_to_nat (x : Q1a_Set) : nat :=
  match x with
  | Q1a_3 => 3
  | Q1a_9 => 9
  | Q1a_21 => 21
  | Q1a_27 => 27
  end.

Definition q1a_op_nat (x y : nat) : nat := Nat.modulo (x * y) 60.

Lemma q1a_op_correct :
  forall x y : Q1a_Set,
    q1a_op_nat (Q1a_to_nat x) (Q1a_to_nat y) = Q1a_to_nat (q1a_op x y).
Proof.
  intros x y.
  destruct x, y; simpl; reflexivity.
Qed.

(* ******************************************************* *)
(*                      Semigroup Proof                    *)
(* ******************************************************* *)

Lemma q1a_op_assoc :
  forall x y z : Q1a_Set, m_op x (m_op y z) = m_op (m_op x y) z.
Proof.
  intros x y z.
  destruct x, y, z; reflexivity.
Qed.

Instance Q1a_Semigroup : Semigroup Q1a_Set := {
  sg_assoc := q1a_op_assoc
}.

(* ******************************************************* *)
(*                      Monoid Proof                       *)
(* ******************************************************* *)

Definition Q1a_id : Q1a_Set := Q1a_21.

Lemma q1a_op_left_id :
  forall x : Q1a_Set, m_op Q1a_id x = x.
Proof.
  intros x.
  destruct x; reflexivity.
Qed.

Lemma q1a_op_right_id :
  forall x : Q1a_Set, m_op x Q1a_id = x.
Proof.
  intros x.
  destruct x; reflexivity.
Qed.

Instance Q1a_Monoid : Monoid Q1a_Set := {
  mn_id := Q1a_id;
  mn_left_id := q1a_op_left_id;
  mn_right_id := q1a_op_right_id
}.

(* ******************************************************* *)
(*                      Group Proof                        *)
(* ******************************************************* *)

Definition Q1a_inv (x : Q1a_Set) : Q1a_Set :=
  match x with
  | Q1a_3 => Q1a_27
  | Q1a_9 => Q1a_9
  | Q1a_21 => Q1a_21
  | Q1a_27 => Q1a_3
  end.

Lemma q1a_op_g_inv_left :
  forall x : Q1a_Set, m_op (Q1a_inv x) x = mn_id.
Proof.
  intros x.
  destruct x; reflexivity.
Qed.

Instance Q1a_Group : Group Q1a_Set := {
  g_inv := Q1a_inv;
  g_inv_left := q1a_op_g_inv_left;
}.
