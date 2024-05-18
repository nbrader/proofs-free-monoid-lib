Require Import Coq.Arith.PeanoNat.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.
Require Import Coq.Arith.Le.

(* Define a custom maximum operation treating 1 as the maximum number *)
Definition max1 (x y : nat) : nat :=
  if (x =? 1) then 1
  else if (y =? 1) then 1
  else max x y.

(* Instance of Magma for this operation *)
Instance NatMax1Magma : Magma nat := {
  m_op := max1
}.

Lemma max_assoc : forall a b c : nat,
  Nat.max a (Nat.max b c) = Nat.max (Nat.max a b) c.
Proof.
  intros a b c.
  apply Nat.max_assoc.
Qed.

Lemma max1_1_l : forall y : nat, max1 1 y = 1.
Proof.
  intros y.
  unfold max1.
  rewrite Nat.eqb_refl. (* This simplifies (1 =? 1) to true *)
  reflexivity.
Qed.

Lemma max1_1_r : forall x : nat, max1 x 1 = 1.
Proof.
  intros x.
  unfold max1.
  destruct (x =? 1) eqn:Hx.
  - reflexivity.
  - simpl.
    reflexivity.
Qed.

Lemma max1_not_1 : forall x y : nat, x <> 1 -> y <> 1 -> max1 x y = Nat.max x y.
Proof.
  intros x y Hx Hy.
  unfold max1.
  destruct (x =? 1) eqn:Hx1.
  - apply Nat.eqb_eq in Hx1. contradiction.
  - destruct (y =? 1) eqn:Hy1.
    + apply Nat.eqb_eq in Hy1. contradiction.
    + reflexivity.
Qed.

Lemma nat_max_is_y_or_z : forall y z : nat, Nat.max y z = y \/ Nat.max y z = z.
Proof.
  intros y z.
  destruct (Nat.max_spec_le y z) as [[Hy Hmax]|[Hz Hmax]]; rewrite Hmax; auto.
Qed.

Lemma nat_max_not_1_when_neither_is_1 : forall x y : nat, x <> 1 -> y <> 1 -> Nat.max x y <> 1.
Proof.
  intros x y Hx Hy.
  destruct (nat_max_is_y_or_z x y) as [Hmax | Hmax]; rewrite Hmax.
  - apply Hx.
  - apply Hy.
Qed.

(* Prove associativity of max1 *)
Lemma max1_assoc : forall x y z : nat, max1 x (max1 y z) = max1 (max1 x y) z.
Proof.
  intros x y z.

  (* Case analysis on x, y, z being 1 *)
  destruct (x =? 1) eqn:Hx.
  - simpl. rewrite Nat.eqb_eq in Hx. rewrite Hx. reflexivity.
  - destruct (y =? 1) eqn:Hy.
    + simpl. rewrite Nat.eqb_eq in Hy. rewrite Hy. simpl. rewrite -> max1_1_l. rewrite max1_1_r. rewrite max1_1_l. reflexivity.
    + destruct (z =? 1) eqn:Hz.
      * simpl. rewrite Nat.eqb_eq in Hz. rewrite Hz. rewrite -> max1_1_r. rewrite max1_1_r. rewrite max1_1_r. reflexivity.
      * simpl.
        rewrite Nat.eqb_neq in Hx.
        rewrite Nat.eqb_neq in Hy.
        rewrite Nat.eqb_neq in Hz.

        rewrite -> (max1_not_1 y z Hy Hz).
        assert (Nat.max y z <> 1).
          -- apply nat_max_not_1_when_neither_is_1.
            ++ apply Hy.
            ++ apply Hz.
          -- rewrite -> (max1_not_1 x (Nat.max y z) Hx H).
            rewrite -> (max1_not_1 x y Hx Hy).
            assert (Nat.max x y <> 1).
            ** apply nat_max_not_1_when_neither_is_1.
              --- apply Hx.
              --- apply Hy.
            ** rewrite -> (max1_not_1 (Nat.max x y) z H0 Hz).
                
                (* Now use the associativity of max *)
                rewrite -> (Nat.max_assoc x y z).
                reflexivity.
Qed.

(* Instance of Semigroup for this operation *)
Instance NatMax1Semigroup : Semigroup nat := {
  sg_assoc := max1_assoc
}.

Theorem NatMax1Monoid_left_id : forall x : nat, max1 0 x = x.
Proof.
  intros.
  unfold max1.
  simpl.
  case x.
  - simpl.
    reflexivity.
  - intros.
    simpl.
    case_eq (n =? 0).
    + intros.
      apply Nat.eqb_eq in H.
      rewrite H.
      reflexivity.
    + intros.
      reflexivity.
Qed.

(* mn_left_id : forall x : A, m_op mn_id x = x;
mn_right_id : forall x : A, m_op x mn_id = x *)
Theorem NatMax1Monoid_right_id : forall x : nat, max1 x 0 = x.
Proof.
  intros.
  unfold max1.
  simpl.
  case x.
  - simpl.
    reflexivity.
  - intros.
    simpl.
    case_eq (n =? 0).
    + intros.
      apply Nat.eqb_eq in H.
      rewrite H.
      reflexivity.
    + intros.
      reflexivity.
Qed.

(* Define the identity element as 0 and prove identity laws *)
Instance NatMax1Monoid : Monoid nat := {
  mn_id := 0;
  mn_left_id := NatMax1Monoid_left_id;
  mn_right_id := NatMax1Monoid_right_id
}.
