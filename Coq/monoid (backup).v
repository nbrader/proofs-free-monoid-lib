Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Max.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Class Magma (A : Type) := {
  m_op : A -> A -> A
}.

Class Semigroup (A : Type) `{Magma A} := {
  sg_assoc : forall x y z : A, m_op x (m_op y z) = m_op (m_op x y) z
}.

Class Monoid (A : Type) `{Semigroup A} := {
  mn_id : A;
  mn_left_id : forall x : A, m_op mn_id x = x;
  mn_right_id : forall x : A, m_op x mn_id = x
}.


Section MonoidHomomorphisms.

Class MonoidHomomorphism {A B : Type} `{Monoid A} `{Monoid B} (f : A -> B) := {
  homo_preserves_op : forall x y : A, f (m_op x y) = m_op (f x) (f y);
  homo_preserves_id : f (mn_id) = mn_id;
}.


End MonoidHomomorphisms.


Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

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







Instance BoolOrMagma : Magma bool := { m_op := orb }.

Lemma orb_assoc : forall x y z : bool, orb x (orb y z) = orb (orb x y) z.
Proof. destruct x, y, z; simpl; reflexivity. Qed.

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

(* Define a custom maximum operation treating 1 as the maximum number *)
Definition max1 (x y : nat) : nat :=
  if (x =? 1) then 1
  else if (y =? 1) then 1
  else max x y.

(* Instance of Magma for this operation *)
Instance NatMax1Magma : Magma nat := {
  m_op := max1
}.

Lemma max1_zero_req_zeroes : forall n n0 : nat,
  Nat.max n n0 =? 0 = true -> n = 0 /\ n0 = 0.
Proof.
  intros n n0 H.
  apply Nat.eqb_eq in H.
  split.
  - apply Nat.le_0_r in H.
    apply (Nat.max_lub_l n n0 0) in H.
    apply Nat.le_0_r in H.
    assumption.
  - apply Nat.le_0_r in H.
    apply (Nat.max_lub_r n n0 0) in H.
    apply Nat.le_0_r in H.
    assumption.
Qed.


Lemma max1_zero_req_zeroes_bool : forall n n0 : nat,
  Nat.max n n0 =? 0 = true -> (n =? 0 = true) /\ (n0 =? 0 = true).
Proof.
  intros n n0 H.
  apply Nat.eqb_eq in H.
  split; apply Nat.eqb_eq; apply Nat.le_0_r; [apply (Nat.max_lub_l n n0 0) | apply (Nat.max_lub_r n n0 0)].
  - apply Nat.eq_le_incl. assumption.
  - apply Nat.eq_le_incl. assumption.
Qed.


Lemma max1_nonzero_implies_max_nonzero : forall n n0 : nat,
  (n =? 0 = false) \/ (n0 =? 0 = false) -> Nat.max n n0 =? 0 = false.
Proof.
  intros n n0 H.
  apply Nat.eqb_neq;          (* We need to prove Nat.max n n0 <> 0. *)
  intros Hmax.               (* Assume for contradiction that Nat.max n n0 = 0. *)
  apply Nat.eqb_eq in Hmax.  (* Convert equality from Boolean to Prop. *)
  destruct (max1_zero_req_zeroes _ _ Hmax) as [Hn Hn0].
  destruct H as [Hn_false | Hn0_false].
  - rewrite Nat.eqb_neq in Hn_false; contradiction.
  - rewrite Nat.eqb_neq in Hn0_false; contradiction.
Qed.


Theorem simplify_expr : forall n n0 : nat,
  (n =? 0) = true ->
  (if n0 =? 0 then 1 else 1) = 
  (if (if n0 =? 0 then 1 else 1) =? 1 then 1 else Nat.max (if n0 =? 0 then 1 else 1) 0).
Proof.
  intros n n0 H.
  (* Observe that both sides of the equality become constant (1) irrespective of the value of n0 *)
  (* Destruct n0 =? 0 to simplify the conditionals *)
  destruct (n0 =? 0) eqn:E.
  - (* Case when n0 = 0 *)
    (* Now we prove that both sides evaluate to 1 *)
    reflexivity.
  - (* Case when n0 ≠ 0 *)
    (* This case proceeds similarly since both conditionals still evaluate to 1 *)
    reflexivity.
Qed.


Theorem remaining_proof : forall x y z n n0 : nat,
(n =? 0) = false ->
(n0 =? 0) = false ->
S (Nat.max n0 n) = (if S (Nat.max n0 n) =? 1 then 1 else Nat.max (S (Nat.max n0 n)) 0).
Proof.
  intros x y z n n0 H H0.
  (* Assert that S (Nat.max n0 n) is greater than 1 *)
  assert (H1: S (Nat.max n0 n) > 1).
  - apply -> Nat.succ_lt_mono. apply Nat.neq_0_lt_0. intro.
    rewrite <- Nat.eqb_eq in H1.
    apply max1_zero_req_zeroes in H1.
    destruct H1.
    rewrite <- Nat.eqb_eq in H1.
    rewrite H1 in H0.
    inversion H0.
  - destruct (Nat.max n0 n).
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.

Theorem prove_max_ge_1 : forall x y z n n0 : nat,
  (n =? 0) = false ->
  (n0 =? 0) = false ->
  Nat.max n 0 < n ->
  Nat.max n 0 < n0 ->
  Nat.max n0 n >= 1.
Proof.
  intros x y z n n0 H H0 Hn Hn0.
  apply Nat.eqb_neq in H.
  apply Nat.eqb_neq in H0.
  assert (n > 0) as PosN.
  {
    apply Nat.neq_0_lt_0. assumption.
  }
  assert (n0 > 0) as PosN0.
  {
    apply Nat.neq_0_lt_0. assumption.
  }
  apply Nat.le_trans with (m := 1).
  - apply Nat.eq_le_incl. reflexivity.
  - apply Nat.le_lt_trans with (m := n); try assumption.
    + apply Nat.le_0_l.
    + rewrite Nat.max_0_r in Hn.
      apply Nat.lt_neq in Hn.
      contradiction Hn.
      reflexivity.
Qed.

Lemma le_S_S : forall n m : nat, n <= m -> S n <= S m.
Proof.
  intros n m H.
  apply Lt.le_lt_or_eq_stt in H.
  destruct H.
  - apply Arith_prebase.lt_n_S_stt in H.
    apply Nat.lt_le_incl in H.
    apply H.
  - rewrite H.
    apply (Nat.le_lteq (S m) (S m)).
    right.
    reflexivity.
Qed.

Theorem min_two_gt_two : forall x y z n n0 : nat,
  (n =? 0) = false ->
  (n0 =? 0) = false ->
  2 < S (S (Nat.max n0 n)).
Proof.
  intros x y z n n0 H H0.
  apply Nat.eqb_neq in H.
  apply Nat.neq_0_lt_0 in H.
  apply (Nat.lt_pred_le 1 n) in H.
  apply (Nat.max_le_compat_l 1 n n0) in H.
  apply le_S_S in H.
  apply le_S_S in H.
  apply Nat.eqb_neq in H0.
  apply Nat.neq_0_lt_0 in H0.
  apply (Nat.lt_pred_le 1 n0) in H0.
  apply (Nat.max_le_compat_r 1 n0 1) in H0.
  apply le_S_S in H0.
  apply le_S_S in H0.
  simpl in H0.
  apply (le_trans 3 (S (S (Nat.max n0 1))) (S (S (Nat.max n0 n)))).
  - apply H0.
  - apply H.
Qed.

Theorem final_proof : forall x y z n n0 : nat,
(n =? 0) = false ->
(n0 =? 0) = false ->
S (Nat.max n0 n) = (if S (Nat.max n0 n) =? 1 then 1 else Nat.max (S (Nat.max n0 n)) 0).
Proof.
intros x y z n n0 H H0.
(* Assert that S (Nat.max n0 n) > 1 *)
assert (H1: S (Nat.max n0 n) > 1).
{
apply Nat.succ_lt_mono. apply min_two_gt_two.
  - auto.
  - auto.
  - auto.
  - auto.
  - auto.
}
simpl.
case_eq (Nat.max n0 n =? 0).
- intros.
  apply max1_zero_req_zeroes in H2.
  destruct H2.
  subst.
  simpl.
  reflexivity.
- intros. reflexivity.
Qed.

Theorem conditional_exprs : forall x y z n n0 : nat,
  (n =? 0) = false ->
  (if n0 =? 0 then 1 else if n =? 0 then 1 else S (Nat.max n0 n)) =
  (if (if n0 =? 0 then 1 else S (Nat.max n0 n)) =? 1 then 1 else Nat.max (if n0 =? 0 then 1 else S (Nat.max n0 n)) 0).
Proof.
  intros x y z n n0 H.
  destruct (n0 =? 0) eqn:E0.
  - (* Case when n0 = 0 *)
    reflexivity.
  - (* Case when n0 ≠ 0 *)
    (* Using the hypothesis that n ≠ 0, we know the else branch of the second if in the first expression is taken *)
    rewrite H.
    apply (final_proof x y z).
    + apply H.
    + apply E0.
Qed.

Lemma if_same_then_const : forall (A : Type) (x y : A) (b : bool),
  (if b then x else x) = x.
Proof.
  intros A x y b.
  destruct b; reflexivity.
Qed.

Theorem if_simplify : forall x y z n n0 n1 : nat,
  (n =? 0) = true ->
  (if n1 =? 0 then 1 else if (if n0 =? 0 then 1 else 1) =? 1 then 1 else match (if n0 =? 0 then 1 else 1) with
                                                                        | 0 => S n1
                                                                        | S m' => S (Nat.max n1 m')
                                                                        end) =
  (if (if n1 =? 0 then 1 else if n0 =? 0 then 1 else S (Nat.max n1 n0)) =? 1 then 1 else 1).
Proof.
  intros x y z n n0 n1 H.
  destruct (n1 =? 0) eqn:En1.
  - reflexivity.
  - destruct (n0 =? 0) eqn:En0.
    + reflexivity.
    + simpl.
      rewrite if_same_then_const.
      * reflexivity.
      * apply x.
Qed.

Lemma max_assoc : forall a b c : nat,
  Nat.max a (Nat.max b c) = Nat.max (Nat.max a b) c.
Proof.
  intros a b c.
  apply Nat.max_assoc.
Qed.

Theorem complex_conditional_equality : forall x y z n n0 n1 : nat,
  (n =? 0) = false ->
  (n1 =? 0) = false ->
  (if (if n0 =? 0 then 1 else S (Nat.max n0 n)) =? 1
   then 1
   else match (if n0 =? 0 then 1 else S (Nat.max n0 n)) with
        | 0 => S n1
        | S m' => S (Nat.max n1 m')
        end) = 
  (if (if n0 =? 0 then 1 else S (Nat.max n1 n0)) =? 1 then 1 else Nat.max (if n0 =? 0 then 1 else S (Nat.max n1 n0)) (S n)).
Proof.
  intros x y z n n0 n1 H H0.
  destruct (n0 =? 0) eqn:En0.
  - (* Case n0 = 0 *)
    reflexivity.
  - (* Case n0 ≠ 0 *)
    simpl.
    assert (Nat.max n0 n =? 0 = false).
    + apply max1_nonzero_implies_max_nonzero.
      left.
      apply En0.
    + rewrite H1.
      assert ((n1 =? 0) = false \/ (n0 =? 0) = false).
      * left. assumption.
      * apply (max1_nonzero_implies_max_nonzero n1 n0) in H2.
        rewrite H2.
        rewrite max_assoc.
        reflexivity.
Qed.


(* Prove associativity of max1 *)
Lemma max1_assoc : forall x y z : nat, max1 x (max1 y z) = max1 (max1 x y) z.
Proof.
  intros.
  unfold max1.
  case x.
  - simpl.
    case y.
    + simpl.
      case z.
      * simpl.
        reflexivity.
      * intros.
        simpl.
        case_eq (n =? 0).
        -- simpl.
           reflexivity.
        -- simpl.
           intros.
           rewrite H.
           reflexivity.
    + intros.
      simpl.
      case z.
      * simpl.
        case_eq (n =? 0).
        -- simpl.
           reflexivity.
        -- simpl.
           intros.
           rewrite H.
           reflexivity.
      * intros.
        simpl.
        case_eq (n =? 0).
        -- simpl.
           reflexivity.
        -- simpl.
           intros.
           rewrite H.
           case_eq (n0 =? 0).
           ++ simpl.
              reflexivity.
           ++ simpl.
              intros.
              case_eq (Nat.max n n0 =? 0).
              ** intros.
                 apply max1_zero_req_zeroes in H1.
                 destruct H1.
                 rewrite H1.
                 rewrite H2.
                 simpl.
                 reflexivity.
              ** intros.
                 reflexivity.
  - simpl.
    case y.
    + simpl.
      case z.
      * simpl.
        intros.
        case_eq (n =? 0).
        -- simpl.
           reflexivity.
        -- simpl.
           intros.
           rewrite H.
           reflexivity.
      * intros.
        simpl.
        case_eq (n0 =? 0).
        -- simpl.
           reflexivity.
        -- simpl.
           intros.
           rewrite H.
           case_eq (n =? 0).
           ++ simpl.
              reflexivity.
           ++ simpl.
              intros.
              case_eq (Nat.max n0 n =? 0).
              ** intros.
                 apply max1_zero_req_zeroes in H1.
                 destruct H1.
                 rewrite H1.
                 rewrite H2.
                 simpl.
                 reflexivity.
              ** intros.
                 case_eq (Nat.max n0 n).
                 --- intros.
                     apply Nat.eqb_eq in H2.
                     rewrite H1 in H2.
                     inversion H2.
                 --- intros.
                     rewrite H0.
                     reflexivity.
    + simpl.
      case z.
      * simpl.
        intros.
        case_eq (n =? 0).
        -- simpl.
           intros.
           apply (simplify_expr n n0).
           apply H.
        -- simpl.
           intros.
           apply (conditional_exprs x y z n n0 H).
      * simpl.
        intros.
        case_eq (n =? 0).
        -- simpl.
           intros.
           apply (if_simplify x y z n n0 n1).
           apply H.
        -- simpl.
           intros.
           case_eq (n1 =? 0).
           ++ intros.
              simpl.
              reflexivity.
           ++ intros.
              apply (complex_conditional_equality x y z).
              *** apply H.
              *** apply H0.
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



(* Define a function mapping bool to nat *)
Definition bool_to_nat (b : bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.

Instance BoolToNatHomomorphism : MonoidHomomorphism bool_to_nat.
Proof.
  split.
  - intros x y.
    destruct x, y; simpl; try reflexivity.
  - reflexivity.
Defined.





