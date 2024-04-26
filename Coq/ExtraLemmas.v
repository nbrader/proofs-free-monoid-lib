Lemma if_same_then_const : forall (A : Type) (x y : A) (b : bool),
  (if b then x else x) = x.
Proof.
  intros A x y b.
  destruct b; reflexivity.
Qed.

Definition mul_1_l : forall n : nat, 1 * n = n :=
  nat_ind
    (fun n0 : nat => 1 * n0 = n0)
    (eq_refl : 1 * 0 = 0)  (* Proof of the base case *)
    (fun (n' : nat) (IHn' : 1 * n' = n') =>
      eq_ind_r
        (fun n0 : nat => S n0 = S n')
        eq_refl
        IHn'  (* Application of the induction hypothesis *)
    : 1 * S n' = S n').
    