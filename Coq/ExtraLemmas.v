Lemma if_same_then_const : forall (A : Type) (x y : A) (b : bool),
  (if b then x else x) = x.
Proof.
  intros A x y b.
  destruct b; reflexivity.
Qed.
