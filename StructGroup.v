Require Import FreeMonoid.StructMonoid. Export FreeMonoid.StructSemigroup.
Require Import Setoid.

Definition is_left_inv (A : Type) (m_op : A -> A -> A) (mn_id : A) (g_inv : A -> A) := forall x : A, m_op (g_inv x) x = mn_id.
Definition is_right_inv (A : Type) (m_op : A -> A -> A) (mn_id : A) (g_inv : A -> A) := forall x : A, m_op x (g_inv x) = mn_id.
Definition is_inv (A : Type) (m_op : A -> A -> A) (mn_id : A) (g_inv : A -> A) := (is_left_inv A m_op mn_id g_inv) /\ (is_right_inv A m_op mn_id g_inv).

(* This actually assumes more than it needs to because Monoid requires you to implement both left and right identity whereas Group only requires left. *)
Class Group (A : Type) `{Monoid A} := {
  g_inv : A -> A;
  g_inv_left : is_left_inv A m_op mn_id g_inv;
}.

Theorem id_unique (A : Type) `{Group A} (x : A) (x_is_left_id : is_left_id A m_op x) : x = mn_id.
Proof.
  unfold is_left_id in *.
  specialize (x_is_left_id mn_id).
  rewrite mn_right_id in x_is_left_id.
  exact x_is_left_id.
Qed.

Theorem g_inv_right (A : Type) `{Group A} : is_right_inv A m_op mn_id g_inv.
Proof.
  unfold is_right_inv.
  intros.
  rewrite <- mn_left_id at 1.
  rewrite <- (g_inv_left (g_inv x)) at 1.
  rewrite <- sg_assoc.
  rewrite (sg_assoc (g_inv x) x (g_inv x)).
  rewrite g_inv_left.
  rewrite mn_left_id.
  rewrite g_inv_left.
  reflexivity.
Qed.

Theorem g_inv_involutive (A : Type) `{Group A} (x : A) : g_inv (g_inv x) = x.
Proof.
  assert (m_op (g_inv (g_inv x)) (m_op (g_inv x) x) = m_op (g_inv (g_inv x)) (m_op (g_inv x) x)) by reflexivity.
  rewrite sg_assoc in H3 at 2.
  rewrite (g_inv_left (g_inv x)) in H3.
  rewrite mn_left_id in H3.
  rewrite (g_inv_left x) in H3.
  rewrite mn_right_id in H3.
  exact H3.
Qed.

Definition is_left_partial_id (A : Type) (m_op : A -> A -> A) (partial_id : A) := exists x : A, m_op partial_id x = x.
Definition is_right_partial_id (A : Type) (m_op : A -> A -> A) (partial_id : A) := exists x : A, m_op x partial_id = x.
Definition is_partial_id (A : Type) (m_op : A -> A -> A) (partial_id : A) := (is_left_partial_id A m_op partial_id) /\ (is_right_partial_id A m_op partial_id).

Theorem partial_id_unique (A : Type) `{Group A} (x : A) (x_is_left_partial_id : is_left_partial_id A m_op x) : x = mn_id.
Proof.
  unfold is_left_partial_id in *.
  destruct x_is_left_partial_id as [z x_is_left_partial_id].
  rewrite <- mn_right_id.
  rewrite <- (@g_inv_right A H H0 H1 H2 z).
  rewrite sg_assoc.
  rewrite x_is_left_partial_id. clear x_is_left_partial_id.
  reflexivity.
Qed.

(* 
Theorem inv_unique (A : Type) `{Group A} (f : A -> A) (f_inv : is_left_inv A m_op mn_id f) : f = g_inv.
Proof.
  admit.
  (* unfold is_id in *.
  destruct x_id.
  specialize (H4 mn_id).
  rewrite mn_left_id in H4.
  apply H4. *)
Admitted.
*)

(* 
Theorem inv_unique_2 (A : Type) `{Group A} (x y : A) (x_y_inverses : m_op x y = mn_id) : y = g_inv x.
Proof.
  admit.
  (* unfold is_id in *.
  destruct x_id.
  specialize (H4 mn_id).
  rewrite mn_left_id in H4.
  apply H4. *)
Admitted.
*)

Theorem inv_unique_3 (A : Type) `{Group A} (x y : A) (x_y_inverses : m_op x y = mn_id) : x = g_inv y.
Proof.
  assert (x = x) by reflexivity.
  rewrite <- mn_right_id in H3 at 2.
  rewrite <- (@g_inv_right A H H0 H1 H2 y) in H3 at 1.
  rewrite sg_assoc in H3.
  rewrite x_y_inverses in H3.
  rewrite mn_left_id in H3.
  exact H3.
Qed.

Require Import List.
Import ListNotations.

Definition is_finite_generating_set_of_group (A : Type) `{Group A} (gen_set : list A) : Prop :=
  forall x : A, exists (gen_pairs : list (A * bool)),
    Forall (fun pair => In (fst pair) gen_set) gen_pairs /\
    x = fold_left (fun acc (pair : A * bool) =>
                     let (g, is_inverse) := pair in
                     if is_inverse then m_op acc (g_inv g) else m_op acc g)
                  gen_pairs mn_id.
