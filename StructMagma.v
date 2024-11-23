Class Magma (A : Type) := {
  m_op : A -> A -> A
}.

Require Import List.
Import ListNotations.

Definition elems_only_from {A : Type} (target : list A) (possible_elems : list A) : Prop := 
  Forall (fun x => In x possible_elems) target.

Definition is_generating_set {A : Type} `{Magma A} (gen_set : list A) : Prop :=
  forall x : A, exists (x_in_terms_of_gen_set : A * list A),
    let g := fst x_in_terms_of_gen_set in
    let gs := snd x_in_terms_of_gen_set in
    elems_only_from (g :: gs) gen_set /\ x = fold_left m_op gs g.

(* Theorem: Magma is associative if associativity holds when middle element is from generating set. *)
Theorem associative_if_associative_with_middle_generators {A : Type} `{Magma A} (gen_set : list A) :
  forall (gen_set_proof : is_generating_set gen_set),
  forall (assoc_mid_gen :
            forall (g : A), (In g gen_set) ->
            forall (x y : A), m_op (m_op x g) y = m_op x (m_op g y)),
  forall (x y z : A), m_op (m_op x y) z = m_op x (m_op y z).
Proof.
  intros.

  specialize (gen_set_proof x) as x_gen.
  destruct x_gen as [x_gs_pair x_gen].
  destruct x_gs_pair as [x_g x_gs].
  simpl in x_gen.
  destruct x_gen as [x_gs_from_gen_set x_gs_make_x].
  assert (x_g_in_gen_set : In x_g gen_set).
  {
    unfold elems_only_from in x_gs_from_gen_set.
    inversion x_gs_from_gen_set.
    apply H2.
  }
  specialize (assoc_mid_gen x_g x_g_in_gen_set) as x_g_assoc. clear x_g_in_gen_set.
  assert (x_gs_in_gen_set : Forall (fun x : A => In x gen_set) x_gs).
  {
    unfold elems_only_from in x_gs_from_gen_set.
    inversion x_gs_from_gen_set.
    apply H3.
  }
  clear x_gs_from_gen_set.
  assert (x_gs_assoc : Forall (fun x : A => forall x y : A, m_op (m_op x x_g) y = m_op x (m_op x_g y)) x_gs).
  {
    inversion x_gs_in_gen_set.
    - admit.
    - admit.
  }
  clear x_gs_in_gen_set.
  
  specialize (gen_set_proof y) as y_gen.
  destruct y_gen as [y_gs_pair y_gen].
  destruct y_gs_pair as [y_g y_gs].
  simpl in y_gen.
  destruct y_gen as [y_gs_from_gen_set y_gs_make_y].
  assert (y_g_in_gen_set : In y_g gen_set).
  {
    unfold elems_only_from in y_gs_from_gen_set.
    inversion y_gs_from_gen_set.
    apply H2.
  }
  specialize (assoc_mid_gen y_g y_g_in_gen_set) as y_g_assoc. clear y_g_in_gen_set.
  assert (y_gs_in_gen_set : Forall (fun y : A => In y gen_set) y_gs).
  {
    unfold elems_only_from in y_gs_from_gen_set.
    inversion y_gs_from_gen_set.
    apply H3.
  }
  clear y_gs_from_gen_set.
  assert (y_gs_assoc : Forall (fun y : A => forall y y : A, m_op (m_op y y_g) y = m_op y (m_op y_g y)) y_gs).
  {
    inversion y_gs_in_gen_set.
    - admit.
    - admit.
  }
  clear y_gs_in_gen_set.
  
  specialize (gen_set_proof z) as z_gen.
  destruct z_gen as [z_gs_pair z_gen].
  destruct z_gs_pair as [z_g z_gs].
  simpl in z_gen.
  destruct z_gen as [z_gs_from_gen_set z_gs_make_z].
  assert (z_g_in_gen_set : In z_g gen_set).
  {
    unfold elems_only_from in z_gs_from_gen_set.
    inversion z_gs_from_gen_set.
    apply H2.
  }
  specialize (assoc_mid_gen z_g z_g_in_gen_set) as z_g_assoc. clear z_g_in_gen_set.
  assert (z_gs_in_gen_set : Forall (fun z : A => In z gen_set) z_gs).
  {
    unfold elems_only_from in z_gs_from_gen_set.
    inversion z_gs_from_gen_set.
    apply H3.
  }
  clear z_gs_from_gen_set.
  assert (z_gs_assoc : Forall (fun z : A => forall z z : A, m_op (m_op z z_g) z = m_op z (m_op z_g z)) z_gs).
  {
    inversion z_gs_in_gen_set.
    - admit.
    - admit.
  }
  clear z_gs_in_gen_set.

  unfold elems_only_from in *.

  (* Make a lemma to prove folds can be combined when the operation is associative over those elements. *)
  assert (fold_xy_z : m_op (m_op x y) z = fold_left m_op (x_gs ++ (y_g :: y_gs) ++ (z_g :: z_gs)) x_g).
  {
    assert (fold_xy : m_op x y = fold_left m_op (x_gs ++ (y_g :: y_gs)) x_g).
    {
      rewrite x_gs_make_x.
      rewrite y_gs_make_y.
      admit. (* Use the above-mentioned lemma. *)
    }
    rewrite fold_xy.
    rewrite z_gs_make_z.
    admit. (* Use the above-mentioned lemma. *)
  }

  assert (fold_x_yz : m_op x (m_op y z) = fold_left m_op (x_gs ++ (y_g :: y_gs) ++ (z_g :: z_gs)) x_g).
  {
    assert (fold_yz : m_op y z = fold_left m_op (y_gs ++ (z_g :: z_gs)) y_g).
    {
      rewrite y_gs_make_y.
      rewrite z_gs_make_z.
      admit. (* Use the above-mentioned lemma. *)
    }
    rewrite fold_yz.
    rewrite x_gs_make_x.
    admit. (* Use the above-mentioned lemma. *)
  }

  rewrite fold_xy_z, fold_x_yz.
  reflexivity.
Admitted.