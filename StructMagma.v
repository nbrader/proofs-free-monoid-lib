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

Lemma extract_gen_info {A : Type} `{Magma A} (gen_set : list A) (x : A) 
  (gen_set_proof : is_generating_set gen_set) :
  exists g gs, 
    In g gen_set /\
    Forall (fun x => In x gen_set) gs /\
    x = fold_left m_op gs g.
Proof.
  specialize (gen_set_proof x) as [pair [elems_proof eq_proof]].
  exists (fst pair), (snd pair).
  inversion elems_proof.
  split; [assumption|].
  split; [assumption|].
  exact eq_proof.
Qed.

Lemma Forall_app {A : Type} (P : A -> Prop) (l1 l2 : list A) :
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  intros H1 H2. induction l1; simpl.
  - exact H2.
  - inversion H1; subst.
    constructor; auto.
Qed.

(* Require Import Coq.Program.Basics. *)
Require Import CoqUtilLib.ListFunctions.

Lemma fold_left_combine {A : Type} `{Magma A} (gen_set : list A) :
  forall (assoc_mid_gen : forall g, In g gen_set -> 
           forall x y, m_op (m_op x g) y = m_op x (m_op g y))
         (l1 l2 : list A) (x g : A),
  Forall (fun x => In x gen_set) l1 ->
  Forall (fun x => In x gen_set) l2 ->
  In g gen_set ->
  m_op (fold_left m_op l1 x) (fold_left m_op l2 g) = 
  fold_left m_op (l1 ++ g :: l2) x.
Proof.
  intros assoc_mid_gen l1 l2 x g H1 H2 Hg.
  admit.
  (* fold_left_combine_middle_assoc *)
Admitted.

Lemma fold_left_three_part_LHS {A : Type} `{Magma A} (gen_set : list A) :
  forall (assoc_mid_gen : forall g, In g gen_set -> 
           forall x y, m_op (m_op x g) y = m_op x (m_op g y))
         (x_g : A) (x_gs : list A) 
         (y_g : A) (y_gs : list A)
         (z_g : A) (z_gs : list A),
  In y_g gen_set ->
  In z_g gen_set ->
  Forall (fun x => In x gen_set) x_gs ->
  Forall (fun x => In x gen_set) y_gs ->
  Forall (fun x => In x gen_set) z_gs ->
  m_op (m_op (fold_left m_op x_gs x_g) (fold_left m_op y_gs y_g)) (fold_left m_op z_gs z_g) =
  fold_left m_op (x_gs ++ y_g :: y_gs ++ z_g :: z_gs) x_g.
Proof.
  intros assoc_mid_gen x_g x_gs y_g y_gs z_g z_gs
         y_g_in z_g_in x_gs_in y_gs_in z_gs_in.
  
  rewrite (fold_left_combine gen_set assoc_mid_gen x_gs y_gs x_g y_g x_gs_in y_gs_in y_g_in).
  rewrite (fold_left_combine gen_set assoc_mid_gen (x_gs ++ y_g :: y_gs) z_gs x_g z_g).
  
  - rewrite <- app_assoc. reflexivity.
  - apply Forall_app.
    + exact x_gs_in.
    + constructor.
      * exact y_g_in.
      * exact y_gs_in.
  - apply z_gs_in.
  - apply z_g_in.
Qed.

Lemma fold_left_three_part_RHS {A : Type} `{Magma A} (gen_set : list A) :
  forall (assoc_mid_gen : forall g, In g gen_set -> 
           forall x y, m_op (m_op x g) y = m_op x (m_op g y))
         (x_g : A) (x_gs : list A) 
         (y_g : A) (y_gs : list A)
         (z_g : A) (z_gs : list A),
  In y_g gen_set ->
  In z_g gen_set ->
  Forall (fun x => In x gen_set) x_gs ->
  Forall (fun x => In x gen_set) y_gs ->
  Forall (fun x => In x gen_set) z_gs ->
  m_op (fold_left m_op x_gs x_g) (m_op (fold_left m_op y_gs y_g) (fold_left m_op z_gs z_g)) =
  fold_left m_op (x_gs ++ y_g :: y_gs ++ z_g :: z_gs) x_g.
Proof.
  intros assoc_mid_gen x_g x_gs y_g y_gs z_g z_gs
         y_g_in z_g_in x_gs_in y_gs_in z_gs_in.
  
  rewrite (fold_left_combine gen_set assoc_mid_gen y_gs z_gs y_g z_g y_gs_in z_gs_in z_g_in).
  rewrite (fold_left_combine gen_set assoc_mid_gen x_gs (y_gs ++ z_g :: z_gs) x_g y_g x_gs_in).
  
  - reflexivity.
  - apply Forall_app.
    + exact y_gs_in.
    + constructor.
      * exact z_g_in.
      * exact z_gs_in.
  - apply y_g_in.
Qed.

Theorem associative_if_associative_with_middle_generators {A : Type} `{Magma A} (gen_set : list A) :
  forall (gen_set_proof : is_generating_set gen_set),
  forall (assoc_mid_gen :
            forall (g : A), (In g gen_set) ->
            forall (x y : A), m_op (m_op x g) y = m_op x (m_op g y)),
  forall (x y z : A), m_op (m_op x y) z = m_op x (m_op y z).
Proof.
  intros gen_set_proof assoc_mid_gen x y z.
  
  (* Extract generator information for x, y, and z *)
  destruct (extract_gen_info gen_set x gen_set_proof) as [x_g [x_gs [x_g_in_gen_set [x_gs_in_gen_set x_eq]]]].
  destruct (extract_gen_info gen_set y gen_set_proof) as [y_g [y_gs [y_g_in_gen_set [y_gs_in_gen_set y_eq]]]].
  destruct (extract_gen_info gen_set z gen_set_proof) as [z_g [z_gs [z_g_in_gen_set [z_gs_in_gen_set z_eq]]]].
  
  (* Replace x, y, z with their generator expressions *)
  rewrite x_eq, y_eq, z_eq.
  
  (* Apply the three-part fold lemma to handle left hand side *)
  rewrite (fold_left_three_part_LHS gen_set assoc_mid_gen x_g x_gs y_g y_gs z_g z_gs y_g_in_gen_set z_g_in_gen_set x_gs_in_gen_set y_gs_in_gen_set z_gs_in_gen_set).
  
  (* Apply the three-part fold lemma to handle right hand side *)
  rewrite (fold_left_three_part_RHS gen_set assoc_mid_gen x_g x_gs y_g y_gs z_g z_gs y_g_in_gen_set z_g_in_gen_set x_gs_in_gen_set y_gs_in_gen_set z_gs_in_gen_set).
  
  (* Now both sides are equal by reflexivity *)
  reflexivity.
Qed.