Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import FreeMonoid.StructSemiring.
Require Import CoqUtilLib.ListFunctions.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

(* Instance showing Z forms a semiring *)
Instance Z_Semiring : Semiring Z := {
  add_op := Z.add;
  add_zero := 0;
  add_assoc := Z.add_assoc;
  add_left_id := Z.add_0_l;
  add_right_id := Z.add_0_r;
  add_comm := Z.add_comm;

  mul_op := Z.mul;
  mul_one := 1;
  mul_assoc := Z.mul_assoc;
  mul_left_id := Z.mul_1_l;
  mul_right_id := Z.mul_1_r;

  mul_add_distr_l := Z.mul_add_distr_l;
  mul_add_distr_r := Z.mul_add_distr_r;

  mul_zero_l := Z.mul_0_l;
  mul_zero_r := Z.mul_0_r;
}.

(* Generalized distributivity lemma for semirings *)
Lemma fold_right_map_mult_dist_semiring (A : Type) `{Semiring A} :
  forall (x : A) (f : list A -> A) (lss : list (list A)),
  x ⊗ (fold_right add_op 𝟎 (map f lss)) = fold_right add_op 𝟎 (map (fun ls => x ⊗ (f ls)) lss).
Proof.
  intros x f lss.
  induction lss as [| ls lss' IH].
  - simpl.
    (* Goal: x ⊗ 𝟎 = 𝟎 *)
    apply mul_zero_r.
  - simpl. rewrite <- IH.
    (* Goal: x ⊗ (f ls ⊕ fold_right add_op 𝟎 (map f lss')) = (x ⊗ f ls) ⊕ fold_right add_op 𝟎 (map (fun ls0 => x ⊗ f ls0) lss') *)
    rewrite mul_add_distr_l.
    reflexivity.
Qed.

(* Generalized Horner's rule for arbitrary semirings *)
Lemma generalised_horners_rule_right (A : Type) `{Semiring A} :
  fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 = fold_right add_op 𝟎 ∘ map (fold_right mul_op 𝟏) ∘ inits.
Proof.
  apply functional_extensionality.
  intros xs.
  unfold compose.
  induction xs as [| x xs' IH].
  - (* Base case: xs = [] *)
    simpl.
    (* Goal: 𝟏 = 𝟏 ⊕ 𝟎 *)
    rewrite add_right_id.
    reflexivity.
  - (* Inductive case: xs = x :: xs' *)
    (* Left side: fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 (x :: xs') = (x ⊗ fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 xs') ⊕ 𝟏 *)
    change (fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 (x :: xs')) with
           ((x ⊗ fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 xs') ⊕ 𝟏).

    (* Right side: work with inits (x :: xs') *)
    rewrite inits_cons.

    (* Expand map over the cons structure *)
    change (map (fold_right mul_op 𝟏) ([] :: map (cons x) (inits xs'))) with
           (fold_right mul_op 𝟏 [] :: map (fold_right mul_op 𝟏) (map (cons x) (inits xs'))).

    (* Simplify fold_right mul_op 𝟏 [] = 𝟏 *)
    change (fold_right mul_op 𝟏 []) with 𝟏.

    (* Simplify fold_right add_op on the cons *)
    change (fold_right add_op 𝟎 (𝟏 :: map (fold_right mul_op 𝟏) (map (cons x) (inits xs')))) with
           (𝟏 ⊕ (fold_right add_op 𝟎 (map (fold_right mul_op 𝟏) (map (cons x) (inits xs'))))).

    (* Apply map composition *)
    rewrite map_map.
    unfold compose.

    (* Simplify fold_right mul_op 𝟏 (x :: l) = x ⊗ fold_right mul_op 𝟏 l *)
    change (map (fun l : list A => fold_right mul_op 𝟏 (x :: l)) (inits xs')) with
           (map (fun l : list A => x ⊗ (fold_right mul_op 𝟏 l)) (inits xs')).

    (* Apply distributivity *)
    rewrite <- (fold_right_map_mult_dist_semiring A).

    (* Apply inductive hypothesis *)
    rewrite <- IH.

    (* Final simplification *)
    (* Goal is: (x ⊗ fold_right (fun x0 y => (x0 ⊗ y) ⊕ 𝟏) 𝟏 xs') ⊕ 𝟏 = 𝟏 ⊕ (x ⊗ fold_right (fun x0 y => (x0 ⊗ y) ⊕ 𝟏) 𝟏 xs') *)
    (* This is just commutativity of addition *)
    rewrite add_comm.
    reflexivity.
Qed.

(* Specialized version for Z (the standard Horner's rule) *)
Lemma horners_rule_right :
  fold_right (fun x y => Zplus (Zmult x y) 1) 1 = fold_right Zplus 0 ∘ map (fold_right Zmult 1) ∘ inits.
Proof.
  (* This follows directly from the generalized version with Z_Semiring *)
  exact (generalised_horners_rule_right Z).
Qed.

(* Tropical Semiring Implementation for MaxSegSum Alternative Proof *)

(* Extended integers with negative infinity for proper tropical semiring *)
Inductive ExtZ : Type :=
  | NegInf : ExtZ
  | Finite : Z -> ExtZ.

(* Tropical addition (max operation) *)
Definition tropical_add (x y : ExtZ) : ExtZ :=
  match x, y with
  | NegInf, z => z
  | z, NegInf => z
  | Finite a, Finite b => Finite (Z.max a b)
  end.

(* Tropical multiplication (regular addition) *)
Definition tropical_mul (x y : ExtZ) : ExtZ :=
  match x, y with
  | NegInf, _ => NegInf
  | _, NegInf => NegInf
  | Finite a, Finite b => Finite (a + b)
  end.

(* Helper lemmas for tropical semiring laws *)
Lemma tropical_add_assoc : forall x y z : ExtZ,
  tropical_add x (tropical_add y z) = tropical_add (tropical_add x y) z.
Proof.
  intros x y z.
  destruct x, y, z; simpl; try reflexivity.
  rewrite Z.max_assoc. reflexivity.
Qed.

Lemma tropical_add_comm : forall x y : ExtZ,
  tropical_add x y = tropical_add y x.
Proof.
  intros x y.
  destruct x, y; simpl; try reflexivity.
  rewrite Z.max_comm. reflexivity.
Qed.

Lemma tropical_add_id_l : forall x : ExtZ,
  tropical_add NegInf x = x.
Proof. intro x. destruct x; reflexivity. Qed.

Lemma tropical_add_id_r : forall x : ExtZ,
  tropical_add x NegInf = x.
Proof. intro x. destruct x; reflexivity. Qed.

Lemma tropical_mul_assoc : forall x y z : ExtZ,
  tropical_mul x (tropical_mul y z) = tropical_mul (tropical_mul x y) z.
Proof.
  intros x y z.
  destruct x, y, z; simpl; try reflexivity.
  rewrite Z.add_assoc. reflexivity.
Qed.

Lemma tropical_mul_id_l : forall x : ExtZ,
  tropical_mul (Finite 0) x = x.
Proof.
  intro x. destruct x; reflexivity.
Qed.

Lemma tropical_mul_id_r : forall x : ExtZ,
  tropical_mul x (Finite 0) = x.
Proof.
  intro x. destruct x; simpl.
  - reflexivity.
  - rewrite Z.add_0_r. reflexivity.
Qed.

Lemma tropical_distr_l : forall x y z : ExtZ,
  tropical_mul x (tropical_add y z) = tropical_add (tropical_mul x y) (tropical_mul x z).
Proof.
  intros x y z.
  destruct x, y, z; simpl; try reflexivity.
  - rewrite Z.add_max_distr_l. reflexivity.
Qed.

Lemma Z_add_max_distr_r : forall n m p : Z, Z.max n m + p = Z.max (n + p) (m + p).
Proof.
  intros n m p.
  rewrite Z.add_comm.
  rewrite Z.add_comm with (n := n).
  rewrite Z.add_comm with (n := m).
  symmetry. apply Z.add_max_distr_l.
Qed.

Lemma tropical_distr_r : forall x y z : ExtZ,
  tropical_mul (tropical_add x y) z = tropical_add (tropical_mul x z) (tropical_mul y z).
Proof.
  intros x y z.
  destruct x, y, z; simpl; try reflexivity.
  - f_equal. apply Z_add_max_distr_r.
Qed.

Lemma tropical_mul_zero_l : forall x : ExtZ,
  tropical_mul NegInf x = NegInf.
Proof. intro x. destruct x; reflexivity. Qed.

Lemma tropical_mul_zero_r : forall x : ExtZ,
  tropical_mul x NegInf = NegInf.
Proof. intro x. destruct x; reflexivity. Qed.

(* Tropical semiring instance *)
Instance ExtZ_TropicalSemiring : Semiring ExtZ := {
  add_op := tropical_add;
  add_zero := NegInf;
  add_assoc := tropical_add_assoc;
  add_left_id := tropical_add_id_l;
  add_right_id := tropical_add_id_r;
  add_comm := tropical_add_comm;

  mul_op := tropical_mul;
  mul_one := Finite 0;
  mul_assoc := tropical_mul_assoc;
  mul_left_id := tropical_mul_id_l;
  mul_right_id := tropical_mul_id_r;

  mul_add_distr_l := tropical_distr_l;
  mul_add_distr_r := tropical_distr_r;

  mul_zero_l := tropical_mul_zero_l;
  mul_zero_r := tropical_mul_zero_r;
}.

(* Tropical Horner's rule *)
Lemma tropical_horners_rule :
  fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 = fold_right add_op add_zero ∘ map (fold_right mul_op mul_one) ∘ inits.
Proof.
  (* This follows from the generalized version with ExtZ_TropicalSemiring *)
  exact (generalised_horners_rule_right ExtZ).
Qed.