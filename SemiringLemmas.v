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

(* Specialized version for Z showing the connection to the original theorem *)
Lemma horners_rule_Z_from_general :
  fold_right (fun x y => Zplus (Zmult x y) 1) 1 = fold_right Zplus 0 ∘ map (fold_right Zmult 1) ∘ inits.
Proof.
  (* This follows directly from the generalized version with Z_Semiring *)
  exact (generalised_horners_rule_right Z).
Qed.