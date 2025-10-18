Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.StructGroup. Export FreeMonoid.StructGroup.
Require Import Coq.Setoids.Setoid.

Section GroupHomomorphisms.

Class GroupHomomorphism {A B : Type} `{Group A} `{Group B} (f : A -> B) := {
  g_hom_preserves_op : forall x y : A, f (m_op x y) = m_op (f x) (f y);
}.

Theorem g_hom_preserves_id {A B : Type} `{Group A} `{Group B} (f : A -> B) (fHom : GroupHomomorphism f) : f (mn_id) = mn_id.
Proof.
  (* Key insight: f(e_A) = f(e_A * e_A) = f(e_A) * f(e_A)
     So f(e_A) satisfies x = x * x, which in a group implies x = e_B *)

  (* First show: f(mn_id) = f(mn_id) * f(mn_id) *)
  assert (H_eq : f mn_id = m_op (f mn_id) (f mn_id)).
  { rewrite <- g_hom_preserves_op.
    rewrite mn_left_id.
    reflexivity.
  }

  (* Now we use the fact that in a group, if x = x * x then x = e
     Proof: Multiply both sides on the right by inv(x):
       x * inv(x) = x * x * inv(x)
       e = x * (x * inv(x))     (by associativity)
       e = x * e                (by definition of inverse)
       e = x                    (by right identity)
  *)

  (* Apply this reasoning *)
  symmetry.
  transitivity (m_op (f mn_id) (g_inv (f mn_id))).
  - (* Show: mn_id = f(mn_id) * inv(f(mn_id)) *)
    symmetry. apply g_inv_right.
  - (* Show: f(mn_id) * inv(f(mn_id)) = f(mn_id) *)
    rewrite H_eq at 1.
    (* Now we have: (f(mn_id) * f(mn_id)) * inv(f(mn_id)) = f(mn_id) *)
    rewrite <- sg_assoc.
    (* Now we have: f(mn_id) * (f(mn_id) * inv(f(mn_id))) = f(mn_id) *)
    rewrite g_inv_right.
    rewrite mn_right_id.
    reflexivity.
Qed.

(* Helper lemma: inverses are unique in a group *)
Lemma inv_unique {A : Type} `{Group A} : forall x y : A,
  m_op x y = mn_id -> m_op y x = mn_id -> y = g_inv x.
Proof.
  intros x y H_right H_left.
  (* We have: y = y * e = y * (x * inv(x)) = (y * x) * inv(x) = e * inv(x) = inv(x) *)
  transitivity (m_op y mn_id).
  - symmetry. apply mn_right_id.
  - transitivity (m_op y (m_op x (g_inv x))).
    + rewrite g_inv_right. reflexivity.
    + rewrite sg_assoc.
      rewrite H_left.
      rewrite mn_left_id.
      reflexivity.
Qed.

Theorem g_hom_preserves_inv {A B : Type} `{Group A} `{Group B} (f : A -> B) (fHom : GroupHomomorphism f) : forall x : A, f (g_inv x) = g_inv (f x).
Proof.
  intros x.
  (* Strategy: Show that f(inv(x)) acts as the inverse of f(x),
     then use uniqueness of inverses *)

  apply inv_unique.

  (* First show: f(x) * f(inv(x)) = mn_id *)
  - rewrite <- (@g_hom_preserves_op A B _ _ _ _ _ _ _ _ f fHom).
    rewrite g_inv_right.
    apply (g_hom_preserves_id f fHom).

  (* Then show: f(inv(x)) * f(x) = mn_id *)
  - rewrite <- (@g_hom_preserves_op A B _ _ _ _ _ _ _ _ f fHom).
    rewrite g_inv_left.
    apply (g_hom_preserves_id f fHom).
Qed.

End GroupHomomorphisms.
