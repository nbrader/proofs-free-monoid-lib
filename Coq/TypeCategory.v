Require Import FreeMonoid.Category.

(* Category of Coq types and functions *)
Instance TypeCategory : Category := {
  Obj := Type;
  Mor := fun X Y => X -> Y;
  id := fun X x => x;
  compose := fun X Y Z g f x => g (f x);
  left_identity := fun X Y f => eq_refl;
  right_identity := fun X Y f => eq_refl;
  associativity := fun X Y Z W f g h => eq_refl
}.
