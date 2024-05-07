Class Category := {
  Obj : Type;  (* Type of objects in the category *)
  Mor : Obj -> Obj -> Type;  (* Type of morphisms between objects *)
  
  id : forall {X}, Mor X X;  (* Identity morphism *)
  compose : forall {X Y Z}, Mor Y Z -> Mor X Y -> Mor X Z;  (* Composition of morphisms *)

  (* Category axioms *)
  left_identity : forall {X Y} (f : Mor X Y), compose id f = f;
  right_identity : forall {X Y} (f : Mor X Y), compose f id = f;
  associativity : forall {X Y Z W} (f : Mor W X) (g : Mor X Y) (h : Mor Y Z),
                  compose h (compose g f) = compose (compose h g) f
}.
