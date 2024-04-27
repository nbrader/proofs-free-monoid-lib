Class Category := {
  Obj : Type;  (* Type of objects in the category *)
  Hom : Obj -> Obj -> Type;  (* Type of morphisms between objects *)
  
  id : forall {X}, Hom X X;  (* Identity morphism *)
  compose : forall {X Y Z}, Hom Y Z -> Hom X Y -> Hom X Z;  (* Composition of morphisms *)

  (* Category axioms *)
  left_identity : forall {X Y} (f : Hom X Y), compose id f = f;
  right_identity : forall {X Y} (f : Hom X Y), compose f id = f;
  associativity : forall {X Y Z W} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
                  compose h (compose g f) = compose (compose h g) f
}.
