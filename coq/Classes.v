Open Scope type_scope.

Class Profunctor (F : Type -> Type -> Type) :=
  {
    dimap {X Y A B} : (A -> X) -> (Y -> B) -> F X Y -> F A B 
  }.

Class StrongProfunctor (F : Type -> Type -> Type) `{Profunctor F} :=
  {
    first' {A B C} : F A B -> F (A * C) (B * C)
  }. 

Class Category (F : Type -> Type -> Type) :=
  {
    id {A} : F A A ;
    comp {A B C} : F A B -> F B C -> F A C
  }.

Class PreArrow  (F : Type -> Type -> Type) `{Category F} :=
  {
    arr {A B} : (A -> B) -> F A B 
  }.

Class Arrow (F : Type -> Type -> Type) `{PreArrow F} `{StrongProfunctor F} :=
  { 
    first  {A B C} : F A B -> F (A * C) (B * C)
  }.
