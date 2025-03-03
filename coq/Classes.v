Open Scope type_scope.

Class Profunctor (F : Type -> Type -> Type) :=
  {
    dimap {X Y A B} : (A -> X) -> (Y -> B) -> F X Y -> F A B 
  }.

Class StrongProfunctor (F : Type -> Type -> Type) `{Profunctor F} :=
  {
    first {A B C} : F A B -> F (A * C) (B * C)
  }.

Class ChoiceProfunctor  (F : Type -> Type -> Type) `{Profunctor F} :=
  {
    left {A B C} : F A B -> F (A + C) (B + C)
  }.

Class Category (F : Type -> Type -> Type) :=
  {
    id {A} : F A A ;
    comp {A B C} : F A B -> F B C -> F A C
  }.

Notation "x >>> y" := (comp x y) (at level 42, right associativity).

Class PreArrow  (F : Type -> Type -> Type) `{Category F} :=
  {
    arr {A B} : (A -> B) -> F A B 
  }.

(* We don't define anything here since [first] is already included. *)
Class Arrow (F : Type -> Type -> Type) `{PreArrow F} `{StrongProfunctor F} :=
  {}.

Class ChoiceArrow (F : Type -> Type -> Type) `{PreArrow F} `{ChoiceProfunctor F} :=
  {}.

#[export] Instance Arrow__Infer F `{PreArrow F} `{StrongProfunctor F} : Arrow F.
Defined.

#[export] Instance ChoiceArrow__Infer F `{PreArrow F} `{ChoiceProfunctor F} : ChoiceArrow F.
Defined.

(** Functional arrows are arrows. *)
#[export] Instance Profunctor__Fun : Profunctor (fun A B => A -> B) :=
  {| dimap := fun _ _ _ _ f g h a => g (h (f a)) |}.

#[export] Instance StrongProfunctor__Fun : StrongProfunctor (fun A B => A -> B) :=
  {| first := fun A _ C f '((a, c) : A * C) => (f a, c) |}.

#[export] Instance ChoiceProfunctor__Fun : ChoiceProfunctor (fun A B => A -> B) :=
  {| left := fun A _ C f (x : A + C) =>
                match x with
                | inl a => inl (f a)
                | inr c => inr c
                end |}.

#[export] Instance Category__Fun : Category (fun A B => A -> B) :=
  {| id := fun _ x => x;
    comp := fun _ _ _ f g a => g (f a) |}.

#[export] Instance PreArrow__Fun : PreArrow (fun A B => A -> B) :=
  {| arr := fun _ _ f => f |}.

#[export] Instance Arrow__Fun : Arrow (fun A B => A -> B) := Arrow__Infer _.

#[export] Instance ChoiceArrow__Fun : ChoiceArrow (fun A B => A -> B) := ChoiceArrow__Infer _.
