Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
From Hammer Require Import Tactics.

Open Scope type_scope.

(** Profunctors and arrows. *)

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

Definition swap {X Y} : X * Y -> Y * X :=
  fun '(x, y) => (y, x).

Definition swapsum {X Y} (s : X + Y) : Y + X :=
  match s with
  | inl x => inr x
  | inr y => inl y
  end.

Definition parMul {I A B X Y} `{Arrow I} (f : I A B) (g : I X Y) : I (A * X) (B * Y) :=
  first f >>> arr swap >>> first g >>> arr swap.

Definition parAdd {I A B X Y} `{ChoiceArrow I} (f : I A B) (g : I X Y) : I (A + X) (B + Y) :=
  left f >>> arr swapsum >>> left g >>> arr swapsum.

Notation " x *** y" := (parMul x y) (at level 40).
Notation " x +++ y" := (parAdd x y) (at level 41).

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

Definition assoc {X Y Z} : X * Y * Z -> X * (Y * Z) :=
  fun '(x, y, z) => (x, (y, z)).

Definition assocsum {X Y Z} (s : X + Y + Z) : X + (Y + Z) :=
  match s with
  | inl (inl x) => inl x
  | inl (inr y) => inr (inl y)
  | inr z => inr (inr z)
  end.

Section Laws.
  Variable I : Type -> Type -> Type.
  Variable eq : forall {A B}, I A B -> I A B -> Prop.
  Context `{forall A B, Equivalence (@eq A B)}.
  
  #[local] Notation "a ≈ b" := (eq a b) (at level 43).

  (** Profunctor laws. *)
  Context `{Profunctor I}.

  Class ProfunctorLaws :=
    { dimap_distr : forall {A B X Y V W}
                       (f : X -> A) (g : V -> X) (h : Y -> W) (i : B -> Y) (x : I A B),
        dimap (fun x => f (g x)) (fun x => h (i x)) x ≈ dimap g h (dimap f i x)
    }.

  (** Category laws. *)
  Context `{Category I}.

  Class CategoryLaws :=
    {
      left_id  : forall {A B} (f : I A B), id >>> f ≈ f ;
      right_id : forall {A B} (f : I A B), f >>> id ≈ f ;
      comp_assoc : forall {A B C Y} (f : I A B) (g : I B C) (h : I C Y), (f >>> g) >>> h ≈ f >>> (g >>> h) 
    }.
  
  (** Pre-arrow laws. *)
  Context `{PreArrow I}.

  Class PreArrowLaws :=
    { arr_id : forall {A}, arr (@id _ _ A) ≈ id ;
      arr_distr : forall {A B C} (f : A -> B) (g : B -> C),  arr (f >>> g) ≈ arr f >>> arr g
    }.

  (** Arrow laws. *)
  Context `{Arrow I}.

  Class ArrowLaws :=
    { first_arr : forall {A B C} (f : A -> B), @first _ _ _ _ _ C (arr f) ≈ arr (first f) ;
      first_distr : forall {A B C} (f : I A B) (g : I B C), @first _ _ _ _ _ C (f >>> g) ≈ first f >>> first g ;
      first_fst : forall {A B C} (f : I A B), @first _ _ _ _ _ C f >>> arr fst ≈ arr fst >>> f ;
      first_and : forall {A B X Y} (f : I A B) (g : X -> Y), first f >>> arr (id *** g) ≈ arr (id *** g) >>> first f ;
      first_first : forall {A B X Y} (f : I A B),
        @first _ _ _ _ _ X (@first _ _ _ _ _ Y f) >>> arr assoc ≈ arr assoc >>> first f
    }.

  (** Choice arrow laws. *)
  Context `{ChoiceArrow I}.
  
  Class ChoiceArrowLaws :=
    { left_arr : forall {A B C} (f : A -> B), @left _ _ _ _ _ C (arr f) ≈ arr (left f) ;
      left_distr : forall {A B C} (f : I A B) (g : I B C), @left _ _ _ _ _ C (f >>> g) ≈ left f >>> left g ;
      left_inl : forall {A B C} (f : I A B), f >>> arr inl ≈ arr inl >>> @left _ _ _ _ _ C f ;
      left_and : forall {A B X Y} (f : I A B) (g : X -> Y), left f >>> arr (id +++ g) ≈ arr (id +++ g) >>> left f ;
      left_left : forall {A B X Y} (f : I A B),
        @left _ _ _ _ _ X (@left _ _ _ _ _ Y f) >>> arr assocsum ≈ arr assocsum >>> left f
    }.

End Laws.
  
Instance ProfunctorLaws__Fun : ProfunctorLaws (fun A B => A -> B) (fun _ _ f g => f = g).
Proof. sfirstorder. Qed.

Instance CategoryLaws__Fun : CategoryLaws (fun A B => A -> B) (fun _ _ f g => f = g).
Proof. sfirstorder. Qed.

Instance PreArrowLaws__Fun : PreArrowLaws (fun A B => A -> B) (fun _ _ f g => f = g).
Proof. sfirstorder. Qed.

Instance ArrowLaws__Fun : ArrowLaws (fun A B => A -> B) (fun _ _ f g => f = g).
Proof.
  constructor; try solve [sfirstorder];
    try solve [intros; sauto lq: on use: functional_extensionality].
Qed.

Instance ChoiceArrowLaws__Fun : ChoiceArrowLaws (fun A B => A -> B) (fun _ _ f g => f = g).
Proof.
  constructor; try solve [sfirstorder];
    try solve [intros; sauto lq: on use: functional_extensionality].
Qed.
