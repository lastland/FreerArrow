Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.

From Hammer Require Import Tactics.

Section ID.
  Context {X : Type}.
  
  Definition id (x : X) : X := x.

  Theorem id_idem : forall (x : X),
      id (id x) = x.
  Proof. intros. reflexivity. Qed.

End ID.

Inductive FreerArrow (E : Type -> Type -> Type) (X Y : Type) : Type :=
| Hom : (X -> Y) -> FreerArrow E X Y
| Comp : forall {A B C Z : Type},
    (X -> A * C) -> (B * C -> Z) -> E A B -> FreerArrow E Z Y -> FreerArrow E X Y.

Arguments Hom {E} {X} {Y}.
Arguments Comp {E} {X} {Y} {A} {B} {C} {Z}.

Section Arrows.

  Context {E :Type -> Type -> Type}.
  Context {X Y A B: Type}.

  Fixpoint dimap {X Y A B}
    (f : A -> X) (g : Y -> B) (x : FreerArrow E X Y) : FreerArrow E A B :=
    match x with
    | Hom h => Hom (fun x => g (h (f x)))
    | Comp f' g' x y => Comp (fun x => f' (f x)) g' x (dimap id g y)
    end.

  Definition lmap (f : A -> X) (x : FreerArrow E X Y) : FreerArrow E A Y :=
    match x with
    | Hom h => Hom (fun x => h (f x))
    | Comp f' g' x y => Comp (fun x => f' (f x)) g' x y
    end.

  Fixpoint first' {X Y A} (x : FreerArrow E X Y) : FreerArrow E (X * A) (Y * A) :=
    match x with
    | Hom f => Hom (fun '(x, a) => (f x, a))
    | Comp f g a b => Comp (fun '(x, a) =>
                             match f x with
                             | (x', b) => (x', (b, a))
                             end)
                          (fun '(y, (b, a)) => (g (y, b), a))
                          a (first' b)
                                      
  end.

  Definition arr : (X -> Y) -> FreerArrow E X Y := Hom.

  Definition first : FreerArrow E X Y -> FreerArrow E (X * A) (Y * A) := first'.

  (* This is (>>>) in Haskell. *)
  Fixpoint comp {X Y Z} (x : FreerArrow E X Y) (y : FreerArrow E Y Z) : FreerArrow E X Z :=
    match x with
    | Hom g => dimap g id y
    | Comp f g a b => Comp f g a (comp b y)
    end.

End Arrows.

Reserved Notation "x ≈ y" (at level 42).

Inductive Similar {E X X' Y} :
  FreerArrow E X Y -> FreerArrow E X' Y -> Prop :=
| HomEq : forall f f', Hom f ≈ Hom f'                    
| CompEq : forall {A B C C' Z Z'}
           (f : X -> A * C) (f' : X' -> A * C')
           (g : B * C -> Z) (g' : B * C' -> Z')
           (e e' : E A B)
           (a : FreerArrow E Z Y) (a' : FreerArrow E Z' Y),
    e = e' ->
    a ≈ a' ->
    Comp f g e a ≈ Comp f' g' e' a'
where "x ≈ y" := (Similar x y).

Section ProfunctorLaws.

  Context {E :Type -> Type -> Type}.
  Context {X Y Z A B: Type}.

  (* Profunctor laws. *)

  Theorem dimap_id : forall (x : FreerArrow E X Y),
      dimap id id x = x.
  Proof. induction x; sauto. Qed.

  Theorem dimap_dimap : forall A' B' (x : FreerArrow E X Y)
                          (f : A -> X) (g : A' -> A) (h : B -> B') (i : Y -> B),
      dimap (fun x => f (g x)) (fun x => h (i x)) x = dimap g h (dimap f i x).
  Proof.
    intros until x. revert A B A' B'.
    induction x; [sauto|].
    intros. cbn. f_equal.
    apply IHx.
  Qed.

End ProfunctorLaws.

#[export]
Hint Resolve dimap_id : freer_arrow.

#[export]
Hint Resolve dimap_dimap : freer_arrow. 

Section ArrowsLaws.

  Context {E :Type -> Type -> Type}.
  Context {X Y Z A B: Type}.
  Parameters (f : X -> Y) (g : Y -> Z).

  (* lmap and dimap *)

  Theorem lmap_dimap : forall (f : A -> X) (x : FreerArrow E X Y),
      lmap f x = dimap f id x.
  Proof.
    induction x; cbn; [reflexivity |].
    f_equal. symmetry. apply dimap_id.
  Qed.
    

  (* Arrow laws. *)

  Theorem arr_id : @arr E X X (fun x => x) = Hom (fun x => x).
  Proof. reflexivity. Qed.

  Theorem arr_comp : 
      @arr E _ _ (fun x => g (f x)) = comp (arr f) (arr g).
  Proof. reflexivity. Qed.

  Theorem first_arr :
    @first E _ _ A (arr f) = arr (fun '(x, y) => (f x, y)).
  Proof. reflexivity. Qed.

  Theorem first_comp :
    forall (a : FreerArrow E X Y) (b : FreerArrow E Y Z),
    @first _ _ _ A (comp a b) = comp (@first _ _ _ A a) (first b).
  Proof.
    induction a; intros; cbn.
    - generalize dependent X.
      generalize dependent A.
      induction b; cbn.
      + intros. f_equal. extensionality a. sauto.
      + intros. f_equal.
        * extensionality a. sauto.
        * specialize (IHb A1 _ id). unfold first in IHb.
          rewrite -> IHb. f_equal.
          extensionality a. sauto.
    - f_equal. sauto. 
  Qed.

  Theorem first_comp_arr :
    forall (a : FreerArrow E X Y),
      comp (@first _ _ _ A a) (arr fst) = comp (@arr _ (X * A) _ fst) a.
  Proof.
    induction a; cbn.
    - f_equal. extensionality a. destruct a as []; cbn. reflexivity.
    - unfold arr. 
      (* Existential types do not match. *)
  Abort.

  Definition assoc {X Y Z} (p : (X * Y * Z)) : (X * (Y * Z)) :=
    match p with
    | (x, y, z) => (x, (y, z))
    end.

  Theorem first_assoc :
    forall (a : FreerArrow E X Y),
      comp (@first _ _ _ A (@first _ _ _ B a)) (arr assoc) = comp (arr assoc) (first a).
  Proof.
    induction a; cbn.
    - f_equal. extensionality a. destruct a as [[] ?]; cbn. reflexivity.
    - (* Existential types do not match. *)
  Abort.

End ArrowsLaws.
