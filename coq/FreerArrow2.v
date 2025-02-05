Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.JMeq.

From Hammer Require Import Tactics Hammer.

Open Scope type_scope.

Section ID.
  Context {X : Type}.
  
  Definition id (x : X) : X := x.

  Theorem id_idem : forall (x : X),
      id (id x) = x.
  Proof. intros. reflexivity. Qed.

End ID.

Inductive FreerArrow (E : Type -> Type -> Type) (X Y : Type) : Type :=
| Hom : (X -> Y) -> FreerArrow E X Y
| Comp : forall {A B C : Type},
    (X -> A * C) -> E A B -> FreerArrow E (B * C) Y -> FreerArrow E X Y.

Arguments Hom {E} {X} {Y}.
Arguments Comp {E} {X} {Y} {A} {B} {C}.

Section Arrows.

  Context {E :Type -> Type -> Type}.
  Context {X Y A B: Type}.

  Definition assoc {X Y Z} (p : (X * Y * Z)) : (X * (Y * Z)) :=
    match p with
    | (x, y, z) => (x, (y, z))
    end.

  Definition unassoc {X Y Z} (p : (X * (Y * Z))) : (X * Y * Z) :=
    match p with
    | (x, (y, z)) => (x, y, z)
    end.

  Definition lmap {A X Y} (f : A -> X) (x : FreerArrow E X Y) : FreerArrow E A Y :=
    match x with
    | Hom h => Hom (fun x => h (f x))
    | Comp f' x y => Comp (fun x => f' (f x)) x y
    end.

  Fixpoint first' {X Y A} (x : FreerArrow E X Y) : FreerArrow E (X * A) (Y * A) :=
    match x with
    | Hom f => Hom (fun '(x, a) => (f x, a))
    | Comp f a b => Comp (fun '(x, a) =>
                             match f x with
                             | (x', b) => (x', (b, a))
                             end)
                          a
                          (lmap unassoc (first' b))
  end.

  Definition arr {X Y} : (X -> Y) -> FreerArrow E X Y := Hom.

  Definition first : FreerArrow E X Y -> FreerArrow E (X * A) (Y * A) := first'.

  (* This is (>>>) in Haskell. *)
  Fixpoint comp {X Y Z} (x : FreerArrow E X Y) (y : FreerArrow E Y Z) :
    FreerArrow E X Z :=
    match x with
    | Hom g => lmap g y
    | Comp f a b => Comp f a (comp b y)                                 
    end.

  Definition dimap {X Y A B}
    (f : A -> X) (g : Y -> B) (x : FreerArrow E X Y) : FreerArrow E A B :=
    match x with
    | Hom h => Hom (fun x => g (h (f x)))
    | Comp f' x y => Comp (fun x => f' (f x)) x
                            (comp y (arr g))
    end.

End Arrows.

Definition join {X Y A B C} (f : X -> A * C) (g : B * C -> Y) (x : X) (b : B) : Y :=
  let '(_, c) := f x in g (b, c).

Fixpoint CharacteristicType {E : Type -> Type -> Type} {X Y : Type}
                              (e : FreerArrow E X Y) : Type :=
  match e with
  | Hom _ => Y
  | @Comp _ _ _ A B C f e y => B -> CharacteristicType y
  end.

Fixpoint Characteristic {E : Type -> Type -> Type} {X Y : Type}  
  (e : FreerArrow E X Y) : (X -> CharacteristicType e) :=
  match e with
  | Hom f => f
  | Comp f e y => join f (Characteristic y)
  end.

(* 
Inductive Characteristic {E : Type -> Type -> Type} {X Y : Type} : 
  forall (e : FreerArrow E X Y), (X -> CharacteristicType e) -> Prop :=
  | HomChar : forall f, Characteristic (Hom f) f
  | CompChar : forall A B C
                 (f : X -> A * C) (e : E A B)
                 (y : FreerArrow E (B * C) Y) (g : B * C -> CharacteristicType y) h,
      Characteristic y g ->
      JMeq h (join f g) ->
      Characteristic (Comp f e y) h.

Lemma CharacteristicCompInv {E : Type -> Type -> Type} {X Y : Type} :
  forall A B C (f : X -> A * C) (e : E A B) (y : FreerArrow E (B * C) Y) h,
  Characteristic (Comp f e y) h ->
  exists g, (JMeq h (join f g) /\ Characteristic y g).
Proof.
  intros A B C f e y h H. cbn in h.
  induction H.
  - admit.
  - 

Lemma CharacteristicUniq {E : Type -> Type -> Type} {X Y : Type} :
  forall (e : FreerArrow E X Y) f g,
    Characteristic e f ->
    Characteristic e g ->
    f = g.
Proof.
  intros e f g H. generalize dependent g.
  induction H.
  - inversion 1; subst.
    sauto use: Eqdep.EqdepTheory.inj_pair2.
  - intros i Hi. subst.
Admitted.
*)

Reserved Notation "x ≈ y" (at level 42).

Variant ArrowEq {E X Y} (x y : FreerArrow E X Y) : Prop :=
| ArrowEqChar : forall f g,
  Characteristic x = f ->
  Characteristic y = g ->
  JMeq f g ->
  x ≈ y
where "x ≈ y" := (ArrowEq x y).

Instance Equivalence__ArrowEq {E X Y} : Equivalence (@ArrowEq E X Y).
Proof.
  constructor.
  - intros x. induction x.
    + sauto lq: on.
    + destruct x; sauto lq: on.
  - intros x y. inversion 1. sauto.
  - intros x y z. do 2 inversion 1; subst.
    econstructor; sauto.
Qed.

Lemma eqImpliesArrowEq : forall {E X Y} (x y : FreerArrow E X Y),
    x = y -> x ≈ y.
Proof. intros ? ? ? ? ? ->. reflexivity. Qed.

Hint Resolve eqImpliesArrowEq : arrows.

Section ArrowsLaws.

  Context {E :Type -> Type -> Type}.
  Context {X Y Z A B: Type}.
  Parameters (f : X -> Y) (g : Y -> Z).

  Theorem comp_id_r : forall (x : FreerArrow E X Y),
      comp x (arr id) = x.
  Proof. induction x; sauto. Qed.

  Corollary comp_id_r' : forall (x : FreerArrow E X Y),
      comp x (arr id) ≈ x.
  Proof. sauto use: comp_id_r, eqImpliesArrowEq. Qed.

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
      destruct b; cbn.
      + intros. f_equal. extensionality a. sauto.
      + intros. f_equal.
        extensionality a. sauto.
    - f_equal. sauto lq: on.
  Qed.

  Theorem first_comp_arr :
    forall (a : FreerArrow E X Y),
      comp (@first _ _ _ A a) (arr fst) ≈ comp (@arr _ (X * A) _ fst) a.
  Proof.
    induction a; cbn.
    - assert ((fun x : X * A => fst (let '(x0, a) := x in (y x0, a))) = (fun x : X * A => y (fst x)))
        by sauto lq: on use: functional_extensionality.
      sauto lq: on.
    - cbn in IHa. econstructor.
      + cbn. reflexivity.
      + cbn. reflexivity.
      + inversion IHa; subst.
        apply JMeq_eq_dep_id in H1.
        (* What do I do now? *)
        (* Existential types do not match. *)
  Abort.

    Theorem first_assoc :
    forall (a : FreerArrow E X Y),
      comp (@first _ _ _ A (@first _ _ _ B a)) (arr assoc) ≈ comp (arr assoc) (first a).
  Proof.
    induction a; cbn.
    - assert ((fun x : X * B * A => assoc (let '(x0, a) := x in (let '(x1, a0) := x0 in (y x1, a0), a))) =
                (fun x : X * B * A => let '(x0, a) := assoc x in (y x0, a)))
        by sauto lq: on use: functional_extensionality.
      sauto lq: on.
    - cbn in IHa. econstructor.
      + cbn. reflexivity.
      + cbn. reflexivity.
      + inversion IHa; subst.
        (* What do I do now? *)
        (* Existential types do not match. *)
  Abort.

End ArrowsLaws.

Section ProfunctorLaws.

  Context {E :Type -> Type -> Type}.
  Context {X Y Z A B: Type}.

  (* Profunctor laws. *)

  Theorem dimap_id : forall (x : FreerArrow E X Y),
      dimap id id x = x.
  Proof. induction x; sauto use:comp_id_r. Qed.

  Theorem dimap_dimap : forall A' B' (x : FreerArrow E X Y)
                          (f : A -> X) (g : A' -> A) (h : B -> B') (i : Y -> B),
      dimap (fun x => f (g x)) (fun x => h (i x)) x = dimap g h (dimap f i x).
  Proof.
    intros until x. revert A B A' B'.
    induction x; [sauto|].
    intros. cbn. f_equal. 
  Abort.

End ProfunctorLaws.

#[export]
Hint Resolve dimap_id : freer_arrow.

(*
#[export]
Hint Resolve dimap_dimap : freer_arrow. 
*)

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

End ArrowsLaws.
