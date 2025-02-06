Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.

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

Fixpoint character {E : Type -> Type -> Type} {X Y : Type}  
  (e : FreerArrow E X Y) : (X -> CharacteristicType e) :=
  match e with
  | Hom f => f
  | Comp f e y => join f (character y)
  end.

Lemma sameE_sameCharTyp : forall {E X Y A B C D Q}
                     (f : X -> A * C) (g : Q -> A * D)
                     (x : FreerArrow E (B * C) Y) (y : FreerArrow E (B * D) Y)
                     (e : E A B),
    CharacteristicType x = CharacteristicType y ->
    CharacteristicType (Comp f e x) = CharacteristicType (Comp g e y).
Proof. sfirstorder. Qed.


(* 
Inductive character {E : Type -> Type -> Type} {X Y : Type} : 
  forall (e : FreerArrow E X Y), (X -> CharacteristicType e) -> Prop :=
  | HomChar : forall f, character (Hom f) f
  | CompChar : forall A B C
                 (f : X -> A * C) (e : E A B)
                 (y : FreerArrow E (B * C) Y) (g : B * C -> CharacteristicType y) h,
      character y g ->
      JMeq h (join f g) ->
      character (Comp f e y) h.

Lemma CharacteristicCompInv {E : Type -> Type -> Type} {X Y : Type} :
  forall A B C (f : X -> A * C) (e : E A B) (y : FreerArrow E (B * C) Y) h,
  character (Comp f e y) h ->
  exists g, (JMeq h (join f g) /\ character y g).
Proof.
  intros A B C f e y h H. cbn in h.
  induction H.
  - admit.
  - 

Lemma CharacteristicUniq {E : Type -> Type -> Type} {X Y : Type} :
  forall (e : FreerArrow E X Y) f g,
    character e f ->
    character e g ->
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

Inductive ArrowSimilar {E X Y P} : FreerArrow E X Y -> FreerArrow E P Y -> Prop :=
| HomSimilar : forall f g, ArrowSimilar (Hom f) (Hom g)
| CompSimilar : forall A B C D x y (f : X -> A * C) (g : P -> A * D) (e : E A B),
    ArrowSimilar x y ->
    ArrowSimilar (Comp f e x) (Comp g e y). 

Theorem ArrowSimilarCharTypEq {E X Y P} : forall (x : FreerArrow E X Y) (y : FreerArrow E P Y),
    ArrowSimilar x y ->
    CharacteristicType x = CharacteristicType y.
Proof.
  intros x. generalize dependent P. induction x.
  - sauto lq: on.
  - intros. inversion H; subst.
    inversion H; subst.
    do 2 apply Eqdep.EqdepTheory.inj_pair2 in H6.
    sfirstorder.
Qed.

(** This is more general than the normal transitivity because it is
    heterogeneous. *)
Lemma Trans__ArrowSimilar :
  forall {E X Y Z R} (x : FreerArrow E X R) (y : FreerArrow E Y R) (z : FreerArrow E Z R),
  ArrowSimilar x y -> ArrowSimilar y z -> ArrowSimilar x z.
Proof.
  intros E X Y Z R x y z H. generalize dependent Z.
  induction H.
  - sauto lq: on.
  - intros. inversion H0; subst.
    do 2 apply inj_pair2 in H5.
    do 2 apply inj_pair2 in H6. 
    do 2 apply inj_pair2 in H7.
    sauto lq: on.
Qed.    

Instance Equivalence__ArrowSimilar {E X Y} : Equivalence (@ArrowSimilar E X Y X).
Proof.
  constructor.
  - intros x. induction x; sauto lq: on.
  - intros x y. induction 1; subst; sauto lq: on.
  - intros x y z. apply Trans__ArrowSimilar.
Qed.

Variant ArrowEq {E X Y} : FreerArrow E X Y -> FreerArrow E X Y -> Prop :=
| ArrowEqSimilar : forall x y (H : ArrowSimilar x y),
    (let H0 := ArrowSimilarCharTypEq x y H in
     let cx := eq_rect _ (fun T : Type => X -> T) (character x) _ H0 in
     cx = character y) ->
    x ≈ y
where "x ≈ y" := (ArrowEq x y).


Theorem ArrowEqInd {E X Y A B C}
  (f g : X -> (A * C)) (e : E A B) (x y : FreerArrow E (B * C) Y) :
  x ≈ y -> f = g -> Comp f e x ≈ Comp g e y.
Proof.
  inversion 1. intros Hfunc; subst.
  eapply ArrowEqSimilar.
  Unshelve. 2: { constructor. assumption. }
  cbn. rewrite <- H1.
  remember (ArrowSimilarCharTypEq (Comp g e x) (Comp g e y) (CompSimilar A B C C x y g g e H0)) as HC1.
  remember (ArrowSimilarCharTypEq x y H0) as HC2.
  cbn in HC1. unfold eq_rect.
  generalize (character x).
  generalize HC1. rewrite HC2. intros.
  rewrite (UIP_refl _ _ HC0). reflexivity.
Qed.

Instance Equivalence__ArrowEq {E X Y} : Equivalence (@ArrowEq E X Y).
Proof.
  constructor.
  - intros x. induction x.
    + econstructor. cbn.
      Unshelve. 2: { constructor. }
      rewrite (UIP_refl _ _ (ArrowSimilarCharTypEq (Hom y) (Hom y) (HomSimilar y y))).
      reflexivity.
    + apply ArrowEqInd; sfirstorder.
  - intros x y. inversion 1; subst.
    econstructor; cbn.
    Unshelve. 2: { symmetry. assumption. }
    cbn in H1. 
    remember (ArrowSimilarCharTypEq y x (symmetry H0)) as HS.
    remember (ArrowSimilarCharTypEq x y H0) as HD.
    revert H1. generalize (character y). unfold eq_rect.
    generalize HS. rewrite <- HD.
    intros. rewrite (UIP_refl _ _ HS0). sfirstorder.
  - intros x y z. do 2 (inversion 1; subst).
    econstructor; cbn in *.
    Unshelve. 2: { etransitivity; eassumption. }
    remember (ArrowSimilarCharTypEq x y H0) as Hxy.
    remember (ArrowSimilarCharTypEq y z H3) as Hyz.
    remember (ArrowSimilarCharTypEq x z (transitivity H0 H3)) as Hxz.
    revert H1 H4. unfold eq_rect.
    generalize (character x) (character y). generalize Hxz.
    rewrite Hxy. rewrite Hyz. intros; subst.
    rewrite (UIP_refl _ _ Hxz0). reflexivity.
Qed.

Lemma eqImpliesArrowEq {E X Y} (x y : FreerArrow E X Y) :
    x = y -> x ≈ y.
Proof. intros ->; reflexivity. Qed.

Hint Resolve eqImpliesArrowEq : arrows.

Lemma comp_lmap_Similar : forall E A B C Y (a : FreerArrow E (B * C) Y),
    ArrowSimilar (comp (@first _ _ _ A a) (arr fst)) (lmap (@fst (B * C) A) a) ->
    ArrowSimilar (comp (lmap unassoc (first' a)) (@arr _ (Y * A) _ fst)) a.
Proof.
  intros.
  (* TODO: Prove this. Looks provable by induction, but I won't directly be able
     to do that without some dealing with types.*)
Admitted.

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


  (*
  @ArrowSimilar E (B0 * C * A) Y (B0 * C * A)
    (@comp E (B0 * C * A) (Y * A) Y (@first E (B0 * C) Y A a) (@arr E (Y * A) Y (@fst Y A)))
    (@lmap E (B0 * C * A) (B0 * C) Y (@fst (B0 * C) A) a) ->
  @ArrowSimilar E (B0 * (C * A)) Y (B0 * C)
    (@comp E (B0 * (C * A)) (Y * A) Y
       (@lmap E (B0 * (C * A)) (B0 * C * A) (Y * A) (@unassoc B0 C A) (@first' E (B0 * C) Y A a))
       (@arr E (Y * A) Y (@fst Y A))) a
       *)
  
  Theorem first_comp_arr :
    forall (a : FreerArrow E X Y),
      comp (@first _ _ _ A a) (arr fst) ≈ comp (@arr _ (X * A) _ fst) a.
  Proof.
    induction a; cbn.
    - assert ((fun x : X * A => fst (let '(x0, a) := x in (y x0, a))) = (fun x : X * A => y (fst x)))
        by sauto lq: on use: functional_extensionality.
      econstructor. Unshelve.
      2: { constructor. }  
      cbn. remember (ArrowSimilarCharTypEq _ _ _) as HA.
      unfold eq_rect. rewrite H.
      generalize (fun x : X * A => y (fst x)). generalize HA.
      rewrite H. intros. rewrite (UIP_refl _ _ HA0).
      reflexivity.
    - cbn in IHa. inversion IHa; subst.
      econstructor. Unshelve.
      2: { constructor; apply comp_lmap_Similar; assumption. }
      revert H0. unfold eq_rect.
      remember (ArrowSimilarCharTypEq (comp _ _) _ _) as H1.
      remember (ArrowSimilarCharTypEq (Comp _ _ _) _ _) as H2.
      cbn in *. generalize H2.
      assert (H3 : CharacteristicType (comp (lmap (@unassoc B0 C A) (first' a)) (arr fst)) =
                     CharacteristicType a).
      { admit. } (* TODO: Make this a lemma. Looks provable. *)
      generalize (character (comp (@first E (B0 * C) Y A a) (arr fst))).
      generalize (@join (X * A) _ _ _ _ (fun '(x, a0) => let (x', b) := p x in (x', (b, a0)))
                    (character (comp (lmap unassoc (first' a)) (arr fst)))).
      rewrite H1. rewrite H3. intros.
      rewrite (UIP_refl _ _ H0).
      (* TODO: This seems provable to me, but I will need to do a bunch of
         things to related [c] and [c0], possibly before generalizing them. *)
  Admitted.

    Theorem first_assoc :
    forall (a : FreerArrow E X Y),
      comp (@first _ _ _ A (@first _ _ _ B a)) (arr assoc) ≈ comp (arr assoc) (first a).
  Proof.
    induction a; cbn.
    - assert ((fun x : X * B * A => assoc (let '(x0, a) := x in (let '(x1, a0) := x0 in (y x1, a0), a))) =
                (fun x : X * B * A => let '(x0, a) := assoc x in (y x0, a)))
        by sauto lq: on use: functional_extensionality.
      econstructor. Unshelve.
      2: { constructor. }
      cbn. remember (ArrowSimilarCharTypEq _ _ _) as HA.
      unfold eq_rect. rewrite H.
      generalize (fun x : X * B * A => let '(x0, a) := assoc x in (y x0, a)).
      generalize HA. rewrite H. intros. rewrite (UIP_refl _ _ HA0). reflexivity.
    - (* TODO: Try this. *)
  Abort.

End ArrowsLaws.

(** TODO: I'm not interested in the following much, but worth proving
    eventually. *)

(*
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
*)
