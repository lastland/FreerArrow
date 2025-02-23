Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.

From Hammer Require Import Tactics Hammer.

Open Scope type_scope.

Ltac inj_pair2_all :=
  repeat (match goal with
          | H: existT _ _ _ = existT _ _ _ |- _ =>
              apply inj_pair2 in H
          end; subst).

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

Definition join {X Y A B C}
  (f : X -> A * C) (g : B * C -> Y) (x : X) : A * (B -> Y) :=
  let '(a, c) := f x in (a, fun b => g (b, c)).


Fixpoint CharacteristicType {E : Type -> Type -> Type} {X Y : Type}
                              (e : FreerArrow E X Y) : Type :=
  match e with
  | Hom _ => Y
  | @Comp _ _ _ A B C f e y => A * (B -> CharacteristicType y)
  end.

Fixpoint character {E : Type -> Type -> Type} {X Y : Type}  
  (e : FreerArrow E X Y) : X -> CharacteristicType e :=
  match e with
  | Hom f => f
  | Comp f _ y => join f (character y)
  end.

Lemma sameE_sameCharTyp : forall {E X Y A B C D Q}
                     (f : X -> A * C) (g : Q -> A * D)
                     (x : FreerArrow E (B * C) Y)
                     (y : FreerArrow E (B * D) Y)
                     (e : E A B),
    CharacteristicType x = CharacteristicType y ->
    CharacteristicType (Comp f e x) = CharacteristicType (Comp g e y).
Proof. sfirstorder. Qed.

Inductive ArrowSimilar {E X Y P} :
  FreerArrow E X Y -> FreerArrow E P Y -> Prop :=
| HomSimilar : forall f g, ArrowSimilar (Hom f) (Hom g)
| CompSimilar : forall A B C D x y
                  (f : X -> A * C) (g : P -> A * D) (e : E A B),
    ArrowSimilar x y ->
    ArrowSimilar (Comp f e x) (Comp g e y). 

(** This is important because Rocq cannot automatically figure out that two
    similar arrows actually have characteristic functions of the same type. *)
Theorem ArrowSimilarCharTypEq {E X Y P} :
  forall (x : FreerArrow E X Y) (y : FreerArrow E P Y),
    ArrowSimilar x y ->
    CharacteristicType x = CharacteristicType y.
Proof.
  intros x. generalize dependent P. induction x.
  - sauto lq: on.
  - intros. inversion H; subst.
    inversion H; subst.
    inj_pair2_all.
    sfirstorder.
Qed.

(** This is more general than the normal transitivity because it is
    heterogeneous. *)
Lemma Trans__ArrowSimilar :
  forall {E X Y Z R}
    (x : FreerArrow E X R)
    (y : FreerArrow E Y R)
    (z : FreerArrow E Z R),
  ArrowSimilar x y -> ArrowSimilar y z -> ArrowSimilar x z.
Proof.
  intros E X Y Z R x y z H. generalize dependent Z.
  induction H.
  - sauto lq: on.
  - intros. inversion H0; subst.
    inj_pair2_all.
    sauto lq: on.
Qed.    

Instance Equivalence__ArrowSimilar {E X Y} :
  Equivalence (@ArrowSimilar E X Y X).
Proof.
  constructor.
  - intros x. induction x; sauto lq: on.
  - intros x y. induction 1; subst; sauto lq: on.
  - intros x y z. apply Trans__ArrowSimilar.
Qed.

Reserved Notation "x ≈ y" (at level 42).

(*
ArrowSimilar x y ->
character x = character y ->
x ≈ y
*)

Variant ArrowEq {E X Y} : FreerArrow E X Y -> FreerArrow E X Y -> Prop :=
| ArrowEqSimilar : forall x y (H : ArrowSimilar x y),
    (** This is essentially [character x = character y]. I need this stated in
    this awkward way to convince Rocq that [character x] and [character y] share
    the same type, so I can use equality on them. *)
    (let H0 := ArrowSimilarCharTypEq x y H in
     let cx := eq_rect _ (fun T : Type => X -> T) (character x) _ H0 in
     cx = character y) ->
    x ≈ y
where "x ≈ y" := (ArrowEq x y).

(** The definition of [ArrowEq] is not exactly structural, because very often
    there are different types. But when we do have the same type, we can use
    this simpler way to establish [ArrowEq]. *)
Theorem ArrowEqInd {E X Y A B C}
  (f g : X -> (A * C)) (e : E A B) (x y : FreerArrow E (B * C) Y) :
  x ≈ y -> f = g -> Comp f e x ≈ Comp g e y.
Proof.
  inversion 1. intros Hfunc; subst.
  eapply ArrowEqSimilar.
  Unshelve. 2: { constructor. assumption. }
  cbn. rewrite <- H1.
  (** Some Rocq engineering stuff so that I can use [UIP_refl] on two
      "different" terms. This is a common pattern that you will see being used
      across this file. *)
  remember (ArrowSimilarCharTypEq (Comp _ _ _) _ _) as HC1.
  remember (ArrowSimilarCharTypEq x y _) as HC2.
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
    remember (ArrowSimilarCharTypEq x y _) as Hxy.
    remember (ArrowSimilarCharTypEq y z _) as Hyz.
    remember (ArrowSimilarCharTypEq x z _) as Hxz.
    revert H1 H4. unfold eq_rect.
    generalize (character x) (character y). generalize Hxz.
    rewrite Hxy. rewrite Hyz. intros; subst.
    rewrite (UIP_refl _ _ Hxz0). reflexivity.
Qed.

(** I can prove most arrow laws using definitional equality, so I don't bother
    with [ArrowEq] directly. Instead, I use this to show definitional equality
    implies [ArrowEq]. The proof is very simple since [ArrowEq] is reflexive
    (shown above). *)
Lemma eqImpliesArrowEq {E X Y} (x y : FreerArrow E X Y) :
    x = y -> x ≈ y.
Proof. intros ->; reflexivity. Qed.

Hint Resolve eqImpliesArrowEq : arrows.

Lemma lmap_Similar : forall {E A B C} (a : FreerArrow E A B) (f : C -> A),
    ArrowSimilar (lmap f a) a.
Proof.
  induction a; constructor. reflexivity.
Qed.

Lemma comp_lmap_Similar : forall {E A B C Y} (a : FreerArrow E (B * C) Y),
    ArrowSimilar (comp (@first _ _ _ A a) (arr fst)) (lmap (@fst (B * C) A) a) ->
    ArrowSimilar (comp (lmap unassoc (first' a)) (@arr _ (Y * A) _ fst)) a.
Proof.
  (* No need for induction *)
  intros. destruct a; [constructor |].
  cbn. constructor. 
  cbn in H. inversion H; subst. 
  inj_pair2_all. 
  subst. apply H1.
Qed.

Lemma comp_lmap_character : forall {E A B C Y} (a : FreerArrow E (B * C) Y)
                              (Hsim: ArrowSimilar (comp (@first _ _ _ A a) (arr fst)) (lmap (@fst (B * C) A) a)),
    let Hpre := ArrowSimilarCharTypEq _ _ Hsim in
    let cpre := eq_rect _ (fun T => B * C * A -> T) (character (comp (@first _ _ _ A a) (arr fst))) _ Hpre in 
    cpre = character (lmap (@fst (B * C) A) a) ->
    let Hpost := ArrowSimilarCharTypEq _ _ (comp_lmap_Similar _ Hsim) in
    let cpost := eq_rect _ (fun T => (B * (C * A)) -> T)
                   (character (comp (lmap unassoc (first' a)) (@arr _ (Y * A) _ fst))) _ Hpost in 
    cpost = (fun '(x, (y, _)) => character a (x, y)).
Proof.
  intros. destruct a.
  - cbn in *. unfold cpost.
    rewrite (UIP_refl _ _ Hpost). cbn.
    intros. extensionality x. destruct x as [b [c a]]. reflexivity.
  - cbn in *. revert H. unfold cpre, cpost, join.
    inversion Hsim; inj_pair2_all.
    pose proof (ArrowSimilarCharTypEq _ _ H0).
    generalize Hpre Hpost.
    generalize (character (comp (lmap (@unassoc B0 C0 A) (first' a)) (arr fst))).
    rewrite H. intros. revert H1.
    rewrite (UIP_refl _ _ Hpre0). rewrite (UIP_refl _ _ Hpost0). cbn.
    intros.
    extensionality x. destruct x as [? [? ?]]. cbn. 
    remember (fun x : B * C * A =>
        let '(a0, c0) := let '(x0, a) := x in let (x', b) := p x0 in (x', (b, a)) in (a0, fun b : B0 => c (b, c0))) as func1.
    remember ((fun x : B * C * A => let '(a0, c) := p (fst x) in (a0, fun b : B0 => character a (b, c)))) as func2.
    assert (func1 (b, c0, a0) = func2 (b, c0, a0)) by (rewrite H1; reflexivity).
    sfirstorder.
Qed.

Lemma lmap_fst_character : forall {E A B C} (a : FreerArrow E A B),
    let H := ArrowSimilarCharTypEq (@lmap _ (A * C) A B fst a) a (lmap_Similar a fst) in
    let ca := eq_rect _ (fun T => (A * C) -> T) (character (@lmap _ (A * C) A B fst a)) _ H in
    ca = (fun '(x, _) => (character a) x).
Proof.
  (* Induction is probably not necessary here, but it's simple. *)
  induction a; cbn; unfold eq_rect.
  - remember (ArrowSimilarCharTypEq _ _ _) as Hs.
    cbn in Hs. rewrite (UIP_refl _ _ Hs).
    extensionality x. destruct x as [x c].
    reflexivity.
  - remember (ArrowSimilarCharTypEq (Comp _ _ _) _ _) as Hs.
    cbn in Hs. rewrite (UIP_refl _ _ Hs).
    extensionality x. destruct x as [x c].
    reflexivity.
Qed.    
  
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

  (* first a >>> arr fst = arr fst >>> a *)
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
      cbn. unfold join.
      pose proof (comp_lmap_character a H) as Htarget.
      cbn in *. revert H0 Htarget.
      remember (ArrowSimilarCharTypEq _ _ H) as H1.
      remember (ArrowSimilarCharTypEq _ _ (comp_lmap_Similar _ _)) as H2.
      remember (ArrowSimilarCharTypEq (Comp _ _ _) _ _) as H3.
      unfold eq_rect. generalize H1 H2 H3.
      generalize (character (comp (@first _ (B0 * C) Y A a) (arr fst))).
      generalize (character (comp (lmap (@unassoc B0 C A) (first' a)) (arr fst))).
      rewrite H1. cbn. rewrite H2. intros. revert Htarget. revert H6.
      rewrite (UIP_refl _ _ H0). rewrite (UIP_refl _ _ H4). rewrite (UIP_refl _ _ H5).
      intros. extensionality x. sauto.
  Qed.

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
    - cbn in IHa. inversion IHa; subst.
      econstructor. Unshelve.
      2: { constructor. admit. (* This won't be pleasant. *) }
      (* TODO: finish this proof. *)
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
