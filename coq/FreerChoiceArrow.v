Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.

From FreerArrows Require Import Common Tactics.
From Hammer Require Import Hammer Tactics.

Open Scope type_scope.

Inductive FreerChoiceArrow (E : Type -> Type -> Type) (X Y : Type) : Type :=
| Hom : (X -> Y) -> FreerChoiceArrow E X Y
| Comp : forall {A B C W : Type},
    (X -> A * C + W) -> E A B -> FreerChoiceArrow E (B * C + W) Y -> FreerChoiceArrow E X Y.

Arguments Hom {E} {X} {Y}.
Arguments Comp {E} {X} {Y} {A} {B} {C} {W}.

Section Arrows.

  Context {E :Type -> Type -> Type}.

  Definition assoc {X Y Z} (p : (X * Y * Z)) : (X * (Y * Z)) :=
    match p with
    | (x, y, z) => (x, (y, z))
    end.

  Definition unassocsum {X Y Z W} (p : (X * (Y * Z)) + W * Z) : ((X * Y + W) * Z) :=
    match p with
    | inl (x, (y, z)) => (inl (x, y), z)
    | inr (w, a) => (inr w, a)                      
    end.

  Definition lmap {A X Y} (f : A -> X) (x : FreerChoiceArrow E X Y) : FreerChoiceArrow E A Y :=
    match x with
    | Hom h => Hom (fun x => h (f x))
    | Comp f' x y => Comp (fun x => f' (f x)) x y
    end.

  Fixpoint first' {X Y A} (x : FreerChoiceArrow E X Y) : FreerChoiceArrow E (X * A) (Y * A) :=
    match x with
    | Hom f => Hom (fun '(x, a) => (f x, a))
    | Comp f a b => Comp (fun '(x, a) =>
                             match f x with
                             | inl (x', b) => inl (x', (b, a))
                             | inr w => inr (w, a)
                             end)
                          a
                          (lmap unassocsum (first' b))
    end.

  Definition arr {X Y} : (X -> Y) -> FreerChoiceArrow E X Y := Hom.

  Definition first {X Y A} : FreerChoiceArrow E X Y -> FreerChoiceArrow E (X * A) (Y * A) := first'.

  Fixpoint left' {X Y A} (x : FreerChoiceArrow E X Y) : FreerChoiceArrow E (X + A) (Y + A) :=
    match x with
    | Hom f => Hom (fun x => match x with
                         | inl x => inl (f x)
                         | inr y => inr y
                         end)
    | Comp f a b => Comp (fun x => match x with
                              | inl x => match (f x) with
                                        | inl (x', z) => inl (x', z)
                                        | inr w => inr (inl w)
                                        end
                              | inr y => inr (inr y)
                              end)
                        a
                        (lmap (fun x => match x with
                                     | inl (y, z) => inl (inl (y, z))
                                     | inr (inl w) => inl (inr w)
                                     | inr (inr y) => inr y
                                     end)
                           (left' b))
    end.

  Definition left {X Y A} : FreerChoiceArrow E X Y -> FreerChoiceArrow E (X + A) (Y + A) := left'.

  (* This is (>>>) in Haskell. *)
  Fixpoint comp {X Y Z} (x : FreerChoiceArrow E X Y) (y : FreerChoiceArrow E Y Z) :
    FreerChoiceArrow E X Z :=
    match x with
    | Hom g => lmap g y
    | Comp f a b => Comp f a (comp b y)                                 
    end.

  Definition dimap {X Y A B}
    (f : A -> X) (g : Y -> B) (x : FreerChoiceArrow E X Y) : FreerChoiceArrow E A B :=
    match x with
    | Hom h => Hom (fun x => g (h (f x)))
    | Comp f' x y => Comp (fun x => f' (f x)) x
                            (comp y (arr g))
    end.

  Definition rmap {X Y B} : (Y -> B) -> FreerChoiceArrow E X Y -> FreerChoiceArrow E X B :=
    dimap id.

End Arrows.

Definition join {X Y A B C W}
  (f : X -> A * C + W) (g : B * C + W -> Y) (x : X) : A * (B -> Y) + Y :=
  match f x with 
  | inl (a, c) => inl (a, fun b => g (inl (b, c)))
  | inr w => inr (g (inr w))
  end.


Fixpoint CharacteristicType {E : Type -> Type -> Type} {X Y : Type}
                              (e : FreerChoiceArrow E X Y) : Type :=
  match e with
  | Hom _ => Y
  | @Comp _ _ _ A B C W f e y =>
      let Z := CharacteristicType y in
      A * (B -> Z) + Z
  end.

Fixpoint character {E : Type -> Type -> Type} {X Y : Type}  
  (e : FreerChoiceArrow E X Y) : X -> CharacteristicType e :=
  match e with
  | Hom f => f
  | Comp f _ y => join f (character y)
  end.

Lemma sameE_sameCharTyp : forall {E X Y A B C D Q W U}
                     (f : X -> A * C + W) (g : Q -> A * D + U)
                     (x : FreerChoiceArrow E (B * C + W) Y)
                     (y : FreerChoiceArrow E (B * D + U) Y)
                     (e : E A B),
    CharacteristicType x = CharacteristicType y ->
    CharacteristicType (Comp f e x) = CharacteristicType (Comp g e y).
Proof. sfirstorder. Qed.

Inductive ArrowSimilar {E X Y P} :
  FreerChoiceArrow E X Y -> FreerChoiceArrow E P Y -> Prop :=
| HomSimilar : forall f g, ArrowSimilar (Hom f) (Hom g)
| CompSimilar : forall A B C D W U x y
                  (f : X -> A * C + W) (g : P -> A * D + U) (e : E A B),
    ArrowSimilar x y ->
    ArrowSimilar (Comp f e x) (Comp g e y). 

(** This is important because Rocq cannot automatically figure out that two
    similar arrows actually have characteristic functions of the same type. *)
Theorem ArrowSimilarCharTypEq {E X Y P} :
  forall (x : FreerChoiceArrow E X Y) (y : FreerChoiceArrow E P Y),
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
    (x : FreerChoiceArrow E X R)
    (y : FreerChoiceArrow E Y R)
    (z : FreerChoiceArrow E Z R),
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

Variant ArrowEq {E X Y} : FreerChoiceArrow E X Y -> FreerChoiceArrow E X Y -> Prop :=
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
Theorem ArrowEqInd {E X Y A B C W}
  (f g : X -> (A * C) + W) (e : E A B) (x y : FreerChoiceArrow E ((B * C) + W) Y) :
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
Lemma eqImpliesArrowEq {E X Y} (x y : FreerChoiceArrow E X Y) :
    x = y -> x ≈ y.
Proof. intros ->; reflexivity. Qed.

Hint Resolve eqImpliesArrowEq : arrows.

Lemma lmap_Similar : forall {E A B C} (a : FreerChoiceArrow E A B) (f : C -> A),
    ArrowSimilar (lmap f a) a.
Proof.
  induction a; constructor. reflexivity.
Qed.

Lemma comp_lmap_Similar : forall {E A B C Y W} (a : FreerChoiceArrow E ((B * C) + W) Y),
    ArrowSimilar (comp (@first _ _ _ A a) (arr fst)) (lmap (@fst (B * C + W) A) a) ->
    ArrowSimilar (comp (lmap unassocsum (first' a)) (@arr _ (Y * A) _ fst)) a.
Proof.
  (* No need for induction *)
  intros. destruct a; [constructor |].
  cbn. constructor. 
  cbn in H. inversion H; subst. 
  inj_pair2_all. sfirstorder.
Qed.

Lemma lmap_fst_character : forall {E A B C} (a : FreerChoiceArrow E A B),
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
  
  Theorem comp_id_r : forall (x : FreerChoiceArrow E X Y),
      comp x (arr id) = x.
  Proof. induction x; sauto. Qed.

  Corollary comp_id_r' : forall (x : FreerChoiceArrow E X Y),
      comp x (arr id) ≈ x.
  Proof. sauto use: comp_id_r, eqImpliesArrowEq. Qed.

  Theorem arr_id : @arr E X X (fun x => x) = Hom (fun x => x).
  Proof. reflexivity. Qed.

  Theorem arr_comp (f : X -> Y) (g : Y -> Z): 
      @arr E _ _ (fun x => g (f x)) = comp (arr f) (arr g).
  Proof. reflexivity. Qed.

  Theorem first_arr (f : X -> Y) :
    @first E _ _ A (arr f) = arr (fun '(x, y) => (f x, y)).
  Proof. reflexivity. Qed.

  Theorem first_comp :
    forall (a : FreerChoiceArrow E X Y) (b : FreerChoiceArrow E Y Z),
    @first _ _ _ A (comp a b) = comp (@first _ _ _ A a) (first b).
  Proof.
    induction a; intros; cbn.
    - destruct b; cbn; f_equal; sauto use: functional_extensionality.
    - sauto lq: on.
  Qed.

  (* first a >>> arr fst = arr fst >>> a *)
  Theorem first_comp_arr :
    forall (a : FreerChoiceArrow E X Y),
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
      destruct a.
      + cbn. unfold eq_rect.
        remember (ArrowSimilarCharTypEq (Comp _ _ _) _ _) as Hs.
        cbn in Hs. rewrite (UIP_refl _ _ Hs).
        extensionality x. destruct x as [? ?]. unfold join. sauto.
      + revert H0. cbn in *. inversion H. inj_pair2_all.
        pose proof (ArrowSimilarCharTypEq _ _ H1) as Ht.
        remember (ArrowSimilarCharTypEq _ _ H) as Hpre.
        remember (ArrowSimilarCharTypEq _ _ (CompSimilar _ _ _ _ _ _ _ _ _ _ _ _)) as Hpost.
        cbn in Hpre, Hpost. generalize Hpre Hpost. unfold eq_rect.
        generalize (character (comp (lmap (@unassocsum B1 C0 A W0) (first' a)) (arr fst))).
        rewrite Ht. intros; revert H0.
        rewrite (UIP_refl _ _ Hpre0). rewrite (UIP_refl _ _ Hpost0).
        unfold join. cbn. intros.
        remember ((fun x : (B0 * C + W) * A =>
                     match (let '(x0, a) := x in match s0 x0 with
                                                 | inl (x', b) => inl (x', (b, a))
                                                 | inr w => inr (w, a)
                                                 end) with
                     | inl (a0, c0) => inl (a0, fun b : B1 => c (inl (b, c0)))
                     | inr w => inr (c (inr w))
                     end)) as func1.
        remember ((fun x : (B0 * C + W) * A =>
                     match s0 (fst x) with
                     | inl (a0, c) => inl (a0, fun b : B1 => character a (inl (b, c)))
                     | inr w => inr (character a (inr w))
                     end)) as func2.
        extensionality x. destruct x as [? ?]. cbn.
        destruct (s x) as [[? ?] | ?].
        * do 2 f_equal. extensionality b.
          assert (func1 (inl (b, c0), a0) = func2 (inl (b, c0), a0)).
          { rewrite H0. reflexivity. }
          rewrite Heqfunc1, Heqfunc2 in H2. apply H2.
        * f_equal.
          assert (func1 (inr w, a0) = func2 (inr w, a0)).
          { rewrite H0. reflexivity. }
          rewrite Heqfunc1, Heqfunc2 in H2. apply H2.
  Qed.

  Theorem first_assoc :
    forall (a : FreerChoiceArrow E X Y),
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
      2: { constructor. destruct a; cbn; [constructor |].
           constructor. inversion H. inj_pair2_all. assumption. }
      cbn. destruct a.
      + cbn. remember (ArrowSimilarCharTypEq (Comp _ _ _) _ _) as Hs.
        cbn in Hs. rewrite (UIP_refl _ _ Hs). cbn.
        extensionality x. destruct x as [[x b] a]. 
        unfold join. hauto.
      + revert H0. cbn in *. inversion H. inj_pair2_all.
        pose proof (ArrowSimilarCharTypEq _ _ H1) as Ht. 
        remember (ArrowSimilarCharTypEq _ _ H) as Hpre.
        remember (ArrowSimilarCharTypEq _ _ (CompSimilar _ _ _ _ _ _ _ _ _ _ _ _)) as Hpost.
        cbn in Hpre, Hpost. generalize Hpre Hpost. unfold eq_rect. cbn.
        generalize (character (comp (lmap (@unassocsum B1 (C0 * B) A (W0 * B))
                                       (first' (lmap unassocsum (first' a)))) (arr assoc))).
        rewrite Ht. intros. revert H0.
        rewrite (UIP_refl _ _ Hpre0). rewrite (UIP_refl _ _ Hpost0).
        unfold join. cbn. intros.
        remember (fun x : (B0 * C + W) * B * A =>
                    match
                      (let
                          '(x0, a) := x in
                        match
                          (let '(x1, a0) := x0 in match s0 x1 with
                                                  | inl (x', b) => inl (x', (b, a0))
                                                  | inr w => inr (w, a0)
                                                  end)
                        with
                        | inl (x', b) => inl (x', (b, a))
                        | inr w => inr (w, a)
                        end)
                    with
                    | inl (a0, c0) => inl (a0, fun b : B1 => c (inl (b, c0)))
                    | inr w => inr (c (inr w))
                    end) as func1.
        remember (fun x : (B0 * C + W) * B * A =>
                    match
                      (let '(x0, a) := assoc x in match s0 x0 with
                                                  | inl (x', b) => inl (x', (b, a))
                                                  | inr w => inr (w, a)
                                                  end)
                    with
                    | inl (a0, c) => inl (a0, fun b : B1 => character (lmap unassocsum (first' a)) (inl (b, c)))
                    | inr w => inr (character (lmap unassocsum (first' a)) (inr w))
                    end) as func2.
        extensionality x.
        destruct x as [[? ?] ?]. cbn.
        destruct (s x) as [[? ?] | ?].
        * do 2 f_equal. extensionality b0. cbn.
          assert (func1 (inl (b0, c0), b, a0) = func2 (inl (b0, c0), b, a0)).
          { rewrite H0. reflexivity. }
          rewrite Heqfunc1, Heqfunc2 in H2. apply H2.
        * f_equal. cbn.
          assert (func1 (inr w, b, a0) = func2 (inr w, b, a0)).
          { rewrite H0. reflexivity. }
          rewrite Heqfunc1, Heqfunc2 in H2. apply H2.
  Qed.
End ArrowsLaws.

Section ProfunctorLaws.

  Context {E :Type -> Type -> Type}.
  Context {X Y A B: Type}.

  (* Profunctor laws. *)

  Theorem dimap_id : forall (x : FreerChoiceArrow E X Y),
      dimap id id x = x.
  Proof. induction x; sauto use:comp_id_r. Qed.

  Theorem dimap_dimap : forall A' B' (x : FreerChoiceArrow E X Y)
                          (f : A -> X) (g : A' -> A) (h : B -> B') (i : Y -> B),
      dimap (fun x => f (g x)) (fun x => h (i x)) x = dimap g h (dimap f i x).
  Proof.
    intros until x. revert A B A' B'.
    induction x; [sauto|].
    intros. cbn. 
    destruct x; [sfirstorder |].
    cbn in IHx. cbn. do 2 f_equal.
    specialize (IHx _ _ _ _ id id h i). 
    inversion IHx. inj_pair2_all. assumption.
  Qed.

  Theorem lmap_dimap : forall (f : A -> X) (x : FreerChoiceArrow E X Y),
      lmap f x = dimap f id x.
  Proof.
    induction x; cbn; [reflexivity |].
    sauto use: @comp_id_r unfold: arr.
  Qed.

End ProfunctorLaws.

#[export]
Hint Resolve dimap_id : freer_arrow.

(*
#[export]
Hint Resolve dimap_dimap : freer_arrow. 
*)

Section MoreProfunctorLaws.

  Context {E :Type -> Type -> Type}.
  Context {X Y Z A B: Type}.
  
  Theorem lmap_lmap :  forall A' (x : FreerChoiceArrow E X Y) (f : A -> X) (g : A' -> A),
      lmap (fun x => f (g x)) x = lmap g (lmap f x).
  Proof.
    intros. rewrite !lmap_dimap.
    apply dimap_dimap.
  Qed.

  Theorem rmap_rmap :  forall B' (x : FreerChoiceArrow E X Y) (h : B -> B') (i : Y -> B),
      rmap (fun x => h (i x)) x = rmap h (rmap i x).
  Proof.
    intros. unfold rmap.
    apply dimap_dimap.
  Qed.

End MoreProfunctorLaws.

Section ChoiceLaws.

    Context {E :Type -> Type -> Type}.
    Context {X Y Z A B: Type}.
  
    Theorem left_arr : forall (f : X -> Y),
        @left' E _ _ A (arr f) = arr (fun x => match x with
                                   | inl a => inl (f a)
                                   | inr b => inr b
                                   end).
    Proof. intros. reflexivity. Qed.

    Theorem left_comp : forall (f : FreerChoiceArrow E X Y) (g : FreerChoiceArrow E Y Z),
      @left _ _ _ A (comp f g) = comp (left f) (left g).
    Proof.
      revert Z A. induction f; intros; cbn.
      - destruct g; cbn; f_equal;
          sauto lq: on drew: off use: functional_extensionality.
      - sauto lq: on.
    Qed.

    Theorem left_comp_arr : forall (f : FreerChoiceArrow E X Y),
      comp f (arr inl) ≈ comp (arr inl) (@left _ _ _ A f).
    Proof.
      revert A. induction f; cbn; [reflexivity |].
      inversion IHf; inj_pair2_all.
      econstructor. Unshelve.
      2: { constructor. destruct f; cbn; [constructor|].
           constructor. inversion H; inj_pair2_all. assumption. }
      destruct f; cbn.
      - unfold eq_rect.
        remember (ArrowSimilarCharTypEq (Comp _ _ _) _ _) as Hs.
        cbn in Hs. rewrite (UIP_refl _ _ Hs). unfold join.
        extensionality x'. sauto.
      - revert H0. cbn in *. inversion H; inj_pair2_all.
        pose proof (ArrowSimilarCharTypEq _ _ H3) as Ht.
        remember (ArrowSimilarCharTypEq _ _ H) as Hpre.
        remember (ArrowSimilarCharTypEq _ _ (CompSimilar _ _ _ _ _ _ _ _ _ _ _ _)) as Hpost.
        cbn in Hpre, Hpost. generalize Hpre Hpost. unfold eq_rect.
        generalize (character (comp f (arr (@inl Y A)))).
        rewrite Ht. intros; revert H0.
        rewrite (UIP_refl _ _ Hpre0). rewrite (UIP_refl _ _ Hpost0).
        unfold join. cbn. intros.
        remember (fun x : B0 * C + W =>
                     match s0 x with
                     | inl (a, c0) => inl (a, fun b : B1 => c (inl (b, c0)))
                     | inr w => inr (c (inr w))
                     end) as func1.
        remember (fun x : B0 * C + W =>
                    match match s0 x with
                          | inl (x', z) => inl (x', z)
                          | inr w => inr (inl w)
                          end with
                    | inl (a, c) =>
                        inl
                          (a,
                            fun b : B1 =>
                              character
                                (lmap
                                   (fun x0 : B1 * C0 + (W0 + A) =>
                                      match x0 with
                                      | inl (y, z) => inl (inl (y, z))
                                      | inr (inl w) => inl (inr w)
                                      | inr (inr y) => inr y
                                      end) (left' f)) (inl (b, c)))
                    | inr w =>
                        inr
                          (character
                             (lmap
                                (fun x0 : B1 * C0 + (W0 + A) =>
                                   match x0 with
                                   | inl (y, z) => inl (inl (y, z))
                                   | inr (inl w0) => inl (inr w0)
                                   | inr (inr y) => inr y
                                   end) (left' f)) (inr w))
                    end) as func2.
        extensionality x'. destruct (s x').
        + destruct p. do 2 f_equal. extensionality b'.
          assert (func1 (inl (b', c0)) = func2 (inl (b', c0))).
          { rewrite H0. reflexivity. }
          rewrite Heqfunc1, Heqfunc2 in H1. assumption.
        + f_equal.
          assert (func1 (inr w) = func2 (inr w)).
          { rewrite H0. reflexivity. }
          rewrite Heqfunc1, Heqfunc2 in H1. assumption.
    Qed.

    Definition assocsum {X Y Z} (x : (X + Y + Z)) : X + (Y + Z) :=
      match x with
      | (inl (inl x)) => inl x
      | (inl (inr y)) => inr (inl y)
      | (inr z) => inr (inr z)
      end.

  Theorem left_assocsum :
    forall (a : FreerChoiceArrow E X Y),
      comp (@left _ _ _ A (@left _ _ _ B a)) (arr assocsum) ≈ comp (arr assocsum) (left a).
  Proof.
    induction a; cbn. 
    - assert ((fun x : X + B + A =>
             assocsum
               match x with
               | inl x0 => inl match x0 with
                               | inl x1 => inl (y x1)
                               | inr y => inr y
                               end
               | inr y => inr y
               end) = (fun x : X + B + A => match assocsum x with
                                         | inl x0 => inl (y x0)
                                         | inr y0 => inr y0
                                         end)) by
      sauto lq: on use: functional_extensionality.
      econstructor. Unshelve.
      2: { constructor. }
      cbn. remember (ArrowSimilarCharTypEq _ _ _) as HA.
      unfold eq_rect. generalize HA. rewrite H.
      intros HA0. rewrite (UIP_refl _ _ HA0). reflexivity.
    - cbn in IHa. inversion IHa; subst.
      econstructor. Unshelve.
      2: { constructor. destruct a; cbn; constructor.
           inversion H; inj_pair2_all. assumption. }
      cbn. destruct a; cbn.
      + remember (ArrowSimilarCharTypEq (Comp _ _ _) _ _) as Hs.
        cbn in Hs. rewrite (UIP_refl _ _ Hs). cbn.
        extensionality x. unfold join. sauto.
      + revert H0. cbn in *. inversion H. inj_pair2_all.
        pose proof (ArrowSimilarCharTypEq _ _ H1) as Ht. 
        remember (ArrowSimilarCharTypEq _ _ H) as Hpre.
        remember (ArrowSimilarCharTypEq _ _ (CompSimilar _ _ _ _ _ _ _ _ _ _ _ _)) as Hpost.
        cbn in Hpre, Hpost. generalize Hpre Hpost. unfold eq_rect. cbn.
        generalize (character
           (comp
              (lmap
                 (fun x : B1 * C0 + (W0 + B + A) =>
                  match x with
                  | inl (y, z) => inl (inl (y, z))
                  | inr (inl w) => inl (inr w)
                  | inr (inr y) => inr y
                  end)
                 (left'
                    (lmap
                       (fun x : B1 * C0 + (W0 + B) =>
                        match x with
                        | inl (y, z) => inl (inl (y, z))
                        | inr (inl w) => inl (inr w)
                        | inr (inr y) => inr y
                        end) (left' a)))) (arr assocsum))).
        rewrite Ht. intros. revert H0.
        rewrite (UIP_refl _ _ Hpre0). rewrite (UIP_refl _ _ Hpost0).
        unfold join. cbn. intros.
        remember (fun x : B0 * C + W + B + A =>
                    match
                      match x with
                      | inl x0 =>
                          match
                            match x0 with
                            | inl x1 => match s0 x1 with
                                       | inl (x', z) => inl (x', z)
                                       | inr w => inr (inl w)
                                       end
                            | inr y => inr (inr y)
                            end
                          with
                          | inl (x', z) => inl (x', z)
                          | inr w => inr (inl w)
                          end
                      | inr y => inr (inr y)
                      end
                    with
                    | inl (a0, c0) => inl (a0, fun b : B1 => c (inl (b, c0)))
                    | inr w => inr (c (inr w))
                    end) as func1.
        remember (fun x : B0 * C + W + B + A =>
                    match
                      match assocsum x with
                      | inl x0 => match s0 x0 with
                                 | inl (x', z) => inl (x', z)
                                 | inr w => inr (inl w)
                                 end
                      | inr y => inr (inr y)
                      end
                    with
                    | inl (a0, c) =>
                        inl
                          (a0,
                            fun b : B1 =>
                              character
                                (lmap
                                   (fun x0 : B1 * C0 + (W0 + (B + A)) =>
                                      match x0 with
                                      | inl (y, z) => inl (inl (y, z))
                                      | inr (inl w) => inl (inr w)
                                      | inr (inr y) => inr y
                                      end) (left' a)) (inl (b, c)))
                    | inr w =>
                        inr
                          (character
                             (lmap
                                (fun x0 : B1 * C0 + (W0 + (B + A)) =>
                                   match x0 with
                                   | inl (y, z) => inl (inl (y, z))
                                   | inr (inl w0) => inl (inr w0)
                                   | inr (inr y) => inr y
                                   end) (left' a)) (inr w))
                    end) as func2.
        extensionality x. destruct x as [[? | ?] | ?]; cbn.
        * destruct (s x).
          -- destruct p. repeat f_equal.
             extensionality b.
             assert (func1 (inl (inl (inl (b, c0)))) = func2 (inl (inl (inl (b, c0))))).
             { rewrite H0. reflexivity. }
             rewrite Heqfunc1, Heqfunc2 in H2. apply H2.
          -- assert (func1 (inl (inl (inr w))) = func2 (inl (inl (inr w)))).
             { rewrite H0. reflexivity. }
             rewrite Heqfunc1, Heqfunc2 in H2. f_equal. apply H2.
        * assert (func1 (inl (inr b)) = func2 (inl (inr b))).
          { rewrite H0. reflexivity. }
          rewrite Heqfunc1, Heqfunc2 in H2. f_equal. apply H2.
        * assert (func1 (inr a0) = func2 (inr a0)).
          { rewrite H0. reflexivity. }
          rewrite Heqfunc1, Heqfunc2 in H2. f_equal. apply H2.
  Qed.
          
End ChoiceLaws.
