Require Import Coq.Classes.Equivalence.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
From FreerArrows Require Import Classes.
From Hammer Require Import Hammer Tactics.

Open Scope type_scope.

Definition CounterT (I : Type -> Type -> Type)  :=
  fun x y => I (x * nat) (y * nat).

Instance Profunctor__CounterT {I} `{Profunctor I} : Profunctor (CounterT I) | 100 :=
  {| dimap := fun _ _ _ _ f g x => @dimap I _ _ _ _ _ (first f) (first g) x |}.

Instance StrongProfunctor__CounterT {I} `{HS: StrongProfunctor I} : StrongProfunctor (CounterT I) | 100 :=
  {| first := fun _ _ _ a => dimap (fun '(a, c, n) => (a, n, c)) (fun '(b, n, c) => (b, c, n)) (@first I _ _ _ _ _ a) |}.

Instance Category__CounterT {I} {HC : Category I} : Category (CounterT I) | 100 :=
  {| id := fun A => @id I HC (A * nat);
     comp := fun A B C x y => @comp I HC (A * nat) (B * nat) (C * nat) x y 
  |}.

Instance PreArrow__CounterT {I} {HC : Category I} {HP : PreArrow I} : PreArrow (CounterT I) | 100 :=
  {| arr := fun A B f => @arr I _ _ (A * nat) (B * nat) (first f) |}.

Instance ChoiceProfunctor__CounterT {I} `{HC: ChoiceProfunctor I} : ChoiceProfunctor (CounterT I) | 100.
constructor.
intros ? ? ? a. unfold CounterT in *.
refine (dimap _ _ (left a)).
- exact (fun '(x, n) => match x with
                     | inl a => inl (a, n)
                     | inr c => inr (c, n)
                     end).
- exact (fun x => match x with
               | inl b => match b with
                         | (b, n) => (inl b, n)
                         end
               | inr c => match c with
                         | (c, n) => (inr c, n)
                         end
               end).
Defined.

Definition tick {I X Y} `{Arrow I} (i : I X Y) : CounterT I X Y :=
  dimap (fun x => x) (fun '(y, n) => (y, S n)) (first i).

Section CounterTLaws.

    Variable I : Type -> Type -> Type.
    Variable eq : forall {A B}, I A B -> I A B -> Prop.
    Context `{forall A B, Equivalence (@eq A B)}.
  
    #[local] Notation "a ≈ b" := (eq a b) (at level 43).

    Definition eqC {A B} (x y : CounterT I A B) : Prop := eq x y.

    Hint Unfold eqC dimap Profunctor__CounterT : counterT.
    
    (** Profunctor laws. *)
    Context `{HP : Profunctor I} `{HL : @ProfunctorLaws I (@eq) HP}.
    
    Instance ProfunctorLawsCounterT : ProfunctorLaws (CounterT I) (@eqC).
    Proof.
      constructor.
      - (* dimap_distr *)
        intros. destruct HP, HL.
        autounfold with counterT in *. cbn.
        rewrite <- dimap_distr; cbn.
        assert ((fun '(a, c) => (f (g a), c)) =
                  (fun x0 : V * nat => let '(a, c) := let '(a, c) := x0 in (g a, c) in (f a, c))).
        { extensionality a. destruct a. reflexivity. }
        assert ((fun '(a, c) => (h (i a), c)) =
                  (fun x0 : B * nat => let '(a, c) := let '(a, c) := x0 in (i a, c) in (h a, c))).
        { extensionality a. destruct a. reflexivity. }
        rewrite <- H0, <- H1. reflexivity.
    Qed.

    (** Category laws. *)
    Context {HC : Category I} {HCL : @CategoryLaws I (@eq) HC}.

    Hint Unfold comp id Category__CounterT Category__Fun : counterT.
    
    Instance CategoryLawsCounterT : CategoryLaws (CounterT I) (@eqC).
    Proof.
      destruct HP, HC, HL, HCL.
      constructor; autounfold with counterT in *; sauto.
    Qed.

    (** Pre-Arrow laws. *)
    Context {HPre : @PreArrow I HC} {HPL: @PreArrowLaws I (@eq) HC HPre}.
    
    Hint Unfold arr PreArrow__CounterT : counterT.
    
    Instance PreArrowLaws__CounterT : PreArrowLaws (CounterT I) (@eqC).
    Proof.
      destruct HP, HC, HPre, HL, HCL, HPL.
      assert (Harr: forall A B x y, x = y -> arr A B x ≈ arr A B y).
      { intros. subst. reflexivity. }
      constructor; autounfold with counterT in *.
      - (* arr_id *)
        intros; cbn.
        assert ((fun '(a, c) => (a, c)) = (fun a : A * nat => a)).
        { extensionality a. fcrush. }
        sauto lq: on.
      - (* arr_distr *)
        intros; cbn. rewrite <- arr_distr.
        apply Harr. extensionality a. fcrush.
    Qed.


    (** Arrow Laws *)
    Context {Hstrong: @StrongProfunctor I HP} {HA: @Arrow I _ _ _ _}.
    Context {HR : @Rigidity I (@eq) _ _ _} {HAL: @ArrowLaws I (@eq) _ _ _ _}.

    Hint Unfold first StrongProfunctor__Fun StrongProfunctor__CounterT : counterT.

    Instance Rigidity__CounterT : Rigidity (CounterT I) (@eqC).
    Proof.
      destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
      constructor; autounfold with counterT in *. fcrush.
    Qed.

    Instance ArrowLaws__CounterT : ArrowLaws (CounterT I) (@eqC).
    Proof.
      destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
      assert (Harr: forall A B x y, x = y -> arr A B x ≈ arr A B y).
      { intros. subst. reflexivity. }
      assert (Hcomp: forall A B C x x' y y', x ≈ x' -> y ≈ y' -> comp A B C x y ≈ comp A B C x' y').
      { intros. rewrite H0, H1. reflexivity. }
      constructor; autounfold with counterT in *.
      - (* first_arr *)
        intros. rewrite !dimap_arr_comp, !first_arr, <- !arr_distr.
        apply Harr. extensionality a. sauto.
      - (* first_distr *)
        intros. rewrite !dimap_arr_comp, !first_distr.
        rewrite !comp_assoc.
        rewrite <- (comp_assoc (B * nat * D) (B * D * nat) _ (C * D * nat)), <- arr_distr.
        remember (fun a : B * nat * D => _) as func.
        assert (func = fun x => x).
        { extensionality a. sauto. }
        rewrite H0, !arr_id, !left_id. reflexivity.
      - (* first_fst *)
        intros. rewrite !dimap_arr_comp, !comp_assoc.
        rewrite <- !arr_distr.
        remember (fun a : B * nat * C => _) as func1.
        assert (func1 = fst).
        { extensionality a. sauto. }
        rewrite H0, first_fst, <- comp_assoc, <- arr_distr.
        remember (fun a : A * C * nat => _) as func2.
        assert (func2 = (fun '(a, c) => (fst a, c))).
        { extensionality a. fcrush. }
        rewrite H1. reflexivity.
      - (* first_and *)
        intros. rewrite !dimap_arr_comp, !comp_assoc.
        rewrite <- !arr_distr.
        remember (fun a : B * nat * X => _) as func1.
        assert (arr _ _ func1 ≈ comp _ _ _ (arr _ _ ((fun x => x) *** g)) (arr _ _ (fun '(b, n, y) => (b, y, n)))).
        { rewrite <- arr_distr. apply Harr.
          extensionality a. fcrush. }
        rewrite H0, <- (comp_assoc (A * nat * X) (B * nat * X) _ (B * Y * nat)), first_and.
        rewrite !comp_assoc, <- (comp_assoc (A * X * nat) (A * nat * X) _ (B * Y * nat)), <- arr_distr.
        rewrite ?comp_assoc, <- (comp_assoc (A * X * nat) (A * Y * nat) _ (B * Y * nat)), <- arr_distr.
        repeat (apply Hcomp; try reflexivity).
        apply Harr. extensionality a. fcrush.
      - (* first_first *)
        intros. rewrite !dimap_arr_comp, !comp_assoc, !first_distr, !first_arr.
        cbn. rewrite !comp_assoc, <- !arr_distr.
        remember (fun a : B * nat * Y * X => _) as func1.
        assert (arr _ _ func1 ≈ comp _ _ _ (arr _ _ assoc) (arr _ _ (fun '(b, n, (y, x)) => (b, (y, x), n)))).
        { rewrite <- arr_distr. apply Harr.
          extensionality a. fcrush. }
        rewrite H0, <- (comp_assoc (A * nat * Y * X) (B * nat * Y * X) _ (B * (Y * X) * nat)).
        rewrite first_first, !comp_assoc.
        rewrite <- (comp_assoc (A * Y * X * nat) (A * Y * nat * X) _ (B * (Y * X) * nat)), <- arr_distr.
        rewrite <- (comp_assoc (A * Y * X * nat) (A * (Y * X) * nat) _ (B * (Y * X) * nat)), <- arr_distr.
        rewrite <- (comp_assoc (A * Y * X * nat) (A * nat * Y * X) _ (B * (Y * X) * nat)), <- arr_distr.
        repeat (apply Hcomp; try reflexivity); apply Harr; extensionality a; fcrush.
      - (* first_proper *)
        intros. intros x1 x2 Heqx. rewrite !dimap_arr_comp. rewrite Heqx. reflexivity.
    Qed.
End CounterTLaws.
