Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.
Require Import Lia.

From FreerArrows Require Import Common Tactics CounterTB FreerArrow Classes.
From Hammer Require Import Hammer Tactics.

Open Scope type_scope.

Fixpoint count {E X Y} (f : FreerArrow E X Y) : nat :=
  match f with
  | Hom _ => 0
  | Comp _ _ x => 1 + count x
end.

Fixpoint interp {E X Y I} `{Arrow I}
                (handler : forall {A B}, E A B -> I A B)
                (f : FreerArrow E X Y) : I X Y :=
    match f with
    | Hom f => arr f
    | Comp f e x =>
        comp (dimap f (fun x => x) (first (handler e))) (interp (@handler) x)
    end.

Fixpoint interp' {E X Y I} `{Arrow I}
                (handler : forall {A B}, E A B -> I A B)
                (f : FreerArrow E X Y) : CounterT I X Y :=
    match f with
    | Hom f => arr f
    | Comp f e x =>
        comp (dimap f (fun x => x) (first (tick (handler e)))) (interp' (@handler) x)
    end.

Section StaticallyCountable.

  Variable I : Type -> Type -> Type.
  Context `{SI: StrongProfunctor I} {CI: Category I} {PI: PreArrow I}.
  Context {AI : @Arrow I CI PI _ SI}.

  Variable eq : forall {A B}, I A B -> I A B -> Prop.
  Context `{forall A B, Equivalence (@eq A B)}.
  Context {HPL : ProfunctorLaws I (@eq)} {HCL : CategoryLaws I (@eq)} {HPAL : PreArrowLaws I (@eq)}.
  Context {HAL : ArrowLaws I (@eq)} {HR : Rigidity I (@eq)}.

  #[local] Notation "a ≊ b" := (eq a b) (at level 43).

  Theorem statically_countable {E X Y} : 
    forall (f : FreerArrow E X Y) (handler : forall {A B}, E A B -> I A B) n,
      @comp _ CI _ _ _  (interp (@handler) f) (arr (fun y => (y, (n + count f)%nat))) ≊
        dimap (fun x => (x, n)) (fun x => x) (interp' (@handler) f). 
  Proof.
    destruct H, SI, CI, PI, AI, HPL, HCL, HPAL, HAL, HR. cbn in *.
    assert (Harr: forall A B x y, x = y -> arr A B x ≊ arr A B y).
    { intros. subst. reflexivity. }
    assert (Hcomp: forall A B C x x' y y', x ≊ x' -> y ≊ y' -> comp A B C x y ≊ comp A B C x' y').
    { intros. rewrite H1, H2. reflexivity. }
    induction f; cbn in *.
    - intros. rewrite !dimap_arr_comp, <- !arr_distr.
      apply Harr. extensionality a. f_equal. lia.
    - intros. specialize (IHf (@handler)). unfold tick.
      rewrite !dimap_arr_comp, !comp_assoc.
      rewrite <- (comp_assoc X (X * nat) _ (Y * nat)), <- arr_distr.
      rewrite <- (comp_assoc X (A * C * nat) _ (Y * nat)), <- arr_distr.
      rewrite !first_distr, !first_arr, !comp_assoc.
      rewrite <- (comp_assoc X (A * nat * C) _ (Y * nat)), <- arr_distr.
      rewrite <- (comp_assoc (B * nat * C) (B * nat * C) _ (Y * nat)), <- arr_distr.
      rewrite <- (comp_assoc (B * nat * C) (B * C * nat) _ (Y * nat)), <- arr_distr.
      specialize (IHf (S n)). rewrite dimap_arr_comp in IHf.
      remember (fun a : B * nat * C => _) as func1.
      assert (arr _ _ func1 ≊ comp _ _ _ (arr _ _ assoc) (arr _ _ (fun '(b, (n, c)) => func1 (b, n, c)))).
      { rewrite <- arr_distr. apply Harr. extensionality a. fcrush. }
      rewrite H1. rewrite !comp_assoc,  <- (comp_assoc (A * nat * C) (B * nat * C) _ (Y * nat)).
      rewrite first_first, !comp_assoc, <- (comp_assoc X (A * nat * C) _ (Y * nat)), <- arr_distr.
      remember (fun a : X => _) as func2.
      assert (arr _ _ func2 ≊ comp _ _ _ (arr _ _ p) (arr _ _ ((fun x : A => x) *** (fun c : C => (n, c))))).
      { rewrite <- arr_distr. apply Harr. extensionality a. sauto. }
      rewrite H2, !comp_assoc, <- (comp_assoc (A * C) (A * (nat * C)) _ (Y * nat)).
      cbn. rewrite <- first_and, !comp_assoc.
      repeat (apply Hcomp; [reflexivity| ]).
      rewrite <- (comp_assoc (B * C) (B * (nat * C)) _ (Y * nat)), <- arr_distr.
      assert ((S n + count f)%nat = (n + S (count f))%nat).
      { lia. }
      rewrite <- H3, IHf, <- (comp_assoc (B * C) (B * C) _ (Y * nat)), <- arr_distr.
      apply Hcomp; [| reflexivity].
      apply Harr. extensionality a. fcrush.
  Qed.

End StaticallyCountable.
