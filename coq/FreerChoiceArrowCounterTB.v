Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.
Require Import Lia.
Require Import Coq.Arith.Arith.

From FreerArrows Require Import Common Tactics CounterTB FreerChoiceArrow Classes.
From Hammer Require Import Hammer Tactics.

Open Scope type_scope.

Fixpoint count {E X Y} (f : FreerChoiceArrow E X Y) : nat :=
  match f with
  | Hom _ => 0
  | Comp _ _ x => 1 + count x
end.

Section Interp.

  Context {I : Type -> Type -> Type}.
  Context `{Arrow I} {CP : ChoiceProfunctor I} {CA : ChoiceArrow I}.

  Fixpoint interp {E X Y} 
    (handler : forall {A B}, E A B -> I A B)
    (f : FreerChoiceArrow E X Y) : I X Y :=
    match f with
    | Hom f => arr f
    | Comp f e x =>
        comp (dimap f (fun x => x) (left (first (handler e)))) (interp (@handler) x)
    end.  

  Fixpoint interp' {E X Y}
    (handler : forall {A B}, E A B -> I A B)
    (f : FreerChoiceArrow E X Y) : CounterT I X Y :=
    match f with
    | Hom f => arr f
    | Comp f e x =>
        comp (dimap f (fun x => x) (left (first (tick (handler e))))) (interp' (@handler) x)
    end.

End Interp.

Section StaticallyCountable.

  Variable I : Type -> Type -> Type.
  Context `{SI: StrongProfunctor I} {CI: Category I} {PI: PreArrow I}.
  Context {AI : @Arrow I CI PI _ SI}.

  Variable eq : forall {A B}, I A B -> I A B -> Prop.
  Context `{forall A B, Equivalence (@eq A B)}.
  Context {HPL : ProfunctorLaws I (@eq)} {HCL : CategoryLaws I (@eq)} {HPAL : PreArrowLaws I (@eq)}.
  Context {HAL : ArrowLaws I (@eq)} {HR : Rigidity I (@eq)}.

  #[local] Notation "a ≊ b" := (eq a b) (at level 43).

  Context {CPI : ChoiceProfunctor I} {CAI: ChoiceArrow I}. 
  Context {HACL : ChoiceArrowLaws I (@eq)} {HCSL : ChoiceStrongLaws I (@eq)}.

  Theorem statically_approximateable' {E X W Y} : 
    forall (f : FreerChoiceArrow E (X + W) Y) (handler : forall {A B}, E A B -> I A B) n,
      @comp _ CI _ _ _  (interp (@handler) f) (arr (fun y => (y, true))) ≊
      dimap (fun x => match x with
                   | inl x => (inl x, S n)
                   | inr w => (inr w, n)
                   end) (fun '(x, m) => (x, m <=? (S n + count f)%nat)) (interp' (@handler) f).
  Proof.
    destruct H, SI, CI, PI, AI, CPI, CAI, HPL, HCL, HPAL, HAL, HR, HACL, HCSL. cbn in *.
    assert (Harr: forall A B x y, x = y -> arr A B x ≊ arr A B y).
    { intros. subst. reflexivity. }
    assert (Hcomp: forall A B C x x' y y', x ≊ x' -> y ≊ y' -> comp A B C x y ≊ comp A B C x' y').
    { intros. rewrite H1, H2. reflexivity. }
    fix SELF 1. destruct f; cbn in *.
    - intros. rewrite !dimap_arr_comp, <- !arr_distr.
      apply Harr. extensionality a. destruct a.
      + f_equal. symmetry. apply Reflect.Nat_ge_leb. lia.
      + f_equal. symmetry. apply Reflect.Nat_ge_leb. lia.
    - intros. rewrite !dimap_arr_comp, !comp_assoc.
      rewrite <- (comp_assoc (X + W) ((X + W) * nat) _ (Y * bool)), <- arr_distr.
      rewrite <- (comp_assoc (X + W) ((A * C + W0) * nat) _ (Y * bool)), <- arr_distr.
      rewrite !first_distr, !left_distr, !first_arr, !left_arr.
      rewrite !comp_assoc, <- (comp_assoc (X + W) (A * C * nat + W0 * nat) _ (Y * bool)), <- arr_distr.
      rewrite <- (comp_assoc (X + W) (A * nat * C + W0 * nat) _ (Y * bool)), <- arr_distr.
      remember (fun a : (X + W) => _) as func1.
      assert ((first (A * nat) (B * nat) C (first A B nat (handler A B e))) ≊
                comp _ _ _ (first (A * nat) (B * nat) C (first A B nat (handler A B e)))
                (comp _ _ _ (arr _ _ assoc) (arr _ _ unassoc))).
      { rewrite <- arr_distr. unfold assoc, unassoc.
        remember (fun a : B * nat * C => _) as func.
        assert (func = (fun x => x)).
        { extensionality a. fcrush. }
        rewrite H1, arr_id, right_id. reflexivity. }
      rewrite H1, <- (comp_assoc (A * nat * C) (B * nat * C) _ (B * nat * C)), first_first.
      rewrite !comp_assoc, !left_distr, !left_arr, !comp_assoc.
      rewrite <- (comp_assoc (X + W) (A * nat * C + W0 * nat) _ (Y * bool)), <- arr_distr.
      rewrite <- (comp_assoc (B * (nat * C) + W0 * nat) (B * nat * C + W0 * nat) _ (Y * bool)), <- arr_distr.
      rewrite <- (comp_assoc (B * (nat * C) + W0 * nat) (B * nat * C + W0 * nat) _ (Y * bool)), <- arr_distr.
      rewrite <- (comp_assoc (B * (nat * C) + W0 * nat) (B * C * nat + W0 * nat) _ (Y * bool)), <- arr_distr.
      rewrite <- (comp_assoc (B * (nat * C) + W0 * nat) ((B * C + W0) * nat) _ (Y * bool)), <- arr_distr.
      remember (fun a : B * (nat * C) + W0 * nat => _) as func2.
      assert (func2 = (fun x => match x with
                             | inl (b, (n, c)) => (inl (b, c), S n)
                             | inr (w, n) => (inr w, n)
                             end)).
      { extensionality a. fcrush. }
      rewrite H2. clear H2. clear Heqfunc2. clear func2.
      remember (fun x : B * (nat * C) + W0 * nat => _) as func2.
      rewrite Heqfunc1. clear Heqfunc1. clear func1.
      remember (fun a : X + W => _) as func1.
      assert (func1 = (fun x : X + W =>
                         match x with
                         | inl x => match s (inl x) with
                                   | inl (a, c) => inl (a, (S n, c))
                                   | inr w => inr (w, S n)
                                   end
                         | inr w => match s (inr w) with
                                   | inl (a, c) => inl (a, (n, c))
                                   | inr w => inr (w, n)
                                   end
                         end)).
      { extensionality a. sauto. }
      (* Unsure what to do. *)
  Abort.
      
  Theorem statically_approximateable {E X Y} : 
    forall (f : FreerChoiceArrow E X Y) (handler : forall {A B}, E A B -> I A B) n,
      @comp _ CI _ _ _  (interp (@handler) f) (arr (fun y => (y, true))) ≊
      dimap (fun x => (x, n)) (fun '(x, m) => (x, m <=? (S n + count f)%nat)) (interp' (@handler) f).
    destruct H, SI, CI, PI, AI, CPI, CAI, HPL, HCL, HPAL, HAL, HR, HACL, HCSL. cbn in *.
    assert (Harr: forall A B x y, x = y -> arr A B x ≊ arr A B y).
    { intros. subst. reflexivity. }
    assert (Hcomp: forall A B C x x' y y', x ≊ x' -> y ≊ y' -> comp A B C x y ≊ comp A B C x' y').
    { intros. rewrite H1, H2. reflexivity. }
    induction f; cbn in *.
    - intros. rewrite !dimap_arr_comp, <- !arr_distr.
      apply Harr. extensionality a. f_equal. symmetry.
      apply Reflect.Nat_ge_leb. lia.
    - intros. rewrite !dimap_arr_comp, !comp_assoc.
      rewrite <- (comp_assoc X (X * nat) _ (Y * bool)), <- arr_distr.
      rewrite <- (comp_assoc X ((A * C + W) * nat) _ (Y * bool)), <- arr_distr.
      rewrite !first_distr, !left_distr, !first_arr, !left_arr.
      rewrite !comp_assoc, <- (comp_assoc X (A * C * nat + W * nat) _ (Y * bool)), <- arr_distr.
      rewrite <- (comp_assoc X (A * nat * C + W * nat) _ (Y * bool)), <- arr_distr.
      remember (fun a : X => _) as func1.
      assert (arr _ _ func1 ≊ comp _ _ _ (arr _ _ s)
                (arr _ _ (fun s =>
                            match s with
                            | inl (a, c) => inl (a, n, c)
                            | inr w => inr (w, n)
                            end))).
      { rewrite <- arr_distr. apply Harr.
        extensionality a. sauto. }
      rewrite H1, !comp_assoc. apply Hcomp; [reflexivity |].
      assert ((first (A * nat) (B * nat) C (first A B nat (handler A B e))) ≊
                comp _ _ _ (first (A * nat) (B * nat) C (first A B nat (handler A B e)))
                (comp _ _ _ (arr _ _ assoc) (arr _ _ unassoc))).
      { rewrite <- arr_distr. unfold assoc, unassoc.
        remember (fun a : B * nat * C => _) as func.
        assert (func = (fun x => x)).
        { extensionality a. fcrush. }
        rewrite H2, arr_id, right_id. reflexivity. }
      rewrite H2, <- (comp_assoc (A * nat * C) (B * nat * C) _ (B * nat * C)), first_first.
      rewrite !comp_assoc, !left_distr, !left_arr, !comp_assoc.
      rewrite <- (comp_assoc (A * C + W) (A * nat * C + W * nat) _ (Y * bool)), <- arr_distr.
      clear H1. clear Heqfunc1. clear func1. clear H2.
      remember (fun a : A * C + W => _) as func1.
      repeat (rewrite <- (comp_assoc (B * (nat * C) + W * nat) (B * nat * C + W * nat) _ (Y * bool)), <- arr_distr).
      rewrite <- (comp_assoc (B * (nat * C) + W * nat) (B * C * nat + W * nat) _ (Y * bool)), <- arr_distr.
      rewrite <- (comp_assoc (B * (nat * C) + W * nat) ((B * C + W) * nat) _ (Y * bool)), <- arr_distr.
      remember (fun a : B * (nat * C) + W * nat => _) as func2.
      assert (func2 = (fun x => match x with
                             | inl (b, (n, c)) => (inl (b, c), S n)
                             | inr (w, n) => (inr w, n)
                             end)).
      { extensionality a. fcrush. }
      rewrite H1. clear H1. clear Heqfunc2. clear func2.
      remember (fun x : B * (nat * C) + W * nat => _) as func2.
      assert (func1 = @parAdd (fun A B => A -> B) (A * C) (A * (nat * C)) W (W * nat) _ _ _ _ _
                        (@parMul (fun A B => A -> B) _ _ _ _ _ _ _ _ _ (fun x : A => x) (fun c : C => (n, c)))
                        (fun w : W => (w, n))).
      { extensionality a. fcrush. }
      rewrite H1. cbn. rewrite <- (comp_assoc (A * C + W) (A * (nat * C) + W * nat) _ (Y * bool)), <- left_first.
      rewrite !comp_assoc. apply Hcomp; [reflexivity|].
      rewrite <- (comp_assoc (B * C + W) (B * (nat * C) + W * nat) _ (Y * bool)), <- arr_distr.
      rewrite arr_id, left_id.
      remember (fun a : B * C + W => _) as func3.
      assert (func3 = (fun a => match a with
                             | inl (b, c) => ((inl (b, c)), S n)
                             | inr w => (inr w, n)
                             end)).
      { extensionality a. fcrush. }
      rewrite H2. clear H2. clear Heqfunc3. clear func3. clear Heqfunc2. clear func2.
      clear H1. clear Heqfunc1. clear func1.
      specialize (IHf handler (S n)). rewrite !dimap_arr_comp in IHf.
      rewrite IHf. apply Hcomp.
      + apply Harr. extensionality x. subst. destruct x.
        * destruct p. cbn. reflexivity.
        * cbn. (* Stuck. *) 
  Abort.

End StaticallyCountable.

