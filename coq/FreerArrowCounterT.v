(** This approach is abandoned in favor of [FreerArrowCounterTB.v]. Please refer
    to that file. *)

Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.

From FreerArrows Require Import Common Tactics CounterT FreerArrow Classes.
From Hammer Require Import Tactics.

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
    forall (f : FreerArrow E X Y) (handler : forall {A B}, E A B -> I A B),
      @comp _ CI _ _ _  (interp (@handler) f) (arr (fun y => (y, count f))) ≊
        interp' (@handler) f. 
  Proof.
  induction f; cbn; [sfirstorder |].
  destruct H, SI, CI, PI, AI, HPL, HCL, HPAL, HAL, HR.
  intros. specialize (IHf (@handler)). unfold tick.
  rewrite !dimap_arr_comp, !arr_id, !left_id.
  rewrite first_distr, first_arr, !comp_assoc, !left_id.
  rewrite <- IHf, !first_distr, !first_arr, !comp_assoc. cbn.
  rewrite <- !arr_distr.
  rewrite <- (comp_assoc (B * C) (B * nat * C) _ (Y * nat)), <- arr_distr; cbn.
  rewrite <- (comp_assoc (B * C) (B * C * nat) _ (Y * nat)), <- arr_distr; cbn.
  remember (fun a : B * C => _) as func1.
  assert (arr _ _ func1 ≊ comp (B * C) (B * C * unit) (B * C * nat) (arr (B * C) (B * C * unit) (fun x => (x, tt))) (arr (B * C * unit) (B * C * nat) (@parMul (fun A B => A -> B) (B * C) (B * C) unit nat _ _ _ _ _ (fun x : B * C => x) (fun _ => 1)))).
  { rewrite <- arr_distr. cbn.
    assert (func1 = (fun a : B * C => (a, 1))).
    { extensionality a. subst. destruct a. reflexivity.  }
    rewrite <- H1. reflexivity. }
  rewrite H1, !comp_assoc. unfold ">>>".
  rewrite <- (comp_assoc (B * C * unit) (B * C * nat) _ (Y * nat)), <- first_and.
  rewrite !comp_assoc, <- arr_distr. cbn.
  remember (fun a : Y * unit => _) as func2.
  assert (func2 = fun '(y, _) => (y, S (count f))).
  { extensionality a. subst. destruct a. cbn. reflexivity. }
  rewrite H2.
  assert (arr _ _  (fun '(y, _) => (y, S (count f))) ≊ comp _ _ _ (arr _ _ (@fst Y unit)) (arr _ _ (fun y : Y => (y, S (count f))))).
  { rewrite <- arr_distr. cbn.
    assert ((fun '(y, _) => (y, S (count f))) = (fun a : Y * unit => (fst a, S (count f)))).
    { extensionality y. destruct y. cbn. reflexivity. }
    rewrite H3. reflexivity. }
  rewrite H3, <- (comp_assoc (B * C * unit) (Y * unit) _ (Y * nat)), first_fst.
  rewrite !comp_assoc, <- (comp_assoc (B * C) (B * C * unit) _ (Y * nat)), <- arr_distr.
  cbn. rewrite arr_id, left_id. reflexivity.
Qed.  

End StaticallyCountable.
