Require Import Coq.Classes.Equivalence.
(* Assume functional extensionality for simplicity. *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.

From FreerArrows Require Import Common Tactics FreerArrow Classes.
From Hammer Require Import Hammer Tactics.

Open Scope type_scope.

Fixpoint count {E X Y} (f : FreerArrow E X Y) : nat :=
  match f with
  | Hom _ => 0
  | Comp _ _ x => 1 + count x
end.

Fixpoint interp {E X Y I} `{Arrow I}
                (handler : forall {A B}, E A B -> I A B)
                (f : FreerArrow E X Y) : (I X Y * nat) :=
    match f with
    | Hom f => (arr f, 0)
    | Comp f e x => let '(z, n) := interp (@handler) x in
        (comp (dimap f (fun x => x) (first (handler e))) z, (n + 1)%nat)
    end.


Theorem statically_countable {E X Y I} `{Arrow I}:
  forall (f : FreerArrow E X Y) (handler : forall {A B}, E A B -> I A B),
    count f = snd (interp (@handler) f).
Proof.
  induction f; cbn; [sfirstorder |].
  intros. specialize (IHf (@handler)).
  destruct (interp handler f); cbn in *.
  sfirstorder.
Qed.
 
