Section ID.
  Context {X : Type}.
  
  Theorem id_idem : forall (x : X),
      id (id x) = x.
  Proof. intros. reflexivity. Qed.
End ID.

Locate id.

Definition parFun {X Y A B} (f : X -> Y) (g : A -> B) : X * A -> Y * B :=
  fun '(x, a) => (f x, g a).

Definition parFunOr {X Y A B} (f : X -> Y) (g : A -> B) (x : X + A) : Y + B :=
  match x with
  | inl x => inl (f x)
  | inr a => inr (g a)
  end.
