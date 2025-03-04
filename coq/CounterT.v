From FreerArrows Require Import Classes.

Open Scope type_scope.

Definition CounterT (I : Type -> Type -> Type)  :=
  fun x y => I x (y * nat). 

Instance Profunctor__CounterT {I} `{Profunctor I} : Profunctor (CounterT I) :=
  {| dimap := fun _ _ _ _ f g x => dimap f (fun '(y, n) => (g y, n)) x |}.

Instance StrongProfunctor__CounterT {I} `{HS: StrongProfunctor I} : StrongProfunctor (CounterT I) :=
  {| first := fun _ _ C a => dimap (fun x => x) (fun '(x, n, y) => (x, y, n)) (@first _ _ HS _ _ C a) |}.

Instance Category__CounterT {I} `{StrongProfunctor I} {HC : Category I} : Category (CounterT I) :=
  {| id := fun _ => dimap (fun x => x) (fun y => (y, 0)) id ;
     comp := fun _ _ _ x y => dimap (fun x => x) (fun '(y, n1, n2) => (y, (n1 + n2)%nat)) (@comp I HC _ _ _ x (first y)) |}.

Instance PreArrow__CounterT {I} `{StrongProfunctor I} {HC : Category I} `{PreArrow I} : PreArrow (CounterT I) :=
  {| arr := fun _ _ f => @comp I HC _ _ _ (arr f) (arr (fun y => (y, 0))) |}.

Definition tick {I X Y} `{Arrow I} (i : I X Y) : CounterT I X Y :=
  dimap (fun x => x) (fun y => (y, 1)) i.
