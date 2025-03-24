Require Import Coq.Classes.Equivalence.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
From FreerArrows Require Import Classes.
From Hammer Require Import Hammer Tactics.

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
        autounfold with counterT in *.  
        specialize (dimap_distr A (B * nat) X (Y * nat) V (W * nat) f g (first h) (first i) x).
        unfold first in dimap_distr. cbn in dimap_distr.
        etransitivity; [ | apply dimap_distr].
        assert ((fun '(y, n) => (h (i y), n)) = (fun x0 : B * nat => let '(a, c) := let '(a, c) := x0 in (i a, c) in (h a, c))).
        { sauto use: functional_extensionality. }
        rewrite H0. reflexivity.
    Qed.

    (** Pre-arrow laws. *)
    Context {HC : Category I} {HPre : @PreArrow I HC} {Hstrong: @StrongProfunctor I HP} {HA: @Arrow I _ _ _ _}.
    Context {HCL : @CategoryLaws I (@eq) HC} {HPL: @PreArrowLaws I (@eq) HC HPre}.
    Context {HR : @Rigidity I (@eq) _ _ _} {HAL: @ArrowLaws I (@eq) _ _ _ _}.

    Hint Unfold comp id first Category__CounterT StrongProfunctor__CounterT Category__Fun : counterT.
    
    Instance CategoryLawsCounterT : CategoryLaws (CounterT I) (@eqC).
    Proof.
      constructor.
      - (* left_id *)
        destruct HP, HC, Hstrong, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *.
        intros. unfold CounterT in f.
        rewrite !dimap_arr_comp, !arr_id, !left_id, !comp_assoc.
        assert (@arr I _ HPre _ _ ((fun y : A => (y, 0))) ≈
                  comp _ _ _ (@arr I _ HPre _ _ (fun x => (x, tt))) 
                  (@arr I _ HPre _ _ (@parMul (fun A B => A -> B) A A unit nat _ _ _ _ _ (fun x : A => x) (fun _ : unit => 0)))).
        { autounfold with counterT. rewrite <- arr_distr. cbn. reflexivity. }
        rewrite H0. rewrite !comp_assoc.
        rewrite <- (comp_assoc (A * unit) (A * nat) (B * nat * nat) (B * nat)).
        rewrite <- first_and. rewrite !comp_assoc.
        rewrite <- !arr_distr.
        remember (fun a : B * nat * unit => _) as func.
        assert (func = fst) as Hfinal.
        { rewrite Heqfunc. extensionality a. fcrush. }
        rewrite Hfinal. rewrite first_fst.
        rewrite <- comp_assoc. rewrite <- arr_distr. cbn.
        rewrite arr_id. apply left_id.
      - (* right_id *)
        destruct HP, HC, Hstrong, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *.
        intros. unfold CounterT in f.
        rewrite !dimap_arr_comp, !arr_id, !left_id, !comp_assoc.
        rewrite first_arr. cbn. rewrite <- !arr_distr.
        remember (fun a : B * nat => _) as func.
        assert (func = fun x => x) as Hfinal.
        { rewrite Heqfunc. extensionality a. sauto. }
        rewrite Hfinal. rewrite arr_id. apply right_id.
      - (* comp_assoc *)
        destruct HP, HC, Hstrong, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *.
        intros. unfold CounterT in f.
        rewrite !dimap_arr_comp.
        (* Weird that I need all these. *)
        rewrite (dimap_arr_comp A (Y * nat * nat) A (Y * nat)),
          (dimap_arr_comp (B * nat) (Y * nat * nat) (B * nat) (Y * nat * nat)),
          (dimap_arr_comp B (Y * nat * nat) B (Y * nat)),
          (dimap_arr_comp (C * nat) (Y * nat * nat) (C * nat) (Y * nat * nat)).
        rewrite !arr_id, !left_id, !comp_assoc.
        rewrite <- !arr_distr.
        remember (fun a : Y * nat * nat => _) as funcY.
        rewrite !first_distr, !first_arr. cbn.
        rewrite <- (comp_assoc (C * nat * nat) (C * nat * nat) _ (Y * nat)).
        rewrite <- arr_distr.
        remember (fun a : C * nat * nat => _) as funcC.
        assert (@arr I _ HPre _ _ funcC ≈
                  comp _ _ _ (@arr I _ HPre _ _ assoc) 
                  (@arr I _ HPre _ _ (@parMul (fun A B => A -> B) C C (nat * nat) nat _ _ _ _ _ (fun x => x) (fun '(n1, n2) => (n2 + n1)%nat)))).
        { rewrite <- arr_distr.
          remember (fun a : C * nat * nat => _ (assoc a)) as funcC2.
          assert (funcC = funcC2).
          { rewrite HeqfuncC, HeqfuncC2.
            extensionality a. destruct a as [[? ?] ?].
            cbn. reflexivity. }
          rewrite H0. reflexivity. }
        rewrite H0. rewrite !comp_assoc.
        rewrite <- (comp_assoc (C * (nat * nat)) (C * nat) _ (Y * nat)).
        rewrite <- first_and, !comp_assoc, <- !arr_distr.
        rewrite <- (comp_assoc (C * nat * nat) (C * (nat * nat)) _ (Y * nat)).
        rewrite <- first_first.
        rewrite !comp_assoc, <- !arr_distr.
        remember (fun a : Y * nat * nat * nat => _) as final1.
        remember (fun a : Y * nat * nat * nat => funcY (let '(a0, c) := a in (funcY a0, c))) as final2.
        assert (final1 = final2).
        { subst. extensionality a. destruct a as [[[? ?] ?] ?].
          cbn. f_equal. lia. }
        rewrite H1. reflexivity.
      - destruct HP, HC, Hstrong, HL, HCL, HPL, HR, HAL.
        intros. intros x1 x2 HeqC1 y1 y2 HeqC2.
        unfold CounterT, eqC in *.
        unfold ">>>". cbn.
        rewrite !dimap_arr_comp, !arr_id, !left_id.
        rewrite HeqC1, HeqC2. reflexivity.
    Qed.

    (** TODO: other laws.  *)

End CounterTLaws.
        
    
