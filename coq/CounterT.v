Require Import Coq.Classes.Equivalence.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
From FreerArrows Require Import Classes.
From Hammer Require Import Tactics.

Open Scope type_scope.

Definition CounterT (I : Type -> Type -> Type)  :=
  fun x y => I x (y * nat). 

Instance Profunctor__CounterT {I} `{Profunctor I} : Profunctor (CounterT I) | 100 :=
  {| dimap := fun _ _ _ _ f g x => dimap f (fun '(y, n) => (g y, n)) x |}.

Instance StrongProfunctor__CounterT {I} `{HS: StrongProfunctor I} : StrongProfunctor (CounterT I) | 100 :=
  {| first := fun _ _ C a => dimap (fun x => x) (fun '(x, n, y) => (x, y, n)) (@first _ _ HS _ _ C a) |}.

Instance Category__CounterT {I} `{StrongProfunctor I} {HC : Category I} : Category (CounterT I) | 100 :=
  {| id := fun _ => dimap (fun x => x) (fun y => (y, 0)) id ;
     comp := fun _ _ _ x y => dimap (fun x => x) (fun '(y, n1, n2) => (y, (n1 + n2)%nat)) (@comp I HC _ _ _ x (first y)) |}.

Instance PreArrow__CounterT {I} `{StrongProfunctor I} {HC : Category I} `{PreArrow I} : PreArrow (CounterT I) | 100 :=
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

    Hint Unfold arr : counterT.
    
    Instance PreArrowLaws__CounterT : PreArrowLaws (CounterT I) (@eqC).
    Proof.
      constructor.
      - (* arr_id *)
        destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *. cbn.
        intros. rewrite !dimap_arr_comp.
        rewrite arr_id, !left_id. reflexivity.
      - (* arr_distr *)
        destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *. cbn.
        intros. rewrite !dimap_arr_comp.
        rewrite arr_id, !left_id.
        rewrite !comp_assoc, <- !arr_distr, !first_arr. cbn.
        repeat (rewrite <- comp_assoc, <- arr_distr).
        rewrite <- arr_distr. cbn. reflexivity.
    Qed.

    Instance Rigidity__CounterT : Rigidity (CounterT I) (@eqC).
    Proof.
      constructor.
      destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
      autounfold with counterT in *. cbn.
      intros. rewrite !dimap_arr_comp, !comp_assoc.
      rewrite <- !arr_distr.
      rewrite !arr_id, !left_id.
      rewrite !first_distr, !first_arr; cbn.
      rewrite !comp_assoc.
      repeat (rewrite <- comp_assoc, <- arr_distr).
      assert ((arr X (A * nat) (fun a : X => (f a, 0))) ≈
              comp _ _ _ (arr X A f)
              (comp _ _ _ (arr A (A * unit) (fun x => (x, tt)))
                 (arr (A * unit) (A * nat) (@parMul (fun A B => A -> B) A A unit nat _ _ _ _ _ (fun x => x) (fun _ => 0))))).
      { rewrite <- !comp_assoc, <- !arr_distr.
        cbn. reflexivity. }
      rewrite H0. rewrite !comp_assoc.
      rewrite <- (comp_assoc (A * unit) (A * nat) _ (Y * nat)), <- first_and.
      rewrite !comp_assoc. repeat (rewrite <- comp_assoc, <- arr_distr).
      remember (fun a : B * nat * unit => _) as func.
      assert (func = (fun '(y, n, _) => (g y, n))).
      { subst. extensionality a.
        destruct a as [[? ?] ?]. cbn.
        f_equal. lia. }
      rewrite H1.
      assert (arr (B * nat * unit) (Y * nat) (fun '(y, n, _) => (g y, n)) ≈
                comp _ _ _ (arr _ _ fst) (arr (B * nat) (Y * nat) (fun '(y, n) => (g y, n)))).
      { rewrite <- arr_distr. cbn.
        assert ((fun '(y, n, _) => (g y, n)) = (fun a : B * nat * unit => let '(y, n) := fst a in (g y, n))).
        { extensionality a. destruct a as [[? ?] ?]. cbn. reflexivity. }
        rewrite H2. reflexivity. }
      rewrite H2. rewrite <- (comp_assoc (A * unit) (B * nat * unit) _ (Y * nat)), first_fst.
      rewrite !comp_assoc. rewrite <- (comp_assoc X (A * unit) _ (Y * nat)), <- arr_distr.
      cbn. reflexivity.
    Qed.

    Hint Unfold first : counterT.
    
    Instance ArrowLaws__CounterT : ArrowLaws (CounterT I) (@eqC).
    Proof.
      constructor.
      - (* first_arr *)
        destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *. cbn.
        intros. rewrite !dimap_arr_comp, !first_distr, !first_arr. cbn.
        repeat (rewrite <- comp_assoc, <- arr_distr).
        rewrite <- !arr_distr. cbn.
        assert ((fun a : A * C => let '(x, n, y) := let '(a0, c) := let '(a0, c) := a in (f a0, c) in (a0, 0, c) in (x, y, n)) =
                  (fun a : A * C => (let '(a0, c) := a in (f a0, c), 0))).
        { extensionality a. destruct a. reflexivity. }
        rewrite H0. reflexivity.
      - (* first_distr *)
        destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *. cbn.
        intros. rewrite !dimap_arr_comp, !first_distr, !first_arr. cbn.
        rewrite !comp_assoc, !arr_id, !left_id.
        repeat (rewrite <- comp_assoc, <- arr_distr).
        assert (Hac: ((fun '(a, c) => (a, c))) = (fun a : A * D => a)).
        { extensionality a. destruct a. reflexivity. }
        rewrite !Hac, !comp_assoc, !arr_id, !left_id.
        replace (fun '(a, c) => (a, c)) with (fun a : B * nat * D => a).
        2: { extensionality a. destruct a. reflexivity. }
        rewrite ?comp_assoc, !arr_id, !left_id.
        rewrite <- (comp_assoc (B * nat * D) (B * D * nat) _ (C * D * nat)).
        rewrite <- arr_distr.
        remember (fun a : C * nat * nat * D => _) as func1.
        remember (fun a : C * nat * D * nat => _) as func2.
        assert (Hfunc1 : func1 = fun '(c, n1, n2, d) => (c, d, (n2 + n1)%nat)).
        { subst. extensionality a. destruct a as [[[? ?] ?] ?]. reflexivity. }
        assert (Hfunc2 : func2 = fun '(c, n1, d, n2) => (c, d, (n2 + n1)%nat)).
        { subst. extensionality a. destruct a as [[[? ?] ?] ?]. reflexivity. }
        rewrite Hfunc1, Hfunc2.
        assert ((arr (C * nat * nat * D) (C * D * nat) (fun '(c, n1, n2, d) => (c, d, (n2 + n1)%nat))) ≈
               comp _ _ _ (arr _ _ assoc) (arr _ _ (fun '(c, n1, (n2, d)) => (c, d, (n2 + n1)%nat)))).
        {
          rewrite <- arr_distr.
          assert ((fun '(c, n1, n2, d) => (c, d, (n2 + n1)%nat)) =
                 (fun a : C * nat * nat * D => let '(c, n1, (n2, d)) := assoc a in (c, d, (n2 + n1)%nat))).
          { extensionality a. destruct a as [[[? ?] ?] ?].
            cbn. reflexivity. }
          rewrite H0. reflexivity. }
        rewrite H0, <- (comp_assoc (B * nat * D) (C * nat * nat * D) _ (C * D * nat)), first_first.
        assert ((arr (C * nat * D * nat) (C * D * nat) (fun '(c, n1, d, n2) => (c, d, (n2 + n1)%nat))) ≈
               comp _ _ _ (arr _ _ assoc) (arr _ _ (fun '(c, n1, (d, n2)) => (c, d, (n2 + n1)%nat)))).
        { rewrite <- arr_distr.
          assert ((fun '(c, n1, d, n2) => (c, d, (n2 + n1)%nat)) =
                 (fun a : C * nat * D * nat => let '(c, n1, (d, n2)) := assoc a in (c, d, (n2 + n1)%nat))).
          { extensionality a. destruct a as [[[? ?] ?] ?].
            cbn. reflexivity. }
          rewrite H1. reflexivity. }
        rewrite H1, <- (comp_assoc (B * D * nat) (C * nat * D * nat) _ (C * D * nat)), first_first.
        rewrite !comp_assoc, <- (comp_assoc (B * nat * D) (B * D * nat) _ (C * D * nat)), <- arr_distr.
        assert ((arr (B * nat * D) (B * (D * nat))
                   (fun a : B * nat * D => assoc (let '(a0, c) := let '(x, n, y) := a in (x, y, n) in (a0, c)))) ≈
                comp _ _ _ (arr _ _ assoc) (arr _ _ (fun '(b, (n, d)) => (b, (d, n))))).
        { rewrite <- arr_distr.
          assert ((fun a : B * nat * D => assoc (let '(a0, c) := let '(x, n, y) := a in (x, y, n) in (a0, c))) =
                    (fun a : B * nat * D => let '(b, (n, d)) := assoc a in (b, (d, n)))).
          { extensionality a. destruct a as [[? ?] ?]. cbn. reflexivity. }
          rewrite H2. reflexivity. }
        rewrite H2.
        assert ((fun '(b, (n, d)) => (b, (d, n))) =
                (@parMul _ B B (nat * D) (D * nat) _ _ _ _ _ (fun x : B => x) (fun '((n, d) : (nat * D)) => (d, n)))).
        { cbn. extensionality a. destruct a as [? [? ?]].
          cbn. reflexivity. }
        rewrite H3, !comp_assoc, <- (comp_assoc (B * (nat * D)) (B * (D * nat)) _ (C * D * nat)).
        rewrite <- first_and, !comp_assoc, <- arr_distr. cbn.
        assert ((fun a : C * nat * (nat * D) =>
                let
                '(c, n1, (d, n2)) :=
                 swap (let '(a0, c) := swap (let '(a0, c) := a in (a0, c)) in (let '(n, d) := a0 in (d, n), c)) in
                 (c, d, (n2 + n1)%nat)) = (fun '(c, n1, (n2, d)) => (c, d, (n2 + n1)%nat))).
        { extensionality a. destruct a as [[? ?] [? ?]]. cbn. reflexivity. }
        rewrite H4. reflexivity.
      - (* first_fst *)
        destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *. cbn.
        intros. rewrite !dimap_arr_comp, !first_distr, !first_arr. cbn.
        rewrite !comp_assoc, !arr_id, !left_id.
        repeat (rewrite <- comp_assoc, <- arr_distr).
        rewrite !comp_assoc.
        repeat (rewrite <- comp_assoc, <- arr_distr).
        rewrite !comp_assoc. rewrite <- arr_distr.
        assert ((fun a : B * nat * C =>
                   let
                     '(y, n1, n2) :=
                     let
                       '(x, n, y) := let '(a0, c) := let '(a0, c) := let '(x, n, y) := a in (x, y, n) in (fst a0, c) in (a0, 0, c) in
                     (x, y, n) in (y, (n1 + n2)%nat)) = fst).
        { extensionality a. destruct a as [[? ?] ?]. cbn. f_equal. lia. }
        rewrite H0.
        assert ((fun a : A * C => (fst a, 0)) =
                  @parMul _ A A C nat _ _ _ _ _ (fun x : A => x) (fun _ : C => 0)).
        { extensionality a. destruct a. cbn. reflexivity. }
        rewrite H1, <- (comp_assoc (A * C) (A * nat) _ (B * nat)), <- first_and, !comp_assoc, <- arr_distr.
        assert ((fun a : B * nat * C =>
                   let
                     '(y, n1, n2) := let '(x, n, y) :=
                                       (@parMul (fun A B => A -> B) (B * nat) (B * nat) C nat _ _ _ _ _ (fun x : B * nat => x) (fun _ : C => 0)) a in (x, y, n) in
                   (y, (n1 + n2)%nat)) = fst).
        { extensionality a. destruct a as [[? ?] ?]. cbn. reflexivity. }
        (* Odd. *) unfold Category__Fun in H2. rewrite H2. reflexivity.
      - (* first_and *)
        destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *. cbn.
        intros. rewrite !dimap_arr_comp, !first_distr, !first_arr. cbn. 
        repeat (rewrite <- comp_assoc, <- arr_distr).
        rewrite !comp_assoc. rewrite <- !arr_distr.
        assert ((arr (B * nat * Y * nat) (B * Y * nat)
                     (fun a : B * nat * Y * nat =>
                      let
                      '(y, n1, n2) :=
                       let '(x, n, y) := let '(a0, c) := a in (let '(x, n, y) := a0 in (x, y, n), c) in (x, y, n) in
                       (y, (n1 + n2)%nat))) ≈
                 comp _ _ _ (arr _ _ assoc) (arr _ _ (fun '(b, n1, (y, n2)) => (b, y, (n2 + n1)%nat)))).
        { rewrite <- arr_distr.
          assert ((fun a : B * nat * Y * nat =>
                     let
                       '(y, n1, n2) := let '(x, n, y) := let '(a0, c) := a in (let '(x, n, y) := a0 in (x, y, n), c) in (x, y, n) in
                     (y, (n1 + n2)%nat)) =
                    (fun a : B * nat * Y * nat => let '(b, n1, (y, n2)) := assoc a in (b, y, (n2 + n1)%nat))).
          { extensionality a. destruct a as [[[? ?] ?] ?]. cbn. reflexivity. }
          rewrite H0. reflexivity. }
        rewrite H0, <- (comp_assoc (A * Y * nat) (B * nat * Y * nat) _ (B * Y * nat)), first_first, !comp_assoc.
        rewrite <- (comp_assoc (A * X) (A * X) (A * Y * nat) (B * Y * nat)), <- arr_distr.
        rewrite <- (comp_assoc (A * X) (A * Y * nat) (A * Y * nat) (B * Y * nat)), <- arr_distr.
        rewrite <- (comp_assoc (A * X) (A * Y * nat) (A * Y * nat) (B * Y * nat)), <- arr_distr.
        rewrite <- (comp_assoc (A * X) (A * Y * nat) (A * (Y * nat)) (B * Y * nat)), <- arr_distr.
        assert ((fun a : A * X => assoc (swap (let '(a0, c) := swap (let '(a0, c) := a in (a0, c)) in (g a0, c)), 0)) =
               (fun '(a, x) => (a, (g x, 0)))).
        { extensionality a. destruct a. cbn. reflexivity. }
        rewrite H1.
        assert ((fun '(a, x) => (a, (g x, 0))) =
                  @parMul _ A A X (Y * nat) _ _ _ _ _ (fun a => a) (fun x => (g x, 0))).
        { extensionality a. destruct a. cbn. reflexivity. }
        rewrite H2, <- (comp_assoc (A * X) (A * (Y * nat)) _ (B * Y * nat)), <- first_and.
        rewrite !comp_assoc, <- arr_distr, arr_id, left_id.
        remember (fun a : B * nat * X => _) as func. cbn.
        assert (func = (fun a : B * nat * X =>
                          let
                            '(b, n1, (y, n2)) := swap (let '(a0, c) := swap (let '(a0, c) := a in (a0, c)) in (g a0, 0, c)) in
                          (b, y, (n2 + n1)%nat))).
        { extensionality a. subst. destruct a as [[? ?] ?]. cbn. f_equal. lia. }
        rewrite <- H3. reflexivity. 
      - (* first_first *)
        destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *. cbn.
        intros. rewrite !dimap_arr_comp, !first_distr, !first_arr. cbn.
        rewrite !arr_id, !left_id, !comp_assoc, <- !arr_distr.
        remember (fun a : B * nat * Y * X => _) as func1.
        assert (func1 = (fun '(b, n, y, x) => (b, (y, x), n))).
        { subst. extensionality a. destruct a as [[[? ?] ?] ?].
          cbn. f_equal. lia. }
        rewrite H0. clear H0. clear Heqfunc1. clear func1.
        remember (fun a : B * nat * (Y * X) * nat => _) as func2.
        assert (func2 = (fun '(b, n1, (y, x), n2) => (b, (y, x), (n2 + n1)%nat))).
        { subst. extensionality a. destruct a as [[[? ?] [? ?]] ?].
          cbn. reflexivity. }
        rewrite H0. clear H0. clear Heqfunc2. clear func2.
        remember (fun a : B * nat * Y * X => _) as func1.
        remember (fun a : B * nat * (Y * X) * nat => _) as func2.
        assert (arr _ _ func1 ≈ comp _ _ _ (arr _ _ assoc) (arr _ _ (fun '(b, n, (y, x)) => (b, (y, x), n)))).
        { rewrite <- arr_distr.
          assert (func1 = (fun a : B * nat * Y * X => let '(b, n, (y, x)) := assoc a in (b, (y, x), n))).
          { extensionality a. subst. destruct a as [[[? ?] ?] ?]. cbn. reflexivity. }
          rewrite <- H0. reflexivity. }
        rewrite H0, <- (comp_assoc (A * Y * X) (B * nat * Y * X) _ (B * (Y * X) * nat)), first_first.
        rewrite !comp_assoc.
        replace (fun '((a, c) : A * Y * X) => (a, c)) with (fun a : A * Y * X => a).
        2: { extensionality a. destruct a as [[? ?] ?]. reflexivity. }
        rewrite arr_id, left_id.
        assert (arr _ _ func2 ≈ comp _ _ _ (arr _ _ assoc) (arr _ _ (fun '(b, n1, ((y, x), n2)) =>
                                                                       (b, (y, x), (n2 + n1)%nat)))).
        { rewrite <- arr_distr.
          assert (func2 = (fun a : B * nat * (Y * X) * nat => let '(b, n1, (y, x, n2)) := assoc a in (b, (y, x), (n2 + n1)%nat))).
          { extensionality a. subst. destruct a as [[[? ?] [? ?]] ?].
            cbn. reflexivity. }
          rewrite <- H1. reflexivity. }               
        rewrite H1, <- (comp_assoc (A * (Y * X) * nat) (B * nat * (Y * X) * nat) _ (B * (Y * X) * nat)), first_first.
        rewrite !comp_assoc.
        rewrite <- (comp_assoc (A * (Y * X)) (A * (Y * X) * nat) _ (B * (Y * X) * nat)), <- arr_distr.
        rewrite <- (comp_assoc (A * (Y * X)) (A * (Y * X) * nat) _ (B * (Y * X) * nat)), <- arr_distr.
        assert ((fun a : A * (Y * X) => assoc (a, 0)) =
                  @parMul _ A A (Y * X) (Y * X * nat) _ _ _ _ _ (fun x : A => x) (fun '((y, x) : Y * X) => ((y, x), 0))).
        { extensionality a. destruct a as [? [? ?]]. cbn. reflexivity. }
        rewrite H2. rewrite <- (comp_assoc (A * (Y * X)) (A * (Y * X * nat)) _ (B * (Y * X) * nat)), <- first_and.
        rewrite !comp_assoc, <- arr_distr. cbn.
        assert ((fun '(b, n, (y, x)) => (b, (y, x), n)) = (fun a : B * nat * (Y * X) =>
                                                          let
                                                            '(b, n1, (y, x, n2)) :=
                                                            swap (let '(a0, c) := swap (let '(a0, c) := a in (a0, c)) in (let '(y, x) := a0 in (y, x, 0), c)) in
                                                          (b, (y, x), (n2 + n1)%nat))).
        { extensionality a. destruct a as [[? ?] [? ?]]. cbn. reflexivity. }
        rewrite <- H3. reflexivity.
      - (* first_proper *)
        destruct HP, HC, Hstrong, HPre, HL, HCL, HPL, HR, HAL.
        autounfold with counterT in *. cbn.
        intros. intros x1 x2 Heqx. rewrite !dimap_arr_comp. rewrite Heqx. reflexivity.
    Qed.
        
End CounterTLaws.
