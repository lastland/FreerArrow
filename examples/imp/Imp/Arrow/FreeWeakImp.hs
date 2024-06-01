{-# LANGUAGE FlexibleContexts #-}

module Imp.Arrow.FreeWeakImp where

import Control.Arrow
import Control.Arrow.Freer.FreerArrow
import Control.Arrow.Freer.Sum2
import Control.Arrow.State.ArrowState
import Data.Profunctor
import Data.Map
import Imp.AST

type Env = Map Var Int

aeval :: Inj2 (StateEff Env) e => AExp -> FreerArrow e a Int
aeval (ANum n) = arr $ const n 
aeval (AId v)  = get >>> arr (findWithDefault 0 v)
aeval (APlus  a b) = aeval a &&& aeval b >>> arr (uncurry (+))
aeval (AMinus a b) = aeval a &&& aeval b >>> arr (uncurry (-))
aeval (AMult  a b) = aeval a &&& aeval b >>> arr (uncurry (*))

beval :: Inj2 (StateEff Env) e => BExp -> FreerArrow e a Bool
beval BTrue  = arr $ const True
beval BFalse = arr $ const False
beval (BEq  a b) = aeval a &&& aeval b >>> arr (uncurry (==))
beval (BNeq a b) = aeval a &&& aeval b >>> arr (uncurry (/=))
beval (BLe  a b) = aeval a &&& aeval b >>> arr (uncurry (<=))
beval (BGt  a b) = aeval a &&& aeval b >>> arr (uncurry (>))
beval (BNot a) = beval a >>> arr not
beval (BAnd a b) = beval a &&& beval b >>> arr (uncurry (&&))

denote :: Inj2 (StateEff Env) e => Com' -> FreerArrow e a ()
denote CSkip' = arr $ const ()
denote (CAssign' v a) = aeval a &&& get >>>
                       arr (uncurry $ insert v) >>>
                       put >>> arr (const ())
denote (CSeq' a b) = denote a >>> denote b

compileWeakImp :: (Profunctor a, ArrowState Env a) =>
  FreerArrow (StateEff Env) x y -> a x y 
compileWeakImp = interp handleState
