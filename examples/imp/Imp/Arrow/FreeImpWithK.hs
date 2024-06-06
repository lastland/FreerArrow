{-# LANGUAGE FlexibleContexts #-}

module Imp.Arrow.FreeImpWithK where

import Control.Arrow
import Control.Arrow.Freer.KleisliFreer
import Control.Arrow.State.ArrowState
import Control.Monad.Freer.Sum1
import Control.Monad.State (MonadState)
import Control.Monad.State.StateEff
import Data.Map
import Imp.AST

type Env = Map Var Int

aeval :: Inj1 (StateEff1 Env) e => AExp -> KleisliFreer e a Int
aeval (ANum n) = arr $ const n 
aeval (AId v)  = get >>> arr (findWithDefault 0 v)
aeval (APlus  a b) = aeval a &&& aeval b >>> arr (uncurry (+))
aeval (AMinus a b) = aeval a &&& aeval b >>> arr (uncurry (-))
aeval (AMult  a b) = aeval a &&& aeval b >>> arr (uncurry (*))

beval :: Inj1 (StateEff1 Env) e => BExp -> KleisliFreer e a Bool
beval BTrue  = arr $ const True
beval BFalse = arr $ const False
beval (BEq  a b) = aeval a &&& aeval b >>> arr (uncurry (==))
beval (BNeq a b) = aeval a &&& aeval b >>> arr (uncurry (/=))
beval (BLe  a b) = aeval a &&& aeval b >>> arr (uncurry (<=))
beval (BGt  a b) = aeval a &&& aeval b >>> arr (uncurry (>))
beval (BNot a) = beval a >>> arr not
beval (BAnd a b) = beval a &&& beval b >>> arr (uncurry (&&))

denote :: Inj1 (StateEff1 Env) e => Com -> KleisliFreer e a ()
denote CSkip         = arr $ const ()
denote (CAssign v a) = aeval a &&& get >>>
                       arr (uncurry $ insert v) >>>
                       put >>> arr (const ())
denote (CSeq a b)    = denote a >>> denote b
denote (CIf c x y)   = beval c >>>
                       arr (\b -> if b then Left () else Right ()) >>>
                       denote x ||| denote y
denote (CWhile c x)  = beval c >>>
                       arr (\b -> if b then Left () else Right ()) >>>
                       (denote x >>> denote (CWhile c x)) ||| arr (const ())

compileImp :: MonadState Env m => KleisliFreer (StateEff1 Env) x y -> x -> m y
compileImp f = case interp handleState1 f of
                 Kleisli g -> g
