{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Arrow.State.ArrowState where

import qualified Control.Monad.State as M
import qualified Control.Arrow.Freer.FreerChoiceArrow as C
import qualified Control.Arrow.Freer.FreerArrowFinal as F
import qualified Control.Arrow.Freer.FreerArrowSimple as S
import qualified Control.Arrow.Freer.FreerArrowOps as O
import qualified Control.Arrow.Freer.KleisliFreer as K
import qualified Control.Arrow.Freer.FreerArrowRouter as R
import qualified Control.Arrow.Freer.FreerChoiceArrowRouter as CR

import Control.Category
import Control.Arrow
import Control.Arrow.Freer.FreerArrow
import Control.Arrow.Freer.FreerChoiceArrow (FreerChoiceArrow)
import Control.Arrow.Freer.KleisliFreer     (KleisliFreer)
import Control.Monad.Freer.Sum1
import Control.Arrow.Freer.Sum2
import Control.Monad.State (State)
import Control.Monad.State.StateEff
import Data.Kind
import Data.Profunctor
import Prelude hiding (id, (.))

class Arrow a => ArrowState s a where
  get :: a b s
  put :: a s s

modify :: ArrowState s a => (s -> b -> s) -> a b s 
modify f = arr (\b -> (b, b)) >>> first get >>> arr (uncurry f)

newtype StateA s a b = StateA { unStateA :: Kleisli (State s) a b }
  deriving (Category, Arrow, ArrowChoice, ArrowApply, Profunctor, Strong, Choice)

-- |- StateA is an ArrowState
instance ArrowState s (StateA s) where
  get = StateA $ Kleisli $ const M.get
  put = StateA $ Kleisli $ \s -> M.put s >> return s

-- |- A freer arrow is an ArrowState.
instance Inj2 (StateEff s) e => ArrowState s (FreerArrow e) where
  get = embed $ inj2 Get
  put = embed $ inj2 Put

instance Inj2 (StateEff s) e => ArrowState s (F.FreerArrow e) where
  get = F.embed $ inj2 Get
  put = F.embed $ inj2 Put

instance Inj2 (StateEff s) e => ArrowState s (S.FreerArrow e) where
  get = S.embed $ inj2 Get
  put = S.embed $ inj2 Put

instance Inj2 (StateEff s) e => ArrowState s (O.FreerArrowOps e) where
  get = O.embed $ inj2 Get
  put = O.embed $ inj2 Put

instance Inj2 (StateEff s) e => ArrowState s (R.FreerArrow e) where
  get = R.embed $ inj2 Get
  put = R.embed $ inj2 Put

instance Inj2 (StateEff s) e => ArrowState s (CR.FreerArrow e) where
  get = CR.embed $ inj2 Get
  put = CR.embed $ inj2 Put

instance Inj2 (StateEff s) e => ArrowState s (FreerChoiceArrow e) where
  get = C.embed $ inj2 Get
  put = C.embed $ inj2 Put

instance Inj1 (StateEff1 s) e => ArrowState s (KleisliFreer e) where
  get = K.embed $ const $ inj1 Get1
  put = K.embed $ inj1 . Put1

-- |- An ADT for stateful effect.
data StateEff :: Type -> Type -> Type -> Type where
  Get :: StateEff s a s
  Put :: StateEff s s s

handleState :: ArrowState s a => StateEff s x y -> a x y
handleState Get = get
handleState Put = put
