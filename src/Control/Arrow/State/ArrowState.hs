{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Arrow.State.ArrowState where

import qualified Control.Monad.State as M
import Control.Arrow
import Control.Arrow.Freer.FreerArrow
import Control.Arrow.Freer.Sum2
import Control.Monad.State (State)
import Data.Kind

class Arrow a => ArrowState s a where
  get :: a b s
  put :: a s s

modify :: ArrowState s a => (s -> b -> s) -> a b s 
modify f = arr (\b -> (b, b)) >>> first get >>> arr (uncurry f)

-- |- State is an ArrowState
instance ArrowState s (Kleisli (State s)) where
  get = Kleisli $ const M.get
  put = Kleisli $ \s -> M.put s >> return s

-- |- A freer arrow is an ArrowState.
instance Inj2 (StateEff s) e => ArrowState s (FreerArrow e) where
  get = embed $ inj2 Get
  put = embed $ inj2 Put

-- |- An ADT for stateful effect.
data StateEff :: Type -> Type -> Type -> Type where
  Get :: StateEff s a s
  Put :: StateEff s s s

handleState :: ArrowState s a => StateEff s x y -> a x y
handleState Get = get
handleState Put = put
