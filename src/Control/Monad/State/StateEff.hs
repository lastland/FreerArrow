{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Control.Monad.State.StateEff where

import Control.Monad.State
import Data.Kind

data StateEff1 :: Type -> Type -> Type where
  Get1 :: StateEff1 s s
  Put1 :: s -> StateEff1 s s  

handleState1 :: MonadState s m => StateEff1 s a -> m a 
handleState1 Get1 = get
handleState1 (Put1 x) = put x >> return x
