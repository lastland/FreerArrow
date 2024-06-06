{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}

-- |- This is a version of [MonadState] with no functional dependency.
module Control.Monad.State.MonadState where

import qualified Control.Monad.State                 as S
import qualified Control.Monad.Freer.FreerMonad      as M
import qualified Control.Monad.Freer.FreerMonadFinal as F

import Control.Monad.Freer.Sum1
import Control.Monad.State.StateEff

class Monad m => MonadState s m where
  get :: m s
  put :: s -> m s

modify :: MonadState s m => (s -> a -> s) -> a -> m s
modify f a = do
  s <- get
  put (f s a)

{--
instance S.MonadState s m => MonadState s m where
  get   = S.get
  put x = S.put x >> return x
--}
    
instance Inj1 (StateEff1 s) e => MonadState s (M.FreerMonad e) where
  get   = M.embed $ inj1 Get1
  put x = M.embed $ inj1 (Put1 x)

instance Inj1 (StateEff1 s) e => MonadState s (F.FreerMonad e) where
  get   = F.embed $ inj1 Get1
  put x = F.embed $ inj1 (Put1 x)
