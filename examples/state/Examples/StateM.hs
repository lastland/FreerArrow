{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Examples.StateM where

import Control.Monad.Freer.FreerMonad
import Control.Monad.State.Class
import Data.Kind


data StateMEff :: Type -> Type -> Type where
  Get :: StateMEff s s
  Put :: s -> StateMEff s ()

instance MonadState s (FreerMonad (StateMEff s)) where
  get = embed Get
  put = embed . Put

handleState :: MonadState s m => StateMEff s a -> m a
handleState Get     = get
handleState (Put x) = put x
