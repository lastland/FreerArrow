{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.State.StateEff where

import Control.Monad.Freer.FreerMonad
import Control.Monad.Freer.Sum1
import Control.Monad.State
import Data.Kind

data StateEff :: Type -> Type -> Type where
  Get :: StateEff s s
  Put :: s -> StateEff s ()

