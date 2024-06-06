{-# LANGUAGE RankNTypes  #-}
module Control.Monad.Freer.FreerMonadFinal where

import Control.Monad

newtype FreerMonad e r = FreerMonad {
  runFreer :: forall m. Monad m =>
              (forall x. e x -> m x) ->
              m r }

embed :: e x -> FreerMonad e x
embed e = FreerMonad ($ e)

instance Monad (FreerMonad e) where
  return             = pure
  FreerMonad m >>= k = FreerMonad $
    \h -> do
      x <- m h
      runFreer (k x) h

instance Applicative (FreerMonad e) where
  pure a = FreerMonad (const $ return a)
  (<*>)  = ap

instance Functor (FreerMonad e) where
  fmap = liftM
