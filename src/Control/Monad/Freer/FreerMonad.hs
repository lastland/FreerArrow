{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE RankNTypes            #-}

module Control.Monad.Freer.FreerMonad where

import Control.Monad

data FreerMonad e r where
  Ret  :: r -> FreerMonad e r
  Bind :: e x -> (x -> FreerMonad e r) -> FreerMonad e r

embed :: e x -> FreerMonad e x
embed e = Bind e Ret 

instance Monad (FreerMonad e) where
  return     = pure
  Ret x    >>= k = k x
  Bind e f >>= k = Bind e (f >=> k)

instance Applicative (FreerMonad e) where
  pure = Ret
  (<*>) = ap

instance Functor (FreerMonad e) where
  fmap = liftM

interp :: Monad m =>
  (forall x. e x -> m x) -> FreerMonad e a -> m a
interp _       (Ret x)    = return x
interp handler (Bind e k) = handler e >>= interp handler . k

